/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Algorithm 5: the Fourier readout layer

Fixed arXiv:1010.4458v2, Algorithm 5 (Main algorithm) and the paragraph that
follows it (Section 4, "Main algorithm").  Step 3 of the algorithm applies
the halving map `|2j⟩_S ↦ |j⟩_S` to the step register, then the Fourier
transform `F_m`, and measures `S`; on outcome `0` it outputs the `I`
register.  The source derives:

* the Fourier transform "effectively erases the `S` register": conditional
  on measuring `0`, every branch's step-label contributes the same factor
  (`rootW^0 = 1` in the zero row), so the output state is the renormalized
  `I`-component sum;
* measuring produces `|0⟩_S` with probability `1/m`, so the success of
  Algorithm 5 needs amplification (the `√m·log(1/ε)` cost factor composed
  in `CostAssembly`).

This module formalizes the readout coefficients exactly: `readoutZeroEntry`
computes the zero-row of `fourierM m` (entries `exp(2πi·uv/m)/√m`), and
`idealErasure` evaluates both the zero-outcome mass `‖β‖²/m` — exactly
`1/m` for a normalized ideal state — and the zero block `β/√m` of an ideal
amplified state `∑ᵢ βᵢ |vᵢ⟩_I ⊗ |2 jᵢ⟩_S` (coefficients `βᵢ` on the `I`
register, halved step label `jᵢ` in `S`), independent of the labels `jᵢ`.

Not formalized here: the unitarity of `F_m` (root-of-unity orthogonality)
and the resulting total-mass preservation of the transform; the random
offsets `x₁,…,xₘ` making eigenvalue estimates unique (the source's
`E[δ] = O(ε)` bound); and the variable-time amplification producing the
ideal state.  Those remain inside the deferred source construction.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

open Complex

namespace Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.MainReadout

/-- The unit-normalizing scalar `1/√m` as a complex number. -/
def invSqrtM (m : ℕ) : ℂ := ((Real.sqrt (m : ℝ)) : ℂ)⁻¹

/-- The primitive `m`-th root of unity `exp(2πi/m)`. -/
def rootW (m : ℕ) : ℂ := exp ((2 * Real.pi * I) / (m : ℂ))

/-- The Fourier transform matrix `F_m` on `Fin m`: integer-power entries
`exp(2πi·uv/m)/√m` with unitary normalization. -/
def fourierM (m : ℕ) : Matrix (Fin m) (Fin m) ℂ := fun u v =>
  rootW m ^ ((u : ℤ) * (v : ℤ)) * invSqrtM m

/-- The readout map: apply the Fourier matrix to the `S` (column) index of a
joint `I × S` coefficient matrix. -/
def readout {d : ℕ} (m : ℕ) (A : Matrix (Fin d) (Fin m) ℂ) :
    Matrix (Fin d) (Fin m) ℂ := A * Matrix.transpose (fourierM m)

/-- The zero-outcome block of the readout: the amplitudes of the states with
`S` measured as `0`. -/
def zeroBlock {d : ℕ} (m : ℕ) [NeZero m] (A : Matrix (Fin d) (Fin m) ℂ) :
    Fin d → ℂ := fun i => readout m A i 0

/-- The zero row of the Fourier matrix is the uniform row: `rootW^0 = 1`
in every entry.  This is the phase-cancellation that "erases" the halved
step labels. -/
theorem fourierM_zero_row (m : ℕ) [NeZero m] (j : Fin m) :
    fourierM m (0 : Fin m) j = invSqrtM m := by
  show rootW m ^ (((0 : Fin m) : ℤ) * (j : ℤ)) * invSqrtM m = invSqrtM m
  simp only [Fin.val_zero, Nat.cast_zero, zero_mul, zpow_zero, one_mul]

/-- Reading out entry `0` sums the corresponding register row scaled by
`1/√m`: the halved step labels all contribute the same phase. -/
theorem readoutZeroEntry {d : ℕ} (m : ℕ) [NeZero m]
    (A : Matrix (Fin d) (Fin m) ℂ) (i : Fin d) :
    zeroBlock m A i = (∑ j, A i j) * invSqrtM m := by
  unfold zeroBlock readout
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, fourierM_zero_row m]
  rw [← Finset.sum_mul]

/-- The ideal amplified state of Algorithm 4/5: amplitude `βᵢ` on the `I`
basis state `i` and `S` in the halved step label `J i`. -/
def idealState {d : ℕ} (m : ℕ) (β : Fin d → ℂ) (J : Fin d → Fin m) :
    Matrix (Fin d) (Fin m) ℂ := fun i j => β i * (if j = J i then (1 : ℂ) else 0)

/-- For the ideal amplified state, the zero-outcome block is exactly
`β·(1/√m)`, independent of the step labels `J`, and the zero-outcome mass is
`‖β‖²/m` — exactly the source's `1/m` success probability when `β` is
normalized (total mass `1`). -/
theorem idealErasure {d : ℕ} (m : ℕ) [NeZero m] (β : Fin d → ℂ)
    (J : Fin d → Fin m) :
    (∑ i, Complex.normSq (zeroBlock m (idealState m β J) i))
      = (∑ i, Complex.normSq (β i)) * ((m : ℝ)⁻¹) ∧
      ∀ i, zeroBlock m (idealState m β J) i = β i * invSqrtM m := by
  have hrow : ∀ i : Fin d, ∑ j, idealState m β J i j = β i := by
    intro i
    unfold idealState
    rw [← Finset.mul_sum, Finset.sum_ite_eq', ite_eq_left (by simp), mul_one]
  have hz : ∀ i : Fin d, zeroBlock m (idealState m β J) i
      = β i * invSqrtM m := by
    intro i
    rw [readoutZeroEntry, hrow]
  constructor
  · have hns : ∀ i : Fin d, Complex.normSq (β i * invSqrtM m)
        = Complex.normSq (β i) * ((m : ℝ)⁻¹) := by
      intro i
      have h1 : Complex.normSq (β i * invSqrtM m)
          = Complex.normSq (β i) * Complex.normSq (invSqrtM m) :=
        Complex.normSq_mul _ _
      have h2 : Complex.normSq (invSqrtM m) = ((m : ℝ)⁻¹) := by
        have hreal : Complex.normSq (((Real.sqrt (m : ℝ)) : ℂ))
            = (m : ℝ) := by
          rw [Complex.normSq_ofReal, ← sq,
            Real.sq_sqrt (by positivity : (0:ℝ) ≤ (m:ℝ))]
        unfold invSqrtM
        rw [Complex.normSq_inv, hreal]
      rw [h1, h2]
    calc (∑ i, Complex.normSq (zeroBlock m (idealState m β J) i))
      = ∑ i, Complex.normSq (β i * invSqrtM m) :=
        Finset.sum_congr rfl (fun i _ => by rw [hz i])
    _ = ∑ i, (Complex.normSq (β i) * ((m : ℝ)⁻¹)) :=
        Finset.sum_congr rfl (fun i _ => hns i)
    _ = (∑ i, Complex.normSq (β i)) * ((m : ℝ)⁻¹) := by
        rw [← Finset.sum_mul]
  · intro i
    rw [readoutZeroEntry, hrow]

end Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.MainReadout
