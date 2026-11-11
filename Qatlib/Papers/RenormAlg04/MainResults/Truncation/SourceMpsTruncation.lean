/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetworkCoreDefs
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# SourceMpsTruncation — quadratic error functional and the linear site update

Fixed source: F. Verstraete and J. I. Cirac, *Renormalization algorithms for
Quantum-Many Body Systems in two and higher dimensions*, arXiv:cond-mat/0407066v1
(2 Jul 2004), pp. 2-3:

  "Given an unnormalized MPS `|ψ_A⟩` parameterized by `D × D` matrices `{A_k^s}`,
  the goal is to find another MPS `|ψ_B⟩` ... such that
  `K := ‖|ψ_A⟩ − |ψ_B⟩‖²` is minimal. ... The key insight is that `K` is quadratic
  in all components of the matrices `{B_k^s}`, and hence if all these matrices are
  fixed except one of them (say `B_j^s`) `K` is quadratic in the components of
  `B_j^s`; the optimal choice for `B_j^s` thus amounts to solving a trivial system
  of linear equations."

PDF SHA-256 `397e011bc798dbb6aa2d4bf93f6d2e666a12f77fd0655e1168d03037d0af4da7`.

Model: the open-chain amplitude `mpsAmplitude` of the frozen vocabulary (boundary
bond indices fixed at `0`).  `mpsUpdate B j M` replaces the whole physical family
`B_j^s` at site `j` by `M`.

Main results:
* `mpsAmplitude_update`, `mpsAmplitude_update_add`, `mpsAmplitude_update_smul`:
  the amplitude is an explicit sum of products in which the site-`j` family enters
  linearly — the "quadratic in `B`" structure.
* `truncationObjective_expansion`: `K` at `M` splits into the constant `K` at the
  zero family, the squared norm of the linear part, and the cross term; the linear
  part is linear in `M` (`linearPairing_add`, `linearPairing_smul`).
* `truncation_stationarity_is_linear_system`: stationarity of `K` at `M` is
  equivalent to a system of equations that is *linear* in `M` with a constant
  right-hand side — the explicit "trivial system of linear equations" of the source.

Boundary: single-site update only (no sweep schedule, no SVD/periodic variant);
the chain is nonempty (`NeZero n`) because `K` uses the amplitude as an affine
function of the site family, which needs the empty product to be handled separately.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Concepts.MpsAdaptation.MpsTransfer

namespace Qatlib.Papers.RenormAlg04.MainResults.Truncation

/-- Replace the physical matrix family `B_j^s` at site `j` by an arbitrary family
`M : Fin d → Matrix (Fin D) (Fin D) ℂ`; all other sites are kept. -/
def mpsUpdate {n d D : ℕ} (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ)
    (j : Fin n) (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ :=
  fun i s => if i = j then M s else B i s

/-- Source p. 3 (`K` quadratic in `B`): the amplitude with the site-`j` family
replaced by `M` is the sum over bond assignments of the product of the untouched
site factors times the corresponding entry of `M`. -/
theorem mpsAmplitude_update {n d D : ℕ} [NeZero D]
    (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    mpsAmplitude (mpsUpdate B j M) x =
      ∑ α : Fin (n - 1) → Fin D,
        (∏ i ∈ Finset.univ.erase j, B i (x i) (mpsLeftIdx α i) (mpsRightIdx α i))
          * M (x j) (mpsLeftIdx α j) (mpsRightIdx α j) := by
  unfold mpsAmplitude
  refine Finset.sum_congr rfl fun α _ => ?_
  set g : Fin n → ℂ :=
    fun i => mpsUpdate B j M i (x i) (mpsLeftIdx α i) (mpsRightIdx α i) with hg
  change (∏ i, g i) = _
  rw [← Finset.prod_erase_mul (Finset.univ) g (Finset.mem_univ j)]
  congr 1
  · apply Finset.prod_congr rfl
    intro i hi
    rw [Finset.mem_erase] at hi
    simp [g, mpsUpdate, hi.1]
  · simp [g, mpsUpdate]

/-- Linearity of the site-`j` family in the amplitude (addition). -/
theorem mpsAmplitude_update_add {n d D : ℕ} [NeZero D]
    (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M M' : Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    mpsAmplitude (mpsUpdate B j (fun s => M s + M' s)) x =
      mpsAmplitude (mpsUpdate B j M) x + mpsAmplitude (mpsUpdate B j M') x := by
  rw [mpsAmplitude_update, mpsAmplitude_update, mpsAmplitude_update,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro α _
  simp only [Matrix.add_apply, mul_add]

/-- Linearity of the site-`j` family in the amplitude (scalars). -/
theorem mpsAmplitude_update_smul {n d D : ℕ} [NeZero D]
    (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (c : ℂ) (M : Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    mpsAmplitude (mpsUpdate B j (fun s => c • M s)) x =
      c * mpsAmplitude (mpsUpdate B j M) x := by
  rw [mpsAmplitude_update, mpsAmplitude_update, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- The zero site family produces the zero amplitude on a nonempty chain. -/
theorem mpsAmplitude_update_zero {n d D : ℕ} [NeZero n] [NeZero D]
    (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n) (x : Fin n → Fin d) :
    mpsAmplitude (mpsUpdate B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ)) x = 0 := by
  rw [mpsAmplitude_update]
  apply Finset.sum_eq_zero
  intro α _
  simp

/-- The value of the amplitude when the site-`j` family is `M` (the linear part of
the truncation state). -/
noncomputable def linAmp {n d D : ℕ} [NeZero D]
    (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) : ℂ :=
  mpsAmplitude (mpsUpdate B j M) x

/-- The truncation residual `|ψ_B(M)⟩ − |ψ_A⟩` at configuration `x`. -/
noncomputable def residual {n d D : ℕ} [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) : ℂ :=
  mpsAmplitude (mpsUpdate B j M) x - mpsAmplitude A x

/-- Source p. 3: `K := ‖|ψ_A⟩ − |ψ_B⟩‖²`, summed over all configurations. -/
noncomputable def truncationObjective {n d D : ℕ} [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) : ℝ :=
  ∑ x, Complex.normSq (residual A B j M x)

/-- The residual at the site family `M` is the residual at the zero family plus the
linear amplitude contribution. -/
theorem residual_eq_zero_add {n d D : ℕ} [NeZero n] [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) (x : Fin n → Fin d) :
    residual A B j M x = residual A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) x
      + linAmp B j M x := by
  unfold residual linAmp
  rw [mpsAmplitude_update_zero]
  ring

/-- Source p. 3: the truncation objective is the constant term plus the norm of the
linear amplitude contribution plus a cross term that is linear in `M`; this is the
precise sense in which `K` is quadratic in the site matrices. -/
theorem truncationObjective_expansion {n d D : ℕ} [NeZero n] [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    truncationObjective A B j M =
      truncationObjective A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ)
        + (∑ x, Complex.normSq (linAmp B j M x))
        + 2 * (∑ x,
            (residual A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) x
              * star (linAmp B j M x)).re) := by
  unfold truncationObjective
  have hpoint : ∀ x, Complex.normSq (residual A B j M x) =
      Complex.normSq (residual A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) x
        + linAmp B j M x) := by
    intro x
    rw [residual_eq_zero_add]
  rw [Finset.sum_congr rfl (fun x _ => hpoint x)]
  have hsplit : ∀ x,
      Complex.normSq (residual A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) x
          + linAmp B j M x)
        = Complex.normSq (residual A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) x)
          + Complex.normSq (linAmp B j M x)
          + 2 * (residual A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) x
              * star (linAmp B j M x)).re := by
    intro x
    simpa [Complex.star_def] using
      Complex.normSq_add (residual A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) x)
        (linAmp B j M x)
  rw [Finset.sum_congr rfl (fun x _ => hsplit x)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

/-- The linear (in `M`) part of the stationarity pairing: `δ†` against the state
with site family `M`. -/
noncomputable def linearPairing {n d D : ℕ} [NeZero D]
    (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M δ : Fin d → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ x, linAmp B j M x * star (linAmp B j δ x)

/-- The stationarity pairing of `K` at site family `M` in direction `δ`. -/
noncomputable def pairing {n d D : ℕ} [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M δ : Fin d → Matrix (Fin D) (Fin D) ℂ) : ℂ :=
  ∑ x, residual A B j M x * star (linAmp B j δ x)

/-- The linear pairing is additive in the site-`j` family. -/
theorem linearPairing_add {n d D : ℕ} [NeZero D]
    (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M M' δ : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    linearPairing B j (fun s => M s + M' s) δ =
      linearPairing B j M δ + linearPairing B j M' δ := by
  unfold linearPairing linAmp
  simp only [mpsAmplitude_update_add]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The linear pairing is compatible with scalar multiplication of the site-`j`
family. -/
theorem linearPairing_smul {n d D : ℕ} [NeZero D]
    (B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (c : ℂ) (M δ : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    linearPairing B j (fun s => c • M s) δ = c * linearPairing B j M δ := by
  unfold linearPairing linAmp
  simp only [mpsAmplitude_update_smul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- The full stationarity pairing is the linear pairing plus the constant pairing of
the zero site family. -/
theorem pairing_eq_linear_add_zero {n d D : ℕ} [NeZero n] [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M δ : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    pairing A B j M δ =
      linearPairing B j M δ + pairing A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) δ := by
  unfold pairing linearPairing residual linAmp
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [mpsAmplitude_update_zero]
  ring

/-- Source pp. 2-3: stationarity of the truncation objective `K` in the site family
`B_j` is equivalent to a system of equations that is **linear** in `B_j` with a
constant right-hand side (the "trivial system of linear equations").  Here the
linearity is exhibited as additivity/scalar compatibility of `linearPairing` in `M`. -/
theorem truncation_stationarity_is_linear_system {n d D : ℕ} [NeZero n] [NeZero D]
    (A B : Fin n → Fin d → Matrix (Fin D) (Fin D) ℂ) (j : Fin n)
    (M : Fin d → Matrix (Fin D) (Fin D) ℂ) :
    (∀ δ, (pairing A B j M δ).re = 0) ↔
      (∀ δ, (linearPairing B j M δ).re
        = -(pairing A B j (0 : Fin d → Matrix (Fin D) (Fin D) ℂ) δ).re) := by
  constructor
  · intro h δ
    have h1 := h δ
    rw [pairing_eq_linear_add_zero, Complex.add_re] at h1
    linarith
  · intro h δ
    have h1 := h δ
    rw [pairing_eq_linear_add_zero, Complex.add_re]
    linarith

end Qatlib.Papers.RenormAlg04.MainResults.Truncation
