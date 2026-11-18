/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! # Algorithm 5's step-label halving and Fourier readout

Fixed source arXiv:1010.4458v2, Algorithm 5 (main algorithm), step 3: after the
variable-time amplification the step register carries the doubled label `2j`,
the map `|2j⟩|j⟩ ↦ |j⟩` halves it, the Fourier transform `F_m` is applied to
the step register, and only outcome `0` outputs the `I` register.

This module proves the exact scalar algebra of that readout: the halving map
relocates step amplitudes to the even labels and preserves the total amplitude
sum, and the post-`F_m` zero-outcome has squared modulus `‖∑ a j‖² / m`,
which is at most the label mass `∑ ‖a j‖²`, equals it exactly for uniform
labels, and loses exactly the factor `1 / m` for a label-concentrated state.
The uniform sampling of `x₁, …, x_m`, the amplification step and the circuit
realizations are not modeled here.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.Algo5Readout

/-- Step amplitudes `a` on `Fin m`, placed at the even labels of `Fin (2*m)`
by the halving map `|2j⟩|j⟩ ↦ |j⟩`; odd labels receive zero amplitude. -/
def halved (m : ℕ) (a : Fin m → ℂ) (k : Fin (2 * m)) : ℂ :=
  if hk : k.val % 2 = 0 then a ⟨k.val / 2, by omega⟩ else 0

/-- The halving map is a relabeling: the total amplitude sum over the doubled
label register equals the sum over the halved step register. -/
theorem halveMass (m : ℕ) (a : Fin m → ℂ) :
    ∑ k : Fin (2 * m), halved m a k = ∑ j : Fin m, a j := by
  have hOdd : ∀ k : Fin (2 * m), k.val % 2 ≠ 0 → halved m a k = 0 := by
    intro k hk
    simp [halved, hk]
  have hEven : ∀ k : Fin (2 * m), k.val % 2 = 0 →
      halved m a k = a ⟨k.val / 2, by omega⟩ := by
    intro k hk
    simp [halved, hk]
  calc ∑ k : Fin (2 * m), halved m a k
      = ∑ k : Fin (2 * m),
          if k.val % 2 = 0 then halved m a k else 0 :=
        Finset.sum_congr rfl fun k _ => by
          by_cases hk : k.val % 2 = 0
          · simp [hk]
          · simp [hOdd k hk]
    _ = ∑ k ∈ Finset.univ.filter (fun k : Fin (2 * m) => k.val % 2 = 0),
          halved m a k := (Finset.sum_filter _ _).symm
    _ = ∑ k ∈ Finset.univ.filter (fun k : Fin (2 * m) => k.val % 2 = 0),
          a ⟨k.val / 2, by omega⟩ :=
        Finset.sum_congr rfl fun k hk => hEven k (Finset.mem_filter.mp hk |>.2)
    _ = ∑ j : Fin m, a j := by
        refine Finset.sum_nbij (fun k : Fin (2 * m) => (⟨k.val / 2, by omega⟩ : Fin m))
          (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_
        · intro k₁ hk₁ k₂ hk₂ heq
          have hb1 : k₁.val < 2 * m := k₁.isLt
          have hb2 : k₂.val < 2 * m := k₂.isLt
          have he1 : k₁.val % 2 = 0 := (Finset.mem_filter.mp hk₁).2
          have he2 : k₂.val % 2 = 0 := (Finset.mem_filter.mp hk₂).2
          have hdiv : k₁.val / 2 = k₂.val / 2 := congrArg Fin.val heq
          exact Fin.ext (by omega)
        · intro j _
          have hj : j.val < m := j.isLt
          refine ⟨⟨2 * j.val, by omega⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, ?_⟩
          · show (2 * j.val) % 2 = 0
            omega
          · simp only [Fin.ext_iff]
            omega
        · intro _ _
          rfl

/-- Cast helper: summing a complex constant over `Fin n` is `n * C`. -/
private theorem sumCast (C : ℂ) (n : ℕ) :
    ∑ _j : Fin n, C = (n : ℝ) * C := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Fin.sum_univ_castSucc, ih]
      push_cast
      ring

/-- Cauchy–Schwarz on the labels: `‖∑ a j‖² ≤ m * ∑ ‖a j‖²`. -/
private theorem csSum (m : ℕ) (a : Fin m → ℂ) :
    ‖(∑ j, a j)‖ ^ 2 ≤ (m : ℝ) * ∑ j, ‖a j‖ ^ 2 := by
  set u : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 fun _ => 1 with hu
  set v : EuclideanSpace ℂ (Fin m) := WithLp.toLp 2 a with hv
  have hin : inner ℂ u v = ∑ j, a j := by
    rw [PiLp.inner_apply, WithLp.ofLp_toLp, WithLp.ofLp_toLp]
    simp [RCLike.inner_apply]
  have h1 : ‖u‖ ^ 2 = (m : ℝ) := by
    rw [EuclideanSpace.norm_sq_eq, WithLp.ofLp_toLp]
    simp
  have h2 : ‖v‖ ^ 2 = ∑ j, ‖a j‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, WithLp.ofLp_toLp]
  have hcs : ‖inner ℂ u v‖ ≤ ‖u‖ * ‖v‖ := norm_inner_le_norm u v
  have hcs2 : ‖inner ℂ u v‖ * ‖inner ℂ u v‖
      ≤ (‖u‖ * ‖v‖) * (‖u‖ * ‖v‖) := mul_self_le_mul_self (norm_nonneg _) hcs
  calc ‖(∑ j, a j)‖ ^ 2 = ‖inner ℂ u v‖ ^ 2 := by rw [hin]
    _ ≤ (‖u‖ * ‖v‖) ^ 2 := by rw [pow_two, pow_two]; exact hcs2
    _ = ‖u‖ ^ 2 * ‖v‖ ^ 2 := by ring
    _ = (m : ℝ) * ∑ j, ‖a j‖ ^ 2 := by rw [h1, h2]

/-- The amplitude of measurement outcome `0` on the step register after the
Fourier transform `F_m` in Algorithm 5 step 3, for step amplitudes `a`: the
zero row of `F_m` contributes `1/√m` to every label. -/
def readoutAmp (m : ℕ) (a : Fin m → ℂ) : ℂ := (∑ j, a j) / Real.sqrt m

/-- The squared modulus (success probability up to the `I`-register factor) of
the Algorithm 5 zero-outcome readout. -/
def readoutProb (m : ℕ) (a : Fin m → ℂ) : ℝ := ‖readoutAmp m a‖ ^ 2

/-- The squared modulus of the real `√m` viewed in `ℂ`, as used by the
zero-outcome denominators below. -/
private theorem sqrtDenom (m : ℕ) (hpos' : 0 < (m : ℝ)) :
    ‖((Real.sqrt m : ℝ) : ℂ)‖ ^ 2 = m := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), Real.sq_sqrt (le_of_lt hpos')]

/-- The zero-outcome readout probability never exceeds the step-register
mass `∑ ‖a j‖²`. -/
theorem readoutUpper (m : ℕ) (a : Fin m → ℂ) :
    readoutProb m a ≤ ∑ j, ‖a j‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp [readoutProb, readoutAmp]
  · unfold readoutProb readoutAmp
    have hpos' : 0 < (m : ℝ) := by exact_mod_cast hpos
    rw [norm_div, div_pow, sqrtDenom m hpos', div_le_iff₀ hpos']
    exact (csSum m a).trans (le_of_eq (by ring))

/-- Uniform step labels read out with no loss: the zero-outcome probability
equals the full step-register mass `m * ‖c‖²`. -/
theorem readoutUniform (m : ℕ) (c : ℂ) :
    readoutProb m (fun _ => c) = (m : ℝ) * ‖c‖ ^ 2 := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0; simp [readoutProb, readoutAmp]
  · unfold readoutProb readoutAmp
    have hpos' : 0 < (m : ℝ) := by exact_mod_cast hpos
    have hnorm : ‖((m : ℝ) : ℂ)‖ = m := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos')]
    have hnum : ‖(((m : ℝ) : ℂ) * c)‖ = m * ‖c‖ := by
      rw [norm_mul, hnorm]
    rw [sumCast c m, norm_div, div_pow, hnum, mul_pow, sqrtDenom m hpos']
    field_simp

/-- A label-concentrated state pays exactly the `1/m` factor: the zero-outcome
probability of `c` at a single step label `j₀` is `‖c‖² / m`. -/
theorem readoutSingle (m : ℕ) (j₀ : Fin m) (c : ℂ) :
    readoutProb m (fun j => if j = j₀ then c else 0) = ‖c‖ ^ 2 / m := by
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · exfalso
    have := j₀.isLt
    omega
  · have hsum : ∑ j : Fin m, (if j = j₀ then c else 0) = c := by
      rw [Finset.sum_ite_eq' Finset.univ j₀ (fun _ => c)]
      simp
    have hpos' : 0 < (m : ℝ) := by exact_mod_cast hpos
    unfold readoutProb readoutAmp
    rw [hsum, norm_div, div_pow, sqrtDenom m hpos']

end Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.Algo5Readout
