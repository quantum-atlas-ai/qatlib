/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GaussSumEst02.MainResults.Source.GaussSumCore
import Qatlib.Papers.GaussSumEst02.MainResults.Source.Cost

/-!
# Finite-field character states

This module proves character identities used in the Gauss-sum estimation algorithms of
[VanDamSeroussi2002]. Additive-character orthogonality and translation give the summation and
phase-kickback identities, while `chiState_normSq` normalizes the multiplicative-character state
supported away from zero.

The discrete-log identities express character values on powers and inverse powers.
`amplificationQueries` supplies a ceiling-based query-count expression for support
amplification.

## Main statements

* `addChar_sum_ite`: Additive-character orthogonality after scaling.
* `addChar_kickback`: Translation acts by the corresponding character phase.
* `chiState_normSq`: Unit squared norm of the character state.
* `amplificationQueries_pos`: Positivity of the query-count expression.

## References

* [van Dam and Seroussi, 2002][VanDamSeroussi2002]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GaussSumEst02.CharacterState

open Qatlib.Papers.GaussSumEst02.MainResults.Source

/-- The sum of an additive character over the scaled finite field is the field cardinality when
the scale is zero, and zero otherwise. See [VanDamSeroussi2002]. -/
theorem addChar_sum_ite {F : Type*} [Field F] [Fintype F] [DecidableEq F] (e : AddChar F)
    (c : F) :
    (∑ x : F, e.toFun (c * x))
      = if c = 0 then ((Fintype.card F : ℕ) : ℂ) else 0 := by
  classical
  by_cases hc : c = 0
  · subst hc
    simp [e.map_zero']
  · rw [if_neg hc]
    exact e.sum_mul_eq_zero hc

/-- Translating the argument of an additive character by `f` multiplies its value function by
the scalar `e.toFun f`. See [VanDamSeroussi2002]. -/
theorem addChar_kickback {F : Type*} [Field F] (e : AddChar F) (f : F) :
    (fun k : F => e.toFun (k + f)) = e.toFun f • (fun k : F => e.toFun k) := by
  funext k
  simp only [Pi.smul_apply, smul_eq_mul, e.map_add']
  ring

/-- The multiplicative-character state has zero amplitude at the field element zero. -/
theorem chiState_support {K : Type*} [Field K] [Fintype K] (χ : MultChar K) :
    chiState χ 0 = 0 := by
  simp [chiState, χ.map_zero']

/-- The sum of squared coordinate norms of the multiplicative-character state equals one. See
[VanDamSeroussi2002]. -/
theorem chiState_normSq {K : Type*} [Field K] [Fintype K] (χ : MultChar K) :
    (∑ x : K, ‖chiState χ x‖ ^ 2) = 1 := by
  classical
  have hcard : 2 ≤ Fintype.card K := by
    have := Fintype.one_lt_card (α := K)
    omega
  have hden_pos : 0 < Real.sqrt ((Fintype.card K - 1 : ℕ) : ℝ) := by
    apply Real.sqrt_pos.mpr
    have hpos : (0 : ℝ) < ((Fintype.card K - 1 : ℕ) : ℝ) := by
      have : 0 < Fintype.card K - 1 := by omega
      exact_mod_cast this
    exact hpos
  have hterm : ∀ x : K, x ≠ 0 → ‖chiState χ x‖ ^ 2
      = 1 / ((Fintype.card K - 1 : ℕ) : ℝ) := by
    intro x hx
    simp only [chiState]
    rw [norm_div, χ.norm_eq_one x hx, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hden_pos, div_pow, one_pow, Real.sq_sqrt (by positivity)]
  have hzero : ‖chiState χ 0‖ ^ 2 = 0 := by
    simp [chiState, χ.map_zero']
  have hsum : (∑ x : K, ‖chiState χ x‖ ^ 2)
      = ((Fintype.card K - 1 : ℕ) : ℝ)
          * (1 / ((Fintype.card K - 1 : ℕ) : ℝ)) := by
    have hsub : (∑ x ∈ Finset.univ.erase (0 : K), ‖chiState χ x‖ ^ 2)
        = ∑ x : K, ‖chiState χ x‖ ^ 2 := by
      refine Finset.sum_subset (Finset.erase_subset _ _) ?_
      intro x _ hx
      have hx0 : x = 0 := by
        by_contra h
        exact hx (Finset.mem_erase.mpr ⟨h, Finset.mem_univ x⟩)
      rw [hx0]
      exact hzero
    rw [← hsub]
    rw [Finset.sum_congr rfl
      (fun x hx => hterm x (Finset.mem_erase.mp hx).1)]
    rw [Finset.sum_const, nsmul_eq_mul,
      Finset.card_erase_of_mem (Finset.mem_univ (0 : K)), Finset.card_univ]
  rw [hsum]
  have hne : ((Fintype.card K - 1 : ℕ) : ℝ) ≠ 0 := by
    have : 0 < Fintype.card K - 1 := by omega
    exact_mod_cast (Nat.pos_iff_ne_zero.mp this)
  field_simp

/-- A multiplicative character sends the natural power `g ^ j` to the same power of its value at
`g`. See [VanDamSeroussi2002]. -/
theorem dlog_pow_char {K : Type*} [Field K] (χ : MultChar K) (g : K) (j : ℕ) :
    χ.toFun (g ^ j) = χ.toFun g ^ j :=
  χ.pow_apply g j

/-- For nonzero `g`, the character value at the inverse of `g ^ j` is the inverse of the `j`th
power of the character value at `g`. -/
theorem dlog_inv_char {K : Type*} [Field K] (χ : MultChar K) {g : K} (hg : g ≠ 0) (j : ℕ) :
    χ.toFun ((g ^ j)⁻¹) = (χ.toFun g ^ j)⁻¹ := by
  have hgpow : g ^ j ≠ 0 := pow_ne_zero j hg
  rw [χ.inv_apply hgpow, dlog_pow_char]

/-- The natural ceiling of `√(S / k)` used as the support-amplification query-count expression. -/
def amplificationQueries (S k : ℕ) : ℕ := Nat.ceil (Real.sqrt ((S : ℝ) / (k : ℝ)))

/-- The support-amplification query-count expression is strictly positive when both `S` and `k`
are positive. See [VanDamSeroussi2002]. -/
theorem amplificationQueries_pos {S k : ℕ} (hS : 0 < S) (hk : 0 < k) :
    0 < amplificationQueries S k := by
  unfold amplificationQueries
  apply Nat.ceil_pos.mpr
  apply Real.sqrt_pos.mpr
  positivity

end Qatlib.Papers.GaussSumEst02.CharacterState
