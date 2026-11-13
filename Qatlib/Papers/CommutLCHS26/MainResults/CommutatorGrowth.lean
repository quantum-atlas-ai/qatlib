/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHMassProducts
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Geometric bounds for nested commutator profiles

This module bounds nested commutator norms by products of generator norms and derives geometric
growth estimates for the profile used in [AftabAnTrivisa2026]. The positive `boundingScale`
normalizes odd profile terms so their series is summable with total at most 1/6.

## Main statements

* `profile_le_pow`: bounds each profile by a power of the generator mass.
* `normalized_summable`: proves summability of the normalized odd profile.
* `normalized_sum_le`: bounds its sum.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.CommutatorGrowth

open scoped BigOperators Classical Matrix.Norms.L2Operator
open BCHDynkin BCHCommBudget BCHMatrixBudget BCHCommMass
open Qatlib.Concepts.TrotterFormula.GeneralOrder
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

/-- The norm of a right-nested bracket is at most 2 to the list length times the product of the
entry norms. -/
theorem rightBracket_norm {B : Type} [NormedRing B] (xs : List B) :
    ‖rightBracket xs‖ ≤ (2 : ℝ) ^ xs.length * (xs.map norm).prod := by
  induction xs with
  | nil => norm_num [rightBracket]
  | cons A xs ih =>
    cases xs with
    | nil =>
      simp only [rightBracket, List.length_cons, List.length_nil, Nat.zero_add, pow_one,
        List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      linarith [norm_nonneg A]
    | cons B xs =>
      rw [rightBracket]
      calc
        _ ≤ ‖A * rightBracket (B :: xs)‖ + ‖rightBracket (B :: xs) * A‖ := norm_sub_le _ _
        _ ≤ ‖A‖ * ‖rightBracket (B :: xs)‖ + ‖rightBracket (B :: xs)‖ * ‖A‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ ≤ ‖A‖ * ((2 : ℝ) ^ (B :: xs).length * ((B :: xs).map norm).prod) +
            ((2 : ℝ) ^ (B :: xs).length * ((B :: xs).map norm).prod) * ‖A‖ :=
          add_le_add (mul_le_mul_of_nonneg_left ih (norm_nonneg _))
            (mul_le_mul_of_nonneg_right ih (norm_nonneg _))
        _ = _ := by simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ]; ring

/-- The length-n commutator norm sum is at most the n-th power of twice the total generator
norm. -/
theorem alphaComm_le_pow {B : Type} [NormedRing B] {Γ : ℕ} (X : Fin Γ → B) (n : ℕ) :
    alphaComm X n ≤ (2 * ∑ i, ‖X i‖) ^ n := by
  unfold alphaComm
  calc
    _ ≤ ∑ f : Fin n → Fin Γ, (2 : ℝ) ^ n * ∏ i, ‖X (f i)‖ := by
      apply Finset.sum_le_sum
      intro f _
      simpa only [List.length_ofFn, List.map_ofFn, Function.comp_def, List.prod_ofFn] using!
        rightBracket_norm (List.ofFn (fun i => X (f i)))
    _ = (2 : ℝ) ^ n * (∑ i, ‖X i‖) ^ n := by
      have he := Fintype.prod_sum (fun (_ : Fin n) (j : Fin Γ) => ‖X j‖)
      have hs : (∑ f : Fin n → Fin Γ, ∏ i, ‖X (f i)‖) = (∑ j, ‖X j‖) ^ n := by
        calc
          _ = ∏ _ : Fin n, ∑ j : Fin Γ, ‖X j‖ := he.symm
          _ = _ := by simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      rw [← Finset.mul_sum, hs]
    _ = _ := (mul_pow _ _ _).symm

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The sum of the generator norms is nonnegative. -/
theorem generator_mass_nonneg (xs : List (Matrix I I ℂ)) : 0 ≤ suzukiMass xs := by
  apply List.sum_nonneg
  intro r hr
  obtain ⟨A, _, rfl⟩ := List.mem_map.mp hr
  exact norm_nonneg _

/-- The order-n commutator profile is bounded by the n-th power of twice the generator mass. -/
theorem profile_le_pow (xs : List (Matrix I I ℂ)) (n : ℕ) :
    pfCommAlphaSelf xs n ≤ (2 * suzukiMass xs) ^ n := by
  have h := alphaComm_le_pow xs.get n
  rw [alphaComm_get_eq_frozen] at h
  have hs : (∑ i : Fin xs.length, ‖xs.get i‖) = suzukiMass xs := by
    have he := congrArg (fun ys : List (Matrix I I ℂ) => (ys.map norm).sum) (List.ofFn_get xs)
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def, suzukiMass] using! he
  simpa only [hs] using! h

/-- The normalization scale 4(M + 1), where M is the generator norm mass. -/
def boundingScale (xs : List (Matrix I I ℂ)) : ℝ := 4 * (suzukiMass xs + 1)

/-- The commutator normalization scale is strictly positive. -/
theorem boundingScale_pos (xs : List (Matrix I I ℂ)) : 0 < boundingScale xs := by
  have h := generator_mass_nonneg xs
  unfold boundingScale
  positivity

/-- Each odd commutator profile divided by the corresponding power of the bounding scale is
nonnegative. -/
theorem normalized_nonneg (xs : List (Matrix I I ℂ)) (j : ℕ) :
    0 ≤ pfCommAlphaSelf xs (2 * j + 3) / boundingScale xs ^ (2 * j + 3) :=
  div_nonneg (profile_nonneg xs _) (pow_nonneg (boundingScale_pos xs).le _)

/-- The normalized profile of order 2j + 3 is at most (1/8)(1/4)^j. -/
theorem normalized_le (xs : List (Matrix I I ℂ)) (j : ℕ) :
    pfCommAlphaSelf xs (2 * j + 3) / boundingScale xs ^ (2 * j + 3) ≤
      (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ j := by
  have hS := generator_mass_nonneg xs
  have hC := boundingScale_pos xs
  have hr : 2 * suzukiMass xs / boundingScale xs ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hC).mpr
    unfold boundingScale
    linarith
  calc
    _ ≤ (2 * suzukiMass xs) ^ (2 * j + 3) / boundingScale xs ^ (2 * j + 3) :=
      div_le_div_of_nonneg_right (profile_le_pow xs _) (pow_nonneg hC.le _)
    _ = (2 * suzukiMass xs / boundingScale xs) ^ (2 * j + 3) := (div_pow _ _ _).symm
    _ ≤ (1 / 2 : ℝ) ^ (2 * j + 3) := pow_le_pow_left₀ (by positivity) hr _
    _ = _ := by rw [pow_add, pow_mul]; norm_num; ring

/-- The normalized odd commutator profiles form a summable series. -/
theorem normalized_summable (xs : List (Matrix I I ℂ)) :
    Summable (fun j => pfCommAlphaSelf xs (2 * j + 3) / boundingScale xs ^ (2 * j + 3)) := by
  have hg := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left
    (1 / 8 : ℝ)
  exact hg.of_nonneg_of_le (normalized_nonneg xs) (normalized_le xs)

/-- The sum of the normalized odd commutator profiles is at most 1/6. -/
theorem normalized_sum_le (xs : List (Matrix I I ℂ)) :
    (∑' j, pfCommAlphaSelf xs (2 * j + 3) / boundingScale xs ^ (2 * j + 3)) ≤ (1 / 6 : ℝ) := by
  have hg := (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left
    (1 / 8 : ℝ)
  calc
    _ ≤ ∑' j, (1 / 8 : ℝ) * (1 / 4 : ℝ) ^ j :=
      Summable.tsum_le_tsum (normalized_le xs) (normalized_summable xs) hg
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)]; norm_num

end Qatlib.Papers.CommutLCHS26.MainResults.CommutatorGrowth
