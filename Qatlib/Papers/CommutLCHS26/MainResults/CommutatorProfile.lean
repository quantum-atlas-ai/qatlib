/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorRefined
import Mathlib.Data.List.OfFn

/-!
# Polynomial dependence of mixed commutator profiles

The coefficients `mixedCoefficient` group nested commutator norms by the number of occurrences
of L in words over H and L. Scaling L by k then expresses the profile as a polynomial in |k|
with nonnegative coefficients, following the decomposition in [AftabAnTrivisa2026].

Word reversal supplies the corresponding right-nested formulation, and a radius bound controls
the profile uniformly for |k| ≤ R.

## Main statements

* `profile_polynomial`: expands the scaled profile in powers of |k|.
* `right_nested_profile_polynomial`: gives the right-nested version of Lemma 3.9.
* `profile_le_radius`: bounds the profile on a parameter window.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.CommutatorProfile

open Matrix
open scoped BigOperators Matrix.Norms.L2Operator
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.GeneralOrder
set_option warningAsError false

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The sum of nested commutator norms over length-j binary words containing exactly ell
occurrences of L. -/
def mixedCoefficient (H L : Matrix I I ℂ) (j ell : ℕ) : ℝ :=
  ∑ w : Fin j → Fin 2, if (List.ofFn w).count 1 = ell then
    ‖pfNestedCommList (pfChosenList [H, L] w)‖ else 0

/-- Every mixed commutator coefficient is nonnegative. -/
theorem mixedCoefficient_nonneg (H L : Matrix I I ℂ) (j ell : ℕ) :
    0 ≤ mixedCoefficient H L j ell := by
  apply Finset.sum_nonneg
  intro w _
  split_ifs <;> positivity

omit [DecidableEq I] in

/-- Scaling each generator in an iterated commutator fold factors out the product of its scalar
multipliers. -/
private theorem fold_map_scale (w : List (Fin 2)) (m g : Fin 2 → Matrix I I ℂ)
    (c : Fin 2 → ℝ) (hm : ∀ b, m b = c b • g b) (X : Matrix I I ℂ) :
    (w.map m).foldl (fun D Y => pfComm Y D) X =
      (w.map c).prod • (w.map g).foldl (fun D Y => pfComm Y D) X := by
  simpa only [List.foldl_map, List.map_map, Function.comp_def, pow_one, List.replicate_one,
    List.foldl_cons, List.foldl_nil] using!
    clause50_fold_groups_scale (w.map (fun b => (b, 1))) c m g hm X

omit [DecidableEq I] in

/-- Scaling the entries of a nested commutator factors out the product of their scalar
multipliers. -/
private theorem nested_map_scale (w : List (Fin 2)) (m g : Fin 2 → Matrix I I ℂ)
    (c : Fin 2 → ℝ) (hm : ∀ b, m b = c b • g b) :
    pfNestedCommList (w.map m) = (w.map c).prod • pfNestedCommList (w.map g) := by
  cases w with
  | nil => simp [pfNestedCommList]
  | cons b w =>
    simp only [List.map_cons, pfNestedCommList, List.prod_cons]
    rw [hm b, fold_map_scale w m g c hm, clause50_fold_seed_scale, smul_smul]
    congr 1
    exact mul_comm _ _

/-- The product of factors k at entries equal to 1 and factors 1 elsewhere equals k to the
number of entries equal to 1. -/
private theorem scale_product (w : List (Fin 2)) (k : ℝ) :
    (w.map (fun b => if b = 1 then k else 1)).prod = k ^ w.count 1 := by
  induction w with
  | nil => simp
  | cons b w ih =>
    fin_cases b <;> simp [ih, pow_succ, mul_comm]

omit [DecidableEq I] in

/-- Selecting matrices from the pair H, L along a binary word equals mapping list lookup over
that word. -/
private theorem chosen_eq_map (H L : Matrix I I ℂ) {j : ℕ} (w : Fin j → Fin 2) :
    pfChosenList [H, L] w = (List.ofFn w).map (fun b => [H, L].getD b.val 0) := by
  simp only [pfChosenList, List.ofFn_eq_map, List.map_map, Function.comp_def]

/-- Reversing the finite index of a function reverses its associated list. -/
private theorem ofFn_reverse {j : ℕ} (w : Fin j → Fin 2) :
    List.ofFn (fun i => w i.rev) = (List.ofFn w).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

omit [DecidableEq I] in

/-- Reversing a binary word reverses its list of selected matrices. -/
private theorem chosen_reverse (H L : Matrix I I ℂ) {j : ℕ}
    (w : Fin j → Fin 2) :
    pfChosenList [H, L] (fun i => w i.rev) = (pfChosenList [H, L] w).reverse := by
  rw [chosen_eq_map, ofFn_reverse, List.map_reverse, chosen_eq_map]

/-- Mixed coefficients are unchanged when each selected commutator word is reversed. -/
theorem mixedCoefficient_right_nested (H L : Matrix I I ℂ) (j ell : ℕ) :
    mixedCoefficient H L j ell =
      ∑ w : Fin j → Fin 2, if (List.ofFn w).count 1 = ell then
        ‖pfNestedCommList (pfChosenList [H, L] w).reverse‖ else 0 := by
  let e : (Fin j → Fin 2) ≃ (Fin j → Fin 2) :=
    { toFun := fun w i => w i.rev
      invFun := fun w i => w i.rev
      left_inv := fun w => by funext i; simp
      right_inv := fun w => by funext i; simp }
  have h := e.sum_comp (fun w => if (List.ofFn w).count 1 = ell then
    ‖pfNestedCommList (pfChosenList [H, L] w).reverse‖ else 0)
  change (∑ w : Fin j → Fin 2, if (List.ofFn (fun i => w i.rev)).count 1 = ell then
    ‖pfNestedCommList (pfChosenList [H, L] (fun i => w i.rev)).reverse‖ else 0) = _ at h
  simpa only [ofFn_reverse, List.count_reverse, chosen_reverse, List.reverse_reverse,
    mixedCoefficient] using! h

omit [DecidableEq I] in

/-- Replacing L by k times L multiplies each selected nested commutator by k to the number of
occurrences of L. -/
theorem selected_word_scaling (H L : Matrix I I ℂ) (k : ℝ) {j : ℕ}
    (w : Fin j → Fin 2) :
    pfNestedCommList (pfChosenList [H, k • L] w) =
      k ^ (List.ofFn w).count 1 • pfNestedCommList (pfChosenList [H, L] w) := by
  have hm (b : Fin 2) : [H, k • L].getD b.val 0 =
      (if b = 1 then k else 1) • [H, L].getD b.val 0 := by
    fin_cases b <;> simp
  rw [chosen_eq_map, chosen_eq_map,
    nested_map_scale (List.ofFn w) _ _ _ hm, scale_product]

/-- The profile for H and kL equals the polynomial in |k| whose coefficients group words by
their number of L entries. -/
theorem profile_polynomial (H L : Matrix I I ℂ) (j : ℕ) (k : ℝ) :
    pfCommAlphaSelf [H, k • L] j =
      ∑ ell ∈ Finset.range (j + 1), |k| ^ ell * mixedCoefficient H L j ell := by
  have hs (w : Fin j → Fin 2) :
      ‖pfNestedCommList (pfChosenList [H, k • L] w)‖ =
        |k| ^ (List.ofFn w).count 1 * ‖pfNestedCommList (pfChosenList [H, L] w)‖ := by
    rw [selected_word_scaling, norm_smul, Real.norm_eq_abs, abs_pow]
  unfold pfCommAlphaSelf
  change (∑ w : Fin j → Fin 2, ‖pfNestedCommList (pfChosenList [H, k • L] w)‖) = _
  simp_rw [hs]
  symm
  simp only [mixedCoefficient, Finset.mul_sum, mul_ite, mul_zero]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  have hw : (List.ofFn w).count 1 < j + 1 := by
    have h := List.count_le_length (a := (1 : Fin 2)) (l := List.ofFn w)
    simpa using! Nat.lt_succ_of_le h
  rw [Finset.sum_eq_single ((List.ofFn w).count 1)]
  · simp
  · intro ell _ hne
    simp [Ne.symm hne]
  · intro hn
    exact (hn (Finset.mem_range.mpr hw)).elim

/-- The right-nested commutator norm sum for H and kL is the polynomial in |k| obtained by
counting occurrences of L [Aftab et al., Lemma 3.9][AftabAnTrivisa2026]. -/
theorem right_nested_profile_polynomial (H L : Matrix I I ℂ) (j : ℕ) (k : ℝ) :
    (∑ w : Fin j → Fin 2, ‖pfNestedCommList (pfChosenList [H, k • L] w).reverse‖) =
      ∑ ell ∈ Finset.range (j + 1), |k| ^ ell *
        (∑ w : Fin j → Fin 2, if (List.ofFn w).count 1 = ell then
          ‖pfNestedCommList (pfChosenList [H, L] w).reverse‖ else 0) := by
  let e : (Fin j → Fin 2) ≃ (Fin j → Fin 2) :=
    { toFun := fun w i => w i.rev
      invFun := fun w i => w i.rev
      left_inv := fun w => by funext i; simp
      right_inv := fun w => by funext i; simp }
  have h := e.sum_comp (fun w => ‖pfNestedCommList (pfChosenList [H, k • L] w)‖)
  change (∑ w : Fin j → Fin 2,
    ‖pfNestedCommList (pfChosenList [H, k • L] (fun i => w i.rev))‖) = _ at h
  simp only [chosen_reverse] at h
  rw [h]
  change pfCommAlphaSelf [H, k • L] j = _
  rw [profile_polynomial]
  simp_rw [mixedCoefficient_right_nested]

/-- If |k| ≤ R, the profile for H and kL is bounded by the mixed-coefficient polynomial
evaluated at R. -/
theorem profile_le_radius (H L : Matrix I I ℂ) (j : ℕ) {k R : ℝ}
    (hk : |k| ≤ R) :
    pfCommAlphaSelf [H, k • L] j ≤
      ∑ ell ∈ Finset.range (j + 1), R ^ ell * mixedCoefficient H L j ell := by
  rw [profile_polynomial]
  apply Finset.sum_le_sum
  intro ell _
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg k) hk ell)
    (mixedCoefficient_nonneg H L j ell)

end Qatlib.Papers.CommutLCHS26.MainResults.CommutatorProfile
