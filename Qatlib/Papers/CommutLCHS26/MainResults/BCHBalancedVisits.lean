/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHMatrixBudget
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHBalancedVisits

open scoped BigOperators MonoidAlgebra Classical
open BCHDynkin BCHWordPowers BCHCloneBudget BCHCommBudget

section Algebra
variable {A R : Type} [Ring A] [CommRing R] [Algebra R A]

theorem rightBracket_smul (c : R) (xs : List A) :
    rightBracket (xs.map (fun X => c • X)) = c ^ xs.length • rightBracket xs := by
  induction xs with
  | nil => simp [rightBracket]
  | cons X xs ih =>
    cases xs with
    | nil => simp [rightBracket]
    | cons Y xs =>
      change (c • X) * rightBracket ((Y :: xs).map (fun Z => c • Z)) -
        rightBracket ((Y :: xs).map (fun Z => c • Z)) * (c • X) =
          c ^ ((Y :: xs).length + 1) •
            (X * rightBracket (Y :: xs) - rightBracket (Y :: xs) * X)
      rw [ih, smul_mul_smul_comm, smul_mul_smul_comm,
        mul_comm (c ^ (Y :: xs).length) c, ← smul_sub, ← pow_succ']

end Algebra

section ScalarBudget
variable {B K : Type} [NormedRing B] [NormedField K] [NormedAlgebra K B]

theorem alphaComm_smul {Γ : ℕ} (X : Fin Γ → B) (c : K) (n : ℕ) :
    alphaComm (fun i => c • X i) n = ‖c‖ ^ n * alphaComm X n := by
  unfold alphaComm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  have h := rightBracket_smul c (List.ofFn (fun j => X (f j)))
  simp only [List.map_ofFn, List.length_ofFn, Function.comp_def] at h
  rw [h, norm_smul, norm_pow]

end ScalarBudget

theorem evaluate_uniform_word {α β : Type} (c : ℚ) (base : β → α) (w : List β) :
    evaluateWords (fun j => c • letter (base j)) (word w) =
      c ^ w.length • word (w.map base) := by
  induction w with
  | nil =>
    rw [evaluateWords_word]
    simp [word, MonoidAlgebra.one_def]
  | cons j w ih =>
    rw [word_cons, map_mul, evaluateWords_letter, ih, smul_mul_smul_comm]
    simp only [List.length_cons, pow_succ', List.map_cons, word_cons]

section Norm
variable {B : Type} [NormedRing B] [NormedAlgebra ℝ B] [Algebra ℚ B]

theorem wordFunctional_weighted_norm {α β : Type} (X : α → B) (base : β → α)
    (c : ℚ) (hc : 0 ≤ c) (w : List β) :
    wordFunctional (fun u => ‖rightBracket (u.map X)‖)
      (evaluateWords (fun j => c • letter (base j)) (word w)) =
        ‖rightBracket (w.map (fun j => c • X (base j)))‖ := by
  have he : rightBracket (w.map (fun j => c • X (base j))) =
      c ^ w.length • rightBracket ((w.map base).map X) := by
    simpa only [List.map_map, List.length_map, Function.comp_def] using!
      rightBracket_smul c ((w.map base).map X)
  have hreal : 0 ≤ (c : ℝ) := by exact_mod_cast hc
  rw [evaluate_uniform_word, map_smul, wordFunctional_word, he]
  simp only [← Rat.cast_smul_eq_qsmul ℝ, smul_eq_mul, norm_smul, Real.norm_eq_abs,
    Rat.cast_pow, abs_of_nonneg (pow_nonneg hreal w.length)]

theorem alphaComm_balanced {Γ Λ : ℕ} (X : Fin Γ → B) (base : Fin Λ → Fin Γ)
    (c : ℚ) (hc : 0 ≤ c)
    (hbalance : (∑ j : Fin Λ, c • letter (base j)) = ∑ i : Fin Γ, letter i)
    (n : ℕ) : alphaComm (fun j => c • X (base j)) n = alphaComm X n := by
  let F : List (Fin Γ) → ℝ := fun w => ‖rightBracket (w.map X)‖
  calc
    _ = wordFunctional F
        (evaluateWords (fun j => c • letter (base j)) ((∑ j : Fin Λ, letter j) ^ n)) := by
      rw [letter_sum_pow, map_sum, map_sum]
      unfold alphaComm
      apply Finset.sum_congr rfl
      intro f _
      simpa only [F, List.map_ofFn, Function.comp_def] using!
        (wordFunctional_weighted_norm X base c hc (List.ofFn f)).symm
    _ = wordFunctional F ((∑ i : Fin Γ, letter i) ^ n) := by
      rw [map_pow, map_sum]
      simp only [evaluateWords_letter]
      rw [hbalance]
    _ = _ := by
      rw [letter_sum_pow, map_sum]
      simp only [wordFunctional_word, F, alphaComm, List.map_ofFn, Function.comp_def]

omit [NormedAlgebra ℝ B] [Algebra ℚ B] in

theorem alphaComm_reindex {Γ Λ : ℕ} (X : Fin Γ → B) (e : Fin Λ ≃ Fin Γ) (n : ℕ) :
    alphaComm (fun i => X (e i)) n = alphaComm X n := by
  let E : (Fin n → Fin Λ) ≃ (Fin n → Fin Γ) := Equiv.piCongrRight (fun _ => e)
  have h := E.sum_comp (fun f => ‖rightBracket (List.ofFn (fun j => X (f j)))‖)
  exact h

omit [NormedAlgebra ℝ B] [Algebra ℚ B] in

theorem alphaComm_get_ofFn {Γ : ℕ} (X : Fin Γ → B) (n : ℕ) :
    alphaComm (List.ofFn X).get n = alphaComm X n := by
  let e : Fin (List.ofFn X).length ≃ Fin Γ :=
      finCongr (show (List.ofFn X).length = Γ from List.length_ofFn)
  have he : (List.ofFn X).get = fun j => X (e j) := by
    funext j
    change getElem (List.ofFn X) j.val j.isLt = X (e j)
    rw [List.getElem_ofFn]
    rfl
  rw [he]
  exact alphaComm_reindex X e n

end Norm

end Qatlib.Papers.CommutLCHS26.MainResults.BCHBalancedVisits
