/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.MainResults.BCHCommBudget
import Qatlib.Papers.CommutLCHS26.MainResults.BCHWordEval
import Qatlib.Concepts.TrotterFormula.GeneralOrder.OrderedCommutatorAlpha

/-!
# Matrix commutator bounds from formal brackets

This module relates `rightBracket` to the reversed list convention of `pfNestedCommList` and
identifies the finite family commutator profile with `pfCommAlphaSelf` on a matrix list.

These identifications transfer the formal word logarithm estimate to the existing matrix
logarithm in `norm_existing_word_log_le`, giving the reciprocal squared degree bound used in
[AftabAnTrivisa2026].

## Main statements

* `rightBracket_eq_frozen_reverse`: reconciles the two nested commutator conventions.
* `alphaComm_get_eq_frozen`: identifies the indexed and list commutator profiles.
* `norm_existing_word_log_le`: bounds positive degree matrix logarithm coefficients.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CommutLCHS26.MainResults.BCHMatrixBudget

open scoped BigOperators Matrix.Norms.L2Operator
open BCHDynkin BCHWordLie BCHCommBudget
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.TrotterFormula.GeneralOrder

variable {I : Type} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in

/-- Appending one matrix to a nonempty list expresses its nested commutator as the commutator of
that matrix with the original nested commutator. -/
private theorem nested_append_singleton (xs : List (Matrix I I ℂ)) (hx : xs ≠ [])
    (A : Matrix I I ℂ) :
    pfNestedCommList (xs ++ [A]) = A * pfNestedCommList xs - pfNestedCommList xs * A := by
  cases xs with
  | nil => exact (hx rfl).elim
  | cons B xs =>
    simpa only [List.cons_append, List.replicate_one, pfAdPower_succ, pfAdPower_zero, pfComm]
      using! pfNestedCommList_append_replicate B A xs 1

/-- The right nested bracket of a matrix list equals `pfNestedCommList` of its reversal. -/
theorem rightBracket_eq_frozen_reverse (xs : List (Matrix I I ℂ)) :
    rightBracket xs = pfNestedCommList xs.reverse := by
  induction xs with
  | nil => rfl
  | cons A xs ih =>
    cases xs with
    | nil => simp [rightBracket, pfNestedCommList]
    | cons B xs =>
      conv_rhs => rw [List.reverse_cons]
      rw [nested_append_singleton _ (by simp)]
      change A * rightBracket (B :: xs) - rightBracket (B :: xs) * A = _
      rw [ih]

omit [DecidableEq I] in

/-- The list selected by a finite index function equals the list formed from the corresponding
matrix entries. -/
private theorem chosen_eq_ofFn (xs : List (Matrix I I ℂ)) {n : ℕ}
    (f : Fin n → Fin xs.length) : pfChosenList xs f = List.ofFn (fun j => xs.get (f j)) := by
  simp only [pfChosenList, ← List.ofFn_eq_map, List.getD_eq_get]

/-- Reversing finite indices reverses the list produced by `List.ofFn`. -/
private theorem ofFn_reverse {α : Type} {n : ℕ} (f : Fin n → α) :
    List.ofFn (fun j => f j.rev) = (List.ofFn f).reverse := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_reverse, List.length_ofFn]
    congr 1
    apply Fin.ext
    simp only [Fin.val_rev]
    omega

/-- The commutator profile of the entry function of a matrix list equals `pfCommAlphaSelf` of
that list. -/
theorem alphaComm_get_eq_frozen (xs : List (Matrix I I ℂ)) (n : ℕ) :
    alphaComm xs.get n = pfCommAlphaSelf xs n := by
  let e : (Fin n → Fin xs.length) ≃ (Fin n → Fin xs.length) :=
    { toFun := fun f j => f j.rev
      invFun := fun f j => f j.rev
      left_inv := fun f => by funext j; simp
      right_inv := fun f => by funext j; simp }
  have h := e.sum_comp (fun f => ‖pfNestedCommList (pfChosenList xs f)‖)
  change (∑ f : Fin n → Fin xs.length,
    ‖pfNestedCommList (pfChosenList xs (fun j => f j.rev))‖) = _ at h
  simp only [chosen_eq_ofFn] at h
  have hr (f : Fin n → Fin xs.length) :
      List.ofFn (fun j => xs.get (f j.rev)) = (List.ofFn (fun j => xs.get (f j))).reverse :=
    ofFn_reverse (fun j => xs.get (f j))
  simp_rw [hr] at h
  simpa only [alphaComm, rightBracket_eq_frozen_reverse, pfCommAlphaSelf, chosen_eq_ofFn] using! h

/-- For positive degree `n`, the matrix word logarithm coefficient has norm at most
`pfCommAlphaSelf xs n / n^2`. This transfers the formal bracket bound to the matrix setting
of [AftabAnTrivisa2026]. -/
theorem norm_existing_word_log_le (xs : List (Matrix I I ℂ))
    (n : ℕ) (hn : 0 < n) :
    ‖BCHFormal.logCoefficient (SubdivisionPolynomial.wordSeries xs) n‖ ≤
      pfCommAlphaSelf xs n / (n : ℝ) ^ 2 := by
  have h := norm_word_log_le xs.get n hn
  have hxs : (List.finRange xs.length).map xs.get = xs := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  rw [hxs, BCHWordEval.wordSeries_eq_suzuki, BCHWordEval.logCoefficient_eq_existing,
    alphaComm_get_eq_frozen] at h
  exact h

end Qatlib.Papers.CommutLCHS26.MainResults.BCHMatrixBudget
