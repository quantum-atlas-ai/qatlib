/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.ClassificationScan

/-!
# Progress bounds for classification

Proves cardinality monotonicity for draining and low-degree removal, and quantifies the pairs
removed by a correct high-degree step. The accumulated inequality `classifyScan_high_account`
controls the number of high branches using the initial pair count; see [Ambainis2005] for
quantum graph-search background.

## Main statements

* `highStep_progress`: A correct degree test reporting high degree after draining ensures that
  the high-step edge bucket receives at least `dLo * τ` pairs.
* `classifyScan_high_account`: With correct tests, the high-branch count times `dLo * τ` plus
  the final remaining pair count is at most the initial pair count plus `dLo * τ`.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.MainResults
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

/-- Draining a symmetric pair set does not increase its edge cardinality. -/
theorem drainedPairSet_card_le (S : SymmetricPairSet n) (τ : ℕ) :
    (drainedPairSet S τ).edges.card≤S.edges.card := Finset.card_le_card (drainPaired_partition S.edges τ S.edges.card).1

/-- Removing the pairs incident to a low-degree vertex does not increase the edge cardinality. -/
theorem lowRemaining_card_le (S : SymmetricPairSet n) (v : Fin n) :
    (lowRemaining S v).edges.card≤S.edges.card := Finset.card_le_card Finset.sdiff_subset

/-- The remaining high-step pairs and the pairs added to the edge bucket have cardinalities
summing to the original pair cardinality. -/
theorem highRemaining_card_balance (G : UGraph n) (S : SymmetricPairSet n) (v : Fin n) :
    (highRemaining G S v).edges.card+(highEadd G S.edges v).card=S.edges.card :=
  Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)

/-- A correct degree test reporting high degree after draining ensures that the high-step edge
bucket receives at least `dLo * τ` pairs. -/
theorem highStep_progress (G : UGraph n) (S : SymmetricPairSet n) (τ dHi dLo K c : ℕ)
    (v : Fin n) (tape : Fin K→Fin c→Fin n)
    (hc : testCorrectCorrected (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v dHi dLo K c tape)
    (hl : degreeTestLowCorrected (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v K c tape=false) :
    dLo*τ≤(highEadd G (drainedPairSet S τ).edges v).card := by
  have hd : dLo≤degOf (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm).edges v := by
    by_contra h
    have hh:=hc.2 (by omega)
    rw [hl] at hh
    cases hh
  exact (Nat.mul_le_mul_right τ hd).trans
    (highEadd_progress G _ (drainedPairSet S τ).symm v τ (drainPaired_fixpoint S.edges τ S.edges.card le_rfl))

/-- With correct tests, the high-branch count times `dLo * τ` plus the final remaining pair
count is at most the initial pair count plus `dLo * τ`. -/
theorem classifyScan_high_account (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n)
    (hc : classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape vs S) :
    (classifyScan G sgs τ K c ttape stape vs S).highs*(dLo*τ)+
      (classifyScan G sgs τ K c ttape stape vs S).left.card≤S.edges.card+dLo*τ := by
  induction vs generalizing S with
  | nil => simp [classifyScan]
  | cons v vs ih =>
    rw [classifyScanTestsCorrect] at hc
    rw [classifyScan]
    dsimp only at hc ⊢
    have hcard:=drainedPairSet_card_le S τ
    split_ifs with he hl
    · have hh:=ih (drainedPairSet S τ) (by simpa only [if_pos he] using hc)
      exact hh.trans (Nat.add_le_add_right hcard _)
    · have hc' := (by simpa only [if_neg he] using hc :
          testCorrectCorrected (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v dHi dLo K c (ttape v) ∧ _)
      have hh:=ih (lowRemaining (drainedPairSet S τ) v) (by simpa only [if_pos hl] using hc'.2)
      exact hh.trans (Nat.add_le_add_right ((lowRemaining_card_le _ v).trans hcard) _)
    · have hc' := (by simpa only [if_neg he] using hc :
          testCorrectCorrected (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v dHi dLo K c (ttape v) ∧ _)
      have hl' :
          degreeTestLowCorrected
          (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v K c
          (ttape v)=false := Bool.eq_false_iff.mpr hl
      have hp:=highStep_progress G S τ dHi dLo K c v (ttape v) hc'.1 hl'
      cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | some p =>
        rcases p with ⟨w,w'⟩
        (try dsimp only)
        omega
      | none =>
        have hh:=ih (highRemaining G (drainedPairSet S τ) v)
            (by simpa only [if_neg hl,hrun] using hc'.2)
        have hb:=highRemaining_card_balance G (drainedPairSet S τ) v
        (try dsimp only)
        nlinarith
end Qatlib.Concepts.WalkSearch.Primitives
