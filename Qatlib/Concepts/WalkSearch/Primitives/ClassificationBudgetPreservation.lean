/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationBudgetRun
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationBounds

/-!
# Preservation under classification budgets

Defines the worst-case reservation for a classification run and proves that a sufficient budget
preserves its full result without timeout. In particular, the corrected source budget suffices
when the complete scan's tests are correct, connecting query accounting with the graph-search
setting of [Ambainis2005].

## Main statements

* `classifyScanBudgeted_preserves`: If the reservation of the ordinary scan fits the budget and
  `n > 0`, the budgeted scan returns exactly the same classification result with `timedOut =
  false`.
* `classifyScanBudgeted_correct_execution`: With correct complete-scan tests and positive `n`,
  `dLo`, and `τ`, the corrected classification budget yields the ordinary scan result without
  timeout.

## References

* [Ambainis, 2005][Ambainis2005]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.MainResults
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

/-- The reserved query count for a classification run: its test count times `K * c`, plus its
high-branch count times `n + neighborhoodFee n sgs`. -/
def classificationReservation (sgs : SGSExecution) (K c : ℕ) (r : ClassificationRun n) : ℕ :=
  r.tests*K*c+r.highs*(n+neighborhoodFee n sgs)

/-- If the reservation of the ordinary scan fits the budget and `n > 0`, the budgeted scan
returns exactly the same classification result with `timedOut = false`. -/
theorem classifyScanBudgeted_preserves (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n) (budget : ℕ) (hn : 0<n)
    (hR : classificationReservation sgs K c (classifyScan G sgs τ K c ttape stape vs S)≤budget) :
    classifyScanBudgeted G sgs τ K c ttape stape vs S budget=
      ⟨classifyScan G sgs τ K c ttape stape vs S,false⟩ := by
  induction vs generalizing S budget with
  | nil => rfl
  | cons v vs ih =>
    rw [classificationReservation,classifyScan] at hR
    rw [classifyScanBudgeted,classifyScan]
    dsimp only at hR ⊢
    by_cases he : pairsAt (drainedPairSet S τ).edges v=∅
    · simp only [if_pos he] at hR ⊢
      rw [ih (drainedPairSet S τ) budget hR]
    · simp only [if_neg he] at hR ⊢
      by_cases hl : degreeTestLowCorrected (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v K c (ttape v)=true
      · simp only [if_pos hl] at hR
        have hclean : K*c+classificationReservation sgs K c (classifyScan G sgs τ K c ttape stape vs (lowRemaining (drainedPairSet S τ) v))≤budget := by
          dsimp only [classificationReservation]
          nlinarith [hR]
        have htest : K*c≤budget := by omega
        have hrest :
            classificationReservation sgs K c
            (classifyScan G sgs τ K c ttape stape vs (lowRemaining (drainedPairSet S τ) v))≤budget-K*c := by omega
        rw [if_pos htest,if_pos hl,ih _ _ hrest]
        simp only [if_pos hl]
      · simp only [if_neg hl] at hR
        have hf:=neighborhoodSearch_charge G sgs v (stape v) hn
        cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
        | some p =>
          rw [hrun] at hR
          rcases p with ⟨w,w'⟩
          dsimp only at hR ⊢
          have hclean : K*c+n+neighborhoodFee n sgs≤budget := by nlinarith [hR]
          have htest : K*c≤budget := by omega
          have hhigh : n+neighborhoodFee n sgs≤budget-K*c := by omega
          rw [if_pos htest,if_neg hl,if_pos hhigh]
          simp only [if_neg hl]
        | none =>
          rw [hrun] at hR
          dsimp only at hR ⊢
          have hclean : K*c+(n+neighborhoodFee n sgs)+classificationReservation sgs K c
              (classifyScan G sgs τ K c ttape stape vs (highRemaining G (drainedPairSet S τ) v))≤budget := by
            dsimp only [classificationReservation]
            nlinarith [hR]
          have htest : K*c≤budget := by omega
          have hhigh : n+neighborhoodFee n sgs≤budget-K*c := by omega
          have hrest : classificationReservation sgs K c (classifyScan G sgs τ K c ttape stape vs (highRemaining G (drainedPairSet S τ) v))≤
              budget-(K*c+n+operationalSgsFindCost sgs (neighborhoodMarked G v) 2 (n*n) (stape v)) := by omega
          rw [if_pos htest,if_neg hl,if_pos hhigh,ih _ _ hrest]
          simp only [if_neg hl]

/-- For a complete scan with correct tests and positive `n`, `dLo`, and `τ`, its reservation is
at most the corrected classification budget. -/
theorem classifyScan_source_reservation (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (S : SymmetricPairSet n) (hn : 0<n) (hdLo : 0<dLo) (hτ : 0<τ)
    (hc : classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape Finset.univ.toList S) :
    classificationReservation sgs K c (classifyScan G sgs τ K c ttape stape Finset.univ.toList S)≤
      classifyBudgetCorrected n dLo τ K c sgs := by
  have hl:=classifyScan_ledger G sgs τ K c ttape stape Finset.univ.toList S hn
  have ht : (classifyScan G sgs τ K c ttape stape Finset.univ.toList S).tests≤n := by
    simpa only [Finset.length_toList,Finset.card_univ,Fintype.card_fin] using hl.1
  have hh:=classifyScan_high_bound G sgs τ dHi dLo K c ttape stape Finset.univ.toList S hdLo hτ hc
  have htest:=Nat.mul_le_mul_right (K*c) ht
  have hhigh:=Nat.mul_le_mul_right (n+neighborhoodFee n sgs) hh
  dsimp only [classificationReservation,classifyBudgetCorrected,neighborhoodFee] at *
  nlinarith

/-- With correct complete-scan tests and positive `n`, `dLo`, and `τ`, the corrected
classification budget yields the ordinary scan result without timeout. -/
theorem classifyScanBudgeted_correct_execution (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (S : SymmetricPairSet n) (hn : 0<n) (hdLo : 0<dLo) (hτ : 0<τ)
    (hc : classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape Finset.univ.toList S) :
    classifyScanBudgeted G sgs τ K c ttape stape Finset.univ.toList S (classifyBudgetCorrected n dLo τ K c sgs)=
      ⟨classifyScan G sgs τ K c ttape stape Finset.univ.toList S,false⟩ :=
  classifyScanBudgeted_preserves G sgs τ K c ttape stape _ _ _ hn
    (classifyScan_source_reservation G sgs τ dHi dLo K c ttape stape S hn hdLo hτ hc)
end Qatlib.Concepts.WalkSearch.Primitives
