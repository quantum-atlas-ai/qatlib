/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationBudgetRun

/-!
# Agreement of completed classification scans

`classifyScanBudgeted_completed_matches` connects the query budget implementation to the
unrestricted classification scan. Whenever the budgeted scan finishes without timing out, its
entire result agrees with `classifyScan` on the same inputs and tapes. For background on quantum
search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `classifyScanBudgeted_completed_matches`: If `classifyScanBudgeted` does not time out, its
  result equals that of the unrestricted `classifyScan` with the same graph, parameters, tapes,
  and initial state.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical
variable {n : ℕ}

/-- If `classifyScanBudgeted` does not time out, its result equals that of the unrestricted
`classifyScan` with the same graph, parameters, tapes, and initial state. -/
theorem classifyScanBudgeted_completed_matches (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n) (budget : ℕ)
    (hc : (classifyScanBudgeted G sgs τ K c ttape stape vs S budget).timedOut=false) :
    (classifyScanBudgeted G sgs τ K c ttape stape vs S budget).result=
      classifyScan G sgs τ K c ttape stape vs S := by
  induction vs generalizing S budget with
  | nil => rfl
  | cons v vs ih =>
    rw [classifyScanBudgeted] at hc ⊢
    rw [classifyScan]
    dsimp only at hc ⊢
    by_cases he : pairsAt (drainedPairSet S τ).edges v=∅
    · simp only [if_pos he] at hc ⊢
      simp only [ih (drainedPairSet S τ) budget hc]
    · simp only [if_neg he] at hc ⊢
      by_cases htest : K*c≤ budget
      · simp only [if_pos htest] at hc ⊢
        by_cases hlow : degreeTestLowCorrected (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v K c (ttape v)=true
        · simp only [if_pos hlow] at hc ⊢
          simp only [ih (lowRemaining (drainedPairSet S τ) v) (budget-K*c) hc]
        · simp only [if_neg hlow] at hc ⊢
          by_cases hhigh : n+neighborhoodFee n sgs≤ budget-K*c
          · simp only [if_pos hhigh] at hc ⊢
            cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
            | some p =>
              rcases p with ⟨w,w'⟩
              rfl
            | none =>
              have hfinish := (by simpa only [hrun] using hc :
                (classifyScanBudgeted G sgs τ K c ttape stape vs (highRemaining G (drainedPairSet S τ) v)
                  (budget-(K*c+n+operationalSgsFindCost sgs (neighborhoodMarked G v) 2 (n*n) (stape v)))).timedOut=false)
              simp only [ih _ _ hfinish]
          · simp only [if_neg hhigh] at hc
            cases hc
      · simp only [if_neg htest] at hc
        cases hc
end Qatlib.Concepts.WalkSearch.MainResults
