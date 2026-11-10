/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.SearchPreflight
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.MainResults
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

structure ClassificationBudgetResult (n : ℕ) where
  result : ClassificationRun n
  timedOut : Bool

def classifyScanBudgeted (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed) :
    List (Fin n)→SymmetricPairSet n→ℕ→ClassificationBudgetResult n
  | [],S,_=>⟨⟨none,S.edges,[],∅,0,0,0⟩,false⟩
  | v::vs,S,budget=>
    let Sd:=drainedPairSet S τ
    let Td:=(drainPaired S.edges τ S.edges.card).2
    if pairsAt Sd.edges v=∅ then
      let r:=classifyScanBudgeted G sgs τ K c ttape stape vs Sd budget
      ⟨⟨r.result.triangle,r.result.left,Td++r.result.movedT,r.result.movedE,
        r.result.queries,r.result.tests,r.result.highs⟩,r.timedOut⟩
    else if K*c ≤ budget then
      if degreeTestLowCorrected (presentGraph G Sd.edges Sd.symm) v K c (ttape v) then
        let r:=classifyScanBudgeted G sgs τ K c ttape stape vs (lowRemaining Sd v) (budget-K*c)
        ⟨⟨r.result.triangle,r.result.left,Td++r.result.movedT,pairsAt Sd.edges v∪r.result.movedE,
          K*c+r.result.queries,1+r.result.tests,r.result.highs⟩,r.timedOut⟩
      else if n+neighborhoodFee n sgs ≤ budget-K*c then
        let marked:=neighborhoodMarked G v
        let fee:=operationalSgsFindCost sgs marked 2 (n*n) (stape v)
        match operationalSgsFind sgs marked 2 (n*n) (stape v) with
        | some (w,w')=>⟨⟨some (v,w,w'),Sd.edges,Td,∅,K*c+n+fee,1,1⟩,false⟩
        | none=>
          let r:=classifyScanBudgeted G sgs τ K c ttape stape vs (highRemaining G Sd v)
              (budget-(K*c+n+fee))
          ⟨⟨r.result.triangle,r.result.left,Td++r.result.movedT,highEadd G Sd.edges v∪r.result.movedE,
            K*c+n+fee+r.result.queries,1+r.result.tests,1+r.result.highs⟩,r.timedOut⟩
      else ⟨⟨none,Sd.edges,Td,∅,K*c,1,0⟩,true⟩
    else ⟨⟨none,Sd.edges,Td,∅,0,0,0⟩,true⟩

theorem classifyScanBudgeted_cost (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n) (budget : ℕ) (hn : 0< n) :
    (classifyScanBudgeted G sgs τ K c ttape stape vs S budget).result.queries≤ budget := by
  induction vs generalizing S budget with
  | nil => simp [classifyScanBudgeted]
  | cons v vs ih =>
    rw [classifyScanBudgeted]
    (try dsimp only)
    split_ifs with he htest hlow hhigh
    · exact ih _ _
    · have hh:=ih (lowRemaining (drainedPairSet S τ) v) (budget-K*c)
      (try dsimp only)
      omega
    · have hf:=neighborhoodSearch_charge G sgs v (stape v) hn
      cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | some p =>
        rcases p with ⟨w,w'⟩
        (try dsimp only)
        omega
      | none=>
        have hh:=ih (highRemaining G (drainedPairSet S τ) v)
          (budget-(K*c+n+operationalSgsFindCost sgs (neighborhoodMarked G v) 2 (n*n) (stape v)))
        (try dsimp only)
        omega
    · (try dsimp only)
      exact htest
    · simp
end Qatlib.Concepts.WalkSearch.Primitives
