/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.PairedDrainTrace
import Qatlib.Concepts.WalkSearch.MainResults.IncidentCrossBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators
variable {n : ℕ}

structure SymmetricPairSet (n : ℕ) where
  edges : Finset (Fin n×Fin n)
  symm : pairSetSymmetric edges

theorem pairsAt_symmetric (S : Finset (Fin n×Fin n)) (hS : pairSetSymmetric S) (v : Fin n) :
    pairSetSymmetric (pairsAt S v) := by
  intro a b h
  simp only [pairsAt,Finset.mem_filter] at h ⊢
  exact ⟨hS a b h.1,h.2.elim Or.inr Or.inl⟩

def drainedPairSet (S : SymmetricPairSet n) (τ : ℕ) : SymmetricPairSet n :=
  ⟨(drainPaired S.edges τ S.edges.card).1,drainPaired_symmetric S.edges S.symm τ S.edges.card⟩

def lowRemaining (S : SymmetricPairSet n) (v : Fin n) : SymmetricPairSet n :=
  ⟨S.edges\pairsAt S.edges v,symmetric_sdiff S.symm (pairsAt_symmetric S.edges S.symm v)⟩

def highRemaining (G : UGraph n) (S : SymmetricPairSet n) (v : Fin n) : SymmetricPairSet n :=
  ⟨S.edges\highEadd G S.edges v,symmetric_sdiff S.symm (highEadd_symmetric G S.edges S.symm v)⟩

structure ClassificationRun (n : ℕ) where
  triangle : Option (Fin n×Fin n×Fin n)
  left : Finset (Fin n×Fin n)
  movedT : List (Fin n×Fin n)
  movedE : Finset (Fin n×Fin n)
  queries : ℕ
  tests : ℕ
  highs : ℕ

def neighborhoodMarked (G : UGraph n) (v : Fin n) : (Fin n×Fin n)→Bool :=
  fun p=>decide (p.1∈nbrOf G.edges v ∧ p.2∈nbrOf G.edges v ∧ p∈G.edges)

def classifyScan (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed) :
    List (Fin n)→SymmetricPairSet n→ClassificationRun n
  | [],S=>⟨none,S.edges,[],∅,0,0,0⟩
  | v::vs,S=>
    let Sd:=drainedPairSet S τ
    let Td:=(drainPaired S.edges τ S.edges.card).2
    if pairsAt Sd.edges v=∅ then
      let r:=classifyScan G sgs τ K c ttape stape vs Sd
      ⟨r.triangle,r.left,Td++r.movedT,r.movedE,r.queries,r.tests,r.highs⟩
    else if degreeTestLowCorrected (presentGraph G Sd.edges Sd.symm) v K c (ttape v) then
      let r:=classifyScan G sgs τ K c ttape stape vs (lowRemaining Sd v)
      ⟨r.triangle,r.left,Td++r.movedT,pairsAt Sd.edges v∪r.movedE,K*c+r.queries,1+r.tests,r.highs⟩
    else
      let marked:=neighborhoodMarked G v
      let fee:=operationalSgsFindCost sgs marked 2 (n*n) (stape v)
      match operationalSgsFind sgs marked 2 (n*n) (stape v) with
      | some (w,w')=>⟨some (v,w,w'),Sd.edges,Td,∅,K*c+n+fee,1,1⟩
      | none=>
        let r:=classifyScan G sgs τ K c ttape stape vs (highRemaining G Sd v)
        ⟨r.triangle,r.left,Td++r.movedT,highEadd G Sd.edges v∪r.movedE,K*c+n+fee+r.queries,1+r.tests,1+r.highs⟩

def classifyScanTestsCorrect (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed) :
    List (Fin n)→SymmetricPairSet n→Prop
  | [],_=>True
  | v::vs,S=>
    let Sd:=drainedPairSet S τ
    if pairsAt Sd.edges v=∅ then
      classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape vs Sd
    else
      testCorrectCorrected (presentGraph G Sd.edges Sd.symm) v dHi dLo K c (ttape v) ∧
      if degreeTestLowCorrected (presentGraph G Sd.edges Sd.symm) v K c (ttape v) then
        classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape vs (lowRemaining Sd v)
      else
        match operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
        | some _=>True
        | none=>classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape vs (highRemaining G Sd v)

def classifyBudgetCorrected (n dLo τ K c : ℕ) (sgs : SGSExecution) : ℕ :=
  n*K*c+(n*n/(dLo*τ)+1)*(n+sgs.κ*(Nat.log 2 (n*n+1)+2)*3*(n+1))
end Qatlib.Concepts.WalkSearch.MainResults
