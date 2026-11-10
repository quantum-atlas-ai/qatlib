/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationLedger
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationProgress
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationEdgeLedger
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.MainResults
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

theorem classifyScan_high_bound (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n) (hdLo : 0<dLo) (hτ : 0<τ)
    (hc : classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape vs S) :
    (classifyScan G sgs τ K c ttape stape vs S).highs≤n*n/(dLo*τ)+1 := by
  have hh:=classifyScan_high_account G sgs τ dHi dLo K c ttape stape vs S hc
  have hS : S.edges.card≤n*n := by
    simpa only [Fintype.card_prod,Fintype.card_fin] using Finset.card_le_univ S.edges
  have hw : 0<dLo*τ := Nat.mul_pos hdLo hτ
  have hminus : ((classifyScan G sgs τ K c ttape stape vs S).highs-1)*(dLo*τ)≤n*n := by
    by_cases hz : (classifyScan G sgs τ K c ttape stape vs S).highs=0
    · simp [hz]
    · have hge : 1≤(classifyScan G sgs τ K c ttape stape vs S).highs := by omega
      have he:=Nat.sub_add_cancel hge
      nlinarith
  have hdiv := (Nat.le_div_iff_mul_le hw).mpr hminus
  omega

theorem classifyScan_cost_bound (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (S : SymmetricPairSet n) (hn : 0<n) (hdLo : 0<dLo) (hτ : 0<τ)
    (hc : classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape Finset.univ.toList S) :
    (classifyScan G sgs τ K c ttape stape Finset.univ.toList S).queries≤classifyBudgetCorrected n dLo τ K c sgs := by
  have hl:=classifyScan_ledger G sgs τ K c ttape stape Finset.univ.toList S hn
  have ht : (classifyScan G sgs τ K c ttape stape Finset.univ.toList S).tests≤n := by
    simpa only [Finset.length_toList,Finset.card_univ,Fintype.card_fin] using hl.1
  have hh:=classifyScan_high_bound G sgs τ dHi dLo K c ttape stape Finset.univ.toList S hdLo hτ hc
  have htest:=Nat.mul_le_mul_right (K*c) ht
  have hhigh:=Nat.mul_le_mul_right (n+neighborhoodFee n sgs) hh
  dsimp only [classifyBudgetCorrected,neighborhoodFee] at *
  nlinarith [hl.2]

theorem classifyScan_E_bound (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c tThin : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (S : SymmetricPairSet n) (hn : 0<n) (hdLo : 0<dLo) (hτ : 0<τ)
    (hc : classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape Finset.univ.toList S)
    (hthin : S.edges⊆thinPairs G.edges tThin) :
    ((classifyScan G sgs τ K c ttape stape Finset.univ.toList S).movedE∩G.edges).card≤
      2*n*dHi+(n*n/(dLo*τ)+1)*(2*n*(tThin+1)) := by
  have hl:=classifyScan_ledger G sgs τ K c ttape stape Finset.univ.toList S hn
  have ht : (classifyScan G sgs τ K c ttape stape Finset.univ.toList S).tests≤n := by
    simpa only [Finset.length_toList,Finset.card_univ,Fintype.card_fin] using hl.1
  have hh:=classifyScan_high_bound G sgs τ dHi dLo K c ttape stape Finset.univ.toList S hdLo hτ hc
  have he:=classifyScan_edge_account G sgs τ dHi dLo K c tThin ttape stape Finset.univ.toList S hc hthin
  have htest:=Nat.mul_le_mul_left (2*dHi) ht
  have hhigh:=Nat.mul_le_mul_left (2*n*(tThin+1)) hh
  nlinarith
end Qatlib.Concepts.WalkSearch.Primitives
