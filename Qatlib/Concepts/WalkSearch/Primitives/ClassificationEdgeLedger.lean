/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.ClassificationScan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.MainResults
set_option autoImplicit false
set_option maxHeartbeats 1200000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

theorem lowStep_graph_card (G : UGraph n) (S : SymmetricPairSet n) (dHi dLo K c : ℕ)
    (v : Fin n) (tape : Fin K→Fin c→Fin n)
    (hc : testCorrectCorrected (presentGraph G S.edges S.symm) v dHi dLo K c tape)
    (hl : degreeTestLowCorrected (presentGraph G S.edges S.symm) v K c tape=true) :
    (pairsAt S.edges v∩G.edges).card≤2*dHi := by
  have hd : degOf (presentGraph G S.edges S.symm).edges v≤dHi := by
    by_contra h
    have hh:=hc.1 (by omega)
    rw [hl] at hh
    cases hh
  rw [pairsAt_inter_graph]
  exact (pairsAt_card_le_twice_degree (G.edges∩S.edges) v).trans (Nat.mul_le_mul_left 2 hd)

theorem classifyScan_edge_account (G : UGraph n) (sgs : SGSExecution) (τ dHi dLo K c tThin : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n)
    (hc : classifyScanTestsCorrect G sgs τ dHi dLo K c ttape stape vs S)
    (hthin : S.edges⊆thinPairs G.edges tThin) :
    ((classifyScan G sgs τ K c ttape stape vs S).movedE∩G.edges).card≤
      2*dHi*(classifyScan G sgs τ K c ttape stape vs S).tests+
        2*n*(tThin+1)*(classifyScan G sgs τ K c ttape stape vs S).highs := by
  induction vs generalizing S with
  | nil => simp [classifyScan]
  | cons v vs ih =>
    have hd : (drainedPairSet S τ).edges⊆S.edges := (drainPaired_partition S.edges τ S.edges.card).1
    have hthinD := hd.trans hthin
    rw [classifyScanTestsCorrect] at hc
    rw [classifyScan]
    dsimp only at hc ⊢
    split_ifs with he hl
    · exact ih (drainedPairSet S τ) (by simpa only [if_pos he] using hc) hthinD
    · have hc' := (by simpa only [if_neg he] using hc :
          testCorrectCorrected (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v dHi dLo K c (ttape v) ∧ _)
      have hh:=ih (lowRemaining (drainedPairSet S τ) v) (by simpa only [if_pos hl] using hc'.2)
          (Finset.sdiff_subset.trans hthinD)
      have hb:=lowStep_graph_card G (drainedPairSet S τ) dHi dLo K c v (ttape v) hc'.1 hl
      (try dsimp only)
      rw [Finset.union_inter_distrib_right]
      have hsum := Finset.card_union_le (pairsAt (drainedPairSet S τ).edges v∩G.edges)
        ((classifyScan G sgs τ K c ttape stape vs (lowRemaining (drainedPairSet S τ) v)).movedE∩G.edges)
      nlinarith
    · have hc' := (by simpa only [if_neg he] using hc :
          testCorrectCorrected (presentGraph G (drainedPairSet S τ).edges (drainedPairSet S τ).symm) v dHi dLo K c (ttape v) ∧ _)
      cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | some p =>
        rcases p with ⟨w,w'⟩
        simp
      | none =>
        have hh:=ih (highRemaining G (drainedPairSet S τ) v)
            (by simpa only [if_neg hl,hrun] using hc'.2) (Finset.sdiff_subset.trans hthinD)
        have hb:=highEadd_graph_card G (drainedPairSet S τ).edges
            (drainedPairSet S τ).symm v tThin hthinD
        (try dsimp only)
        rw [Finset.union_inter_distrib_right]
        have hsum := Finset.card_union_le (highEadd G (drainedPairSet S τ).edges v∩G.edges)
          ((classifyScan G sgs τ K c ttape stape vs (highRemaining G (drainedPairSet S τ) v)).movedE∩G.edges)
        nlinarith
end Qatlib.Concepts.WalkSearch.Primitives
