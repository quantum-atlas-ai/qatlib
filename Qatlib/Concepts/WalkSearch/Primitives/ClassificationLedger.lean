/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.ClassificationScan

/-!
# Query ledgers for classification scans

Defines a uniform neighborhood-search fee and bounds the query cost of a classification scan by
its recorded test and high-branch counts. These estimates supply the resource ledger used in the
graph-search analysis; see [Ambainis2005] for quantum search background.

## Main statements

* `classifyScan_ledger`: For `n > 0`, the scan performs at most one degree test per listed
  vertex, and its queries are bounded by `tests * K * c + highs * (n + neighborhoodFee n sgs)`.
* `neighborhoodSearch_charge`: For `n > 0`, the operational search for a triangle in the
  neighborhood of `v` costs at most `neighborhoodFee n sgs`.

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

/-- The uniform neighborhood-search query reservation `sgs.κ * (Nat.log 2 (n * n + 1) + 2) * 3 *
(n + 1)`. -/
def neighborhoodFee (n : ℕ) (sgs : SGSExecution) : ℕ :=
  sgs.κ*(Nat.log 2 (n*n+1)+2)*3*(n+1)

/-- For `n > 0`, the operational search for a triangle in the neighborhood of `v` costs at most
`neighborhoodFee n sgs`. -/
theorem neighborhoodSearch_charge (G : UGraph n) (sgs : SGSExecution) (v : Fin n) (ρ : sgs.seed) (hn : 0<n) :
    operationalSgsFindCost sgs (neighborhoodMarked G v) 2 (n*n) ρ≤neighborhoodFee n sgs := by
  have hh :=
      sgs.charges (fun i=>neighborhoodMarked G v ((Fintype.equivFin (Fin n×Fin n)).symm i)) 2
      (n*n) ρ
  simp only [Fintype.card_prod,Fintype.card_fin,max_self] at hh
  have hs : Nat.sqrt (n*n+1)≤n := by
    have hsq:=Nat.sqrt_le (n*n+1)
    by_contra h
    have hge : n+1≤Nat.sqrt (n*n+1) := by omega
    have hp:=Nat.mul_le_mul hge hge
    nlinarith
  exact hh.trans (Nat.mul_le_mul_left (sgs.κ*(Nat.log 2 (n*n+1)+2)*3) (by omega))

/-- For `n > 0`, the scan performs at most one degree test per listed vertex, and its queries
are bounded by `tests * K * c + highs * (n + neighborhoodFee n sgs)`. -/
theorem classifyScan_ledger (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n) (hn : 0<n) :
    (classifyScan G sgs τ K c ttape stape vs S).tests≤vs.length ∧
    (classifyScan G sgs τ K c ttape stape vs S).queries≤
      (classifyScan G sgs τ K c ttape stape vs S).tests*K*c+
        (classifyScan G sgs τ K c ttape stape vs S).highs*(n+neighborhoodFee n sgs) := by
  induction vs generalizing S with
  | nil => simp [classifyScan]
  | cons v vs ih =>
    rw [classifyScan]
    (try dsimp only)
    split_ifs with he hl
    · simpa only [List.length_cons] using
        ⟨(ih (drainedPairSet S τ)).1.trans (by omega),(ih (drainedPairSet S τ)).2⟩
    · have hh:=ih (lowRemaining (drainedPairSet S τ) v)
      (try dsimp only)
      constructor
      · simpa only [List.length_cons,Nat.add_comm] using Nat.add_le_add_left hh.1 1
      · nlinarith [hh.2]
    · have hf:=neighborhoodSearch_charge G sgs v (stape v) hn
      cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | none =>
        have hh:=ih (highRemaining G (drainedPairSet S τ) v)
        (try dsimp only)
        constructor
        · simpa only [List.length_cons,Nat.add_comm] using Nat.add_le_add_left hh.1 1
        · nlinarith [hh.2]
      | some p =>
        rcases p with ⟨w,w'⟩
        (try dsimp only)
        constructor
        · simp
        · nlinarith
end Qatlib.Concepts.WalkSearch.Primitives
