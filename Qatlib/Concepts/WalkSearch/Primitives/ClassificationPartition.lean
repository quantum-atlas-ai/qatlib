/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.ClassificationPartitionHelpers

/-!
# Partition invariant of classification

Proves that `classifyScan` partitions its original pair set into the remaining pairs, the
triangle-removal trace, and the edge bucket. The invariant includes pairwise disjointness and
absence of repetitions in the trace, providing combinatorial infrastructure for graph search as
surveyed in [Ambainis2005].

## Main statements

* `classifyScan_partition`: Every classification scan satisfies `partitionPayload`: its
  remaining pairs, triangle-removal trace, and edge bucket form a disjoint partition of the
  original pairs, and the trace has no repetitions.

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

/-- Every classification scan satisfies `partitionPayload`: its remaining pairs,
triangle-removal trace, and edge bucket form a disjoint partition of the original pairs, and
the trace has no repetitions. -/
theorem classifyScan_partition (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n) :
    partitionPayload S.edges (classifyScan G sgs τ K c ttape stape vs S).left
      (classifyScan G sgs τ K c ttape stape vs S).movedT
      (classifyScan G sgs τ K c ttape stape vs S).movedE := by
  induction vs generalizing S with
  | nil => simp [classifyScan,partitionPayload]
  | cons v vs ih =>
    have hd:=drainPaired_partition S.edges τ S.edges.card
    have hdn:=drainPaired_trace_nodup S.edges τ S.edges.card
    rw [classifyScan]
    (try dsimp only)
    split_ifs with he hl
    · exact partitionPayload_addT hd.2.2.1 hd.2.2.2 hdn (ih (drainedPairSet S τ))
    · exact partitionPayload_addT hd.2.2.1 hd.2.2.2 hdn
        (partitionPayload_addE (Finset.filter_subset _ _) (ih (lowRemaining (drainedPairSet S τ) v)))
    · cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | none =>
        (try dsimp only)
        exact partitionPayload_addT hd.2.2.1 hd.2.2.2 hdn
          (partitionPayload_addE (Finset.filter_subset _ _) (ih (highRemaining G (drainedPairSet S τ) v)))
      | some p =>
        rcases p with ⟨w,w'⟩
        (try dsimp only)
        have hbase : partitionPayload (drainedPairSet S τ).edges (drainedPairSet S τ).edges [] ∅ := by
          simp [partitionPayload]
        simpa only [List.append_nil] using partitionPayload_addT hd.2.2.1 hd.2.2.2 hdn hbase
end Qatlib.Concepts.WalkSearch.Primitives
