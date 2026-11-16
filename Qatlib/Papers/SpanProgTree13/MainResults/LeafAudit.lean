/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpanProgTree13.MainResults.RootedTreeChain

@[expose] public section

set_option autoImplicit false
namespace Qatlib.Papers.SpanProgTree13.MainResults.LeafAudit
open Qatlib.Papers.SpanProgTree13.MainResults
/-- The legacy predicate classifies exactly the root as a leaf. -/
theorem legacyLeafRoot {V : Type*} [Fintype V] (t : RootedTree V) (v : V) :
    t.IsLeaf v ↔ v = t.root := by
  constructor
  · intro h
    by_contra hv
    exact h (t.parB v) (t.par_parB hv)
  · rintro rfl a h
    have hp := t.par_root
    unfold RootedTree.child at h
    rw [hp] at h
    cases h
/-- Every non-root vertex fails the legacy leaf predicate. -/
theorem nonrootNotLeaf {V : Type*} [Fintype V] (t : RootedTree V) (v : V)
    (hv : v ≠ t.root) : ¬ t.IsLeaf v := by
  intro h
  exact hv ((legacyLeafRoot t v).mp h)
end Qatlib.Papers.SpanProgTree13.MainResults.LeafAudit
