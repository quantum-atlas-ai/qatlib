/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.ClassificationScan

/-!
# Sound triangle outputs from classification

Proves witness soundness for neighborhood search and the full classification scan. Every
reported triple forms a triangle in the input graph, independently of the degree-test
correctness assumptions used in separate resource bounds; see [Ambainis2005] for quantum search
background.

## Main statements

* `neighborhoodSearch_sound`: A pair returned by the operational neighborhood search at `v`
  forms a triangle with `v`, with all three required edges in `G.edges`.
* `classifyScan_sound`: Every triple returned by `classifyScan` satisfies `tri3` and has all
  three required edges in `G.edges`.

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

/-- A pair returned by the operational neighborhood search at `v` forms a triangle with `v`,
with all three required edges in `G.edges`. -/
theorem neighborhoodSearch_sound (G : UGraph n) (sgs : SGSExecution) (v : Fin n) (ρ : sgs.seed)
    (w w' : Fin n) (h : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) ρ=some (w,w')) :
    tri3 G.edges v w w' ∧ (v,w)∈G.edges ∧ (v,w')∈G.edges ∧ (w,w')∈G.edges := by
  have hm:=operationalSgsFind_sound sgs (neighborhoodMarked G v) 2 (n*n) ρ (w,w') h
  simp only [neighborhoodMarked,decide_eq_true_eq] at hm
  have h1 : (v,w)∈G.edges := (mem_graph_nbr_iff G v w).mp hm.1
  have h2 : (v,w')∈G.edges := (mem_graph_nbr_iff G v w').mp hm.2.1
  have h3 : (w,w')∈G.edges := hm.2.2
  have hne1 : v≠w := by intro he;subst w;exact G.loopless v h1
  have hne2 : v≠w' := by intro he;subst w';exact G.loopless v h2
  have hne3 : w≠w' := by intro he;subst w';exact G.loopless w h3
  exact ⟨(tri3_iff _ _ _ _).mpr ⟨hne1,hne3,hne2,Or.inl h1,Or.inl h3,Or.inl h2⟩,h1,h2,h3⟩

/-- Every triple returned by `classifyScan` satisfies `tri3` and has all three required edges in
`G.edges`. -/
theorem classifyScan_sound (G : UGraph n) (sgs : SGSExecution) (τ K c : ℕ)
    (ttape : Fin n→Fin K→Fin c→Fin n) (stape : Fin n→sgs.seed)
    (vs : List (Fin n)) (S : SymmetricPairSet n) :
    ∀ a b cc,(classifyScan G sgs τ K c ttape stape vs S).triangle=some (a,b,cc)→
      tri3 G.edges a b cc ∧ (a,b)∈G.edges ∧ (a,cc)∈G.edges ∧ (b,cc)∈G.edges := by
  induction vs generalizing S with
  | nil => simp [classifyScan]
  | cons v vs ih =>
    rw [classifyScan]
    (try dsimp only)
    split_ifs with he hl
    · exact ih (drainedPairSet S τ)
    · exact ih (lowRemaining (drainedPairSet S τ) v)
    · cases hrun : operationalSgsFind sgs (neighborhoodMarked G v) 2 (n*n) (stape v) with
      | none => exact ih (highRemaining G (drainedPairSet S τ) v)
      | some p =>
        rcases p with ⟨w,w'⟩
        intro a b cc hout
        dsimp only at hout
        have hp:=Prod.mk.inj (Option.some.inj hout)
        have hp2:=Prod.mk.inj hp.2
        rw [← hp.1,← hp2.1,← hp2.2]
        exact neighborhoodSearch_sound G sgs v (stape v) w w' hrun
end Qatlib.Concepts.WalkSearch.Primitives
