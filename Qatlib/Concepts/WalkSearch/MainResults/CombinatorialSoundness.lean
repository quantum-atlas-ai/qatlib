/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialBudgetRun

/-!
# Soundness of combinatorial triangle outputs

`CombOut.Sound` states that a returned triple is a triangle with all three graph edges, while
placing no condition on rejection outputs. `sourceCombAlg_sound_at` verifies this property for
each tape and `sourceCombAlg_sound` packages it as universal algorithm soundness. For background
on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `CombOut.Sound`: A triangle output satisfies `tri3` and has all three edges in `G`; a
  rejection output satisfies this predicate automatically.
* `sourceCombAlg_sound`: The combinatorial algorithm satisfies `sourceCombSound` for all graphs,
  search families, and integer parameters.

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

/-- A triangle output satisfies `tri3` and has all three edges in `G`; a rejection output
satisfies this predicate automatically. -/
def CombOut.Sound (G : UGraph n) : CombOut n→Prop
  | .tri a b c _=>tri3 G.edges a b c ∧ (a,b)∈G.edges ∧ (a,c)∈G.edges ∧ (b,c)∈G.edges
  | .reject _=>True

/-- The output of `sourceCombAlg` is sound for every fixed tape and every choice of its integer
parameters. -/
theorem sourceCombAlg_sound_at (G : UGraph n) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily)
    (k K c dHi dLo τ tThin : ℕ) (t : sourceCombTape n k K c sgs ets) :
    Qatlib.Concepts.WalkSearch.MainResults.CombOut.Sound G (sourceCombAlg G sgs ets k K c dHi dLo τ tThin t) := by
  let S : SymmetricPairSet n:=⟨sampledSurvivors G t.1,sampledSurvivors_symmetric G t.1⟩
  unfold sourceCombAlg
  (try dsimp only)
  cases h0 : (preparationScan G sgs t.2.1 (Finset.univ.image t.1).toList).triangle with
  | some p=>
    rcases p with ⟨a,b,cc⟩
    exact preparationScan_sound G sgs t.2.1 _ a b cc h0
  | none=>
    (try dsimp only)
    split_ifs with ht
    · trivial
    · have hfinish:=classifyScanBudgeted_completed_matches G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
        (classifyBudgetCorrected n dLo τ K c sgs) (Bool.eq_false_iff.mpr ht)
      cases h1 : (classifyScanBudgeted G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
        (classifyBudgetCorrected n dLo τ K c sgs)).result.triangle with
      | some p=>
        rcases p with ⟨a,b,cc⟩
        exact classifyScan_sound G sgs τ K c t.2.2.1 t.2.2.2.1 _ S a b cc
            (by simpa only [hfinish] using h1)
      | none=>
        let T:=(classifyScanBudgeted G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
          (classifyBudgetCorrected n dLo τ K c sgs)).result.movedT.toFinset
        let E:=(classifyScanBudgeted G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
          (classifyBudgetCorrected n dLo τ K c sgs)).result.movedE
        cases hT :
            safeGroverPreflight sgs (triangleMarked G T) 3 (n*n)
            (sourceTriangleReservation sgs n τ) t.2.2.2.2.1 with
        | timeout=>trivial
        | completed out qT=>
          cases out with
          | some tri=>
            have hrun:=safeGroverPreflight_output sgs (triangleMarked G T) 3 (n*n)
                (sourceTriangleReservation sgs n τ) t.2.2.2.2.1 (some tri) qT hT
            exact triangleMarked_sound G T tri
                (operationalSgsFind_sound sgs (triangleMarked G T) 3 (n*n) t.2.2.2.2.1 tri hrun)
          | none=>
            cases hE : ets.run G E (sourceEdgeMassBound n dHi dLo τ tThin) t.2.2.2.2.2 with
            | none=>trivial
            | some p=>
              rcases p with ⟨a,b,cc⟩
              obtain ⟨h1,h2,h3,_,ha,hb,hc⟩:=ets.sound G E _ _ hE
              exact ⟨(tri3_iff _ _ _ _).mpr ⟨h1,h2,h3,Or.inl ha,Or.inl hc,Or.inl hb⟩,ha,hb,hc⟩

/-- The combinatorial algorithm satisfies `sourceCombSound` for all graphs, search families, and
integer parameters. -/
theorem sourceCombAlg_sound (G : UGraph n) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily)
    (k K c dHi dLo τ tThin : ℕ) : sourceCombSound G sgs ets k K c dHi dLo τ tThin := by
  intro t a b cc q hout
  have hs:=sourceCombAlg_sound_at G sgs ets k K c dHi dLo τ tThin t
  simpa only [hout,CombOut.Sound] using hs
end Qatlib.Concepts.WalkSearch.MainResults
