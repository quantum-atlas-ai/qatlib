/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialCallScopes
import Qatlib.Concepts.WalkSearch.MainResults.SearchEventBounds
import Qatlib.Concepts.WalkSearch.MainResults.ClassificationAdaptiveTape

/-!
# Successful tapes prevent combinatorial rejection

`sourceTapeClass` extracts the unrestricted classification run determined by a complete
algorithm tape. `sourceComb_good_tape_not_reject` proves that a graph containing a triangle
avoids rejection when sampling, preparation, degree tests, and the two final searches satisfy
their stated guarantees. For background on quantum search and amplitude amplification, see
[BrassardEtAl2002].

## Main statements

* `sourceTapeClass`: Run the unrestricted classification scan from the sampled survivor set
  using the classification components of a complete source tape.
* `sourceComb_good_tape_not_reject`: If a triangle exists and the tape satisfies the sampling,
  preparation, degree test, and final search guarantees, then `sourceCombAlg` does not reject
  under the stated positive threshold assumptions.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkSearch.Primitives

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical BigOperators

/-- Run the unrestricted classification scan from the sampled survivor set using the
classification components of a complete source tape. -/
def sourceTapeClass {n : ℕ} (G : UGraph n) (sgs : SGSExecution)
    (ets : PromisedEdgeSearchFamily) (k K c τ : ℕ) (t : sourceCombTape n k K c sgs ets) : ClassificationRun n :=
  classifyScan G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList
    ⟨sampledSurvivors G t.1, sampledSurvivors_symmetric G t.1⟩

/-- If a triangle exists and the tape satisfies the sampling, preparation, degree test, and
final search guarantees, then `sourceCombAlg` does not reject under the stated positive
threshold assumptions. -/
theorem sourceComb_good_tape_not_reject {n : ℕ} (G : UGraph n) (sgs : SGSExecution)
    (ets : PromisedEdgeSearchFamily) (k K c dHi dLo τ tThin : ℕ)
    (t : sourceCombTape n k K c sgs ets) (hn : 0 < n) (hdLo : 1 ≤ dLo)
    (hhi : dLo ≤ dHi) (hτ : 1 ≤ τ) (htri : 1 ≤ triCount G.edges)
    (hsample : sampledSurvivors G t.1 ⊆ thinPairs G.edges tThin)
    (hprep : preparationCallsGood G sgs t.2.1 (Finset.univ.image t.1).toList)
    (htest : classifyScanTestsCorrect G sgs τ dHi dLo K c t.2.2.1 t.2.2.2.1
      Finset.univ.toList ⟨sampledSurvivors G t.1, sampledSurvivors_symmetric G t.1⟩)
    (hT : (∃ z, triangleMarked G (sourceTapeClass G sgs ets k K c τ t).movedT.toFinset z = true) →
      operationalSgsFind sgs (triangleMarked G (sourceTapeClass G sgs ets k K c τ t).movedT.toFinset)
        3 (n*n) t.2.2.2.2.1 ≠ none)
    (hE : edgeTriangleExists G (sourceTapeClass G sgs ets k K c τ t).movedE →
      ets.run G (sourceTapeClass G sgs ets k K c τ t).movedE
        (sourceEdgeMassBound n dHi dLo τ tThin) t.2.2.2.2.2 ≠ none) :
    ¬ sourceCombRejects G sgs ets k K c dHi dLo τ tThin t := by
  let S : SymmetricPairSet n := ⟨sampledSurvivors G t.1, sampledSurvivors_symmetric G t.1⟩
  let r := sourceTapeClass G sgs ets k K c τ t
  have hc := classifyScanBudgeted_correct_execution G sgs τ dHi dLo K c
    t.2.2.1 t.2.2.2.1 S hn (by omega) (by omega) htest
  change classifyScanBudgeted G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
      (classifyBudgetCorrected n dLo τ K c sgs) = ⟨r, false⟩ at hc
  unfold sourceCombRejects sourceCombAlg
  (try dsimp only)
  cases hp : (preparationScan G sgs t.2.1 (Finset.univ.image t.1).toList).triangle with
  | some p => rcases p with ⟨a,b,cc⟩; simp
  | none =>
    (try dsimp only)
    change ¬ (match (if _ then _ else _ : CombOut n) with | CombOut.tri _ _ _ _ => False | CombOut.reject _ => True)
    rw [hc]
    simp only [Bool.false_eq_true, if_false]
    have hG := preparationScan_survivors_contain_graph G sgs t.2.1 t.1 hprep hp
    have hspec := (classifySpec_source_complete n G sgs τ dHi dLo K c tThin
      hn hdLo hhi hτ t.2.2.1 t.2.2.2.1 S hG hsample htest).2
    change (match r.triangle with | some (a,b,cc) => _ | none => _) at hspec
    cases hr : r.triangle with
    | some p => rcases p with ⟨a,b,cc⟩; simp
    | none =>
      rw [hr] at hspec
      change r.movedT.toFinset ∪ r.movedE = S.edges ∧ Disjoint r.movedT.toFinset r.movedE ∧
        triCount r.movedT.toFinset ≤ n.choose 2*τ ∧ (r.movedE ∩ G.edges).card ≤ sourceEdgeMassBound n dHi dLo τ tThin at hspec
      have hcover : G.edges ⊆ r.movedT.toFinset ∪ r.movedE := by
        rw [hspec.1]
        exact hG
      have hf := source_triangle_preflight_fits sgs n τ r.movedT.toFinset hspec.2.2.1
      have hpre := safeGroverPreflight_preserves sgs (triangleMarked G r.movedT.toFinset)
        3 (n*n) (sourceTriangleReservation sgs n τ) t.2.2.2.2.1 hf
      rw [hpre]
      cases hout : operationalSgsFind sgs (triangleMarked G r.movedT.toFinset)
          3 (n*n) t.2.2.2.2.1 with
      | some z => simp
      | none =>
        have hex : edgeTriangleExists G r.movedE :=
          (true_triangle_partition_coverage G _ _ hcover htri).resolve_left (by
            intro hm
            exact hT hm hout)
        have hfind := hE hex
        change ets.run G r.movedE
            (sourceEdgeMassBound n dHi dLo τ tThin) t.2.2.2.2.2 ≠ none at hfind
        cases he : ets.run G r.movedE (sourceEdgeMassBound n dHi dLo τ tThin) t.2.2.2.2.2 with
        | none => exact (hfind he).elim
        | some p => rcases p with ⟨a,b,cc⟩; simp

end Qatlib.Concepts.WalkSearch.MainResults
