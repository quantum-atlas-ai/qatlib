/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.CombinatorialBudgetRun

/-!
# Allocated costs of the combinatorial algorithm

`preparationScan_sample_cost` bounds preparation queries by the sample size, including repeated
sampled vertices. `sourceCombAlg_allocated_cost` combines preparation, classification, triangle
search, and promised edge search reservations into the total budget for every tape. For
background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `preparationScan_sample_cost`: For positive `n`, preparation on the distinct vertices in a
  sample of length `k` uses at most `k * (n + neighborhoodFee n sgs)` queries.
* `sourceCombAlg_allocated_cost`: For positive `n`, the query count recorded by `sourceCombAlg`
  on any tape is bounded by `sourceCombinatorialBudget`.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.WalkSearch.Primitives
set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.MainResults
open scoped Classical
variable {n : ℕ}

/-- For positive `n`, preparation on the distinct vertices in a sample of length `k` uses at
most `k * (n + neighborhoodFee n sgs)` queries. -/
theorem preparationScan_sample_cost (G : UGraph n) (sgs : SGSExecution) (k : ℕ)
    (s : Fin k→Fin n) (stape : Fin n→sgs.seed) (hn : 0<n) :
    (preparationScan G sgs stape (Finset.univ.image s).toList).queries≤k*(n+neighborhoodFee n sgs) := by
  have hh:=preparationScan_cost G sgs stape (Finset.univ.image s).toList hn
  have hk : (Finset.univ.image s).toList.length≤k := by
    rw [Finset.length_toList]
    simpa only [Finset.card_univ,Fintype.card_fin] using
        (Finset.card_image_le (s:=Finset.univ) (f:=s))
  exact hh.trans (Nat.mul_le_mul_right _ hk)

/-- For positive `n`, the query count recorded by `sourceCombAlg` on any tape is bounded by
`sourceCombinatorialBudget`. -/
theorem sourceCombAlg_allocated_cost (G : UGraph n) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily)
    (k K c dHi dLo τ tThin : ℕ) (t : sourceCombTape n k K c sgs ets) (hn : 0<n) :
    (Qatlib.Concepts.WalkSearch.MainResults.CombOut.queries (sourceCombAlg G sgs ets k K c dHi dLo τ tThin t))≤
      sourceCombinatorialBudget sgs ets n k dHi dLo τ K c tThin := by
  have hp:=preparationScan_sample_cost G sgs k t.1 t.2.1 hn
  let S : SymmetricPairSet n:=⟨sampledSurvivors G t.1,sampledSurvivors_symmetric G t.1⟩
  have hc:=classifyScanBudgeted_cost G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
    (classifyBudgetCorrected n dLo τ K c sgs) hn
  dsimp only [S] at hc
  unfold sourceCombAlg sourceCombinatorialBudget
  (try dsimp only)
  cases h0 : (preparationScan G sgs t.2.1 (Finset.univ.image t.1).toList).triangle with
  | some p=>rcases p with ⟨a,b,cc⟩;dsimp only [CombOut.queries];omega
  | none=>
    (try dsimp only)
    split_ifs with htimeout
    · dsimp only [CombOut.queries]
      omega
    · cases h1 : (classifyScanBudgeted G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
        (classifyBudgetCorrected n dLo τ K c sgs)).result.triangle with
      | some p=>rcases p with ⟨a,b,cc⟩;dsimp only [CombOut.queries];omega
      | none=>
        let T:=(classifyScanBudgeted G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
          (classifyBudgetCorrected n dLo τ K c sgs)).result.movedT.toFinset
        let E:=(classifyScanBudgeted G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
          (classifyBudgetCorrected n dLo τ K c sgs)).result.movedE
        cases hT :
            safeGroverPreflight sgs (triangleMarked G T) 3 (n*n)
            (sourceTriangleReservation sgs n τ) t.2.2.2.2.1 with
        | timeout=>dsimp only [CombOut.queries];omega
        | completed out qT=>
          have hqT:=safeGroverPreflight_charge sgs (triangleMarked G T) 3 (n*n)
              (sourceTriangleReservation sgs n τ) t.2.2.2.2.1 out qT hT
          cases out with
          | some tri=>dsimp only [CombOut.queries];omega
          | none=>
            have heCard : E.card≤n*n := by
              simpa only [Fintype.card_prod,Fintype.card_fin] using Finset.card_le_univ E
            have hqE:=promisedEdge_cost_le_reservation ets G E
                (sourceEdgeMassBound n dHi dLo τ tThin) t.2.2.2.2.2 (n*n) heCard
            dsimp only [E,S,sourceEdgeReservation] at hqE ⊢
            cases hE : ets.run G E (sourceEdgeMassBound n dHi dLo τ tThin) t.2.2.2.2.2 with
            | none=>dsimp only [CombOut.queries];omega
            | some p=>rcases p with ⟨a,b,cc⟩;dsimp only [CombOut.queries];omega

end Qatlib.Concepts.WalkSearch.MainResults
