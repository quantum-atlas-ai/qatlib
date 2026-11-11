/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.MainResults.PreparationScan
import Qatlib.Concepts.WalkSearch.MainResults.TrianglePartitionCoverage
import Qatlib.Concepts.WalkSearch.Primitives.ClassificationBudgetPreservation
import Qatlib.Concepts.WalkSearch.MainResults.ClassificationBudget

/-!
# A budgeted combinatorial triangle algorithm

`sourceCombAlg` combines sampled preparation, a budgeted classification scan, and reserved
triangle and promised edge searches. `sourceCombTape` packages its finite choices, while
`sourceCombinatorialBudget` and the component reservations specify the allocated query costs.
For background on quantum search and amplitude amplification, see [BrassardEtAl2002].

## Main statements

* `sourceEdgeMassBound`: The integer bound `2 * n * dHi + (n * n / (dLo * τ) + 1) * (2 * n *
  (tThin + 1))` used for the graph edge mass of moved candidates.
* `sourceCombRejects`: The algorithm returns the rejection constructor on the specified tape.

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

/-- The integer bound `2 * n * dHi + (n * n / (dLo * τ) + 1) * (2 * n * (tThin + 1))` used for
the graph edge mass of moved candidates. -/
def sourceEdgeMassBound (n dHi dLo τ tThin : ℕ) : ℕ :=
  2*n*dHi+(n*n/(dLo*τ)+1)*(2*n*(tThin+1))

/-- Reserve a safe Grover search over at most `n.choose 2 * τ` candidate triangles with checking
cost three and floor `n * n`. -/
def sourceTriangleReservation (sgs : SGSExecution) (n τ : ℕ) : ℕ :=
  safeGroverReservation sgs (n.choose 2*τ) 3 (n*n)

/-- Reserve the promised edge search cost using `n * n` candidate pairs and the bound
`sourceEdgeMassBound`. -/
def sourceEdgeReservation (ets : PromisedEdgeSearchFamily) (n dHi dLo τ tThin : ℕ) : ℕ :=
  promisedEdgeReservation ets n (n*n) (sourceEdgeMassBound n dHi dLo τ tThin)

/-- The sum of the preparation budget, corrected classification budget, triangle search
reservation, and promised edge search reservation. -/
def sourceCombinatorialBudget (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) (n k dHi dLo τ K c tThin : ℕ) : ℕ :=
  k*(n+neighborhoodFee n sgs)+classifyBudgetCorrected n dLo τ K c sgs+
    sourceTriangleReservation sgs n τ+sourceEdgeReservation ets n dHi dLo τ tThin

/-- The product of the sampled vertices and the seeds and degree test tapes used by preparation,
classification, triangle search, and promised edge search. -/
@[reducible]
def sourceCombTape (n k K c : ℕ) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily) : Type :=
  (Fin k→Fin n)×(Fin n→sgs.seed)×(Fin n→Fin K→Fin c→Fin n)×(Fin n→sgs.seed)×sgs.seed×ets.seed n

/-- Execute the budgeted combinatorial triangle algorithm on a fixed tape, returning a triangle
or rejection together with the accumulated query count. -/
def sourceCombAlg {n : ℕ} (G : UGraph n) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily)
    (k K c dHi dLo τ tThin : ℕ) (t : sourceCombTape n k K c sgs ets) : CombOut n :=
  let r0:=preparationScan G sgs t.2.1 (Finset.univ.image t.1).toList
  match r0.triangle with
  | some (a,b,cc)=>.tri a b cc r0.queries
  | none=>
    let S : SymmetricPairSet n:=⟨sampledSurvivors G t.1,sampledSurvivors_symmetric G t.1⟩
    let r1:=classifyScanBudgeted G sgs τ K c t.2.2.1 t.2.2.2.1 Finset.univ.toList S
      (classifyBudgetCorrected n dLo τ K c sgs)
    if r1.timedOut then .reject (r0.queries+r1.result.queries)
    else match r1.result.triangle with
      | some (a,b,cc)=>.tri a b cc (r0.queries+r1.result.queries)
      | none=>
        let T:=r1.result.movedT.toFinset
        let E:=r1.result.movedE
        match safeGroverPreflight sgs (triangleMarked G T) 3 (n*n) (sourceTriangleReservation sgs n τ) t.2.2.2.2.1 with
        | .timeout=>.reject (r0.queries+r1.result.queries)
        | .completed (some tri) qT=>
          let a:=tri.val.1;let b:=tri.val.2.1;let cc:=tri.val.2.2
          .tri a b cc (r0.queries+r1.result.queries+qT)
        | .completed none qT=>
          let mBound:=sourceEdgeMassBound n dHi dLo τ tThin
          let qE:=ets.cost G E mBound t.2.2.2.2.2
          match ets.run G E mBound t.2.2.2.2.2 with
          | none=>.reject (r0.queries+r1.result.queries+qT+qE)
          | some (a,b,cc)=>.tri a b cc (r0.queries+r1.result.queries+qT+qE)

/-- Extract the recorded query count from either a triangle output or a rejection output. -/
def CombOut.queries {n : ℕ} : CombOut n→ℕ
  | .tri _ _ _ q=>q
  | .reject q=>q

/-- Every triangle returned by `sourceCombAlg`, on every tape, satisfies `tri3` and has all
three edges in `G`. -/
def sourceCombSound {n : ℕ} (G : UGraph n) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily)
    (k K c dHi dLo τ tThin : ℕ) : Prop :=
  ∀ t : sourceCombTape n k K c sgs ets,∀ a b cc q,
    sourceCombAlg G sgs ets k K c dHi dLo τ tThin t=.tri a b cc q→
      tri3 G.edges a b cc ∧ (a,b)∈G.edges ∧ (a,cc)∈G.edges ∧ (b,cc)∈G.edges

/-- The algorithm returns the rejection constructor on the specified tape. -/
def sourceCombRejects {n : ℕ} (G : UGraph n) (sgs : SGSExecution) (ets : PromisedEdgeSearchFamily)
    (k K c dHi dLo τ tThin : ℕ) (t : sourceCombTape n k K c sgs ets) : Prop :=
  match sourceCombAlg G sgs ets k K c dHi dLo τ tThin t with
  | .tri _ _ _ _=>False
  | .reject _=>True
end Qatlib.Concepts.WalkSearch.MainResults
