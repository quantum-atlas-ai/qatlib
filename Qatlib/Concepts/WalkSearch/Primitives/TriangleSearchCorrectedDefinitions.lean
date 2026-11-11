/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.TriangleDiagnostics

/-!
# Corrected degree-test and reliability definitions

`degreeTestLowCorrected` uses the intended low-hit majority condition, and
`testCorrectCorrected` states the corresponding threshold behavior. The module also defines a
positive fee factor and minimum failure exponents for reliable search capabilities.

The reliability conditions strengthen the basic interfaces used for quantum search
[BoyerEtAl1998].

## Main statements

* `emptyGraph_degreeTest_corrected`: the corrected test accepts an empty graph.
* `rejecting_capabilities_not_reliable`: the rejecting examples fail reliability.
* `source_dense_four_term_budget`: the four real-power terms are at most `4 * n ^ (10 / 7)`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace Qatlib.Concepts.WalkSearch.Primitives
open scoped Classical BigOperators
variable {n : ℕ}

/-- The corrected low-degree Boolean test, true exactly when `2 * hitRounds G v K c tape + 1 ≤
K`. -/
def degreeTestLowCorrected (G : UGraph n) (v : Fin n) (K c : ℕ) (tape : Fin K→Fin c→Fin n) : Bool :=
  decide (2*hitRounds G v K c tape+1 ≤ K)

/-- The threshold correctness condition for the corrected test: false above `dHi` and true below
`dLo`. -/
def testCorrectCorrected (G : UGraph n) (v : Fin n) (dHi dLo K c : ℕ)
    (tape : Fin K→Fin c→Fin n) : Prop :=
  (dHi<degOf G.edges v→degreeTestLowCorrected G v K c tape=false) ∧
  (degOf G.edges v<dLo→degreeTestLowCorrected G v K c tape=true)

/-- The condition that both the Grover and edge-triangle search failure exponents are at least
three. -/
def reliableCapabilities (sgs : SafeGrover) (ets : EdgeTriSearch) : Prop :=
    3 ≤ sgs.cExp ∧ 3 ≤ ets.cExp

/-- The maximum of one and the two search capabilities' fee constants. -/
def capabilityFeeFactor (sgs : SafeGrover) (ets : EdgeTriSearch) : ℕ := max 1 (max sgs.κ ets.κ)

/-- With a positive number of rounds, the corrected degree test returns `true` on the empty
graph for every tape. -/
theorem emptyGraph_degreeTest_corrected (v : Fin n) (K c : ℕ) (hK : 0<K)
    (tape : Fin K→Fin c→Fin n) : degreeTestLowCorrected (emptyGraph n) v K c tape=true := by
  simpa [degreeTestLowCorrected,hitRounds,emptyGraph] using! hK

/-- The always-rejecting Grover and edge-search capabilities do not satisfy
`reliableCapabilities`. -/
theorem rejecting_capabilities_not_reliable : ¬ reliableCapabilities rejectingGrover rejectingEdgeSearch := by
  norm_num [reliableCapabilities,rejectingGrover,rejectingEdgeSearch]

/-- For `n ≥ 1`, the displayed four-term dense-parameter power expression is at most `4 * n ^
(10 / 7)`. -/
theorem source_dense_four_term_budget (n : ℕ) (hn : 1 ≤ n) :
    (n:ℝ)^(1+(3/7:ℝ))+(n:ℝ)^(1+(1/7:ℝ)+(1/7:ℝ))+
      (n:ℝ)^((3-(1/7:ℝ))/2)+(n:ℝ)^((3-min (1/7:ℝ) ((3/7:ℝ)-(1/7:ℝ)-(1/7:ℝ)))/2) ≤
        4*(n:ℝ)^(10/7:ℝ) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  rw [show (1+(3/7:ℝ))=(10/7:ℝ) by norm_num,
    show (1+(1/7:ℝ)+(1/7:ℝ))=(9/7:ℝ) by norm_num,
    show ((3-(1/7:ℝ))/2)=(10/7:ℝ) by norm_num,
    show ((3-min (1/7:ℝ) ((3/7:ℝ)-(1/7:ℝ)-(1/7:ℝ)))/2)=(10/7:ℝ) by norm_num]
  have hh := Real.rpow_le_rpow_of_exponent_le hnR (by norm_num : (9/7:ℝ) ≤ 10/7)
  linarith
end Qatlib.Concepts.WalkSearch.Primitives
