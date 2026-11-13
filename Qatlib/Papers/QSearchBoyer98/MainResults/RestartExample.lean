/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.RestartLaw.Section3RestartStationaritySubgoalTigh
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3OptimalAngleSubgoalTigh
import Qatlib.Concepts.SearchStopping.RestartLaw.Section3OptimalConstantsSubgoalTigh
import Qatlib.Concepts.SearchStopping.PaidRestart.Section3StrictImprovementSubgoalTigh
import Qatlib.Concepts.SearchStopping.PaidRestart.ActualRestartExpectedReceiptTigh
import Mathlib.Tactic

/-!
# Certified restart constants and a finite search example

This module certifies rational windows around a solution of tan(z/2) = z and its associated
success, iteration, and expected-cost coefficients. It also records the zero-iteration profile
and verifies an actual 596-iteration restart experiment with one marked item among 2²⁰
possibilities, including the additional verification query.

The source paper is [BoyerEtAl1998].

## Main statements

* `pinned_restart_constants`: There exists a root of tan(z/2) = z between 2.33112 and 2.33113
  whose success, iteration, and expected-cost coefficients lie in the stated rational windows.
  Its expected-cost coefficient lies strictly between 0.87(π/4) and 0.88(π/4).
* `printed_restart_actual_receipt`: For one marked item in a space of size 2²⁰, the unitary
  596-iteration bit-search circuit followed by verification costs 597 queries per attempt, never
  fails to terminate, and has expected paid time 597/p and expected iteration charge 596/p. The
  bounds 705 < 596/p < 804 and 597/p < 804 hold for its Grover success probability p.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option autoImplicit false
open scoped Classical BigOperators ENNReal
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.RestartLaw
open Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.StoppingCore.BranchCostCore
open Qatlib.Concepts.StoppingCore.BranchCostCore.GeneralExecution
open Qatlib.Concepts.QueryWordCore.QueryMachinery

namespace Qatlib.Papers.QSearchBoyer98.MainResults

noncomputable section

/-- There exists a root of tan(z/2) = z between 2.33112 and 2.33113 whose success, iteration,
and expected-cost coefficients lie in the stated rational windows. Its expected-cost
coefficient lies strictly between 0.87(π/4) and 0.88(π/4) [BoyerEtAl1998]. -/
theorem pinned_restart_constants : ∃ z : ℝ,
    Real.tan (z/2)=z ∧ 233112/100000 < z ∧ z < 233113/100000 ∧
    8445/10000 < Real.sin (z/2)^2 ∧ Real.sin (z/2)^2 < 8446/10000 ∧
    58278/100000 < z/4 ∧ z/4 < 58279/100000 ∧
    69002/100000 < z/(4*Real.sin (z/2)^2) ∧ z/(4*Real.sin (z/2)^2) < 69003/100000 ∧
    87/100*(Real.pi/4) < z/(4*Real.sin (z/2)^2) ∧
      z/(4*Real.sin (z/2)^2) < 22/25*(Real.pi/4) := by
  obtain ⟨z,hz,_⟩ := section3OptimalAngleSubgoal
  exact ⟨z,hz.1,hz.2.1,hz.2.2,
    section3OptimalConstantsSubgoal z hz.1 hz.2.1 hz.2.2⟩

/-- The real-valued restart expected-iteration expression at zero iterations is zero. -/
theorem zero_iteration_profile (θ : ℝ) : restartExpectedIterations θ 0=0 := by
  simp [restartExpectedIterations]

/-- For one marked item in a space of size 2²⁰, the unitary 596-iteration bit-search circuit
followed by verification costs 597 queries per attempt, never fails to terminate, and has
expected paid time 597/p and expected iteration charge 596/p. The bounds 705 < 596/p < 804
and 597/p < 804 hold for its Grover success probability p [BoyerEtAl1998]. -/
theorem printed_restart_actual_receipt (I : Type) [Fintype I] [DecidableEq I]
    (hN : Fintype.card I=2^20) (A : Finset I) (hA : A.card=1) :
    ∃ hC : IsUnitaryCircuit (bbhtBitSearchCircuit (1:Matrix I I ℂ) (Uniform I) 596),
    let p := MeasureProb (GroverState A 596) A
    let next := bbhtActualRestartNextPrice (1:Matrix I I ℂ) (Uniform I) 596 A hC
      (normalized_uniform (by rw [hN]; norm_num)) 597
    QueryCount (bbhtBitSearchCircuit (1:Matrix I I ℂ) (Uniform I) 596) +
      QueryCount ([Step.query] : Circuit (I × Bool)) = 597 ∧
    generalNeverMass (branchClockNext next) (branchClockEmbed (Sum.inr ()))=0 ∧
    generalUnboundedTime (branchClockNext next) (branchClockEmbed (Sum.inr ()))=
      ENNReal.ofReal (597/p) ∧
    (∑' r : ℕ, (((r+1)*596:ℕ):ℝ≥0∞) *
      ∑ i : I, branchHaltJoint next (Sum.inr ()) i ((r+1)*597))=ENNReal.ofReal (596/p) ∧
    705 < 596/p ∧ 596/p < 804 ∧ 597/p < 804 := by
  have hn : 0 < Fintype.card I := by rw [hN]; norm_num
  have hvalid := actualRestartSearchWord I hn (1:Matrix I I ℂ) (Uniform I)
    (Submonoid.one_mem _) (normalized_uniform hn) (by simp) A 596
  have hnum := section3StrictImprovementSubgoal I hN A hA
  have hp : 0 < MeasureProb (GroverState A 596) A := by linarith [hnum.2.1]
  have he := (actualRestartExpectedReceipt I hn (1:Matrix I I ℂ) (Uniform I)
    (Submonoid.one_mem _) (normalized_uniform hn) (by simp) A 596 hvalid.1 597 (by norm_num)).2 hp
  refine ⟨hvalid.1,?_,he.1,he.2.1,he.2.2,hnum.2.2.2.2,hnum.2.2.2.1,?_⟩
  · rw [hvalid.2.1]
    rfl
  · apply (div_lt_iff₀ hp).mpr
    linarith [hnum.2.1]

end

end Qatlib.Papers.QSearchBoyer98.MainResults
