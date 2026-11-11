/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.BiasedProcess.ActualOracle
import Qatlib.Papers.QAOAScaling23.SearchFees.ActualFees

/-!
# Expected charges and failures of actual oracle rows

This module identifies the charge and bad-event means of `actualRow` with the corresponding
quantities of the actual scheduled search. It transfers geometric-schedule fee and confidence
bounds to those rows, supporting the resource analysis of [ShaydulinEtAl2024].

## Main statements

* `actual_charge_mean`: The mean charge of the actual completed row equals the expected actual
  search fee for schedule `1 :: ms`, converted to a real number.
* `actual_bad_mean`: The mean bad indicator of the actual completed row equals the actual
  scheduled search failure probability converted to a real number.
* `actual_charge_bound`: For the stated interleaved geometric schedule and sufficient cap, the
  actual row's mean charge is at most `5000 / sqrt Q`, where `Q` is the strict marked mass.
* `actual_bad_bound`: For the stated confidence schedule and sufficient cap, the actual row's
  bad-event mean is at most `(25 / 32) ^ L`.

## References

* [Shaydulin et al., 2024][ShaydulinEtAl2024]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2200000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Papers.QAOAScaling23.CausalSearch
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Foundations.ProbabilityCore.FiniteBranch
open Qatlib.Papers.QAOAScaling23.BiasedProcess
open Qatlib.Papers.QAOAScaling23.WeightedCost
namespace Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeRows

/-- For a finite probability mass function, the real weighted mean of a natural-valued fee
equals the real part of its extended nonnegative expectation. -/
theorem finite_nat_mean {A : Type} [Fintype A] (p : PMF A) (fee : A → ℕ) :
    (∑a,(p a).toReal * (fee a : ℝ)) = (expectation p (fun a => (fee a : ℝ≥0∞))).toReal := by
  unfold expectation
  rw [tsum_fintype,ENNReal.toReal_sum (fun a _ => ENNReal.mul_ne_top (PMF.apply_ne_top p a) (by finiteness))]
  apply Finset.sum_congr rfl
  intro a _
  simp only [ENNReal.toReal_mul,ENNReal.toReal_natCast]

/-- For a finite probability mass function, the real mean of an event indicator equals the event
probability converted to a real number. -/
theorem finite_bad_mean {A : Type} [Fintype A] (p : PMF A) (P : A → Prop) [DecidablePred P] :
    (∑a,(p a).toReal * (if P a then 1 else 0)) = (event p P).toReal := by
  unfold event expectation
  rw [tsum_fintype,ENNReal.toReal_sum (fun a _ => by (try dsimp only);split_ifs <;> simp [PMF.apply_ne_top])]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> simp_all

/-- For a positive cap `M`, the interleaved geometric schedule of length parameter `5 * M + L`
can be written as `1 :: ms`. -/
theorem confidence_tail_exists (M L : ℕ) (hM : 0 < M) :
    ∃ms : List ℕ,1::ms = Qatlib.Papers.QAOAScaling23.SearchFees.interleavePlain (geometricSearchSchedule M (5*M+L)) := by
  have hT : 0 < 5*M+L := by omega
  cases he : 5*M+L with
  | zero => omega
  | succ n =>
    rw [← schedFrom_zero,schedFrom_succ]
    exact ⟨geometricWindow M 0 :: Qatlib.Papers.QAOAScaling23.SearchFees.interleavePlain (schedFrom M 1 n),rfl⟩

/-- A chosen tail whose prefix by one is the interleaved geometric confidence schedule. -/
def confidenceTail (M L : ℕ) (hM : 0 < M) : List ℕ :=
    Classical.choose (confidence_tail_exists M L hM)

/-- Prefixing `confidenceTail` by one yields the interleaved geometric schedule with parameters
`M` and `5 * M + L`. -/
theorem confidenceTail_spec (M L : ℕ) (hM : 0 < M) :
    1::confidenceTail M L hM = Qatlib.Papers.QAOAScaling23.SearchFees.interleavePlain (geometricSearchSchedule M (5*M+L)) :=
  Classical.choose_spec (confidence_tail_exists M L hM)
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The mean charge of the actual completed row equals the expected actual search fee for
schedule `1 :: ms`, converted to a real number. -/
theorem actual_charge_mean (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1)) (ms : List ℕ) :
    let row := actualRow U hU seed cost current r hr hpos ms
    (∑a,(row.law a).toReal * (row.charge a : ℝ)) =
      (expectation (searchForSchedule U hU seed (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictValid cost current) (1::ms))
        (fun tr => (Qatlib.Papers.QAOAScaling23.CausalSearch.searchFee tr : ℝ≥0∞))).toReal := by
  (try dsimp only)
  change (∑a,((Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row _ _ _ _).law a).toReal * ((Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row _ _ _ _).charge a : ℝ)) = _
  rw [Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row_charge_mean,finite_nat_mean]
  congr 1
  rw [← expectation_map (Tree.indexedLeafLaw (receiptTree U hU seed cost current (1::ms)))
    (Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms)))
    (fun tr => (Qatlib.Papers.QAOAScaling23.CausalSearch.searchFee tr : ℝ≥0∞)),Tree.indexedLeafLaw_value,receiptTree_law]

/-- The mean bad indicator of the actual completed row equals the actual scheduled search
failure probability converted to a real number. -/
theorem actual_bad_mean (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1)) (ms : List ℕ) :
    let row := actualRow U hU seed cost current r hr hpos ms
    (∑a,(row.law a).toReal * (if row.bad a then 1 else 0)) =
      (Qatlib.Papers.QAOAScaling23.SearchFees.failure U hU seed (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictValid cost current) (1::ms)).toReal := by
  (try dsimp only)
  change (∑a,((Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row _ _ _ _).law a).toReal * (if (Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row _ _ _ _).bad a then 1 else 0)) = _
  rw [Qatlib.Papers.QAOAScaling23.BiasedProcess.Completion.row_bad_mean]
  have he (a) : ((Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms)) a).result.bind
      (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.lowerRank cost (r+1))).isNone =
      (Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms)) a).result.isNone := by
    cases hi : (Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms)) a).result with
    | none => rfl
    | some i => simp only [Option.bind_some,Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.lowerRank,dif_pos (indexed_sound U hU seed cost current (1::ms) r hr a i hi),Option.isNone_some]
  simp_rw [he]
  rw [finite_bad_mean]
  congr 1
  change event (Tree.indexedLeafLaw (receiptTree U hU seed cost current (1::ms)))
    (fun a => (Tree.indexedLeafValue (receiptTree U hU seed cost current (1::ms)) a).result.isNone) = _
  rw [Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.indexed_event (receiptTree U hU seed cost current (1::ms)) (fun tr => tr.result.isNone),receiptTree_law]
  apply event_congr
  intro tr
  cases tr.result <;> simp

/-- For the stated interleaved geometric schedule and sufficient cap, the actual row's mean
charge is at most `5000 / sqrt Q`, where `Q` is the strict marked mass. -/
theorem actual_charge_bound (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1))
    (ms : List ℕ) (M T : ℕ) (hms : 1::ms = Qatlib.Papers.QAOAScaling23.SearchFees.interleavePlain (geometricSearchSchedule M T))
    (hcap : 1 ≤ (M : ℝ) * Real.sqrt (MeasureProb (preparedAAState U seed) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current))) :
    let row := actualRow U hU seed cost current r hr hpos ms
    (∑a,(row.law a).toReal * (row.charge a : ℝ)) ≤
      5000 / Real.sqrt (MeasureProb (preparedAAState U seed) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current)) := by
  (try dsimp only)
  rw [actual_charge_mean,hms]
  have hQ : 0 < MeasureProb (preparedAAState U seed) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current) := by
    rw [Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.strict_mass_prefix,hr]
    exact hpos
  have h :=
      Qatlib.Papers.QAOAScaling23.SearchFees.actual_aggregate_budget U hU seed _ _
      (Qatlib.Papers.QAOAScaling23.CausalSearch.strictValid_correct cost current) M T hQ hcap
  have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) h
  simpa only [Qatlib.Papers.QAOAScaling23.SearchFees.totalLedger,Qatlib.Papers.QAOAScaling23.CausalSearch.searchFee,ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ 5000 / Real.sqrt (MeasureProb (preparedAAState U seed) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current)))] using hh

/-- For the stated confidence schedule and sufficient cap, the actual row's bad-event mean is at
most `(25 / 32) ^ L`. -/
theorem actual_bad_bound (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ) (seed : I)
    (cost : I → ℝ) (current : I) (r : ℕ) (hr : (costRank cost current).val = r+1)
    (hpos : 0 < prefixSum (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.weights cost (Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.preparedLaw U hU seed)) (r+1))
    (ms : List ℕ) (M L : ℕ) (hms : 1::ms = Qatlib.Papers.QAOAScaling23.SearchFees.interleavePlain (geometricSearchSchedule M (5*M+L)))
    (hcap : 1 ≤ (M : ℝ) * Real.sqrt (MeasureProb (preparedAAState U seed) (Qatlib.Papers.QAOAScaling23.CausalSearch.strictMarked cost current))) :
    let row := actualRow U hU seed cost current r hr hpos ms
    (∑a,(row.law a).toReal * (if row.bad a then 1 else 0)) ≤ (25/32 : ℝ)^L := by
  (try dsimp only)
  rw [actual_bad_mean,hms]
  apply Qatlib.Papers.QAOAScaling23.SearchFees.actual_source_confidence U hU seed _ _
      (Qatlib.Papers.QAOAScaling23.CausalSearch.strictValid_correct cost current) M L _ hcap
  rw [Qatlib.Papers.QAOAScaling23.BiasedProcess.Born.strict_mass_prefix,hr]
  exact hpos
end Qatlib.Papers.QAOAScaling23.BiasedProcess.NativeRows
