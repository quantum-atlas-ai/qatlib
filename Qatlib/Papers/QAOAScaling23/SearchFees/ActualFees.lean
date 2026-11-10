/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.ResourceBudget
import Qatlib.Papers.QAOAScaling23.SearchFees.Confidence
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
open scoped Classical ENNReal Topology
open Filter
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchFees
variable {I:Type} [Fintype I] [DecidableEq I]

theorem actual_five_ledger_budgets (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M T:ℕ)
    (hQ:0<MeasureProb (preparedAAState U seed) S)
    (hcap:1≤(M:ℝ)*Real.sqrt (MeasureProb (preparedAAState U seed) S)) :
    let p:=searchForSchedule U hU seed S valid (interleavePlain (geometricSearchSchedule M T))
    expectation p (fun tr=>(tr.phaseQueries:ℝ≥0∞))≤ENNReal.ofReal (1000/Real.sqrt (MeasureProb (preparedAAState U seed) S)) ∧
    expectation p (fun tr=>(tr.bits:ℝ≥0∞))≤ENNReal.ofReal (1000/Real.sqrt (MeasureProb (preparedAAState U seed) S)) ∧
    expectation p (fun tr=>(tr.validationQueries:ℝ≥0∞))≤ENNReal.ofReal (1000/Real.sqrt (MeasureProb (preparedAAState U seed) S)) ∧
    expectation p (fun tr=>(tr.prepareCalls:ℝ≥0∞))≤ENNReal.ofReal (1000/Real.sqrt (MeasureProb (preparedAAState U seed) S)) ∧
    expectation p (fun tr=>(tr.macroGates:ℝ≥0∞))≤ENNReal.ofReal (1000/Real.sqrt (MeasureProb (preparedAAState U seed) S)) := by
  exact ⟨actual_sqrt_mass_budget U hU seed S valid hvalid M T hQ hcap .phase (by decide),
    actual_sqrt_mass_budget U hU seed S valid hvalid M T hQ hcap .bits (by decide),
    actual_sqrt_mass_budget U hU seed S valid hvalid M T hQ hcap .validation (by decide),
    actual_sqrt_mass_budget U hU seed S valid hvalid M T hQ hcap .prepare (by decide),
    actual_sqrt_mass_budget U hU seed S valid hvalid M T hQ hcap .gates (by decide)⟩

def totalLedger (tr:CappedSearchTrace I) : ℕ :=
  tr.bits+tr.phaseQueries+tr.validationQueries+tr.prepareCalls+tr.macroGates

theorem aggregate_expectation (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (ms:List ℕ) :
    expectation (searchForSchedule U hU seed S valid ms) (fun tr=>(totalLedger tr:ℝ≥0∞))=
      expected U hU seed S valid .bits ms+expected U hU seed S valid .phase ms+
      expected U hU seed S valid .validation ms+expected U hU seed S valid .prepare ms+
      expected U hU seed S valid .gates ms := by
  unfold totalLedger
  simp only [Nat.cast_add]
  rw [expectation_add,expectation_add,expectation_add,expectation_add]
  rfl

theorem actual_aggregate_budget (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M T:ℕ)
    (hQ:0<MeasureProb (preparedAAState U seed) S)
    (hcap:1≤(M:ℝ)*Real.sqrt (MeasureProb (preparedAAState U seed) S)) :
    expectation (searchForSchedule U hU seed S valid (interleavePlain (geometricSearchSchedule M T)))
      (fun tr=>(totalLedger tr:ℝ≥0∞))≤ENNReal.ofReal (5000/Real.sqrt (MeasureProb (preparedAAState U seed) S)) := by
  rw [aggregate_expectation]
  have h:=actual_sqrt_mass_budget U hU seed S valid hvalid M T hQ hcap
  have hb:=h .bits (by decide)
  have hp:=h .phase (by decide)
  have hv:=h .validation (by decide)
  have hpre:=h .prepare (by decide)
  have hg:=h .gates (by decide)
  refine (add_le_add (add_le_add (add_le_add (add_le_add hb hp) hv) hpre) hg).trans ?_
  calc
    _ = 5*ENNReal.ofReal (1000/Real.sqrt (MeasureProb (preparedAAState U seed) S)) := by ring
    _ = ENNReal.ofReal (5*(1000/Real.sqrt (MeasureProb (preparedAAState U seed) S))) := by
      rw [show (5:ℝ≥0∞)=ENNReal.ofReal (5:ℝ) by norm_num,← ENNReal.ofReal_mul (by norm_num : (0:ℝ)≤5)]
    _ ≤ ENNReal.ofReal (5000/Real.sqrt (MeasureProb (preparedAAState U seed) S)) := by
      apply le_of_eq
      congr 1
      ring

theorem Q_one_geometric_failure (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (hQ:MeasureProb (preparedAAState U seed) S=1)
    (M T:ℕ) (hT:0<T) :
    failure U hU seed S valid (interleavePlain (geometricSearchSchedule M T))=0 := by
  cases T with
  | zero=>omega
  | succ T=>rw [← schedFrom_zero,schedFrom_succ,Q_one_failure U hU seed S valid hvalid hQ]

theorem actual_source_confidence (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M L:ℕ)
    (hQ:0<MeasureProb (preparedAAState U seed) S)
    (hcap:1≤(M:ℝ)*Real.sqrt (MeasureProb (preparedAAState U seed) S)) :
    (failure U hU seed S valid (interleavePlain (geometricSearchSchedule M (5*M+L)))).toReal≤(25/32:ℝ)^L := by
  have hQ1:=prepared_mass_le_one U hU seed S
  rcases eq_or_lt_of_le hQ1 with he|hl
  · have hM:0<M:=by
      by_contra hz
      have hM0:M=0:=by omega
      subst M
      norm_num at hcap
    rw [Q_one_geometric_failure U hU seed S valid hvalid he M (5*M+L) (by omega)]
    simp only [ENNReal.toReal_zero]
    positivity
  · obtain ⟨θ,h0,h1,hθ⟩:=actual_mass_angle _ hQ hl
    have hmass:MeasureProb (preparedAAState U seed) S=(Real.sin θ)^2:=by rw [hθ,Real.sq_sqrt hQ.le]
    have hc:1≤(M:ℝ)*Real.sin θ:=by simpa only [hθ] using hcap
    exact source_confidence U hU seed S valid hvalid M L θ h0 h1 hmass hc

theorem actual_failure_tendsto_zero (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (hvalid:∀y,valid y=true↔y∈S) (M:ℕ)
    (hQ:0<MeasureProb (preparedAAState U seed) S)
    (hcap:1≤(M:ℝ)*Real.sqrt (MeasureProb (preparedAAState U seed) S)) :
    Tendsto (fun L:ℕ=>(failure U hU seed S valid (interleavePlain (geometricSearchSchedule M (5*M+L)))).toReal) atTop (𝓝 0) := by
  exact squeeze_zero (fun _=>ENNReal.toReal_nonneg)
    (fun L=>actual_source_confidence U hU seed S valid hvalid M L hQ hcap)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ)≤25/32) (by norm_num : (25/32:ℝ)<1))
end Qatlib.Papers.QAOAScaling23.SearchFees
