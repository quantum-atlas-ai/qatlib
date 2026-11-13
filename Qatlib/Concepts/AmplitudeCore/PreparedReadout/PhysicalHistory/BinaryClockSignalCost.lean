/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Query bounds for binary clock signal words

`segmentSum` and `queryLedger` sum the segment and query costs of the dyadic clock pulses. A
common factor controlled by `rMax` bounds each pulse cost.

The resulting explicit ledger bound depends linearly on `q+1+2*|τ|`, with the stated precision
and logarithmic segment factor for quantum signal processing simulation [LowChuang2017].

## Main statements

* `segmentSum_le`: the total segment count is at most `q+1+2*|τ|`.
* `instructions_query_bound`: the compiled instruction word satisfies the explicit ledger bound.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalCost

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory

open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord
open scoped BigOperators

/-- The computed signal segment count for the full simulation time `τ`. -/
def rMax (τ : ℚ) : ℕ := computedSignalSegments τ
/-- The sum of computed signal segment counts over all dyadic clock pulse axes. -/
def segmentSum (q : ℕ) (τ : ℚ) : ℕ :=
  ((DyadicClockPulses.axes q).map (fun a => computedSignalSegments (atomTime q τ a))).sum
/-- The common query-cost factor `27*(128*(k+clog₂(rMax τ)+16)+1)`. -/
def factor (τ : ℚ) (k : ℕ) : ℕ := 27 * (128 * (k + Nat.clog 2 (rMax τ) + 16) + 1)
/-- The total query cost summed over all dyadic clock pulses. -/
def queryLedger (q : ℕ) (τ : ℚ) (k : ℕ) : ℕ :=
  ((DyadicClockPulses.axes q).map (fun a => queryCost (atomTime q τ a) k)).sum

/-- Every dyadic clock pulse time has absolute value at most `|τ|`. -/
theorem atom_abs_le (q : ℕ) (τ : ℚ) (a : Option (Fin q)) : |atomTime q τ a| ≤ |τ| := by
  have hd := DyadicClockPulses.denominator_pos q
  have hD := DyadicClockPulses.denominator_one_le q
  have hc : 0 ≤ DyadicClockPulses.midpointCoefficient q a ∧
      DyadicClockPulses.midpointCoefficient q a ≤ 1 := by
    cases a with
    | none =>
      change 0 ≤ 1 / (2 * DyadicClockPulses.denominator q) ∧
        1 / (2 * DyadicClockPulses.denominator q) ≤ 1
      refine ⟨by positivity, (div_le_one (by positivity)).mpr ?_⟩
      linarith
    | some i =>
      change 0 ≤ (2 : ℚ) ^ i.val / DyadicClockPulses.denominator q ∧
        (2 : ℚ) ^ i.val / DyadicClockPulses.denominator q ≤ 1
      refine ⟨by positivity, (div_le_one hd).mpr ?_⟩
      exact pow_le_pow_right₀ (by norm_num : (1 : ℚ) ≤ 2) i.isLt.le
  rw [atomTime, abs_mul, abs_of_nonneg hc.1]
  exact mul_le_of_le_one_right (abs_nonneg τ) hc.2

/-- The segment count of each dyadic pulse is at most the full-time segment count `rMax τ`. -/
theorem segment_le_rMax (q : ℕ) (τ : ℚ) (a : Option (Fin q)) :
    computedSignalSegments (atomTime q τ a) ≤ rMax τ := by
  apply max_le_max le_rfl
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (atom_abs_le q τ a) (by norm_num))

/-- The computed segment count for time `t` is at most `1+2*|t|`. -/
theorem segment_upper (t : ℚ) : (computedSignalSegments t : ℚ) ≤ 1 + 2 * |t| := by
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ (2 : ℚ) * |t|)).le
  unfold computedSignalSegments
  rcases le_total 1 ⌈(2 : ℚ) * |t|⌉₊ with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    change (1 : ℚ) ≤ 1 + 2 * |t|
    linarith [abs_nonneg t]

/-- The sum of segment counts over a pulse list is bounded by its length plus twice the sum of
absolute pulse times. -/
private theorem sum_segments (q : ℕ) (τ : ℚ) (as : List (Option (Fin q))) :
    ((as.map (fun a => computedSignalSegments (atomTime q τ a))).sum : ℚ) ≤
      (as.length : ℚ) + 2 * (as.map (fun a => |atomTime q τ a|)).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [segment_upper (atomTime q τ a)]

/-- The total dyadic segment count is at most `q+1+2*|τ|` as a rational inequality. -/
theorem segmentSum_le (q : ℕ) (τ : ℚ) :
    (segmentSum q τ : ℚ) ≤ ((q + 1 : ℕ) : ℚ) + 2 * |τ| := by
  have hh := sum_segments q τ (DyadicClockPulses.axes q)
  rw [DyadicClockPulses.axes_length] at hh
  have hg : (2 : ℚ) *
      ((DyadicClockPulses.axes q).map (fun a => |atomTime q τ a|)).sum ≤ 2 * |τ| :=
    mul_le_mul_of_nonneg_left (midpoint_absolute_time_le q τ)
      (by norm_num : (0 : ℚ) ≤ 2)
  have ha : ((q + 1 : ℕ) : ℚ) + (2 : ℚ) *
      ((DyadicClockPulses.axes q).map (fun a => |atomTime q τ a|)).sum ≤
      ((q + 1 : ℕ) : ℚ) + 2 * |τ| :=
    add_le_add le_rfl hg
  exact hh.trans ha

/-- The total dyadic segment count is at most `q+1+2*|τ|` as a real inequality. -/
theorem segmentSum_le_real (q : ℕ) (τ : ℚ) :
    (segmentSum q τ : ℝ) ≤ ((q + 1 : ℕ) : ℝ) + 2 * |(τ : ℝ)| := by
  exact_mod_cast segmentSum_le q τ

/-- Each pulse query cost is bounded by its segment count times the common factor `factor τ k`. -/
theorem atom_query_le (q : ℕ) (τ : ℚ) (k : ℕ) (a : Option (Fin q)) :
    queryCost (atomTime q τ a) k ≤ computedSignalSegments (atomTime q τ a) * factor τ k := by
  have hl := Nat.clog_mono_right 2 (segment_le_rMax q τ a)
  have hc : computedSignalCutoff (atomTime q τ a) k ≤ 32 * (k + Nat.clog 2 (rMax τ) + 16) := by
    unfold computedSignalCutoff
    omega
  have hf : 27 * (4 * computedSignalCutoff (atomTime q τ a) k + 1) ≤ factor τ k := by
    unfold factor
    omega
  exact Nat.mul_le_mul_left _ hf

/-- The total query cost of a pulse list is bounded by its total segment count times `factor τ
k`. -/
private theorem sum_queries (q : ℕ) (τ : ℚ) (k : ℕ) (as : List (Option (Fin q))) :
    (as.map (fun a => queryCost (atomTime q τ a) k)).sum ≤
      (as.map (fun a => computedSignalSegments (atomTime q τ a))).sum * factor τ k := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (Nat.add_le_add (atom_query_le q τ k a) ih).trans_eq (by ring)

/-- At zero simulation time, the total dyadic segment count equals `q+1`. -/
theorem segmentSum_zero (q : ℕ) : segmentSum q 0 = q + 1 := by
  simp [segmentSum, atomTime, computedSignalSegments, DyadicClockPulses.axes,
    List.map_ofFn, Function.comp_def, add_comm]

/-- The total dyadic query ledger is strictly positive. -/
theorem queryLedger_pos (q : ℕ) (τ : ℚ) (k : ℕ) : 0 < queryLedger q τ k := by
  unfold queryLedger
  rw [DyadicClockPulses.axes, List.map_cons, List.sum_cons]
  apply lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
  unfold queryCost
  apply Nat.mul_pos (computed_signal_segment_size _).1
  omega

/-- The rational query ledger is at most `27*((q+1)+2*|τ|)*(128*(k+clog₂(rMax τ)+16)+1)`. -/
theorem queryLedger_le (q : ℕ) (τ : ℚ) (k : ℕ) :
    (queryLedger q τ k : ℚ) ≤ 27 * (((q + 1 : ℕ) : ℚ) + 2 * |τ|) *
      (128 * ((k + Nat.clog 2 (rMax τ) + 16 : ℕ) : ℚ) + 1) := by
  have hq : queryLedger q τ k ≤ segmentSum q τ * factor τ k :=
    sum_queries q τ k (DyadicClockPulses.axes q)
  have hq' : (queryLedger q τ k : ℚ) ≤ (segmentSum q τ : ℚ) * (factor τ k : ℚ) := by
    exact_mod_cast hq
  calc
    _ ≤ (((q + 1 : ℕ) : ℚ) + 2 * |τ|) * (factor τ k : ℚ) :=
      hq'.trans (mul_le_mul_of_nonneg_right (segmentSum_le q τ) (Nat.cast_nonneg _))
    _ = _ := by
      simp only [factor, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
      ring

/-- The real cast of the query ledger satisfies the same explicit clock, time, and precision
bound. -/
theorem queryLedger_le_real (q : ℕ) (τ : ℚ) (k : ℕ) :
    (queryLedger q τ k : ℝ) ≤ 27 * (((q + 1 : ℕ) : ℝ) + 2 * |(τ : ℝ)|) *
      (128 * ((k + Nat.clog 2 (rMax τ) + 16 : ℕ) : ℝ) + 1) := by
  exact_mod_cast queryLedger_le q τ k

/-- For a projected unitary encoding of a Hermitian matrix, the compiled signal word's query
count satisfies the explicit dyadic ledger bound. -/
theorem instructions_query_bound {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (q : ℕ) (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (F : Matrix H I ℂ) (τ : ℚ) (k : ℕ) (hA : A.IsHermitian)
    (h : ProjectedUnitaryEncoding A U F F) :
    (adjointQueryCount (instructions q F τ k) : ℚ) ≤
      27 * (((q + 1 : ℕ) : ℚ) + 2 * |τ|) *
        (128 * ((k + Nat.clog 2 (rMax τ) + 16 : ℕ) : ℚ) + 1) := by
  rw [(instructions_resources q A U F τ k hA h).2.1]
  exact queryLedger_le q τ k

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalCost
