/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSignalWord
import Mathlib.Algebra.Order.Floor.Semiring
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

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

def rMax (τ : ℚ) : ℕ := computedSignalSegments τ
def segmentSum (q : ℕ) (τ : ℚ) : ℕ :=
  ((DyadicClockPulses.axes q).map (fun a => computedSignalSegments (atomTime q τ a))).sum
def factor (τ : ℚ) (k : ℕ) : ℕ := 27 * (128 * (k + Nat.clog 2 (rMax τ) + 16) + 1)
def queryLedger (q : ℕ) (τ : ℚ) (k : ℕ) : ℕ :=
  ((DyadicClockPulses.axes q).map (fun a => queryCost (atomTime q τ a) k)).sum

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

theorem segment_le_rMax (q : ℕ) (τ : ℚ) (a : Option (Fin q)) :
    computedSignalSegments (atomTime q τ a) ≤ rMax τ := by
  apply max_le_max le_rfl
  exact Nat.ceil_mono (mul_le_mul_of_nonneg_left (atom_abs_le q τ a) (by norm_num))

theorem segment_upper (t : ℚ) : (computedSignalSegments t : ℚ) ≤ 1 + 2 * |t| := by
  have hc := (Nat.ceil_lt_add_one (by positivity : 0 ≤ (2 : ℚ) * |t|)).le
  unfold computedSignalSegments
  rcases le_total 1 ⌈(2 : ℚ) * |t|⌉₊ with h | h
  · rw [max_eq_right h]
    linarith
  · rw [max_eq_left h]
    change (1 : ℚ) ≤ 1 + 2 * |t|
    linarith [abs_nonneg t]

private theorem sum_segments (q : ℕ) (τ : ℚ) (as : List (Option (Fin q))) :
    ((as.map (fun a => computedSignalSegments (atomTime q τ a))).sum : ℚ) ≤
      (as.length : ℚ) + 2 * (as.map (fun a => |atomTime q τ a|)).sum := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
    linarith [segment_upper (atomTime q τ a)]

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

theorem segmentSum_le_real (q : ℕ) (τ : ℚ) :
    (segmentSum q τ : ℝ) ≤ ((q + 1 : ℕ) : ℝ) + 2 * |(τ : ℝ)| := by
  exact_mod_cast segmentSum_le q τ

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

private theorem sum_queries (q : ℕ) (τ : ℚ) (k : ℕ) (as : List (Option (Fin q))) :
    (as.map (fun a => queryCost (atomTime q τ a) k)).sum ≤
      (as.map (fun a => computedSignalSegments (atomTime q τ a))).sum * factor τ k := by
  induction as with
  | nil => simp
  | cons a as ih =>
    simp only [List.map_cons, List.sum_cons]
    exact (Nat.add_le_add (atom_query_le q τ k a) ih).trans_eq (by ring)

theorem segmentSum_zero (q : ℕ) : segmentSum q 0 = q + 1 := by
  simp [segmentSum, atomTime, computedSignalSegments, DyadicClockPulses.axes,
    List.map_ofFn, Function.comp_def, add_comm]

theorem queryLedger_pos (q : ℕ) (τ : ℚ) (k : ℕ) : 0 < queryLedger q τ k := by
  unfold queryLedger
  rw [DyadicClockPulses.axes, List.map_cons, List.sum_cons]
  apply lt_of_lt_of_le ?_ (Nat.le_add_right _ _)
  unfold queryCost
  apply Nat.mul_pos (computed_signal_segment_size _).1
  omega

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

theorem queryLedger_le_real (q : ℕ) (τ : ℚ) (k : ℕ) :
    (queryLedger q τ k : ℝ) ≤ 27 * (((q + 1 : ℕ) : ℝ) + 2 * |(τ : ℝ)|) *
      (128 * ((k + Nat.clog 2 (rMax τ) + 16 : ℕ) : ℝ) + 1) := by
  exact_mod_cast queryLedger_le q τ k

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
