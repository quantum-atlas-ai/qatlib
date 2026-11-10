/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockSingleCU
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockPhysicalTime

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
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory
open scoped Classical BigOperators Matrix.Norms.L2Operator

variable {W I : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

noncomputable local instance executionDecidableEq (q : ℕ) :
    DecidableEq (BinaryClockSingleCU.New q W) := BinaryClockSingleCU.newDecidableEq q W

noncomputable def normalized (α : ℚ) (H : Matrix I I ℂ) : Matrix I I ℂ :=
  (((α : ℝ)⁻¹ : ℝ) : ℂ) • H

omit [Fintype I] [DecidableEq I] in

theorem normalized_hermitian (α : ℚ) (H : Matrix I I ℂ) (hH : H.IsHermitian) :
    (normalized α H).IsHermitian := by
  change (normalized α H)ᴴ = normalized α H
  simp only [normalized, Matrix.conjTranspose_smul, hH.eq]
  simp

theorem source_norm_le (α : ℚ) (H : Matrix I I ℂ) (U : Matrix W W ℂ)
    (F : Matrix W I ℂ) (hα : 0 < α)
    (h : ProjectedUnitaryEncoding (normalized α H) U F F) : ‖H‖ ≤ (α : ℝ) := by
  have ha : (0 : ℝ) < (α : ℝ) := by exact_mod_cast hα
  have hn : ‖normalized α H‖ ≤ 1 := by
    rw [← h.encoded]
    exact l2_norm_compress_le_one h.left_isometry h.unitary h.right_isometry
  rw [normalized, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr ha)] at hn
  have hm : (α : ℝ) * ((α : ℝ)⁻¹ * ‖H‖) ≤ (α : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left hn ha.le
  calc
    ‖H‖ = (α : ℝ) * ((α : ℝ)⁻¹ * ‖H‖) := by
      rw [← mul_assoc, mul_inv_cancel₀ ha.ne', one_mul]
    _ ≤ (α : ℝ) * 1 := hm
    _ = (α : ℝ) := mul_one _

theorem evolution_scale_cancel (α : ℚ) (H : Matrix I I ℂ) (hα : 0 < α) (t : ℝ) :
    hamiltonianEvolution (normalized α H) ((α : ℝ) * t) = HamiltonianEvolution H t := by
  have ha : (α : ℝ) ≠ 0 := by exact_mod_cast hα.ne'
  have hac : ((α : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ha
  unfold hamiltonianEvolution HamiltonianEvolution normalized
  apply congrArg NormedSpace.exp
  rw [smul_smul]
  have hc : (-Complex.I * (((α : ℝ) * t : ℝ) : ℂ)) *
      (((α : ℝ)⁻¹ : ℝ) : ℂ) = -Complex.I * (t : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_inv]
    calc
      _ = (-Complex.I * (t : ℂ)) * (((α : ℝ) : ℂ) * ((α : ℝ) : ℂ)⁻¹) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hac, mul_one]
  rw [hc]

theorem evolution_physicalTime (α T : ℚ) (H : Matrix I I ℂ) (hα : 0 < α) :
    hamiltonianEvolution (normalized α H) ((α * T : ℚ) : ℝ) =
      HamiltonianEvolution H (T : ℝ) := by
  rw [Rat.cast_mul]
  exact evolution_scale_cancel α H hα (T : ℝ)

theorem midpoint_evolution (q : ℕ) (α T : ℚ) (H : Matrix I I ℂ)
    (hα : 0 < α) (x : Reg q) :
    hamiltonianEvolution (normalized α H)
      (((α * T) * Clock.rationalMidpoint (2 ^ q)
        (Clock.clockLabel q x) : ℚ) : ℝ) =
    HamiltonianEvolution H
      ((T * Clock.rationalMidpoint (2 ^ q)
        (Clock.clockLabel q x) : ℚ) : ℝ) := by
  rw [mul_assoc]
  exact evolution_physicalTime α _ H hα

noncomputable def physicalTarget (q : ℕ) (H : Matrix I I ℂ) (T : ℚ) :
    Matrix (Reg q × I) (Reg q × I) ℂ :=
  Qatlib.Concepts.BlockEncoding.LCU.select (fun x : Reg q => HamiltonianEvolution H
    ((T * Clock.rationalMidpoint (2 ^ q)
      (Clock.clockLabel q x) : ℚ) : ℝ))

theorem physicalTarget_unitary (q : ℕ) (H : Matrix I I ℂ) (T : ℚ) (hH : H.IsHermitian) :
    physicalTarget q H T ∈ Matrix.unitaryGroup (Reg q × I) ℂ :=
  Qatlib.Concepts.BlockEncoding.LCU.select_unitary
    (fun x : Reg q => HamiltonianEvolution H
      ((T * Clock.rationalMidpoint (2 ^ q)
        (Clock.clockLabel q x) : ℚ) : ℝ))
    (fun _ => hamiltonianEvolution_unitary hH _)

theorem target_eq (q : ℕ) (α T : ℚ) (H : Matrix I I ℂ) (hα : 0 < α) :
    BinaryClockSignalWord.target q (normalized α H) (α * T) (DyadicClockPulses.axes q) =
      physicalTarget q H T := by
  rw [BinaryClockSignalWord.target_midpoint]
  unfold physicalTarget
  apply congrArg (fun V : Reg q → Matrix I I ℂ => Qatlib.Concepts.BlockEncoding.LCU.select V)
  funext x
  exact midpoint_evolution q α T H hα x

noncomputable def instructions (q : ℕ) (F : Matrix W I ℂ) (α T : ℚ) (k : ℕ) :
    List (AdjointStep (BinaryClockSingleCU.New q W)) :=
  BinaryClockSingleCU.instructions q F (α * T) k

noncomputable def initialFrame (q : ℕ) (F : Matrix W I ℂ) :
    Matrix (BinaryClockSingleCU.New q W) (Reg q × I) ℂ :=
  BinaryClockSingleCU.initialFrame q F

theorem initialFrame_isometry (q : ℕ) (α : ℚ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (normalized α H) U F F) :
    IsIsometry (initialFrame q F) :=
  BinaryClockSingleCU.initialFrame_isometry q (normalized α H) U F
    (normalized_hermitian α H hH) h

theorem full_output_error (q : ℕ) (α T : ℚ) (k : ℕ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hα : 0 < α) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (normalized α H) U F F) (Ψ : QState (Reg q × I)) :
    ‖toEuclidean_fromVec
      (evaluate (BinaryClockSingleCU.oracle q U) (instructions q F α T k) *ᵥ
        (initialFrame q F *ᵥ Ψ) - initialFrame q F *ᵥ (physicalTarget q H T *ᵥ Ψ))‖ ≤
      ((q + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k * ‖toEuclidean_fromVec Ψ‖ := by
  have he := BinaryClockSingleCU.instructions_full_output_error q (normalized α H) U F
    (α * T) k (normalized_hermitian α H hH) h Ψ
  rw [target_eq q α T H hα] at he
  exact he

theorem resources (q : ℕ) (α T : ℚ) (k : ℕ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (normalized α H) U F F) :
    WellFormedAdjointCircuit (instructions q F α T k) ∧
      adjointQueryCount (instructions q F α T k) =
        BinaryClockSignalCost.queryLedger q (α * T) k ∧
      adjointGateCount (instructions q F α T k) =
        adjointGateCount (BinaryClockSignalWord.instructions q F (α * T) k) +
          2 * BinaryClockSignalCost.queryLedger q (α * T) k := by
  have hr := BinaryClockSingleCU.instructions_resources q (normalized α H) U F
    (α * T) k (normalized_hermitian α H hH) h
  have hq := (BinaryClockSignalWord.instructions_resources q (normalized α H) U F
    (α * T) k (normalized_hermitian α H hH) h).2.1
  simp only [hq] at hr
  exact hr

theorem actual_unitary (q : ℕ) (α T : ℚ) (k : ℕ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (normalized α H) U F F) :
    evaluate (BinaryClockSingleCU.oracle q U) (instructions q F α T k) ∈
      Matrix.unitaryGroup _ ℂ :=
  BinaryClockSingleCU.instructions_unitary q (normalized α H) U F
    (α * T) k (normalized_hermitian α H hH) h

theorem query_bound (q : ℕ) (α T : ℚ) (k : ℕ) (H : Matrix I I ℂ)
    (U : Matrix W W ℂ) (F : Matrix W I ℂ) (hH : H.IsHermitian)
    (h : ProjectedUnitaryEncoding (normalized α H) U F F) :
    (adjointQueryCount (instructions q F α T k) : ℚ) ≤
      27 * (((q + 1 : ℕ) : ℚ) + 2 * |α * T|) *
        (128 * ((k + Nat.clog 2 (BinaryClockSignalCost.rMax (α * T)) + 16 : ℕ) : ℚ) + 1) :=
  BinaryClockSingleCU.instructions_query_bound q (normalized α H) U F
    (α * T) k (normalized_hermitian α H hH) h

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockPhysicalTime
