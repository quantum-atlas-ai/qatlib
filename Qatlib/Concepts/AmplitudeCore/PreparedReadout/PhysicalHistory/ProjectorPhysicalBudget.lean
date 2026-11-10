/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockPhysicalTime
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ProjectorHistoryBorn
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ProjectorPhysicalBudget

open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
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

open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.InstrumentCore.PovmBridge
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

open MeasureTheory
open scoped Classical BigOperators Interval Matrix.Norms.L2Operator

def clockBits (α T eps : ℚ) : ℕ :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits (4*α*T^2/eps)

def precisionBits (α T eps : ℚ) : ℕ :=
  Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits (16*T*((clockBits α T eps+1 : ℕ) : ℚ)/eps)

def clockSize (α T eps : ℚ) : ℕ := 2^(clockBits α T eps)

def massCap (Jbar eps : ℚ) : ℚ := Jbar + eps/4

theorem mass_cap_of_bias (T eps Jbar : ℚ) (J p : ℝ)
    (hJ : J ≤ (Jbar : ℝ)) (hbias : |J-(T:ℝ)*p| ≤ (eps:ℝ)/4) :
    (T:ℝ)*p ≤ (massCap Jbar eps : ℝ) := by
  have h := (abs_le.mp hbias).1
  change (T:ℝ)*p ≤ ((Jbar + eps/4 : ℚ) : ℝ)
  push_cast
  linarith

theorem clockSize_pos (α T eps : ℚ) : 0 < clockSize α T eps := by
  exact pow_pos (by decide) _

theorem quadrature_budget_rat (α T eps : ℚ) (heps : 0 < eps) :
    α*T^2/(2*(clockSize α T eps : ℚ)) ≤ eps/8 := by
  have hh :=
      Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits_bound
      (4*α*T^2/eps)
  change 4*α*T^2/eps ≤ (2:ℚ)^(clockBits α T eps) at hh
  have hcast : (clockSize α T eps : ℚ) = (2:ℚ)^(clockBits α T eps) := by
    simp [clockSize]
  rw [← hcast] at hh
  have hc := (div_le_iff₀ heps).mp hh
  have hsize : (0 : ℚ) < clockSize α T eps := by
    exact_mod_cast clockSize_pos α T eps
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < 2*(clockSize α T eps : ℚ))).mpr
  nlinarith

theorem simulation_budget_rat (α T eps : ℚ) (heps : 0 < eps) :
    2*T*((clockBits α T eps+1 : ℕ) : ℚ)/(2 : ℚ)^(precisionBits α T eps) ≤ eps/8 := by
  have hh := Qatlib.Concepts.AmplitudeCore.PreparedReadout.SmallProbabilitySchedule.dyadicBits_bound
    (16*T*((clockBits α T eps+1 : ℕ) : ℚ)/eps)
  change 16*T*((clockBits α T eps+1 : ℕ) : ℚ)/eps ≤
    (2 : ℚ)^(precisionBits α T eps) at hh
  have hc := (div_le_iff₀ heps).mp hh
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < (2 : ℚ)^(precisionBits α T eps))).mpr
  nlinarith

variable {W I E A : Type} [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
  [Fintype E] [DecidableEq E] [Fintype A] [DecidableEq A]

theorem projector_norm_le_one (Pi : Matrix I I ℂ) (U : Matrix (A × I) (A × I) ℂ)
    (a : A) (h : ProjectedUnitaryEncoding Pi U (encodingFiber a) (encodingFiber a)) :
    ‖Pi‖ ≤ 1 := by
  rw [← h.encoded]
  exact l2_norm_compress_le_one h.left_isometry h.unitary h.right_isometry

theorem integral_bias (α T eps : ℚ) (hα : 0 < α) (hT : 0 < T) (heps : 0 < eps)
    (H Pi : Matrix I I ℂ) (hH : H.IsHermitian)
    (UH : Matrix W W ℂ) (F : Matrix W I ℂ)
    (hsource : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) UH F F)
    (UPi : Matrix (A × I) (A × I) ℂ) (a : A)
    (hPi : ProjectedUnitaryEncoding Pi UPi (encodingFiber a) (encodingFiber a))
    (hstar : Piᴴ = Pi) (hsq : Pi*Pi = Pi)
    (ψ : QState (E × I)) (hψ : Normalized ψ)
    (actual : QState (Fin (clockSize α T eps) × (E × (A × I)))) (hactual : Normalized actual)
    (herr : ‖toEuclidean_fromVec (actual - ProjectorHistoryBorn.idealOutput UPi a
      (fun j : Fin (clockSize α T eps) => HamiltonianEvolution H
        ((T : ℝ)*Clock.midpoint (clockSize α T eps) j)) ψ)‖ ≤
        ((clockBits α T eps+1 : ℕ) : ℝ)*(1/2 : ℝ)^(precisionBits α T eps)) :
    |(∫ t in (0:ℝ)..(T:ℝ), ProjectorHistoryBorn.physicalReadout H Pi (purifiedDensity ψ) t) -
      (T:ℝ)*MeasureProb actual {x | x.2.2.1 = a}| ≤ (eps:ℝ)/4 := by
  have hnorm := BinaryClockPhysicalTime.source_norm_le α H UH F hα hsource
  have hp := projector_norm_le_one Pi UPi a hPi
  have hT' : (0 : ℝ) ≤ T := by exact_mod_cast hT.le
  have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα.le
  have hquad : (α:ℝ)*(T:ℝ)^2/(2*(clockSize α T eps : ℝ)) ≤ (eps:ℝ)/8 := by
    exact_mod_cast quadrature_budget_rat α T eps heps
  have hsim : 2*(T:ℝ)*((clockBits α T eps+1 : ℕ) : ℝ)*
      (1/2 : ℝ)^(precisionBits α T eps) ≤ (eps:ℝ)/8 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (simulation_budget_rat α T eps heps)
    push_cast at hh
    simpa only [one_div, one_mul, inv_pow, div_eq_mul_inv, mul_assoc, Nat.cast_add,
        Nat.cast_one] using! hh
  have hquad' : (α:ℝ)*‖Pi‖*(T:ℝ)^2/(2*(clockSize α T eps : ℝ)) ≤ (eps:ℝ)/8 := by
    calc
      _ = ((α:ℝ)*(T:ℝ)^2/(2*(clockSize α T eps : ℝ)))*‖Pi‖ := by ring
      _ ≤ ((α:ℝ)*(T:ℝ)^2/(2*(clockSize α T eps : ℝ)))*1 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ := by simpa using! hquad
  have h := ProjectorHistoryBorn.approximate_history_integral_error H hH Pi UPi a hPi
    hstar hsq ψ hψ (α:ℝ) (T:ℝ) hnorm hT' (clockSize α T eps)
    (clockSize_pos α T eps) actual hactual
    (((clockBits α T eps+1 : ℕ) : ℝ)*(1/2 : ℝ)^(precisionBits α T eps)) herr
  linarith

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ProjectorPhysicalBudget
