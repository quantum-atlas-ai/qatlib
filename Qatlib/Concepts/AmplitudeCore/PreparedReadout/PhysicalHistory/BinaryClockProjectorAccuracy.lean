/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockProjectorReadout
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.ProjectorPhysicalBudget

/-!
# Accuracy budget for the physical projector history

`actualProbability` selects the zero-projector-ancilla event in the binary clock simulation at
the clock size and precision chosen by `ProjectorPhysicalBudget`. The resulting probability,
scaled by `T`, approximates the integrated projector expectation.

These bounds provide a bias allowance and a mass cap for subsequent amplitude estimation in the
sense of [BrassardEtAl2002].

## Main statements

* `actual_integral_bias`: the scaled actual probability differs from the physical integral by at
  most `eps/4`.
* `actual_mass_le_cap`: an upper bound on the integral yields the scheduled mass cap.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockProjectorAccuracy

open Matrix
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
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

open Qatlib.Concepts.OperatorAccess.EncodedAccess
open Qatlib.Concepts.InstrumentCore.PovmBridge
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement

open MeasureTheory
open scoped Classical BigOperators Interval Matrix.Norms.L2Operator

variable {I E : Type} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]

/-- The zero-projector-ancilla probability of the actual history state at the scheduled clock
size and simulation precision. -/
noncomputable def actualProbability (α T eps : ℚ) (a m : ℕ)
    (U_H : Matrix (Reg a × I) (Reg a × I) ℂ)
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ) (ψ : QState (E × I)) : ℝ :=
  MeasureProb
    (BinaryClockProjectorReadout.actual (ProjectorPhysicalBudget.clockBits α T eps)
      a m α T (ProjectorPhysicalBudget.precisionBits α T eps) U_H UPi ψ)
    {x | x.2.2.1 = ZeroStr m}

/-- For a normalized purification and the stated Hamiltonian and projector encodings, the
physical integral differs from `T` times the scheduled actual probability by at most
`eps/4`. -/
theorem actual_integral_bias (α T eps : ℚ) (hα : 0 < α) (hT : 0 < T)
    (heps : 0 < eps) (a m : ℕ) (H Pi : Matrix I I ℂ) (hH : H.IsHermitian)
    (U_H : Matrix (Reg a × I) (Reg a × I) ℂ)
    (hHenc : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U_H
      (encodingFiber (I := I) (ZeroStr a)) (encodingFiber (I := I) (ZeroStr a)))
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (hPienc : ProjectedUnitaryEncoding Pi UPi (encodingFiber (I := I) (ZeroStr m))
      (encodingFiber (I := I) (ZeroStr m))) (hPistar : Piᴴ = Pi) (hPisq : Pi * Pi = Pi)
    (ψ : QState (E × I)) (hψ : Normalized ψ) :
    |(∫ t in (0:ℝ)..(T:ℝ), ProjectorHistoryBorn.physicalReadout H Pi (purifiedDensity ψ) t) -
      (T:ℝ) * actualProbability α T eps a m U_H UPi ψ| ≤ (eps:ℝ)/4 := by
  have hp : ‖Pi‖ ≤ (1 : ℝ) :=
    ProjectorPhysicalBudget.projector_norm_le_one Pi UPi (ZeroStr m) hPienc
  have hT' : (0 : ℝ) ≤ T := by exact_mod_cast hT.le
  have hα' : (0 : ℝ) ≤ α := by exact_mod_cast hα.le
  have hquad : (α:ℝ)*(T:ℝ)^2/(2*(ProjectorPhysicalBudget.clockSize α T eps : ℝ)) ≤
      (eps:ℝ)/8 := by
    exact_mod_cast ProjectorPhysicalBudget.quadrature_budget_rat α T eps heps
  have hsim : 2*(T:ℝ)*((ProjectorPhysicalBudget.clockBits α T eps+1 : ℕ) : ℝ)*
      (1/2 : ℝ)^(ProjectorPhysicalBudget.precisionBits α T eps) ≤ (eps:ℝ)/8 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr
      (ProjectorPhysicalBudget.simulation_budget_rat α T eps heps)
    push_cast at hh
    simpa only [one_div, one_mul, inv_pow, div_eq_mul_inv, mul_assoc, Nat.cast_add,
        Nat.cast_one] using! hh
  have hquad' : (α:ℝ)*‖Pi‖*(T:ℝ)^2/
      (2*(ProjectorPhysicalBudget.clockSize α T eps : ℝ)) ≤ (eps:ℝ)/8 := by
    calc
      _ = ((α:ℝ)*(T:ℝ)^2/(2*(ProjectorPhysicalBudget.clockSize α T eps : ℝ)))*‖Pi‖ := by ring
      _ ≤ ((α:ℝ)*(T:ℝ)^2/(2*(ProjectorPhysicalBudget.clockSize α T eps : ℝ)))*1 :=
        mul_le_mul_of_nonneg_left hp (by positivity)
      _ ≤ _ := by simpa using! hquad
  have h := BinaryClockProjectorReadout.actual_integral_error
    (ProjectorPhysicalBudget.clockBits α T eps) a m α T
    (ProjectorPhysicalBudget.precisionBits α T eps) hα hT.le H Pi hH U_H hHenc
    UPi hPienc hPistar hPisq ψ hψ
  change |(∫ t in (0:ℝ)..(T:ℝ),
      ProjectorHistoryBorn.physicalReadout H Pi (purifiedDensity ψ) t) -
      (T:ℝ) * actualProbability α T eps a m U_H UPi ψ| ≤ _ at h
  change |(∫ t in (0:ℝ)..(T:ℝ),
      ProjectorHistoryBorn.physicalReadout H Pi (purifiedDensity ψ) t) -
      (T:ℝ) * actualProbability α T eps a m U_H UPi ψ| ≤
      (α:ℝ)*‖Pi‖*(T:ℝ)^2/(2*(ProjectorPhysicalBudget.clockSize α T eps : ℝ)) +
        2*(T:ℝ)*(((ProjectorPhysicalBudget.clockBits α T eps+1 : ℕ) : ℝ)*
          (1/2 : ℝ)^(ProjectorPhysicalBudget.precisionBits α T eps)) at h
  linarith

/-- If the physical projector integral is at most `Jbar`, its scheduled actual probability
scaled by `T` is at most `massCap Jbar eps`. -/
theorem actual_mass_le_cap (α T eps Jbar : ℚ) (hα : 0 < α) (hT : 0 < T)
    (heps : 0 < eps) (a m : ℕ) (H Pi : Matrix I I ℂ) (hH : H.IsHermitian)
    (U_H : Matrix (Reg a × I) (Reg a × I) ℂ)
    (hHenc : ProjectedUnitaryEncoding (BinaryClockPhysicalTime.normalized α H) U_H
      (encodingFiber (I := I) (ZeroStr a)) (encodingFiber (I := I) (ZeroStr a)))
    (UPi : Matrix (Reg m × I) (Reg m × I) ℂ)
    (hPienc : ProjectedUnitaryEncoding Pi UPi (encodingFiber (I := I) (ZeroStr m))
      (encodingFiber (I := I) (ZeroStr m))) (hPistar : Piᴴ = Pi) (hPisq : Pi * Pi = Pi)
    (ψ : QState (E × I)) (hψ : Normalized ψ)
    (hJbar : (∫ t in (0:ℝ)..(T:ℝ),
      ProjectorHistoryBorn.physicalReadout H Pi (purifiedDensity ψ) t) ≤ (Jbar : ℝ)) :
    (T:ℝ) * actualProbability α T eps a m U_H UPi ψ ≤
      (ProjectorPhysicalBudget.massCap Jbar eps : ℝ) := by
  exact ProjectorPhysicalBudget.mass_cap_of_bias T eps Jbar _ _ hJbar
    (actual_integral_bias α T eps hα hT heps a m H Pi hH U_H hHenc UPi hPienc
      hPistar hPisq ψ hψ)

end Qatlib.Concepts.AmplitudeCore.PreparedReadout.PhysicalHistory.BinaryClockProjectorAccuracy
