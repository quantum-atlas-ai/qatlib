/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Papers.TrotterError19.GroupedError.TrotterCommutatorScalingStepsStat
public import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterCommutatorScalingCorrected
public import Qatlib.Papers.TrotterError19.GroupedError.TrotterCommutatorScalingSteps

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.TrotterFormula.TrotterCommutatorContracts Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
noncomputable section
open Qatlib.Concepts.TrotterFormula.GeneralOrder

namespace Qatlib.Papers.TrotterError19.GroupedError
open Matrix
open scoped Classical Matrix.Norms.L2Operator

/-- The corrected commutator based step count is positive, gives product formula error at most
the tolerance, and yields the stated exact word length. -/
theorem trotterCommutatorScalingStepsCorrected : TrotterCommutatorScalingStepsCorrected := by
  intro I _ _ xs H p hp hxs hH hc t ε hε
  (try dsimp only)
  let α := (p.factorial:ℝ)*pfCommAlphaSelf xs (p+1)
  have hα : 0≤α := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun _ _=>norm_nonneg _))
  have hb := trotter_selected_scalar_budget α t ε p hα hε hp
  have hs := trotterCommutatorScalingCorrected I xs H p _ hp hb.1 hxs hH hc t
  exact ⟨hb.1,hs.2.2.trans hb.2,hs.2.1⟩
end Qatlib.Papers.TrotterError19.GroupedError
