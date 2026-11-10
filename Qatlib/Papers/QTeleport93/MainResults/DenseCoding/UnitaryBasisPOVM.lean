/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuditTeleport.NoSignalCode.QuantumMessageCount
import Qatlib.Concepts.ShadowModels.ShadowChannel.FiniteEnsembleMeasurement
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
namespace Qatlib.Papers.QTeleport93.MainResults.DenseCoding
open Matrix
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Foundations.InstrumentCore.Measurement

noncomputable def unitaryBasisPOVM {d : ℕ} (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) : FinitePOVM (Fin d) d where
  effect b := ensembleProjector (fun _ : Unit => V) ((), b)
  effect_sum := ensembleProjector_sum_axis (fun _ : Unit => V) (fun _ => hV) ()
  weight _ := 1
  weight_nonneg _ := by norm_num
  factor b := ensembleProjector (fun _ : Unit => V) ((), b)
  effect_eq_factor b := by
    rw [ensembleProjector_conjTranspose, ensembleProjector_idem _ (fun _ => hV)]
    simp

theorem unitary_basis_code_density {d : ℕ} (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (x : Fin d) :
    IsDensityOperator ((unitaryBasisPOVM V hV).effect x) := by
  change IsDensityOperator (ensembleProjector (fun _ : Unit => V) ((), x))
  exact ⟨ensembleProjector_posSemidef (fun _ : Unit => V) ((), x),
    ensembleProjector_trace (fun _ : Unit => V) (fun _ => hV) ((), x)⟩

theorem unitary_basis_code_decode {d : ℕ} (V : Operator d)
    (hV : V ∈ Matrix.unitaryGroup (Fin d) ℂ) (b x : Fin d) :
    Matrix.trace ((unitaryBasisPOVM V hV).effect b *
      (unitaryBasisPOVM V hV).effect x) = if b = x then 1 else 0 := by
  have hVV : V * Vᴴ = 1 := Matrix.mem_unitaryGroup_iff.mp hV
  change Matrix.trace ((Vᴴ * Projector {b} * V) * (Vᴴ * Projector {x} * V)) = _
  have hp : (Vᴴ * Projector {b} * V) * (Vᴴ * Projector {x} * V) =
      Vᴴ * (Projector {b} * Projector {x}) * V := by
    calc
      _ = Vᴴ * Projector {b} * (V * Vᴴ) * Projector {x} * V := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hVV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  rw [hp, Matrix.trace_mul_cycle, hVV, Matrix.one_mul,
    trace_projector_singleton_mul]
  simp [Projector, Matrix.diagonal_apply_eq]

end Qatlib.Papers.QTeleport93.MainResults.DenseCoding
