/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Equation12Stat
import Qatlib.Concepts.BlockEncoding.StateBlockEncoding.FiberBridge
import Qatlib.Concepts.CoherentSim.ResetDiscard.CountedObliviousAmplification
set_option warningAsError false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

theorem equation12 : Equation12 := by
  intro J I _ _ _ _ W j₀ U hW hU ψ
  have hUU : U * Uᴴ = 1 := Unitary.mul_star_self_of_mem hU
  have hUtU : Uᴴ * U = 1 := Unitary.star_mul_self_of_mem hU
  have hP := isOrthogonalProjector_fiberProjector (I := I) j₀
  have hA := obliviousAmplitudeAmplification_mem_unitary (FiberProjector j₀) W hP hW.1
  have hblock := projected_obliviousAmplitudeAmplification_blockEncoding W j₀ U 2 hW
  have hpoly : (((3 / (2 : ℝ) : ℝ) : ℂ) • U) -
      (((4 / (2 : ℝ) ^ 3 : ℝ) : ℂ) • (U * Uᴴ * U)) = U := by
    rw [hUU, one_mul, ← sub_smul]
    norm_num
  rw [hpoly] at hblock
  have hcompress :
      (FiberProjector j₀ * ObliviousAmplitudeAmplification (FiberProjector j₀) W *
        FiberProjector j₀)ᴴ *
      (FiberProjector j₀ * ObliviousAmplitudeAmplification (FiberProjector j₀) W *
        FiberProjector j₀) = FiberProjector j₀ := by
    rw [hblock, fiberEmbed_conjTranspose, fiberEmbed_mul, hUtU,
      ← fiberProjector_eq_fiberEmbed_one]
  have hleak := unitary_preserves_projector_of_compressed_isometry (FiberProjector j₀)
    (ObliviousAmplitudeAmplification (FiberProjector j₀) W) hP hA hcompress
  calc
    _ = (ObliviousAmplitudeAmplification (FiberProjector j₀) W * FiberProjector j₀) *ᵥ
        TensorState (Ket j₀) ψ := by
      rw [← Matrix.mulVec_mulVec, fiberProjector_mulVec_tensorState_ket]
    _ = _ := by rw [hleak, hblock, fiberEmbed_mulVec_tensorState_ket]

theorem equation12_counted {J I : Type*} [Fintype J] [DecidableEq J]
    [Fintype I] [DecidableEq I] {W : Matrix (J × I) (J × I) ℂ} {j₀ : J}
    {U : Matrix I I ℂ} (hW : IsBlockEncoding W j₀ U 2)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    ∃ cs : List (AdjointStep (J × I)),
      WellFormedAdjointCircuit cs ∧
      Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding U (evaluate W cs)
        (encodingFiber j₀) (encodingFiber j₀) ∧
      (evaluate W cs * encodingFiber j₀ : Matrix (J × I) I ℂ) =
        (encodingFiber j₀ * U : Matrix (J × I) I ℂ) ∧
      adjointQueryCount cs = 3 ∧ adjointGateCount cs = 4 := by
  have henc : Qatlib.Concepts.Execution.WorkspaceCP.ProjectedUnitaryEncoding ((1 / 2 : ℂ) • U) W
      (encodingFiber j₀) (encodingFiber j₀) := by
    simpa using hW.toProjectedUnitaryEncoding
  have hiso : Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry U := by
    simpa only [Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry,
        Matrix.star_eq_conjTranspose] using hU.1
  exact Qatlib.Concepts.CoherentSim.ResetDiscard.oblivious_half_isometry_counted_wellFormed henc hiso

end Qatlib.Concepts.CoherentSim.ResetDiscard
