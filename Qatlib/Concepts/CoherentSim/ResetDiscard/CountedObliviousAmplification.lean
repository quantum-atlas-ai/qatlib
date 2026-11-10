/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.ObliviousAmplification
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

namespace Qatlib.Concepts.CoherentSim.ResetDiscard

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

theorem oblivious_half_isometry_counted_wellFormed {V : Matrix O I ℂ}
    {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding ((1 / 2 : ℂ) • V) U L R) (hV : IsIsometry V) :
    ∃ cs : List (AdjointStep H),
      WellFormedAdjointCircuit cs ∧
      ProjectedUnitaryEncoding V (evaluate U cs) L R ∧
      (evaluate U cs * R : Matrix H I ℂ) = (L * V : Matrix H I ℂ) ∧
      adjointQueryCount cs = 3 ∧ adjointGateCount cs = 4 := by
  refine ⟨compileQSVT (rangeProjector R) (rangeProjector L) (-Complex.I) cubicPhases,
    ?_, ?_, ?_, ?_, ?_⟩
  · apply compileQSVT_wellFormed
      (rangeProjector_isOrthogonalProjector h.right_isometry)
      (rangeProjector_isOrthogonalProjector h.left_isometry)
    · norm_num [IsPhase]
    · simp [cubicPhases, IsPhase]
  · rw [evaluate_compileQSVT]
    exact oblivious_half_isometry_projectedEncoding h hV
  · rw [evaluate_compileQSVT]
    exact oblivious_half_isometry_action h hV
  · rw [queryCount_compileQSVT]
    rfl
  · rw [gateCount_compileQSVT]
    rfl

end Qatlib.Concepts.CoherentSim.ResetDiscard
