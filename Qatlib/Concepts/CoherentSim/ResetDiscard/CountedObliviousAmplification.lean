/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.ObliviousAmplification
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed

/-!
# Counted oblivious amplification

`oblivious_half_isometry_counted_wellFormed` realizes exact oblivious amplification of a
half-scaled isometry by a well-formed adjoint circuit. It records both the projected encoding
and the full action on the input frame, together with exact resource counts, as in the
amplification step of [BerryEtAl2015Taylor].

## Main statements

* `oblivious_half_isometry_counted_wellFormed`: Exact amplification using three queries and four
  gates.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

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

/-- A projected unitary encoding of half an isometry yields a well-formed circuit that encodes
the full isometry and acts exactly on the input frame. The circuit uses three queries and
four gates. See [BerryEtAl2015Taylor]. -/
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
