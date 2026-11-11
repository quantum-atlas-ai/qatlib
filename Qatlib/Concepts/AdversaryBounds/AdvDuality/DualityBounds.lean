/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.MatrixAccess.FrameFilterProd
import Qatlib.Concepts.QsvtCore.QsVtMain.CPPPhaseCompiler
import Qatlib.Concepts.OperatorErrors.Robustness
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalConsumers
import Qatlib.Concepts.MatrixAccess.FrameFilterUse
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ImplementationBackendDefs
import Qatlib.Concepts.AdversaryBounds.AdvDuality.ImplementationBackend
import Qatlib.Concepts.ReferenceError.RefTraceError.TensorOperatorNorm
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DualityDefs

/-!
# Finite-frame preparation and filtered composition bounds

This module collects the finite-frame approximation and filtered-program guarantees into
`clause11_endpoint` and `clause12_endpoint`. The first joins exact reflection-circuit
preparation of an approximating state with normalization, error bounds, and phase-compilation
counts; the second joins filtered-product semantics with circuit and memory-event accounting.

The estimates use finite-dimensional matrix perturbation methods as in [Bhatia1997] and the
circuit framework of [NielsenChuang2010].

## Main statements

* `clause11_endpoint`: preparation, approximation, phase-error, and phase-compilation guarantees
  for finite frame data.
* `clause12_endpoint`: filtered-program evaluation, compressed products, resource counts, and
  finite-data read accounting.

## References

* [Bhatia, 1997][Bhatia1997]
* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Foundations.QueryWordCore.Circuit

set_option autoImplicit false

noncomputable section

namespace Qatlib.Concepts.AdversaryBounds.AdvDuality
namespace ConstructionStageA
namespace WalkSpectral4

open Matrix
open Qatlib
open scoped BigOperators Classical Matrix.Norms.L2Operator

/-- For faithful finite data approximating an isometry with operator error below one, a legal
bounded-length reflection circuit prepares the normalized approximate target. The theorem
also gives target, projector, and phase errors and the exact compiled phase-call ledger. -/
theorem clause11_endpoint {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} (hF : IsIsometry F) (hf : FrameDataFidelity d F)
    {ψ : QState (Fin m)} (hψ : Normalized ψ) (hδ : finiteFrameOpError d < 1) :
    (∃ gs : List (ReflectionGate (n + (n + 1))), reflectionLegal gs ∧
        gs.length ≤ 128 * (n + 1) ^ 2 * 4 ^ n ∧
        Run 1 (reflectionCompile gs) (knownFrameEmbed n (Ket (fun _ => false))) =
          knownFrameEmbed n (finiteFramePrepared d ψ)) ∧
      Normalized (finiteFramePrepared d ψ) ∧
      ‖stateVector (finiteFramePrepared d ψ) - stateVector (F *ᵥ ψ)‖
        ≤ 2 * finiteFrameOpError d * ‖stateVector (d.realize *ᵥ ψ)‖⁻¹ ∧
      1 - finiteFrameOpError d ≤ ‖stateVector (d.realize *ᵥ ψ)‖ ∧
      ‖finiteFrameProjector d - rangeProjector F‖ ≤ finiteFrameProjectorError d ∧
      (∀ z : ℂ, IsPhase z →
        ‖phaseRotation (finiteFrameProjector d) z - phaseRotation (rangeProjector F) z‖
          ≤ 2 * finiteFrameProjectorError d) ∧
      (∀ fs : List (Fin m → ℝ), cppCounts (cppCompile fs) =
        (fs.length, 2 * (fs.length / 2), 2 * ((fs.length + 1) / 2), fs.length)) := by
  have hnorm := finiteFrame_prepared_normalized hF hψ hf hδ
  obtain ⟨gs, hgs, hlen, hrun⟩ :=
    known_complex_state_actual_local_preparation n (finiteFramePrepared d ψ) hnorm
  refine ⟨⟨gs, hgs, hlen, hrun⟩, hnorm, ?_, ?_, ?_, ?_, ?_⟩
  · exact finiteFrame_prepared_error hF hψ hf hδ
  · exact finiteFrame_target_norm_lower hF hψ hf
  · exact finiteFrame_projector_deviation hF hf
  · exact finiteFrame_phase_deviation hF hf
  · exact cpp_call_ledger_of_phases

/-- A caller-filtered program evaluates to the filtered product with the stated compressed
corner and additive query count plus one extra gate. Faithful frame data also yield the
projector-error bound and an event ledger with the prescribed error and read count. -/
theorem clause12_endpoint {n m : ℕ} {d : FiniteFrameData n m}
    {F : Matrix (Reg n) (Fin m) ℂ} (hF : IsIsometry F) (hf : FrameDataFidelity d F)
    (O : Matrix (Reg n) (Reg n) ℂ) (R : Matrix (Reg n) (Fin m) ℂ)
    (L : Matrix (Reg n) (Reg n) ℂ) (ca cb : List (AdjointStep (Reg n))) :
    evaluate (parallelOracle (J := Bool) O) (callerFilteredProgram F ca cb)
        = frameFilteredProduct F (evaluate O ca) (evaluate O cb) ∧
      (∀ x y, frameFilteredProduct F (evaluate O ca) (evaluate O cb) (false, x) (false, y)
        = ((evaluate O cb) * rangeProjector F * (evaluate O ca)) x y) ∧
      compress (flagFrame L) (frameFilteredProduct F (evaluate O ca) (evaluate O cb))
          (flagFrame R)
        = compress L (evaluate O cb) F * compress F (evaluate O ca) R ∧
      adjointQueryCount (callerFilteredProgram F ca cb)
        = adjointQueryCount ca + adjointQueryCount cb ∧
      adjointGateCount (callerFilteredProgram F ca cb)
        = adjointGateCount ca + adjointGateCount cb + 1 ∧
      ‖finiteFrameProjector d - rangeProjector F‖ ≤ finiteFrameProjectorError d ∧
      (∀ err : ℚ, errOf (callerFilteredEvents d ca cb err) = err ∧
        countEvent isReadEvent (callerFilteredEvents d ca cb err) = finiteFrameBitCost d) := by
  refine ⟨caller_filtered_evaluation F O ca cb, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x y
    exact caller_filtered_false_block F (evaluate O ca) (evaluate O cb) x y
  · exact caller_filtered_corner R F L (evaluate O ca) (evaluate O cb)
  · exact (caller_filtered_cost F O ca cb).1
  · exact (caller_filtered_cost F O ca cb).2
  · exact finiteFrame_projector_deviation hF hf
  · intro err
    exact ⟨caller_filtered_events_error d ca cb err,
      caller_filtered_events_reads d ca cb err⟩

end WalkSpectral4
end ConstructionStageA
end Qatlib.Concepts.AdversaryBounds.AdvDuality
