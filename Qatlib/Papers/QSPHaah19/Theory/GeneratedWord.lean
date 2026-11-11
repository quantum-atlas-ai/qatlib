/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeGeneratedSourcePackets

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

/-! Exact consumer of the rational Chebyshev producer.
This finite real-input contract supports preprocessing and word conventions; it does
not assert the full complex-Laurent uniqueness theorem or the paper RAM bound. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.QSPHaah19.Theory
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays

/-- The complete generated rational-input contract is consumed with every original premise and ordered output. -/
theorem generated_rectangular_signal_word
    {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
 (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (henc : ProjectedUnitaryEncoding A U L R) :
    ∃ (standard native : PhaseData) (trace : List ℕ),
      rootProjectionGeneratedPacket cs N E hparity=some (standard,native,trace) ∧
    let data := standard
    let word := nativeStandardPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data) ∧
      WellFormedAdjointCircuit word ∧
      adjointQueryCount word=N ∧ adjointGateCount word=N+1 ∧
      adjointQueryCount (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data)=N ∧
      adjointGateCount (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data)=N+1 ∧
      (N%2=1 →
        BlockEncoding (oddSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle U) word) (averageFrame L) (averageFrame R) 1 (E : ℝ)) ∧
      (N%2=0 →
        BlockEncoding (rightSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle Uᴴ)
            (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data))
          (averageFrame R) (averageFrame R) 1 (E : ℝ)) :=
  Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.source_original_generated_word A U L R cs N E hE htail hparity hnorm henc

end Qatlib.Papers.QSPHaah19.Theory
