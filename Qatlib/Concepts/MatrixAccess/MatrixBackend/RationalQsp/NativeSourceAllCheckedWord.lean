/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.NativeSourceAllPackets
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Public
import Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.Verifier
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.RationalCircle
import Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords.HouseholderRotationTable
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativeHouseholder
import Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.NativePhasePrecision

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Foundations.PureStateMath.Reflection

/-! Actual source zero/constant/N=0 dispatch and the original-input all-branch packet.
Accepted raw roots are required only on the nonconstant path; proposer execution and total fees remain outside this value theorem. -/
set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays Qatlib.Concepts.MatrixAccess.MatrixBackend.PolynomialArrays.SourceInput Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Prep Qatlib.Concepts.MatrixAccess.MatrixBackend.GeneratedWords.Data Qatlib.Concepts.MatrixAccess.MatrixBackend.NativeWords


section AllWord

section AllWord

open Qatlib
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
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

open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data
open Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
open scoped Matrix.Norms.L2Operator

/-- The finite construction in `NativeSourceAllCheckedWord` satisfies `source_all_checked_word_transform` under the displayed hypotheses. -/
theorem source_all_checked_word_transform
    {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ)
 (cs : List ℚ) (N : ℕ) (E : ℚ) (hE : 0<E)
    (htail : ∀ k,N+1 ≤ k → cs.getD k 0=0)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    (hnorm : ∀ x∈Set.Icc (-1 : ℝ) 1,|(nativeChebyshevPolynomialFrom 0 cs).eval x| ≤ 1)
    (m : ℕ) (content : ℤ) (f : Fin m → RootIntegerFactorData)
    (hcert : 0<N → 0<sourceDegree cs N E → SourceNonconstantRawCertificate cs N E content f)
    (henc : ProjectedUnitaryEncoding A U L R) :
    let data := sourceAllBoundaryPacket cs N E f
    let word := nativeStandardPhaseWord (rangeProjector R) (rangeProjector L) data
    WellFormedAdjointCircuit (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data) ∧
      WellFormedAdjointCircuit word ∧
      adjointQueryCount word=N ∧ adjointGateCount word=N+1 ∧
      (N%2=1 →
        BlockEncoding (oddSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle U) word) (averageFrame L) (averageFrame R) 1 (E : ℝ)) ∧
      (N%2=0 →
        BlockEncoding (rightSingularTransform A (fun x => (((nativeChebyshevPolynomialFrom 0 cs).eval x : ℝ) : ℂ)))
          (evaluate (parallelOracle Uᴴ)
            (nativeStandardPhaseWord (rangeProjector L) (rangeProjector R) data))
          (averageFrame R) (averageFrame R) 1 (E : ℝ)) := by
  let data := sourceAllBoundaryPacket cs N E f
  have hc := source_all_posterior_accepts cs N E hE htail hparity hnorm content f hcert
  have hw := native_chebyshev_checked_word_transform A U L R cs (sourceResidual cs data) data E henc hc
  have hlen := (source_all_boundary_packet_spec cs N E f hparity).1
  simpa only [data,hlen] using hw

/-- The same emitted instruction list satisfies `source_all_word_counts` with the displayed gate and query accounting. -/
theorem source_all_word_counts {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (cs : List ℚ) (N : ℕ) (E : ℚ)
    (hparity : ∀ j : Fin (N+1),j.val%2≠N%2 → cs.getD j.val 0=0)
    {m : ℕ} (f : Fin m → RootIntegerFactorData) :
    adjointQueryCount (nativeStandardPhaseWord P Q (sourceAllBoundaryPacket cs N E f))=N ∧
      adjointGateCount (nativeStandardPhaseWord P Q (sourceAllBoundaryPacket cs N E f))=N+1 := by
  have hs := native_standard_phase_word_counts P Q (sourceAllBoundaryPacket cs N E f)
  rwa [(source_all_boundary_packet_spec cs N E f hparity).1] at hs

end AllWord

end AllWord

end Qatlib.Concepts.MatrixAccess.MatrixBackend.RationalQsp.Data.SourceInput
