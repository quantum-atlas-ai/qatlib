/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.IndexedQSVTBridge

/-!
# Register Reindexing for LCU Encodings

`reindexFrame` transports an encoding frame along a workspace equivalence while preserving
isometry and compression. Consequently, `reindexWorkspace_blockEncoding` changes the workspace
indexing without changing the encoded matrix, normalization, or error.

`swapLabelEquiv` exchanges two label registers. The identities for `prepareRegister` and
`coefficientLCUUnitary` show that coefficient preparation and LCU evaluation commute with
selecting an independent label, providing register bookkeeping for the CBMD algorithms of
[WangEtAl2026].

## Main statements

* `reindexFrame_isIsometry` and `compress_reindexFrame` preserve the frame and compressed
  operator.
* `reindexWorkspace_blockEncoding` transports block encodings along a workspace equivalence.
* `prepareRegister_swap_labels` and `coefficientLCUUnitary_swap_labels` distribute the reindexed
  preparation and LCU across the outer selected label.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

section Frames
variable {H K I : Type} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K]
  [Fintype I] [DecidableEq I]

/-- Reindexes the workspace rows of an encoding frame along the equivalence `e`. -/
def reindexFrame (e : K ≃ H) (F : Matrix H I ℂ) : Matrix K I ℂ :=
  F.submatrix e id

omit [DecidableEq H] [DecidableEq K] [Fintype I] in

/-- Reindexing a frame along a workspace equivalence preserves its isometry property. -/
theorem reindexFrame_isIsometry (e : K ≃ H) (F : Matrix H I ℂ) (hF : IsIsometry F) :
    IsIsometry (reindexFrame e F) := by
  unfold IsIsometry reindexFrame
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  simpa using! hF

omit [DecidableEq H] [DecidableEq K] [Fintype I] [DecidableEq I] in

/-- Simultaneously reindexing an operator and its encoding frame leaves their compressed
operator unchanged. -/
theorem compress_reindexFrame (e : K ≃ H) (F : Matrix H I ℂ) (U : Matrix H H ℂ) :
    compress (reindexFrame e F) (U.submatrix e e) (reindexFrame e F) = compress F U F := by
  simp only [compress, reindexFrame, Matrix.conjTranspose_submatrix]
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
  rfl

/-- A workspace equivalence transports a block encoding with the same target, normalization, and
error to the reindexed operator and frame. -/
theorem reindexWorkspace_blockEncoding (e : K ≃ H) (A : Matrix I I ℂ)
    (U : Matrix H H ℂ) (F : Matrix H I ℂ) (α ε : ℝ)
    (henc : BlockEncoding A U F F α ε) :
    BlockEncoding A (U.submatrix e e) (reindexFrame e F) (reindexFrame e F) α ε := by
  refine ⟨relabelGate_mem_unitary henc.unitary e.symm,
    reindexFrame_isIsometry e F henc.left_isometry,
    reindexFrame_isIsometry e F henc.right_isometry,
    henc.normalization_pos, henc.error_nonneg, ?_⟩
  rw [compress_reindexFrame]
  exact henc.error_le
end Frames

/-- Exchanges the two label registers in `J × (K × H)` while leaving the data register
unchanged. -/
def swapLabelEquiv (J K H : Type) : J × (K × H) ≃ K × (J × H) where
  toFun p := (p.2.1, (p.1, p.2.2))
  invFun p := (p.2.1, (p.1, p.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

section LCU
variable {J K H : Type} [Fintype J] [DecidableEq J] [Fintype K] [DecidableEq K]
  [Fintype H] [DecidableEq H]

omit [Fintype J] [Fintype K] [DecidableEq K] [Fintype H] in

/-- Swapping the two label registers turns preparation on the `K` register into a `J`-selected
family of the same preparation. -/
theorem prepareRegister_swap_labels (V : Matrix K K ℂ) :
    (prepareRegister (I := J × H) V).submatrix (swapLabelEquiv J K H) (swapLabelEquiv J K H) =
      select (fun _ : J => prepareRegister (I := H) V) := by
  ext ⟨j,k,i⟩ ⟨l,m,n⟩
  by_cases hj : j = l <;> by_cases hi : i = n <;>
    simp [prepareRegister, select, swapLabelEquiv, Matrix.kroneckerMap_apply,
      Matrix.one_apply, hj, hi]

/-- Swapping the two label registers distributes a coefficient LCU of selected operators into
the selected family of coefficient LCUs. -/
theorem coefficientLCUUnitary_swap_labels (c : K → ℂ) (k₀ : K)
    (U : K → J → Matrix H H ℂ) :
    (coefficientLCUUnitary c (fun k => select (U k)) k₀).submatrix
        (swapLabelEquiv J K H) (swapLabelEquiv J K H) =
      select (fun j => coefficientLCUUnitary c (fun k => U k j) k₀) := by
  have hphase : (select (phaseAbsorbed c (fun k => select (U k)))).submatrix
      (swapLabelEquiv J K H) (swapLabelEquiv J K H) =
      select (fun j => select (phaseAbsorbed c (fun k => U k j))) := by
    ext ⟨j,k,i⟩ ⟨l,m,n⟩
    by_cases hj : j = l <;> by_cases hk : k = m <;>
      simp [select, phaseAbsorbed, swapLabelEquiv, hj, hk]
  simp only [coefficientLCUUnitary]
  rw [← Matrix.submatrix_mul_equiv _ _ (swapLabelEquiv J K H) (swapLabelEquiv J K H) (swapLabelEquiv J K H),
    ← Matrix.submatrix_mul_equiv _ _ (swapLabelEquiv J K H) (swapLabelEquiv J K H) (swapLabelEquiv J K H)]
  rw [← Matrix.conjTranspose_submatrix, prepareRegister_swap_labels,
    hphase, parallel_select_adjoint,
    parallel_select_mul, parallel_select_mul]

end LCU
end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
