/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicOriginalOracleBridge

/-!
# Time-indexed compilation to the original oracle

`dynamicTimeWorkspaceEquiv` regroups the sample and time registers so that the original oracle
depends only on its time address. `dynamicTimeOriginalWord` transports the compiled circuit to
this workspace, preserving its block-encoding parameters while doubling the query count and
adding twelve fixed gates per source query. This supplies a circuit interface for the
time-dependent construction of [WangEtAl2026].

## Main statements

* `dynamicTimeSource_reindex`: identifies the controlled oracle after regrouping the registers.
* `dynamicTimeOriginalWord_blockEncoding`: combines well-formedness, the transported encoding,
  and exact circuit counts.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

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
set_option maxHeartbeats 800000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator
variable {T F J W I : Type} [Fintype T] [DecidableEq T] [Fintype F] [DecidableEq F]
  [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]

local instance cbmdDynamicTimeOracleBridgeInstance1 (T : Type) [DecidableEq T] : DecidableEq (DynamicOriginalLabels T) :=
  inferInstanceAs (DecidableEq (T × (Bool × (Bool × Bool))))
local instance cbmdDynamicTimeOracleBridgeInstance2 (J W : Type) [DecidableEq J] [DecidableEq W] :
    DecidableEq (DynamicSampleWorkspace J W) :=
  inferInstanceAs (DecidableEq (Bool × (J × (Bool × (Bool × W)))))

/-- The workspace equivalence that moves the sample register `F` beside the time address `J`,
leaving the control and original-oracle labels intact. -/
def dynamicTimeWorkspaceEquiv (T F J W : Type) :
    Bool × ((DynamicOriginalLabels T × F) × (J × W)) ≃
    Bool × (DynamicOriginalLabels T × ((F × J) × W)) where
  toFun := fun ⟨b,⟨l,f⟩,j,w⟩ => (b,l,(f,j),w)
  invFun := fun ⟨b,l,⟨f,j⟩,w⟩ => (b,(l,f),j,w)
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype T] [Fintype F] [Fintype J] [Fintype W] in

/-- Reindexing the controlled oracle by `dynamicTimeWorkspaceEquiv` turns the sample register
into a spectator and leaves selection on the time address. -/
theorem dynamicTimeSource_reindex (U : J → Matrix W W ℂ) :
    (controlOracle (parallelOracle (J := DynamicOriginalLabels T)
      (select (fun fj : F × J => U fj.2)))).submatrix
        (dynamicTimeWorkspaceEquiv T F J W) (dynamicTimeWorkspaceEquiv T F J W) =
    controlOracle (parallelOracle (J := DynamicOriginalLabels T × F) (select U)) := by
  ext ⟨b,⟨l,f⟩,j,w⟩ ⟨c,⟨l',f'⟩,j',w'⟩
  by_cases hl : l = l' <;> by_cases hf : f = f' <;>
    by_cases hj : j = j' <;> by_cases hw : w = w' <;>
    cases b <;> cases c <;>
    simp [dynamicTimeWorkspaceEquiv, controlOracle, parallelOracle, select,
      hl, hf, hj, hw]

/-- The original-oracle compilation of `cs`, reindexed so that the sample register is a
spectator to the time-selected oracle. -/
def dynamicTimeOriginalWord (α Λ : ℝ) (s : F × J → ℝ)
    (cs : List (AdjointStep (T × DynamicSampleWorkspace (F × J) W))) :
    List (AdjointStep (Bool × ((DynamicOriginalLabels T × F) × (J × W)))) :=
  reindexAdjointWord (dynamicTimeWorkspaceEquiv T F J W) (dynamicOriginalWord α Λ s cs)

/-- Evaluation of the time-indexed compiled word is the reindexing of the evaluation of
`dynamicOriginalWord`. -/
theorem dynamicTimeOriginalWord_evaluate (α Λ : ℝ) (s : F × J → ℝ)
    (cs : List (AdjointStep (T × DynamicSampleWorkspace (F × J) W)))
    (U : J → Matrix W W ℂ) :
    evaluate (controlOracle (parallelOracle (J := DynamicOriginalLabels T × F) (select U)))
      (dynamicTimeOriginalWord α Λ s cs) =
    (evaluate (controlOracle (parallelOracle (J := DynamicOriginalLabels T)
      (select (fun fj : F × J => U fj.2)))) (dynamicOriginalWord α Λ s cs)).submatrix
        (dynamicTimeWorkspaceEquiv T F J W) (dynamicTimeWorkspaceEquiv T F J W) := by
  rw [← dynamicTimeSource_reindex (T := T) (F := F), dynamicTimeOriginalWord,
    reindexAdjointWord_evaluate]

/-- The compiled word uses twice as many queries as `cs` and its fixed-gate count is that of
`cs` plus twelve times its query count. -/
theorem dynamicTimeOriginalWord_cost (α Λ : ℝ) (s : F × J → ℝ)
    (cs : List (AdjointStep (T × DynamicSampleWorkspace (F × J) W))) :
    adjointQueryCount (dynamicTimeOriginalWord α Λ s cs) = 2 * adjointQueryCount cs ∧
    adjointGateCount (dynamicTimeOriginalWord α Λ s cs) =
      adjointGateCount cs + 12 * adjointQueryCount cs := by
  simp only [dynamicTimeOriginalWord, (reindexAdjointWord_cost _ _).1,
    (reindexAdjointWord_cost _ _).2]
  exact dynamicOriginalWord_cost α Λ s cs

/-- Under the positivity, sample bound, unitarity, and source-encoding hypotheses, the compiled
word is well formed and preserves the block encoding with reindexed frames. Its query count
doubles and it adds twelve fixed gates per source query. -/
theorem dynamicTimeOriginalWord_blockEncoding (α Λ : ℝ) (s : F × J → ℝ)
    (hα : 0 < α) (hΛ : 0 < Λ) (hbound : ∀ j, α * Real.sqrt (1 + (s j)^2) ≤ Λ)
    (U : J → Matrix W W ℂ) (hU : ∀ j, U j ∈ Matrix.unitaryGroup W ℂ)
    (cs : List (AdjointStep (T × DynamicSampleWorkspace (F × J) W)))
    (hcs : WellFormedAdjointCircuit cs)
    (A : Matrix I I ℂ) (R : Matrix (T × DynamicSampleWorkspace (F × J) W) I ℂ) (β ε : ℝ)
    (henc : BlockEncoding A
      (evaluate (parallelOracle (J := T)
        (controlOracle (select (fun j => paddedFirstOrderInputUnitary (U j.2) α Λ (s j))))) cs)
      R R β ε) :
    WellFormedAdjointCircuit (dynamicTimeOriginalWord α Λ s cs) ∧
    BlockEncoding A
      (evaluate (controlOracle (parallelOracle (J := DynamicOriginalLabels T × F) (select U)))
        (dynamicTimeOriginalWord α Λ s cs))
      (reindexFrame (dynamicTimeWorkspaceEquiv T F J W)
        (tagFrame false (reindexFrame (dynamicOriginalWorkspaceEquiv T (F × J) W) R)))
      (reindexFrame (dynamicTimeWorkspaceEquiv T F J W)
        (tagFrame false (reindexFrame (dynamicOriginalWorkspaceEquiv T (F × J) W) R))) β ε ∧
    adjointQueryCount (dynamicTimeOriginalWord α Λ s cs) = 2 * adjointQueryCount cs ∧
    adjointGateCount (dynamicTimeOriginalWord α Λ s cs) =
      adjointGateCount cs + 12 * adjointQueryCount cs := by
  obtain ⟨hw,he,_,_⟩ := dynamicOriginalWord_blockEncoding α Λ s hα hΛ hbound
    (fun j => U j.2) (fun j => hU j.2) cs hcs A R β ε henc
  have hr := reindexWorkspace_blockEncoding (dynamicTimeWorkspaceEquiv T F J W)
    _ _ _ _ _ he
  rw [← dynamicTimeOriginalWord_evaluate] at hr
  exact ⟨reindexAdjointWord_wellFormed _ hw, hr, dynamicTimeOriginalWord_cost α Λ s cs⟩

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
