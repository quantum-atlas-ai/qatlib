/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.DynamicTimeOracleBridge
import Qatlib.Papers.Cbmd26.Algorithms.CoherentFreshWordBridge
import Qatlib.Papers.Cbmd26.Algorithms.ComputationalWorkspaceBridge

/-!
# Register layouts for fresh dynamic circuits

Defines the register types and basis equivalences connecting fresh-query circuits with dynamic
sample and original-oracle workspaces. It transports evaluations and costs through
`dynamicFreshReindexedWord` and identifies `dynamicFreshFinalFrame` with a computational ancilla
frame. These results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `dynamicFreshReindexedWord_evaluate`: transports fresh-word semantics.
* `dynamicFreshFinalFrame_computational`: identifies the final frame as a computational event
  frame.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SharedAncilla.AncillaProduct
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

/-- Abbreviates the sample ancilla as two Boolean registers together with the original ancilla. -/
abbrev DynamicSampleAnc (Anc : Type) := Bool × (Bool × Anc)
/-- Reassociates the sample ancilla and system register into two Boolean registers followed by
the original ancilla-system pair. -/
def sampleAncillaEquiv (Anc I : Type) :
    DynamicSampleAnc Anc × I ≃ Bool × (Bool × (Anc × I)) where
  toFun := fun ⟨⟨p,c,a⟩,i⟩ => (p,c,a,i)
  invFun := fun ⟨p,c,a,i⟩ => ((p,c,a),i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Abbreviates the stored Taylor label and fresh signal registers. -/
abbrev DynamicFreshStored (Anc J : Type) (K : ℕ) :=
  TaylorWordLabel J K × FreshSignals (DynamicSampleAnc Anc) K
/-- Abbreviates the frequency-labelled Taylor and fresh-query workspace. -/
abbrev DynamicFreshSpace (F Anc J I : Type) (K : ℕ) :=
  F × (TaylorWordLabel J K × FreshQueryWorkspace (DynamicSampleAnc Anc) J I K)

/-- Rearranges the stored labels and dynamic sample workspace into the frequency-labelled
fresh-query layout. -/
def dynamicFreshWorkspaceEquiv (F Anc J I : Type) (K : ℕ) :
    DynamicFreshStored Anc J K × DynamicSampleWorkspace (F × J) (Anc × I) ≃
      DynamicFreshSpace F Anc J I K where
  toFun := fun ⟨⟨tay,sig⟩,b,⟨f,j⟩,p,c,a,i⟩ => (f,tay,sig,b,j,(p,c,a),i)
  invFun := fun ⟨f,tay,sig,b,j,⟨p,c,a⟩,i⟩ => ((tay,sig),b,(f,j),p,c,a,i)
  left_inv _ := rfl
  right_inv _ := rfl

variable {F Anc J I : Type} [Fintype F] [DecidableEq F]
  [Fintype Anc] [DecidableEq Anc] [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

local instance cbmdDynamicFreshRegisterBridgeInstance1 (Anc : Type) [DecidableEq Anc] : DecidableEq (DynamicSampleAnc Anc) :=
  inferInstanceAs (DecidableEq (Bool × (Bool × Anc)))
local instance cbmdDynamicFreshRegisterBridgeInstance2 (T : Type) [DecidableEq T] : DecidableEq (DynamicOriginalLabels T) :=
  inferInstanceAs (DecidableEq (T × (Bool × (Bool × Bool))))
local instance cbmdDynamicFreshRegisterBridgeInstance3 (J W : Type) [DecidableEq J] [DecidableEq W] :
    DecidableEq (DynamicSampleWorkspace J W) :=
  inferInstanceAs (DecidableEq (Bool × (J × (Bool × (Bool × W)))))
local instance cbmdDynamicFreshRegisterBridgeInstance4 (F Anc J I : Type) (K : ℕ) [DecidableEq F] [DecidableEq Anc]
    [DecidableEq J] [DecidableEq I] : DecidableEq (DynamicFreshSpace F Anc J I K) :=
  inferInstanceAs (DecidableEq (F × (TaylorWordLabel J K ×
    (FreshSignals (DynamicSampleAnc Anc) K × (Bool × (J × (DynamicSampleAnc Anc × I)))))))

local instance cbmdDynamicFreshRegisterBridgeInstance5 (Anc J : Type) (K : ℕ) [DecidableEq Anc] [DecidableEq J] :
    DecidableEq (DynamicFreshStored Anc J K) :=
  inferInstanceAs (DecidableEq (TaylorWordLabel J K × FreshSignals (DynamicSampleAnc Anc) K))

omit [Fintype F] [Fintype Anc] [Fintype J] [Fintype I] in

/-- Reindexing the selected fresh primitive source gives the stored-register spectator lift of
the controlled frequency-time selected sample source. -/
theorem dynamicFreshSource_reindex (K : ℕ)
    (V : F → J → Matrix (Bool × (Bool × (Anc × I))) (Bool × (Bool × (Anc × I))) ℂ) :
    (select (fun f => parallelOracle (J := TaylorWordLabel J K)
      (freshPrimitiveQuery K (fun j => (V f j).submatrix
        (sampleAncillaEquiv Anc I) (sampleAncillaEquiv Anc I))))).submatrix
      (dynamicFreshWorkspaceEquiv F Anc J I K) (dynamicFreshWorkspaceEquiv F Anc J I K) =
    parallelOracle (J := DynamicFreshStored Anc J K)
      (controlOracle (select (fun fj : F × J => V fj.1 fj.2))) := by
  ext ⟨⟨tay,sig⟩,b,⟨f,j⟩,p,c,a,i⟩ ⟨⟨tay',sig'⟩,b',⟨f',j'⟩,p',c',a',i'⟩
  by_cases hf : f = f' <;> by_cases ht : tay = tay' <;>
    by_cases hs : sig = sig' <;> by_cases hj : j = j' <;>
    cases b <;> cases b' <;>
    simp [dynamicFreshWorkspaceEquiv, sampleAncillaEquiv, freshPrimitiveQuery,
      parallelOracle, controlOracle, select, hf, ht, hs, hj, Matrix.one_apply, and_assoc]

/-- Reindexes a fresh dynamic word to the stored-label and dynamic sample layout. -/
def dynamicFreshReindexedWord (K : ℕ)
    (cs : List (AdjointStep (DynamicFreshSpace F Anc J I K))) :
    List (AdjointStep (DynamicFreshStored Anc J K ×
      DynamicSampleWorkspace (F × J) (Anc × I))) :=
  reindexAdjointWord (dynamicFreshWorkspaceEquiv F Anc J I K) cs

/-- Evaluation of the reindexed word against the stored-register dynamic sample source equals
reindexing the original selected fresh evaluation. -/
theorem dynamicFreshReindexedWord_evaluate (K : ℕ)
    (V : F → J → Matrix (Bool × (Bool × (Anc × I))) (Bool × (Bool × (Anc × I))) ℂ)
    (cs : List (AdjointStep (DynamicFreshSpace F Anc J I K))) :
    evaluate (parallelOracle (J := DynamicFreshStored Anc J K)
      (controlOracle (select (fun fj : F × J => V fj.1 fj.2))))
      (dynamicFreshReindexedWord K cs) =
    (evaluate (select (fun f => parallelOracle (J := TaylorWordLabel J K)
      (freshPrimitiveQuery K (fun j => (V f j).submatrix
        (sampleAncillaEquiv Anc I) (sampleAncillaEquiv Anc I))))) cs).submatrix
      (dynamicFreshWorkspaceEquiv F Anc J I K) (dynamicFreshWorkspaceEquiv F Anc J I K) := by
  rw [← dynamicFreshSource_reindex K V, dynamicFreshReindexedWord, reindexAdjointWord_evaluate]

omit [Fintype F] [DecidableEq F] [Fintype Anc] [DecidableEq Anc]
  [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] in

/-- Reindexing a fresh dynamic word preserves its query and gate counts. -/
theorem dynamicFreshReindexedWord_cost (K : ℕ)
    (cs : List (AdjointStep (DynamicFreshSpace F Anc J I K))) :
    adjointQueryCount (dynamicFreshReindexedWord K cs) = adjointQueryCount cs ∧
    adjointGateCount (dynamicFreshReindexedWord K cs) = adjointGateCount cs :=
  reindexAdjointWord_cost _ _

/-- Reindexing a well-formed fresh dynamic word preserves well-formedness. -/
theorem dynamicFreshReindexedWord_wellFormed (K : ℕ)
    (cs : List (AdjointStep (DynamicFreshSpace F Anc J I K)))
    (hcs : WellFormedAdjointCircuit cs) :
    WellFormedAdjointCircuit (dynamicFreshReindexedWord K cs) :=
  reindexAdjointWord_wellFormed _ hcs

/-- Abbreviates the final controlled original-oracle workspace, including frequency, time,
ancilla, and system registers. -/
abbrev DynamicFreshFinalSpace (F Anc J I : Type) (K : ℕ) :=
  Bool × ((DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) × (J × (Anc × I)))
/-- Abbreviates the auxiliary registers of the final fresh dynamic workspace. -/
abbrev DynamicFreshAux (F Anc J : Type) (K : ℕ) :=
  Bool × ((DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) × (J × Anc))

local instance cbmdDynamicFreshRegisterBridgeInstance6 (F Anc J : Type) (K : ℕ) [DecidableEq F] [DecidableEq Anc]
    [DecidableEq J] : DecidableEq (DynamicFreshAux F Anc J K) :=
  inferInstanceAs (DecidableEq (Bool × ((DynamicOriginalLabels (DynamicFreshStored Anc J K) × F) × (J × Anc))))

/-- Separates the final fresh dynamic workspace into its auxiliary registers and system
register. -/
def dynamicFreshFinalEquiv (F Anc J I : Type) (K : ℕ) :
    DynamicFreshFinalSpace F Anc J I K ≃ DynamicFreshAux F Anc J K × I where
  toFun := fun ⟨b,⟨l,f⟩,j,a,i⟩ => ((b,(l,f),j,a),i)
  invFun := fun ⟨⟨b,⟨l,f⟩,j,a⟩,i⟩ => (b,(l,f),j,a,i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Defines the clean auxiliary label with empty Taylor word, zero fresh signals, false control
bits, and the specified frequency, time, and ancilla labels. -/
def dynamicFreshCleanAux (f₀ : F) (j₀ : J) (a₀ : Anc) (K : ℕ) :
    DynamicFreshAux F Anc J K :=
  (false,(((taylorEmptyLabel J K, freshSignalsZero (false,false,a₀) K),false,false,false),f₀),j₀,a₀)

/-- Transports the clean fresh-word frame through the original-oracle and time-workspace
register equivalences. -/
def dynamicFreshFinalFrame (f₀ : F) (j₀ : J) (a₀ : Anc) (K : ℕ) :
    Matrix (DynamicFreshFinalSpace F Anc J I K) I ℂ :=
  reindexFrame (dynamicTimeWorkspaceEquiv (DynamicFreshStored Anc J K) F J (Anc × I))
    (tagFrame false (reindexFrame (dynamicOriginalWorkspaceEquiv
      (DynamicFreshStored Anc J K) (F × J) (Anc × I))
      (reindexFrame (dynamicFreshWorkspaceEquiv F Anc J I K)
        (tagFrame f₀ (tagFrame (taylorEmptyLabel J K)
          (freshWordFrame (I := I) j₀ (false,false,a₀) K))))))

omit [Fintype J] in

/-- The fresh-word frame entry is one exactly at its clean signal, control, oracle-label,
ancilla, and system basis tuple, and zero elsewhere. -/
private theorem freshWordFrame_entry (j₀ : J) (a₀ : Anc) (K : ℕ)
    (x : FreshQueryWorkspace Anc J I K) (i : I) :
    freshWordFrame j₀ a₀ K x i =
      if x = (freshSignalsZero a₀ K,false,j₀,a₀,i) then 1 else 0 := by
  change (∑ y : FreshSignals Anc K × I,
    freshScratchFrame j₀ a₀ K x y * encodingFiber (freshSignalsZero a₀ K) y i) = _
  simp [encodingFiber_apply, freshScratchFrame]

omit [Fintype F] [Fintype J] in

/-- The final fresh dynamic frame equals the computational workspace frame at the clean
auxiliary label. -/
theorem dynamicFreshFinalFrame_computational (f₀ : F) (j₀ : J) (a₀ : Anc) (K : ℕ) :
    dynamicFreshFinalFrame (I := I) f₀ j₀ a₀ K =
      computationalWorkspaceFrame (dynamicFreshFinalEquiv F Anc J I K)
        (dynamicFreshCleanAux f₀ j₀ a₀ K) := by
  ext ⟨b,⟨⟨⟨tay,sig⟩,act,p,c⟩,f⟩,j,a,i⟩ k
  simp only [dynamicFreshFinalFrame, reindexFrame, Matrix.submatrix_apply,
    dynamicTimeWorkspaceEquiv, dynamicOriginalWorkspaceEquiv, dynamicFreshWorkspaceEquiv,
    Equiv.coe_fn_mk, id_eq, tagFrame, Matrix.of_apply, freshWordFrame_entry,
    computationalWorkspaceFrame, dynamicFreshFinalEquiv, dynamicFreshCleanAux,
    Matrix.one_apply, Prod.mk.injEq]
  by_cases hb : b = false <;> by_cases hf : f = f₀ <;> by_cases ht : tay = taylorEmptyLabel J K <;>
    by_cases hs : sig = freshSignalsZero (false,false,a₀) K <;> by_cases ha : act = false <;>
    by_cases hp : p = false <;> by_cases hc : c = false <;> by_cases hj : j = j₀ <;>
    by_cases haa : a = a₀ <;> by_cases hi : i = k <;>
    simp_all

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
