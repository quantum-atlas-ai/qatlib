/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ControlledAccessBridge
import Qatlib.Papers.Cbmd26.Algorithms.SeparateOracleBridge
import Qatlib.Papers.Cbmd26.Algorithms.OriginalAStaticConsumer

/-!
# Compiling dynamic samples to original oracles

Extends coherent sample and padding evaluation to label-dependent original oracle families. The
construction `dynamicOriginalWord` compiles controlled padded first-order samples using register
reindexing and clean Boolean masks, preserving the encoded matrix and tracking the resource
overhead. These results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `dynamicSampleWord_evaluate`: implements the controlled padded sample family.
* `dynamicOriginalWord_blockEncoding`: transfers encodings to original-oracle words with exact
  costs.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace CBMD
open Matrix
open scoped Matrix.Norms.L2Operator

variable {J W I T : Type} [Fintype J] [DecidableEq J] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype T] [DecidableEq T]

/-- For a label-dependent oracle family, the coherent coefficient word evaluates to the selected
coefficient LCU unitaries of each oracle-adjoint pair. -/
theorem coherentCoefficientAdjointWord_evaluate_family (d : J → Bool → ℂ) (b₀ : Bool)
    (U : J → Matrix W W ℂ) :
    evaluate (select (fun j => controlOracle (U j)))
        (coherentCoefficientAdjointWord d b₀) =
      select (fun j => coefficientLCUUnitary (d j) (oracleAdjointPair (U j)) b₀) := by
  have hmiddle : evaluate (select (fun j => controlOracle (U j)))
      (spectatorLiftWord J
        (compileSelected ([.backward] : List (AdjointStep W)) [.forward])) =
      select (fun j => select (oracleAdjointPair (U j))) := by
    rw [evaluate_spectatorLiftWord_select]
    simp only [evaluate_compileSelected, evaluate, instructionMatrix, Matrix.mul_one]
    congr 1
  simp only [coherentCoefficientAdjointWord, evaluate_append, evaluate,
    instructionMatrix, Matrix.mul_one, hmiddle, parallel_select_mul]
  congr 1
  funext j
  have hphase : coefficientLabelPhase (d j) * select (oracleAdjointPair (U j)) =
      select (phaseAbsorbed (d j) (oracleAdjointPair (U j))) := by
    rw [coefficientLabelPhase, parallel_select_mul]
    congr 1
    funext b
    simp [phaseAbsorbed]
  rw [Matrix.mul_assoc _ (coefficientLabelPhase (d j)) (select (oracleAdjointPair (U j))), hphase]
  rfl

/-- For a selected oracle family, inserting the padding register lifts every branch evaluation
by a Boolean spectator. -/
theorem insertPaddingWord_evaluate_family (O : J → Matrix W W ℂ)
    (cs : List (AdjointStep (J × W))) (V : J → Matrix W W ℂ)
    (he : evaluate (select O) cs = select V) :
    evaluate (select (fun j => parallelOracle (J := Bool) (O j)))
        (insertPaddingWord cs) = select (fun j => parallelOracle (J := Bool) (V j)) := by
  have ho : select (fun j => parallelOracle (J := Bool) (O j)) =
      (parallelOracle (J := Bool) (select O)).submatrix
        (controlSpectatorEquiv J W).symm (controlSpectatorEquiv J W).symm := by
    ext ⟨j, b, i⟩ ⟨k, c, l⟩
    by_cases hj : j = k <;> by_cases hb : b = c <;>
      simp [parallelOracle, select, controlSpectatorEquiv, hj, hb]
  rw [ho, insertPaddingWord, reindexAdjointWord_evaluate, spectatorLiftWord_evaluate, he]
  ext ⟨j, b, i⟩ ⟨k, c, l⟩
  by_cases hj : j = k <;> by_cases hb : b = c <;>
    simp [parallelOracle, select, controlSpectatorEquiv, hj, hb]

/-- For a selected oracle family, coherent padding evaluates branchwise to the padding
coefficient LCU unitary. -/
theorem coherentPaddingWord_evaluate_family (r : J → ℝ) (O : J → Matrix W W ℂ)
    (cs : List (AdjointStep (J × W))) (V : J → Matrix W W ℂ)
    (he : evaluate (select O) cs = select V) :
    evaluate (select (fun j => parallelOracle (J := Bool) (O j)))
        (coherentPaddingWord r cs) =
      select (fun j => coefficientLCUUnitary (paddingCoefficients (r j))
        (fun _ : Bool => V j) false) := by
  have hphase : ∀ j, coefficientLabelPhase (paddingCoefficients (r j)) *
      parallelOracle (J := Bool) (V j) =
      select (phaseAbsorbed (paddingCoefficients (r j)) (fun _ : Bool => V j)) := by
    intro j
    rw [coefficientLabelPhase, parallelOracle, parallel_select_mul]
    congr 1
    funext b
    simp [phaseAbsorbed]
  simp only [coherentPaddingWord, evaluate_append, evaluate, instructionMatrix,
    Matrix.mul_one, insertPaddingWord_evaluate_family O cs V he, parallel_select_mul]
  congr 1
  funext j
  rw [Matrix.mul_assoc _ (coefficientLabelPhase _) (parallelOracle _), hphase]
  rfl

/-- Against a selected family of controlled original oracles, the padded first-order word
evaluates to the selected padded first-order unitaries. -/
theorem paddedFirstOrderInputWord_evaluate_family (α Λ : ℝ) (s : J → ℝ)
    (U : J → Matrix W W ℂ) :
    evaluate (select (fun j => parallelOracle (J := Bool) (controlOracle (U j))))
        (paddedFirstOrderInputWord α Λ s) =
      select (fun j => paddedFirstOrderInputUnitary (U j) α Λ (s j)) :=
  coherentPaddingWord_evaluate_family _ _ _ _
    (coherentCoefficientAdjointWord_evaluate_family _ _ U)

/-- Abbreviates the controlled sample workspace with label, padding, and original workspace
registers. -/
abbrev DynamicSampleWorkspace (J W : Type) := Bool × (J × (Bool × (Bool × W)))
/-- Abbreviates the spectator label together with the three Boolean labels used by the
original-oracle compilation. -/
abbrev DynamicOriginalLabels (T : Type) := T × (Bool × (Bool × Bool))

/-- Defines the controlled selected original-oracle family with an additional Boolean spectator
register. -/
def dynamicSampleQuery (U : J → Matrix W W ℂ) :
    Matrix (DynamicSampleWorkspace J W) (DynamicSampleWorkspace J W) ℂ :=
  controlOracle (select (fun j => parallelOracle (J := Bool) (controlOracle (U j))))

/-- Compiles the padded first-order input word into a controlled sample word. -/
def dynamicSampleWord (α Λ : ℝ) (s : J → ℝ) :
    List (AdjointStep (DynamicSampleWorkspace J W)) :=
  compileControlled (paddedFirstOrderInputWord α Λ s)

/-- The dynamic sample word evaluates to the controlled selected family of padded first-order
input unitaries. -/
theorem dynamicSampleWord_evaluate (α Λ : ℝ) (s : J → ℝ) (U : J → Matrix W W ℂ) :
    evaluate (dynamicSampleQuery U) (dynamicSampleWord α Λ s) =
      controlOracle (select (fun j => paddedFirstOrderInputUnitary (U j) α Λ (s j))) := by
  rw [dynamicSampleQuery, dynamicSampleWord, evaluate_compileControlled,
    paddedFirstOrderInputWord_evaluate_family]

omit [Fintype J] [Fintype W] in

/-- The dynamic sample word uses exactly two queries and eight gates. -/
theorem dynamicSampleWord_cost (α Λ : ℝ) (s : J → ℝ) :
    adjointQueryCount (dynamicSampleWord (W := W) α Λ s) = 2 ∧
    adjointGateCount (dynamicSampleWord (W := W) α Λ s) = 8 := by
  simpa only [dynamicSampleWord, queryCount_compileControlled, gateCount_compileControlled]
    using! paddedFirstOrderInputWord_cost (W := W) α Λ s

/-- Positive normalizations and the pointwise sample bound make the dynamic sample word well
formed. -/
theorem dynamicSampleWord_wellFormed (α Λ : ℝ) (s : J → ℝ)
    (hα : 0 < α) (hΛ : 0 < Λ) (hbound : ∀ j, α * Real.sqrt (1 + (s j)^2) ≤ Λ) :
    WellFormedAdjointCircuit (dynamicSampleWord (W := W) α Λ s) :=
  compileControlled_wellFormed (paddedFirstOrderInputWord_wellFormed α Λ s hα hΛ hbound)

/-- Rearranges the original-oracle labels and selected workspace into the spectator and dynamic
sample layout. -/
def dynamicOriginalWorkspaceEquiv (T J W : Type) :
    DynamicOriginalLabels T × (J × W) ≃ T × DynamicSampleWorkspace J W where
  toFun := fun ⟨⟨t,b,p,c⟩,j,w⟩ => (t,b,j,p,c,w)
  invFun := fun ⟨t,b,j,p,c,w⟩ => ((t,b,p,c),j,w)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Enables the original oracle exactly when both the outer sample control and inner oracle
control are true. -/
def dynamicOriginalMask (l : DynamicOriginalLabels T) : Bool := l.2.1 && l.2.2.2

omit [Fintype J] [Fintype W] [Fintype T] in

/-- Reindexing the spectator-lifted dynamic sample query gives the selected original oracle
masked by `dynamicOriginalMask`. -/
theorem dynamicSampleQuery_reindex (U : J → Matrix W W ℂ) :
    (parallelOracle (J := T) (dynamicSampleQuery U)).submatrix
      (dynamicOriginalWorkspaceEquiv T J W) (dynamicOriginalWorkspaceEquiv T J W) =
    maskedOracle dynamicOriginalMask (select U) := by
  ext ⟨⟨t,b,p,c⟩,j,i⟩ ⟨⟨t',b',p',c'⟩,j',l⟩
  by_cases ht : t = t' <;> by_cases hb : b = b' <;>
    by_cases hp : p = p' <;> by_cases hc : c = c' <;> by_cases hj : j = j' <;>
    simp [dynamicSampleQuery, dynamicOriginalWorkspaceEquiv, dynamicOriginalMask,
      maskedOracle, select, parallelOracle, controlOracle, ht, hb, hp, hc, hj]
  all_goals cases b <;> cases c <;> simp_all [Matrix.one_apply]

/-- Substitutes the controlled sample implementation into a word, reindexes its registers, and
compiles the resulting mask with a clean Boolean control. -/
def dynamicOriginalWord (α Λ : ℝ) (s : J → ℝ)
    (cs : List (AdjointStep (T × DynamicSampleWorkspace J W))) :
    List (AdjointStep (Bool × (DynamicOriginalLabels T × (J × W)))) :=
  cleanMaskedWord dynamicOriginalMask
    (reindexAdjointWord (dynamicOriginalWorkspaceEquiv T J W)
      (substituteAdjointCircuit (spectatorLiftWord T (dynamicSampleWord α Λ s)) cs))

/-- Original-oracle compilation doubles the query count and adds twelve gates per original
query. -/
theorem dynamicOriginalWord_cost (α Λ : ℝ) (s : J → ℝ)
    (cs : List (AdjointStep (T × DynamicSampleWorkspace J W))) :
    adjointQueryCount (dynamicOriginalWord α Λ s cs) = 2 * adjointQueryCount cs ∧
    adjointGateCount (dynamicOriginalWord α Λ s cs) =
      adjointGateCount cs + 12 * adjointQueryCount cs := by
  obtain ⟨_,hq,hg,_⟩ := substitute_adjoint_evaluate_cost
    (1 : Matrix (T × DynamicSampleWorkspace J W) (T × DynamicSampleWorkspace J W) ℂ)
    (spectatorLiftWord T (dynamicSampleWord α Λ s)) cs
  rw [(spectatorLiftWord_cost _ _).1, (dynamicSampleWord_cost α Λ s).1] at hq
  rw [(spectatorLiftWord_cost _ _).2, (dynamicSampleWord_cost α Λ s).2] at hg
  obtain ⟨hqc,hgc⟩ := cleanMaskedWord_cost dynamicOriginalMask
    (reindexAdjointWord (dynamicOriginalWorkspaceEquiv T J W)
      (substituteAdjointCircuit (spectatorLiftWord T (dynamicSampleWord α Λ s)) cs))
  rw [(reindexAdjointWord_cost _ _).1, hq] at hqc
  rw [(reindexAdjointWord_cost _ _).1, (reindexAdjointWord_cost _ _).2, hq, hg] at hgc
  exact ⟨hqc.trans (by omega), hgc.trans (by omega)⟩

/-- Under the stated unitary and normalization bounds, original-oracle compilation preserves the
encoded matrix, scale, and error on the transported frame, doubling queries and adding
twelve gates per query. -/
theorem dynamicOriginalWord_blockEncoding (α Λ : ℝ) (s : J → ℝ)
    (hα : 0 < α) (hΛ : 0 < Λ) (hbound : ∀ j, α * Real.sqrt (1 + (s j)^2) ≤ Λ)
    (U : J → Matrix W W ℂ) (hU : ∀ j, U j ∈ Matrix.unitaryGroup W ℂ)
    (cs : List (AdjointStep (T × DynamicSampleWorkspace J W)))
    (hcs : WellFormedAdjointCircuit cs)
    (A : Matrix I I ℂ) (F : Matrix (T × DynamicSampleWorkspace J W) I ℂ) (β ε : ℝ)
    (henc : BlockEncoding A
      (evaluate (parallelOracle (J := T)
        (controlOracle (select (fun j => paddedFirstOrderInputUnitary (U j) α Λ (s j))))) cs)
      F F β ε) :
    WellFormedAdjointCircuit (dynamicOriginalWord α Λ s cs) ∧
    BlockEncoding A
      (evaluate (controlOracle (parallelOracle (J := DynamicOriginalLabels T) (select U)))
        (dynamicOriginalWord α Λ s cs))
      (tagFrame false (reindexFrame (dynamicOriginalWorkspaceEquiv T J W) F))
      (tagFrame false (reindexFrame (dynamicOriginalWorkspaceEquiv T J W) F)) β ε ∧
    adjointQueryCount (dynamicOriginalWord α Λ s cs) = 2 * adjointQueryCount cs ∧
    adjointGateCount (dynamicOriginalWord α Λ s cs) =
      adjointGateCount cs + 12 * adjointQueryCount cs := by
  have he := (substitute_adjoint_evaluate_cost
    (parallelOracle (J := T) (dynamicSampleQuery U))
    (spectatorLiftWord T (dynamicSampleWord α Λ s)) cs).1
  rw [spectatorLiftWord_evaluate, dynamicSampleWord_evaluate] at he
  rw [← he] at henc
  have hr := reindexWorkspace_blockEncoding (dynamicOriginalWorkspaceEquiv T J W)
    _ _ _ _ _ henc
  rw [← reindexAdjointWord_evaluate, dynamicSampleQuery_reindex] at hr
  have hw := (substitute_adjoint_evaluate_cost
    (parallelOracle (J := T) (dynamicSampleQuery U))
    (spectatorLiftWord T (dynamicSampleWord α Λ s)) cs).2.2.2
    (spectatorLiftWord_wellFormed T (dynamicSampleWord_wellFormed α Λ s hα hΛ hbound)) hcs
  have hc := cleanMaskedWord_blockEncoding dynamicOriginalMask (select U)
    (select_unitary _ hU) _ (reindexAdjointWord_wellFormed _ hw) _ _ _ _ hr
  exact ⟨hc.1, hc.2.1, dynamicOriginalWord_cost α Λ s cs⟩

omit [Fintype J] [DecidableEq J] in

/-- Exact encodings of the Hermitian-component family `L + iH` yield exact projected encodings
of `(H + sL) / Λ` using the padded first-order sample unitaries. -/
theorem dynamic_original_sample_encodings (L H : J → Matrix I I ℂ)
    (hL : ∀ j, (L j).IsHermitian) (hH : ∀ j, (H j).IsHermitian)
    (U : J → Matrix W W ℂ) (R : Matrix W I ℂ) (α Λ : ℝ) (s : J → ℝ)
    (henc : ∀ j, BlockEncoding (L j + Complex.I • H j) (U j) R R α 0)
    (hbound : ∀ j, α * Real.sqrt (1 + (s j)^2) ≤ Λ) :
    ∀ j, ProjectedUnitaryEncoding (Λ⁻¹ • (H j + (s j : ℂ) • L j))
      (paddedFirstOrderInputUnitary (U j) α Λ (s j))
      (tagFrame false (tagFrame false R)) (tagFrame false (tagFrame false R)) := by
  intro j
  apply exact_blockEncoding_normalized
  simpa using! commonNormalization_blockEncoding _ _ _ _ Λ _
    (original_oracle_first_order_blockEncoding (L j) (H j) (hL j) (hH j)
      (U j) R α 0 (s j) (henc j)) (hbound j)

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
