/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws

/-!
# Finite phase synthesis and postselection examples

This module verifies the default finite-synthesis packets for the identity and linear responses
and transfers them to projected unitary encodings. A concrete Hadamard example connects the
synthesized packets to postselection probabilities, conditional output states, and exact gate
and query counts. Background and related constructions are discussed in [GilyenSuLowWiebe2019].

## Main statements

* `default_word_encodings`: encodings obtained from the two default phase packets.
* `finite_phase_default_and_kernel_consumers`: combines synthesis and encoding guarantees.
* `finite_phase_hadamard_actual_born_consumer`: a concrete postselection and resource
  calculation.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.PhaseGeometry.Phase
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix Polynomial
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The default phase packet `⟨gone, [gone]⟩` has zero score for the linear target with rational
coefficients `[0, 1]` at degree one. -/
theorem default_X_score : (scoreData ([0,1]:List ℚ) 1 ⟨gone,[gone]⟩).1.1 = 0 := by
  norm_num [scoreData,responseData,gscale,gaddList,gsubList,gshift,gconj,gzero,gone,gmul,gadd,gsub,scoreLoop]

/-- The default phase packet `⟨gone, []⟩` has zero score for the constant target with rational
coefficients `[1]` at degree zero. -/
theorem default_one_score : (scoreData ([1]:List ℚ) 0 ⟨gone,[]⟩).1.1 = 0 := by
  norm_num [scoreData,responseData,gzero,gone,scoreLoop]

/-- For every rational tolerance, finite phase synthesis of the linear target returns the
default packet after testing one candidate and making no backend calls. -/
theorem synthesis_default_X (eps : ℚ) :
    (finitePhaseSynthesis ([0,1]:List ℚ) 1 eps).value = some (⟨gone,[gone]⟩:PhaseData) ∧
    (finitePhaseSynthesis ([0,1]:List ℚ) 1 eps).backendCalls = 0 ∧
    (finitePhaseSynthesis ([0,1]:List ℚ) 1 eps).tested = 1 := by
  have hs : (scoreData ([0,1]:List ℚ) 1 ⟨gone,[gone]⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps := by
    rw [default_X_score]; positivity
  simp only [finitePhaseSynthesis,show List.replicate 1 gone = [gone] from rfl,hs,ite_true]
  simp

/-- For every rational tolerance, finite phase synthesis of the constant-one target returns the
default packet and makes no backend calls. -/
theorem synthesis_default_one (eps : ℚ) :
    (finitePhaseSynthesis ([1]:List ℚ) 0 eps).value = some (⟨gone,[]⟩:PhaseData) ∧
    (finitePhaseSynthesis ([1]:List ℚ) 0 eps).backendCalls = 0 := by
  have hs : (scoreData ([1]:List ℚ) 0 ⟨gone,[]⟩).1.1 ≤ (1/2:ℚ)^phaseToleranceBits eps := by
    rw [default_one_score]; positivity
  simp only [finitePhaseSynthesis,List.replicate_zero,hs,ite_true]
  simp

/-- The default linear and constant-one phase packets yield projected unitary encodings of `A`
and the identity, respectively, in the corresponding averaged frames. -/
theorem default_word_encodings {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (henc : ProjectedUnitaryEncoding A U L R) :
    ProjectedUnitaryEncoding A
      (evaluate (parallelOracle U) (computedPhaseWord (rangeProjector R) (rangeProjector L) ⟨gone,[gone]⟩))
      (averageFrame L) (averageFrame R) ∧
    ProjectedUnitaryEncoding (1:Matrix I I ℂ)
      (evaluate (parallelOracle Uᴴ) (computedPhaseWord (rangeProjector L) (rangeProjector R) ⟨gone,[]⟩))
      (averageFrame R) (averageFrame R) := by
  have hb : IsPhase (1:ℂ) := by simp [IsPhase]
  have hlist : ∀ z ∈ ([1]:List ℂ),IsPhase z := by simpa using hb
  have hX := realPartQSVT_odd_singularEncoding henc hb [1] hlist (by decide)
  have hOne := realPartQSVT_even_right_singularEncoding henc hb [] (by simp) (by decide)
  constructor
  · simpa [computedPhaseWord,complex_gone,evaluate_compileRealPartQSVT,responseP_singleton,oddSingularTransform_id] using hX
  · simpa [computedPhaseWord,complex_gone,evaluate_compileRealPartQSVT,rightSingularTransform_const] using hOne

/-- Combines the positive-tolerance synthesis guarantees for the default linear and constant-one
packets with their projected unitary encoding guarantees. -/
theorem finite_phase_default_and_kernel_consumers :
  (∀ (eps : ℚ), 0<eps → (finitePhaseSynthesis ([0,1]:List ℚ) 1 eps).value =
    some (⟨gone,[gone]⟩ : PhaseData) ∧ (finitePhaseSynthesis ([0,1]:List ℚ) 1 eps).backendCalls=0 ∧
    (finitePhaseSynthesis ([0,1]:List ℚ) 1 eps).tested=1) ∧
  (∀ (eps : ℚ), 0<eps → (finitePhaseSynthesis ([1]:List ℚ) 0 eps).value =
    some (⟨gone,[]⟩ : PhaseData) ∧ (finitePhaseSynthesis ([1]:List ℚ) 0 eps).backendCalls=0) ∧
  (∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
      (L : Matrix H O ℂ) (R : Matrix H I ℂ), ProjectedUnitaryEncoding A U L R →
    ProjectedUnitaryEncoding A
      (evaluate (parallelOracle U) (computedPhaseWord (rangeProjector R) (rangeProjector L) ⟨gone,[gone]⟩))
      (averageFrame L) (averageFrame R) ∧
    ProjectedUnitaryEncoding (1:Matrix I I ℂ)
      (evaluate (parallelOracle Uᴴ) (computedPhaseWord (rangeProjector L) (rangeProjector R) ⟨gone,[]⟩))
      (averageFrame R) (averageFrame R))
 := by
  refine ⟨?_,?_,?_⟩
  · intro eps heps; exact synthesis_default_X eps
  · intro eps heps; exact synthesis_default_one eps
  · intro H I O _ _ _ _ _ _ A U L R henc
    exact default_word_encodings A U L R henc

/-- The isometric frame embedding the one-dimensional `Unit` register into the `false`
coordinate of the Boolean register. -/
noncomputable def enumExampleFrame : Matrix Bool Unit ℂ := Matrix.of (fun b _ => if b then 0 else 1)

/-- The example frame `enumExampleFrame` is an isometry. -/
theorem enumExampleFrame_isometry : IsIsometry enumExampleFrame := by
  change enumExampleFrameᴴ*enumExampleFrame = 1
  ext i j
  cases i; cases j
  norm_num [enumExampleFrame,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_bool]

/-- Compression by `enumExampleFrame` extracts the `false, false` entry of a Boolean-indexed
matrix as a one-dimensional matrix. -/
theorem enumExampleFrame_corner (U : Matrix Bool Bool ℂ) :
    compress enumExampleFrame U enumExampleFrame = Matrix.of (fun _ _ : Unit => U false false) := by
  ext i j
  cases i; cases j
  simp [enumExampleFrame,compress,Matrix.mul_apply,Matrix.conjTranspose_apply]

/-- In the example frame, the Hadamard matrix encodes the scalar 1/√2 and `PauliX` encodes the
zero matrix. -/
theorem enumExampleFrame_encodings :
    ProjectedUnitaryEncoding (Matrix.of (fun _ _ : Unit => (Real.sqrt 2:ℂ)⁻¹)) Hadamard enumExampleFrame enumExampleFrame ∧
    ProjectedUnitaryEncoding (0:Matrix Unit Unit ℂ) PauliX enumExampleFrame enumExampleFrame := by
  refine ⟨⟨hadamard_unitary,enumExampleFrame_isometry,enumExampleFrame_isometry,?_⟩,
    ⟨pauliX_unitary,enumExampleFrame_isometry,enumExampleFrame_isometry,?_⟩⟩
  · rw [enumExampleFrame_corner]
    ext i j; cases i; cases j; norm_num [Hadamard]
  · rw [enumExampleFrame_corner]
    ext i j
    cases i; cases j
    simp [PauliX,permMatrix]

/-- Conditioning the one-dimensional vector scaled by 1/√2 yields the normalized basis state
`Ket ()`. -/
theorem enum_scalar_conditional : ConditionalState ((Real.sqrt 2:ℂ)⁻¹ • (Ket ():QState Unit)) = some (Ket ()) := by
  have hsR : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsC : (Real.sqrt 2:ℂ) ≠ 0 := by exact_mod_cast hsR.ne'
  have hv : ((Real.sqrt 2:ℂ)⁻¹ • (Ket ():QState Unit)) ≠ 0 := by
    intro he
    have hz := congrFun he ()
    simp only [Pi.smul_apply,Ket,ite_true,smul_eq_mul,mul_one,Pi.zero_apply] at hz
    exact inv_ne_zero hsC hz
  have hn : ‖stateVector ((Real.sqrt 2:ℂ)⁻¹ • (Ket ():QState Unit))‖ = (Real.sqrt 2)⁻¹ := by
    change ‖(Real.sqrt 2:ℂ)⁻¹ • stateVector (Ket ())‖ = _
    rw [norm_smul,(normalized_iff_stateVector_norm (Ket ())).mp (normalized_ket ()),mul_one,
      norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hsR]
  rw [conditionalState_eq_some_of_ne_zero hv,postMeasure_univ_eq_smul,hn,inv_inv]
  congr 1
  ext i
  cases i
  simp [Pi.smul_apply,Ket,Complex.real_smul,smul_eq_mul,hsC]

/-- Provides synthesized packets at tolerance 1/8 whose Hadamard consumer succeeds with
probability 1/2 and returns `Ket ()`, using one query and two fixed gates. The
constant-response consumer for `PauliX` succeeds with probability one using no queries and
one fixed gate. -/
theorem finite_phase_hadamard_actual_born_consumer : ∃ (data data0 : PhaseData),
  (finitePhaseSynthesis ([0,1]:List ℚ) 1 (1/8)).value = some data ∧
  (finitePhaseSynthesis ([1]:List ℚ) 0 (1/8)).value = some data0 ∧
  let F := enumExampleFrame
  let L := averageFrame F
  let cs := computedPhaseWord (rangeProjector F) (rangeProjector F) data
  let cs0 := computedPhaseWord (rangeProjector F) (rangeProjector F) data0
  ProjectedUnitaryEncoding (Matrix.of (fun _ _ : Unit => (Real.sqrt 2:ℂ)⁻¹)) Hadamard F F ∧
  postselectionProbability (evaluate (parallelOracle Hadamard) cs) L L (Ket ()) = 1/2 ∧
  postselectionOutput (evaluate (parallelOracle Hadamard) cs) L L (Ket ()) = some (Ket ()) ∧
  adjointQueryCount cs = 1 ∧ adjointGateCount cs = 2 ∧
  ProjectedUnitaryEncoding (0 : Matrix Unit Unit ℂ) PauliX F F ∧
  postselectionProbability (evaluate (parallelOracle PauliX) cs0) L L (Ket ()) = 1 ∧
  adjointQueryCount cs0 = 0 ∧ adjointGateCount cs0 = 1

 := by
  let data : PhaseData := ⟨gone,[gone]⟩
  let data0 : PhaseData := ⟨gone,[]⟩
  let F := enumExampleFrame
  let L := averageFrame F
  let cs := computedPhaseWord (rangeProjector F) (rangeProjector F) data
  let cs0 := computedPhaseWord (rangeProjector F) (rangeProjector F) data0
  have hH := enumExampleFrame_encodings.1
  have hX := enumExampleFrame_encodings.2
  have henc := (default_word_encodings _ Hadamard F F hH).1
  have henc0 := (default_word_encodings _ PauliX F F hX).2
  have hPX : PauliXᴴ = PauliX := permMatrix_conjTranspose Bool.not_not
  rw [hPX] at henc0
  have hc := counts_compileRealPartQSVT (rangeProjector F) (rangeProjector F) (1:ℂ) ([1]:List ℂ)
  have hc0 := counts_compileRealPartQSVT (rangeProjector F) (rangeProjector F) (1:ℂ) ([]:List ℂ)
  have hv : postselectionVector (evaluate (parallelOracle Hadamard) cs) L L (Ket ()) =
      (Real.sqrt 2:ℂ)⁻¹ • (Ket ():QState Unit) := by
    unfold postselectionVector
    rw [henc.encoded]
    ext i
    cases i
    simp [Matrix.mulVec,dotProduct,Ket]
  refine ⟨data,data0,(synthesis_default_X (1/8)).1,(synthesis_default_one (1/8)).1,?_⟩
  (try dsimp only)
  refine ⟨hH,?_,?_,by simpa [cs,data,computedPhaseWord] using hc.1,
    by simpa [cs,data,computedPhaseWord] using hc.2,hX,?_,
    by simpa [cs0,data0,computedPhaseWord] using hc0.1,by simpa [cs0,data0,computedPhaseWord] using hc0.2⟩
  · rw [postselectionProbability_eq_norm_sq henc.left_isometry, hv,stateVector_norm_sq]
    norm_num [MeasureProb,BornProb,Ket,Pi.smul_apply,smul_eq_mul,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg (2:ℝ)),inv_pow]
  · rw [postselectionOutput,hv,enum_scalar_conditional]
  · rw [postselectionProbability_eq_norm_sq henc0.left_isometry]
    unfold postselectionVector
    rw [henc0.encoded,Matrix.one_mulVec,(normalized_iff_stateVector_norm (Ket ())).mp (normalized_ket ())]
    norm_num

end Qatlib.Concepts.QspSimulation.WordModel
