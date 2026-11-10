/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.ComputedPhaseQSVT
import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation
import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitReciprocalCutoff
import Qatlib.Concepts.QsvtCore.LinearSystems.PseudoinverseState
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitNoisyQSVTSolver
import Qatlib.Concepts.BlockEncoding.EncodingCore.AncillaErrorLaws
set_option warningAsError false

open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix Polynomial
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator

def nativeReciprocalFactor : ℕ → List ℚ
  | 0 => []
  | n+1 => ratAddList [1] (ratMulList [1,0,-1] (nativeReciprocalFactor n))
def nativeReciprocalCoefficients (n : ℕ) : List ℚ := 0::nativeReciprocalFactor n
def nativeScaleBits (n : ℕ) := Nat.clog 2 (8*max 1 n)
def nativeInverseScale (n : ℕ) : ℚ := (rationalSqrtBracket ((1:ℚ)/(n:ℚ)) (nativeScaleBits n)).1/2
def nativeInverseCoefficients (n : ℕ) : List ℚ :=
  (nativeReciprocalCoefficients n).map (fun x=>nativeInverseScale n*x)
def nativeInverseTolerance (n k : ℕ) : ℚ := nativeInverseScale n*(1/2:ℚ)^(k+2)
noncomputable def coordinatePhaseFrame {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) := encodingFiber (I := H) false*F
noncomputable def fullComputedPhaseWord {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (data : PhaseData) : List (AdjointStep (Bool × H)) :=
  [.gate (TensorGate Hadamard (1 : Matrix H H ℂ))] ++ computedPhaseWord P Q data ++
    [.gate (TensorGate Hadamard (1 : Matrix H H ℂ))]
noncomputable def finiteInverseWord {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (kappa k : ℕ) : List (AdjointStep (Bool × H)) :=
  let n := explicitInverseCutoff kappa (k+2)
  let result :=
      finitePhaseSynthesis (nativeInverseCoefficients n) (2*n-1) (nativeInverseTolerance n k)
  match result.value with
    | none => []
    | some data => adjointCircuit (fullComputedPhaseWord (rangeProjector R) (rangeProjector L) data)

theorem nativeReciprocalFactor_semantics (n : ℕ) :
    realTarget (nativeReciprocalFactor n) = ∑ i ∈ Finset.range n,(1-X^2:Polynomial ℝ)^i := by
  induction n with
  | zero => simp [nativeReciprocalFactor]
  | succ n ih =>
    rw [nativeReciprocalFactor,realTarget_add,realTarget_mul,ih,Finset.sum_range_succ']
    have hp : realTarget ([1,0,-1]:List ℚ) = 1-X^2 := by simp [realTarget_cons]; ring
    have h1 : realTarget ([1]:List ℚ) = 1 := by simp [realTarget_cons]
    rw [hp,h1,Finset.mul_sum]
    simp only [pow_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring

theorem nativeReciprocalCoefficients_semantics (n : ℕ) :
    realTarget (nativeReciprocalCoefficients n) = reciprocalPolynomial n := by
  rw [nativeReciprocalCoefficients,realTarget_cons,nativeReciprocalFactor_semantics,reciprocalPolynomial_eq_sum]
  simp

theorem nativeInverseCoefficients_semantics (n : ℕ) :
    realTarget (nativeInverseCoefficients n) = C (nativeInverseScale n:ℝ)*reciprocalPolynomial n := by
  rw [nativeInverseCoefficients,realTarget_scale,nativeReciprocalCoefficients_semantics]

theorem nativeInverseScale_bounds (n : ℕ) (hn : 0 < n) :
    0 < nativeInverseScale n ∧ 1/(4*Real.sqrt (n:ℝ)) ≤ (nativeInverseScale n:ℝ) ∧
    (nativeInverseScale n:ℝ) ≤ 1/(2*Real.sqrt (n:ℝ)) ∧
    (rationalSqrtBracket ((1:ℚ)/(n:ℚ)) (nativeScaleBits n)).2.2 = nativeScaleBits n := by
  have hnQ : (0:ℚ) < n := by exact_mod_cast hn
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hq : (0:ℚ) ≤ 1/(n:ℚ) := by positivity
  have hq1 : (1:ℚ)/(n:ℚ) ≤ 1 := (div_le_one hnQ).mpr (by exact_mod_cast hn)
  obtain ⟨hL,hLU,hU,hLs,hUs,hw,hcount,herror⟩ :=
    rational_sqrt_bracket_actual_interval_and_comparisons ((1:ℚ)/(n:ℚ)) (nativeScaleBits n) hq hq1
  have hs : (0:ℝ) < Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr hnR
  have hsquare := Real.sq_sqrt hnR.le
  have hsn : Real.sqrt (n:ℝ) ≤ (n:ℝ) := by nlinarith [Real.sqrt_nonneg (n:ℝ)]
  have hroot : Real.sqrt (((1:ℚ)/(n:ℚ):ℚ):ℝ) = 1/Real.sqrt (n:ℝ) := by
    simp only [Rat.cast_div,Rat.cast_one,Rat.cast_natCast]
    rw [Real.sqrt_div (by norm_num : (0:ℝ) ≤ 1),Real.sqrt_one]
  rw [hroot] at herror
  have hpower : 8*n ≤ 2^nativeScaleBits n := by
    have h := Nat.le_pow_clog (by decide : 1 < 2) (8*max 1 n)
    simpa [nativeScaleBits,max_eq_right (show 1 ≤ n by omega)] using h
  have hpowerR : 8*(n:ℝ) ≤ (2:ℝ)^nativeScaleBits n := by exact_mod_cast hpower
  have hwidth : 1/(2:ℝ)^nativeScaleBits n ≤ 1/(8*(n:ℝ)) :=
      one_div_le_one_div_of_le (by positivity) hpowerR
  have hhalf : 1/(8*(n:ℝ)) ≤ 1/(2*Real.sqrt (n:ℝ)) :=
      one_div_le_one_div_of_le (by positivity) (by nlinarith)
  have hupper : ((rationalSqrtBracket ((1:ℚ)/(n:ℚ)) (nativeScaleBits n)).1:ℝ) ≤ 1/Real.sqrt (n:ℝ) := by
    have hlr : (0:ℝ) ≤ (rationalSqrtBracket ((1:ℚ)/(n:ℚ)) (nativeScaleBits n)).1 := by
      exact_mod_cast hL
    have hsq : (((rationalSqrtBracket ((1:ℚ)/(n:ℚ)) (nativeScaleBits n)).1):ℝ)^2 ≤ 1/(n:ℝ) := by
      have hh := (Rat.cast_le (K:=ℝ)).mpr hLs
      simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_natCast] using hh
    have hqroot : (1/Real.sqrt (n:ℝ))^2 = 1/(n:ℝ) := by rw [div_pow,one_pow,hsquare]
    nlinarith [show (0:ℝ) ≤ 1/Real.sqrt (n:ℝ) by positivity]
  have hlower : 1/(2*Real.sqrt (n:ℝ)) ≤ ((rationalSqrtBracket ((1:ℚ)/(n:ℚ)) (nativeScaleBits n)).1:ℝ) := by
    have hlow := (abs_le.mp herror).1
    have he : 1/Real.sqrt (n:ℝ)-1/(2*Real.sqrt (n:ℝ)) = 1/(2*Real.sqrt (n:ℝ)) := by ring
    have hw := hwidth.trans hhalf
    linarith
  have hc : (nativeInverseScale n:ℝ) = ((rationalSqrtBracket ((1:ℚ)/(n:ℚ)) (nativeScaleBits n)).1:ℝ)/2 := by
    simp [nativeInverseScale]
  have hcL : 1/(4*Real.sqrt (n:ℝ)) ≤ (nativeInverseScale n:ℝ) := by
    calc
      _ = (1/(2*Real.sqrt (n:ℝ)))/2 := by ring
      _ ≤ ((rationalSqrtBracket ((1:ℚ)/(n:ℚ)) (nativeScaleBits n)).1:ℝ)/2 := div_le_div_of_nonneg_right hlower (by norm_num)
      _ = _ := hc.symm
  have hcU : (nativeInverseScale n:ℝ) ≤ 1/(2*Real.sqrt (n:ℝ)) := by
    rw [hc]
    exact (div_le_div_of_nonneg_right hupper (by norm_num)).trans_eq (by ring)
  have hcPos : (0:ℝ) < nativeInverseScale n := lt_of_lt_of_le (by positivity) hcL
  exact ⟨by exact_mod_cast hcPos,hcL,hcU,hcount⟩

theorem native_reciprocal_coefficients_and_scale : ∀ n : ℕ, 0 < n →
  realTarget (nativeReciprocalCoefficients n)=reciprocalPolynomial n ∧
  0 < nativeInverseScale n ∧
  1/(4*Real.sqrt (n:ℝ)) ≤ (nativeInverseScale n:ℝ) ∧
  (nativeInverseScale n:ℝ) ≤ 1/(2*Real.sqrt (n:ℝ)) ∧
  (rationalSqrtBracket ((1:ℚ)/(n:ℚ)) (nativeScaleBits n)).2.2 = nativeScaleBits n ∧
  (realTarget (nativeInverseCoefficients n)).degree ≤ (((2*n-1):ℕ):WithBot ℕ) ∧
  Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2*n-1) (realTarget (nativeInverseCoefficients n)) ∧
  (∀ x ∈ Set.Icc (-1:ℝ) 1, |(realTarget (nativeInverseCoefficients n)).eval x| ≤ 1)
 := by
  intro n hn
  have hs := nativeInverseScale_bounds n hn
  have he := nativeInverseCoefficients_semantics n
  refine ⟨nativeReciprocalCoefficients_semantics n,hs.1,hs.2.1,hs.2.2.1,hs.2.2.2,?_,?_,?_⟩
  · rw [he]
    apply Polynomial.natDegree_le_iff_degree_le.mp
    exact (Polynomial.natDegree_C_mul_le _ _).trans (reciprocalPolynomial_natDegree_le n)
  · have hodd : Odd (2*n-1) := ⟨n-1,by omega⟩
    rw [he]
    unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
    simp [Polynomial.mul_comp,reciprocalPolynomial_comp_neg_X,hodd.neg_one_pow]
  · intro x hx
    rw [he,Polynomial.eval_mul,Polynomial.eval_C,abs_mul,abs_of_pos (show (0:ℝ) < nativeInverseScale n by exact_mod_cast hs.1)]
    have hc := mul_le_mul_of_nonneg_right hs.2.2.1 (Real.sqrt_nonneg (n:ℝ))
    have hproduct : (1/(2*Real.sqrt (n:ℝ)))*Real.sqrt (n:ℝ) = 1/2 := by
      have hpos := Real.sqrt_pos.mpr (show (0:ℝ) < n by exact_mod_cast hn)
      field_simp
    have hbound :=
        mul_le_mul_of_nonneg_left (reciprocalPolynomial_abs_le_sqrt n hx)
        (show (0:ℝ) ≤ nativeInverseScale n by exact_mod_cast hs.1.le)
    rw [hproduct] at hc
    linarith

noncomputable def inverseLabelH {H : Type} [Fintype H] [DecidableEq H] : Matrix (Bool×H) (Bool×H) ℂ :=
  TensorGate Hadamard (1:Matrix H H ℂ)

noncomputable def inverseLabelPhase : ℂ := (1+Complex.I)/(Real.sqrt 2:ℂ)

theorem inverseLabelPhase_unit : star inverseLabelPhase*inverseLabelPhase = 1 := by
  have hs : (Real.sqrt 2:ℂ)^2 = 2 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2))
  have hn : (Real.sqrt 2:ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  unfold inverseLabelPhase
  change (starRingEnd ℂ) ((1+Complex.I)/(Real.sqrt 2:ℂ))*((1+Complex.I)/(Real.sqrt 2:ℂ)) = _
  simp only [map_div₀,map_add,map_one,Complex.conj_I,Complex.conj_ofReal]
  field_simp
  linear_combination -Complex.I_sq - hs

theorem coordinatePhaseFrame_apply {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (F : Matrix H I ℂ) (b : Bool) (h : H) (i : I) :
    coordinatePhaseFrame F (b,h) i = if b = false then F h i else 0 := by
  simp [coordinatePhaseFrame,encodingFiber,Matrix.mul_apply,ite_and]

theorem averageFrame_labelH {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (F : Matrix H I ℂ) : averageFrame F = inverseLabelPhase • (inverseLabelH*coordinatePhaseFrame F) := by
  have hs : (Real.sqrt 2:ℂ)^2 = 2 := by exact_mod_cast (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2))
  have hn : (Real.sqrt 2:ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne'
  ext ⟨b,h⟩ i
  cases b <;>
    simp [averageFrame,prepareLift,realPartAmplitude,inverseLabelH,Matrix.mul_apply,Fintype.sum_prod_type,
      tensorGate_apply,coordinatePhaseFrame_apply,Matrix.one_apply,Matrix.smul_apply,
      inverseLabelPhase,Hadamard]
  all_goals field_simp
  all_goals ring_nf
  all_goals simp only [hs]

theorem fullComputedPhaseWord_compress {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (L : Matrix H O ℂ) (R : Matrix H I ℂ) (U P Q : Matrix H H ℂ) (data : PhaseData) :
    compress (coordinatePhaseFrame L) (evaluate (parallelOracle U) (fullComputedPhaseWord P Q data)) (coordinatePhaseFrame R) =
      compress (averageFrame L) (evaluate (parallelOracle U) (computedPhaseWord P Q data)) (averageFrame R) := by
  have hh : (inverseLabelH (H:=H))ᴴ = inverseLabelH := by
    rw [inverseLabelH,tensorGate_conjTranspose,hadamard_conjTranspose,Matrix.conjTranspose_one]
  have he : evaluate (parallelOracle U) (fullComputedPhaseWord P Q data) =
      inverseLabelH*evaluate (parallelOracle U) (computedPhaseWord P Q data)*inverseLabelH := by
    simp only [fullComputedPhaseWord,evaluate_append,evaluate,instructionMatrix,Matrix.mul_one,inverseLabelH,Matrix.mul_assoc]
  rw [averageFrame_labelH,averageFrame_labelH]
  unfold compress
  rw [Matrix.conjTranspose_smul]
  simp only [Matrix.smul_mul,Matrix.mul_smul,smul_smul,Matrix.conjTranspose_mul,hh]
  have hu : inverseLabelPhase*star inverseLabelPhase = 1 := by
    rw [mul_comm]; exact inverseLabelPhase_unit
  rw [hu,one_smul,he]
  simp only [Matrix.mul_assoc]

theorem coordinatePhaseFrame_isometry {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    {F : Matrix H I ℂ} (hF : IsIsometry F) : IsIsometry (coordinatePhaseFrame F) := by
  have hE := encodingFiber_isIsometry (I:=H) (J:=Bool) false
  change (encodingFiber (I:=H) (J:=Bool) false)ᴴ*encodingFiber false = 1 at hE
  unfold coordinatePhaseFrame IsIsometry
  rw [Matrix.conjTranspose_mul,Matrix.mul_assoc,← Matrix.mul_assoc (encodingFiber (I:=H) false)ᴴ (encodingFiber false) F,
    hE,Matrix.one_mul]
  exact hF

theorem coordinatePhaseFrame_parallel_compress {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (L : Matrix H O ℂ) (R : Matrix H I ℂ) (U : Matrix H H ℂ) :
    compress (coordinatePhaseFrame L) (parallelOracle U) (coordinatePhaseFrame R) = compress L U R := by
  ext i j
  simp [compress,Matrix.mul_apply,Matrix.conjTranspose_apply,Fintype.sum_prod_type,
    coordinatePhaseFrame_apply,parallelOracle,select]

theorem coordinatePhaseFrame_encoding {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) :
    ProjectedUnitaryEncoding A (parallelOracle U) (coordinatePhaseFrame L) (coordinatePhaseFrame R) :=
  ⟨parallelOracle_unitary h.unitary,coordinatePhaseFrame_isometry h.left_isometry,
    coordinatePhaseFrame_isometry h.right_isometry,(coordinatePhaseFrame_parallel_compress L R U).trans h.encoded⟩

theorem fullComputedPhaseWord_wellFormed_counts {H : Type} [Fintype H] [DecidableEq H]
    (P Q : Matrix H H ℂ) (data : PhaseData) (hword : WellFormedAdjointCircuit (computedPhaseWord P Q data)) :
    WellFormedAdjointCircuit (fullComputedPhaseWord P Q data) ∧
    adjointQueryCount (fullComputedPhaseWord P Q data) = data.phases.length ∧
    adjointGateCount (fullComputedPhaseWord P Q data) = data.phases.length+3 := by
  have hh : WellFormedAdjointCircuit ([.gate (inverseLabelH (H:=H))]:List (AdjointStep (Bool×H))) := by
    simp only [WellFormedAdjointCircuit,List.mem_singleton]
    intro c hc
    have he : c = inverseLabelH (H:=H) := AdjointStep.gate.inj hc
    rw [he]
    exact tensorGate_unitary hadamard_unitary (Matrix.unitaryGroup H ℂ).one_mem
  have hc :=
      counts_compileRealPartQSVT P Q (gaussianRatComplex data.base)
      (data.phases.map gaussianRatComplex)
  refine ⟨hh.append (hword.append hh),?_,?_⟩
  · simp [fullComputedPhaseWord,adjointQueryCount_append,adjointQueryCount,computedPhaseWord,hc.1]
  · simp [fullComputedPhaseWord,adjointGateCount_append,adjointGateCount,computedPhaseWord,hc.2]

theorem nativeInverseTolerance_real (n k : ℕ) : (nativeInverseTolerance n k:ℝ) = (nativeInverseScale n:ℝ)*(1/2:ℝ)^(k+2) := by
  simp [nativeInverseTolerance]

theorem fullComputedPhaseWord_block {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (L : Matrix H O ℂ) (R : Matrix H I ℂ) (U P Q : Matrix H H ℂ)
    (data : PhaseData) (B : Matrix O I ℂ) (E : ℝ) (hL : IsIsometry L) (hR : IsIsometry R)
    (hword : WellFormedAdjointCircuit (fullComputedPhaseWord P Q data)) (hU : U ∈ Matrix.unitaryGroup H ℂ)
    (hraw : BlockEncoding B (evaluate (parallelOracle U) (computedPhaseWord P Q data)) (averageFrame L) (averageFrame R) 1 E) :
    BlockEncoding B (evaluate (parallelOracle U) (fullComputedPhaseWord P Q data))
      (coordinatePhaseFrame L) (coordinatePhaseFrame R) 1 E := by
  refine ⟨hword.evaluate_unitary (parallelOracle_unitary hU),coordinatePhaseFrame_isometry hL,
    coordinatePhaseFrame_isometry hR,by norm_num,hraw.error_nonneg,?_⟩
  rw [one_smul,fullComputedPhaseWord_compress]
  simpa only [one_smul] using hraw.error_le

theorem native_inverse_singular_adjoint {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (n : ℕ) :
    (oddSingularTransform A (fun x => (((realTarget (nativeInverseCoefficients n)).eval x:ℝ):ℂ)))ᴴ =
      ((nativeInverseScale n:ℝ):ℂ) • reciprocalMatrixApprox A n := by
  have hf : (fun x : ℝ => (((realTarget (nativeInverseCoefficients n)).eval x:ℝ):ℂ)) =
      fun x : ℝ => (((nativeInverseScale n:ℝ):ℂ)*(complexReciprocalPolynomial n).eval (x:ℂ)) := by
    funext x
    rw [nativeInverseCoefficients_semantics,Polynomial.eval_mul,Polynomial.eval_C,complexReciprocalPolynomial_eval_real,
      Complex.ofReal_mul]
  rw [hf,oddSingularTransform_smul,Matrix.conjTranspose_smul,← reciprocalMatrixApprox_eq_oddSingularTransform]
  simp

theorem computed_full_inverse_actual_encoding_and_cost : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (kappa k : ℕ),
  ProjectedUnitaryEncoding A U L R → 0 < kappa →
  (∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
    (kappa:ℝ)⁻¹ ≤ matrixSingularValues A i) →
  let n := explicitInverseCutoff kappa (k+2)
  let c := (nativeInverseScale n:ℝ)
  let eps := nativeInverseTolerance n k
  let result := finitePhaseSynthesis (nativeInverseCoefficients n) (2*n-1) eps
  let cs := finiteInverseWord L R kappa k
  (∃ data : PhaseData, result.value=some data ∧ data.phases.length=2*n-1) ∧
  WellFormedAdjointCircuit cs ∧
  BlockEncoding ((c:ℂ) • matrixPseudoinverse A) (evaluate (parallelOracle U) cs)
    (coordinatePhaseFrame R) (coordinatePhaseFrame L) 1 ((c/2)*(1/2:ℝ)^k) ∧
  adjointQueryCount cs=2*n-1 ∧ adjointGateCount cs=2*n+2
 := by
  intro H I O _ _ _ _ _ _ A U L R kappa k henc hkappa hgap
  (try dsimp only)
  let n := explicitInverseCutoff kappa (k+2)
  let c : ℝ := nativeInverseScale n
  let eps := nativeInverseTolerance n k
  have hn : 0 < n := (explicit_inverse_cutoff_integer_formula kappa (k+2)).2 hkappa
  have hnative := native_reciprocal_coefficients_and_scale n hn
  have heps : (0:ℚ) < eps := by
    dsimp [eps,nativeInverseTolerance]; exact mul_pos hnative.2.1 (by positivity)
  obtain ⟨data,hdata,hWF,hQ,hG,hOdd,hEven⟩ := computed_phase_word_actual_matrix_transform H I O A U L R
    (nativeInverseCoefficients n) (2*n-1) eps henc heps hnative.2.2.2.2.2.1 hnative.2.2.2.2.2.2.1 hnative.2.2.2.2.2.2.2
  have hlen : data.phases.length = 2*n-1 := by
    have hc := counts_compileRealPartQSVT (rangeProjector R) (rangeProjector L)
      (gaussianRatComplex data.base) (data.phases.map gaussianRatComplex)
    have hh : adjointQueryCount (computedPhaseWord (rangeProjector R) (rangeProjector L) data) = data.phases.length := by
      simpa only [List.length_map,computedPhaseWord] using hc.1
    exact hh.symm.trans hQ
  have hodd : (2*n-1)%2 = 1 := by omega
  have hraw := hOdd hodd
  have hfull :=
      fullComputedPhaseWord_wellFormed_counts (rangeProjector R) (rangeProjector L) data hWF
  have hforward := fullComputedPhaseWord_block L R U (rangeProjector R) (rangeProjector L) data _ (eps:ℝ)
    henc.left_isometry henc.right_isometry hfull.1 henc.unitary hraw
  have hback := Qatlib.Concepts.BlockEncoding.Encoding.BlockEncoding.adjoint hforward
  rw [native_inverse_singular_adjoint] at hback
  have heword : finiteInverseWord L R kappa k = adjointCircuit (fullComputedPhaseWord (rangeProjector R) (rangeProjector L) data) := by
    unfold finiteInverseWord
    change (match (finitePhaseSynthesis (nativeInverseCoefficients n) (2*n-1) eps).value with
      | none => []
      | some data => adjointCircuit (fullComputedPhaseWord (rangeProjector R) (rangeProjector L) data)) = _
    rw [hdata]
  have hbackword : BlockEncoding ((c:ℂ) • reciprocalMatrixApprox A n)
      (evaluate (parallelOracle U) (finiteInverseWord L R kappa k)) (coordinatePhaseFrame R) (coordinatePhaseFrame L) 1 (eps:ℝ) := by
    rw [heword,evaluate_adjointCircuit]
    exact hback
  have hkR : (0:ℝ) < kappa := by exact_mod_cast hkappa
  have hdelta : (0:ℝ) < (kappa:ℝ)⁻¹ := by positivity
  have hdelta1 : (kappa:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ hkR).mpr (by exact_mod_cast hkappa)
  have hrec := reciprocalMatrixApprox_error_le A hdelta hdelta1
    (fun i => (encoded_singularValues_mem_unitInterval henc i.val).2) hgap n
  have hprecision := explicit_inverse_geometric_precision kappa (k+2) hkappa
  have hcpos : 0 < c := Rat.cast_pos.mpr hnative.2.1
  have herr : ‖(c:ℂ) • matrixPseudoinverse A-(c:ℂ) • reciprocalMatrixApprox A n‖ ≤ c*(1/2:ℝ)^(k+2) := by
    rw [← smul_sub,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hcpos,norm_sub_rev]
    have hrec' := hrec.trans hprecision
    simpa only [show ((2:ℝ)⁻¹) = (1/2:ℝ) by norm_num] using mul_le_mul_of_nonneg_left hrec' hcpos.le
  have hE : (0:ℝ) ≤ c*(1/2:ℝ)^(k+2) := by positivity
  have hpseudo := hbackword.perturb hE herr
  have heE : (eps:ℝ)+c*(1/2:ℝ)^(k+2) = (c/2)*(1/2:ℝ)^k := by
    rw [show (eps:ℝ) = c*(1/2:ℝ)^(k+2) from nativeInverseTolerance_real n k,pow_add]
    norm_num
    ring
  refine ⟨⟨data,hdata,hlen⟩,by rw [heword]; exact hfull.1.adjointCircuit,
    by simpa only [heE] using hpseudo,?_,?_⟩
  · rw [heword,adjointQueryCount_adjointCircuit,hfull.2.1,hlen]
  · rw [heword,adjointGateCount_adjointCircuit,hfull.2.2,hlen]
    omega

theorem native_inverse_packet_valid (n k : ℕ) (hn : 0 < n) (data : PhaseData)
    (hout : (finitePhaseSynthesis (nativeInverseCoefficients n) (2*n-1) (nativeInverseTolerance n k)).value = some data) :
    data.phases.length = 2*n-1 ∧ IsPhase (gaussianRatComplex data.base) ∧
      ∀ z ∈ data.phases.map gaussianRatComplex,IsPhase z := by
  have hs := native_reciprocal_coefficients_and_scale n hn
  have heps : (0:ℚ) < nativeInverseTolerance n k := by
    unfold nativeInverseTolerance; exact mul_pos hs.2.1 (by positivity)
  obtain ⟨actual,hactual,hlen,hbase,hphases,hrest⟩ := finite_rational_phase_synthesis_terminates
    (nativeInverseCoefficients n) (2*n-1) (nativeInverseTolerance n k) heps
    hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2
  have he : actual = data := Option.some.inj (hactual.symm.trans hout)
  subst actual
  exact ⟨hlen,(data_phase_valid data hbase hphases).1,(data_phase_valid data hbase hphases).2⟩

theorem finiteInverseWord_of_some {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (L : Matrix H O ℂ) (R : Matrix H I ℂ) (kappa k : ℕ) (data : PhaseData)
    (hout : (finitePhaseSynthesis (nativeInverseCoefficients (explicitInverseCutoff kappa (k+2)))
      (2*explicitInverseCutoff kappa (k+2)-1) (nativeInverseTolerance (explicitInverseCutoff kappa (k+2)) k)).value = some data) :
    finiteInverseWord L R kappa k = adjointCircuit (fullComputedPhaseWord (rangeProjector R) (rangeProjector L) data) := by
  unfold finiteInverseWord
  (try dsimp only)
  rw [hout]

theorem finiteInverseWord_actual_odd_corner {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (henc : ProjectedUnitaryEncoding A U L R) (kappa k : ℕ) (hkappa : 0 < kappa) (data : PhaseData)
    (hout : (finitePhaseSynthesis (nativeInverseCoefficients (explicitInverseCutoff kappa (k+2)))
      (2*explicitInverseCutoff kappa (k+2)-1) (nativeInverseTolerance (explicitInverseCutoff kappa (k+2)) k)).value = some data) :
    compress (coordinatePhaseFrame R) (evaluate (parallelOracle U) (finiteInverseWord L R kappa k)) (coordinatePhaseFrame L) =
      (oddSingularTransform A (fun x => (((responseP (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)).eval (x:ℂ)).re:ℂ)))ᴴ := by
  let n := explicitInverseCutoff kappa (k+2)
  have hn : 0 < n := (explicit_inverse_cutoff_integer_formula kappa (k+2)).2 hkappa
  have hv := native_inverse_packet_valid n k hn data hout
  have hodd : (data.phases.map gaussianRatComplex).length%2 = 1 := by
    simp only [List.length_map,hv.1]; omega
  have hraw :=
      realPartQSVT_odd_singularEncoding henc hv.2.1 (data.phases.map gaussianRatComplex) hv.2.2 hodd
  have hforward : compress (coordinatePhaseFrame L)
      (evaluate (parallelOracle U) (fullComputedPhaseWord (rangeProjector R) (rangeProjector L) data)) (coordinatePhaseFrame R) =
      oddSingularTransform A (fun x => (((responseP (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)).eval (x:ℂ)).re:ℂ)) := by
    rw [fullComputedPhaseWord_compress]
    simpa only [computedPhaseWord,evaluate_compileRealPartQSVT] using hraw.encoded
  rw [finiteInverseWord_of_some L R kappa k data hout,evaluate_adjointCircuit,← compress_adjoint,hforward]

end Qatlib.Concepts.QsvtCore.LinearSystems
