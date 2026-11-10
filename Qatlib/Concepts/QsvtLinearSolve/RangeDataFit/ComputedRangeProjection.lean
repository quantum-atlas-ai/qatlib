/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseConsumers
import Qatlib.Concepts.AmplitudeCore.PreparedReadout.PreparedAmplitudeEstimation
set_option warningAsError false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open scoped Classical BigOperators Matrix.Norms.L2Operator

noncomputable def fitLeft {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] :
    Matrix (O⊕I) O ℂ := fun h o => if h=Sum.inl o then 1 else 0

noncomputable def fitRight {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] :
    Matrix (O⊕I) I ℂ := fun h i => if h=Sum.inr i then 1 else 0

def nativeRangeCoefficients (n : ℕ) : List ℚ := ratMulList [0,1] (nativeReciprocalCoefficients n)

noncomputable def fitProjectionWord {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (κ k : ℕ) : List (AdjointStep (Bool×(O⊕I))) :=
  let n := explicitInverseCutoff κ (k+2)
  match (finitePhaseSynthesis (nativeRangeCoefficients n) (2*n) ((1/2:ℚ)^(k+2))).value with
  | none => []
  | some data => fullComputedPhaseWord (rangeProjector (fitRight (O:=O) (I:=I)))
      (rangeProjector (fitLeft (O:=O) (I:=I))) data

noncomputable def fitProjectionPrepare {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (U B : Matrix (O⊕I) (O⊕I) ℂ) (κ k : ℕ) :
    Matrix (Bool×(O⊕I)) (Bool×(O⊕I)) ℂ :=
  evaluate (parallelOracle U) (fitProjectionWord (O:=O) (I:=I) κ k) *
    TensorGate (1 : Matrix Bool Bool ℂ) B

def fitOutputEvent (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I] :
    Finset (Bool×(O⊕I)) := Finset.univ.filter (fun h => h.1=false ∧ ∃ o : O,h.2=Sum.inl o)

theorem nativeRangeCoefficients_semantics (n : ℕ) :
    realTarget (nativeRangeCoefficients n) = 1 - (1 - Polynomial.X^2)^n := by
  rw [nativeRangeCoefficients, realTarget_mul, nativeReciprocalCoefficients_semantics]
  have hx : realTarget ([0,1] : List ℚ) = Polynomial.X := by simp [realTarget_cons]
  rw [hx, X_mul_reciprocalPolynomial]

theorem nativeRangeCoefficients_bounded (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (-1 : ℝ) 1) :
    |(realTarget (nativeRangeCoefficients n)).eval x| ≤ 1 := by
  rw [nativeRangeCoefficients_semantics]
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
  have hq0 : 0 ≤ 1 - x^2 := by nlinarith [hx.1, hx.2]
  have hq1 : 1 - x^2 ≤ 1 := by nlinarith [sq_nonneg x]
  have hp0 := pow_nonneg hq0 n
  have hp1 := pow_le_one₀ hq0 hq1 (n:=n)
  rw [abs_of_nonneg (by linarith)]
  linarith

theorem computed_range_native_polynomial_and_gap (κ k : ℕ) (hκ : 0 < κ) :
    let n := explicitInverseCutoff κ (k+2)
    realTarget (nativeRangeCoefficients n) = 1 - (1 - Polynomial.X^2)^n ∧
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |(realTarget (nativeRangeCoefficients n)).eval x| ≤ 1) ∧
    (∀ x : ℝ, (κ : ℝ)⁻¹ ≤ |x| → |x| ≤ 1 →
      |(realTarget (nativeRangeCoefficients n)).eval x - 1| ≤ (1/2 : ℝ)^(k+2)) := by
  (try dsimp only)
  let n := explicitInverseCutoff κ (k+2)
  refine ⟨nativeRangeCoefficients_semantics n, nativeRangeCoefficients_bounded n, ?_⟩
  intro x hx hx1
  have hκR : (0 : ℝ) < κ := Nat.cast_pos.mpr hκ
  have hδ : 0 < (κ : ℝ)⁻¹ := inv_pos.mpr hκR
  have hx0 : 0 < |x| := hδ.trans_le hx
  have hr := reciprocalPolynomial_error_le n hδ ⟨hx, hx1⟩
  have he := explicit_inverse_geometric_precision κ (k+2) hκ
  have hq0 : 0 ≤ 1 - x^2 := by nlinarith [sq_abs x]
  have hres : |(realTarget (nativeRangeCoefficients n)).eval x - 1| = (1-x^2)^n := by
    rw [nativeRangeCoefficients_semantics]
    simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X]
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (pow_nonneg hq0 n)]
  rw [reciprocalPolynomial_error_eq n hx0 hx1, sq_abs] at hr
  rw [hres]
  have hm := mul_le_mul_of_nonneg_right (hr.trans he) (abs_nonneg x)
  rw [div_mul_cancel₀ _ (ne_of_gt hx0)] at hm
  exact hm.trans (by simpa using! mul_le_mul_of_nonneg_left hx1 (by positivity : 0 ≤ (1/2:ℝ)^(k+2)))

theorem nativeRangeCoefficients_admissible (n : ℕ) :
    (realTarget (nativeRangeCoefficients n)).degree ≤ ((2*n : ℕ) : WithBot ℕ) ∧
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity (2*n) (realTarget (nativeRangeCoefficients n)) := by
  rw [nativeRangeCoefficients_semantics]
  constructor
  · apply Polynomial.natDegree_le_iff_degree_le.mp
    have hd : (1 - Polynomial.X^2 : Polynomial ℝ).natDegree ≤ 2 :=
      (Polynomial.natDegree_sub_le _ _).trans (by simp)
    have hp : ((1 - Polynomial.X^2 : Polynomial ℝ)^n).natDegree ≤
        n*(1-Polynomial.X^2 : Polynomial ℝ).natDegree := Polynomial.natDegree_pow_le
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) (hp.trans (by nlinarith)))
  · unfold Qatlib.Concepts.QspSimulation.Achievability.HasRealParity
    simp [Polynomial.sub_comp, Polynomial.pow_comp,
        Even.neg_one_pow (show Even (2*n) from ⟨n, by omega⟩)]

theorem computed_range_packet {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (U : Matrix (O⊕I) (O⊕I) ℂ)
    (κ k : ℕ) (henc : ProjectedUnitaryEncoding A U fitLeft fitRight) :
    ∃ data,
      (finitePhaseSynthesis (nativeRangeCoefficients (explicitInverseCutoff κ (k+2)))
        (2*explicitInverseCutoff κ (k+2)) ((1/2:ℚ)^(k+2))).value = some data ∧
      data.phases.length = 2*explicitInverseCutoff κ (k+2) ∧
      WellFormedAdjointCircuit (fitProjectionWord (O:=O) (I:=I) κ k) ∧
      adjointQueryCount (fitProjectionWord (O:=O) (I:=I) κ k) = 2*explicitInverseCutoff κ (k+2) ∧
      adjointGateCount (fitProjectionWord (O:=O) (I:=I) κ k) = 2*explicitInverseCutoff κ (k+2)+3 ∧
      BlockEncoding
        (leftSingularTransform A (fun x => (((realTarget (nativeRangeCoefficients
          (explicitInverseCutoff κ (k+2)))).eval x : ℝ) : ℂ)))
        (evaluate (parallelOracle U) (fitProjectionWord (O:=O) (I:=I) κ k))
        (coordinatePhaseFrame fitLeft) (coordinatePhaseFrame fitLeft) 1 ((1/2:ℝ)^(k+2)) := by
  let n := explicitInverseCutoff κ (k+2)
  obtain ⟨data,hdata,hlen,hbase,hphases,_,happrox,_⟩ := finite_rational_phase_synthesis_terminates
    (nativeRangeCoefficients n) (2*n) ((1/2:ℚ)^(k+2)) (by positivity)
    (nativeRangeCoefficients_admissible n).1 (nativeRangeCoefficients_admissible n).2
    (nativeRangeCoefficients_bounded n)
  have hph := data_phase_valid data hbase hphases
  have hWF := compileRealPartQSVT_wellFormed
    (rangeProjector_isOrthogonalProjector henc.right_isometry)
    (rangeProjector_isOrthogonalProjector henc.left_isometry) hph.1 _ hph.2
  have hfull := fullComputedPhaseWord_wellFormed_counts (rangeProjector (fitRight (O:=O) (I:=I)))
    (rangeProjector (fitLeft (O:=O) (I:=I))) data hWF
  have hword : fitProjectionWord (O:=O) (I:=I) κ k =
      fullComputedPhaseWord (rangeProjector fitRight) (rangeProjector fitLeft) data := by
    unfold fitProjectionWord
    (try dsimp only)
    rw [hdata]
  have hactual := realPartQSVT_even_left_singularEncoding henc hph.1
    (data.phases.map gaussianRatComplex) hph.2 (by simp [hlen])
  have herr : ‖leftSingularTransform A (fun x => (((realTarget (nativeRangeCoefficients n)).eval x:ℝ):ℂ)) -
      leftSingularTransform A (fun x => (((responseP (gaussianRatComplex data.base)
        (data.phases.map gaussianRatComplex)).eval (x:ℂ)).re:ℂ))‖ ≤ ((1/2:ℝ)^(k+2)) := by
    apply leftSingularTransform_error_le A _ _ (by positivity)
    intro i
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have hs := encoded_singularValues_mem_unitInterval henc i.val
    have hh := happrox (matrixSingularValues A i) ⟨by linarith [hs.1], hs.2⟩
    simpa using! hh
  have hraw : BlockEncoding
      (leftSingularTransform A (fun x => (((realTarget (nativeRangeCoefficients n)).eval x:ℝ):ℂ)))
      (evaluate (parallelOracle U) (computedPhaseWord (rangeProjector fitRight) (rangeProjector fitLeft) data))
      (averageFrame fitLeft) (averageFrame fitLeft) 1 ((1/2:ℝ)^(k+2)) := by
    simpa only [zero_add, evaluate_compileRealPartQSVT, computedPhaseWord] using!
      (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding hactual).perturb (by positivity) herr
  refine ⟨data,hdata,hlen,?_,?_,?_,?_⟩
  · rw [hword]; exact hfull.1
  · rw [hword, hfull.2.1, hlen]
  · rw [hword, hfull.2.2, hlen]
  · rw [hword]
    exact fullComputedPhaseWord_block fitLeft fitLeft U (rangeProjector fitRight) (rangeProjector fitLeft)
      data _ _ henc.left_isometry henc.left_isometry hfull.1 henc.unitary hraw

theorem fitOutputEvent_mass {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (v : QState (Bool×(O⊕I))) :
    MeasureProb v (fitOutputEvent O I) =
      ‖stateVector ((coordinatePhaseFrame (fitLeft (O:=O) (I:=I)))ᴴ *ᵥ v)‖^2 := by
  have hv : ((coordinatePhaseFrame (fitLeft (O:=O) (I:=I)))ᴴ *ᵥ v) = fun o => v (false, Sum.inl o) := by
    ext o
    simp [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, coordinatePhaseFrame_apply,
      fitLeft, Fintype.sum_prod_type, Fintype.sum_sum_type]
  rw [hv, stateVector_norm_sq]
  simp [MeasureProb, BornProb, fitOutputEvent, Finset.sum_filter, Fintype.sum_prod_type,
    Fintype.sum_sum_type]

theorem fitProjection_input {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (B : Matrix (O⊕I) (O⊕I) ℂ) (j : O⊕I) (b : QState O)
    (hB : B*ᵥKet j = fitLeft*ᵥb) :
    TensorGate (1 : Matrix Bool Bool ℂ) B *ᵥ Qatlib.Foundations.PureStateMath.Ket (false,j) = coordinatePhaseFrame fitLeft*ᵥb := by
  have hBB : TensorGate (1 : Matrix Bool Bool ℂ) B *ᵥ Qatlib.Foundations.PureStateMath.Ket (false,j) =
      fun p => if p.1=false then (B*ᵥKet j) p.2 else 0 := by
    ext ⟨c,h⟩
    cases c <;> simp [Matrix.mulVec, dotProduct, TensorGate, Matrix.kroneckerMap_apply,
      Matrix.one_apply, Qatlib.Foundations.PureStateMath.Ket]
  rw [hBB, hB]
  ext ⟨c,h⟩
  cases c <;> simp [coordinatePhaseFrame_apply, Matrix.mulVec, dotProduct]

theorem fitProjection_mass {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (U B : Matrix (O⊕I) (O⊕I) ℂ) (j : O⊕I) (b : QState O) (κ k : ℕ)
    (hB : B*ᵥKet j = fitLeft*ᵥb) :
    MeasureProb (fitProjectionPrepare U B κ k*ᵥKet (false,j)) (fitOutputEvent O I) =
      ‖stateVector (postselectionVector
        (evaluate (parallelOracle U) (fitProjectionWord (O:=O) (I:=I) κ k))
        (coordinatePhaseFrame fitLeft) (coordinatePhaseFrame fitLeft) b)‖^2 := by
  rw [fitProjectionPrepare, ← Matrix.mulVec_mulVec, fitProjection_input B j b hB,
      fitOutputEvent_mass]
  congr 2
  simp only [postselectionVector, compress, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem nativeRange_left_aeval {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (n : ℕ) :
    leftSingularTransform A (fun x => (((realTarget (nativeRangeCoefficients n)).eval x:ℝ):ℂ)) =
      Polynomial.aeval (A*Aᴴ) (1-(1-Polynomial.X : Polynomial ℂ)^n) := by
  rw [leftGram_aeval_eq_leftSingularTransform]
  apply congrArg (leftSingularTransform A)
  funext x
  simp [nativeRangeCoefficients_semantics]

theorem nativeRange_left_kernel {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (b : QState O) (n : ℕ)
    (hb : Aᴴ*ᵥb=0) :
    leftSingularTransform A (fun x => (((realTarget (nativeRangeCoefficients n)).eval x:ℝ):ℂ)) *ᵥ b = 0 := by
  have hg : (A*Aᴴ)*ᵥb=0 := by rw [← Matrix.mulVec_mulVec, hb, Matrix.mulVec_zero]
  have hact : (A*Aᴴ).toEuclideanLin (stateVector b) = (0:ℂ) • stateVector b := by
    change stateVector ((A*Aᴴ)*ᵥb) = _
    rw [hg]; simp [stateVector]
  have hh := matrix_aeval_apply_of_action (A*Aᴴ) (1-(1-Polynomial.X:Polynomial ℂ)^n)
    (stateVector b) 0 hact
  rw [← nativeRange_left_aeval] at hh
  simp only [Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_pow, Polynomial.eval_X,
    sub_zero, one_pow, sub_self, zero_smul] at hh
  exact (stateVector_eq_zero_iff _).mp hh

theorem fit_left_support {O I : Type} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) :
    A*matrixPseudoinverse A = leftSingularTransform A (fun x => if x=0 then 0 else 1) := by
  apply eq_spectralDiagonal_of_action (leftSingularBasis A)
  intro j
  (try dsimp only)
  by_cases hj : 0 < matrixSingularValues A j
  · have hr := (matrixSingularValues_pos_iff_lt_finrank_range A).mp hj
    rw [if_neg (ne_of_gt hj), one_smul, leftSingularBasis_apply_of_lt A j hr, leftSingularVector,
        map_smul]
    congr 1
    have he := congrArg (fun M : Matrix O I ℂ => M.toEuclideanLin)
      (mul_matrixPseudoinverse_mul A)
    (try dsimp only at he)
    rw [Matrix.toLpLin_mul_same] at he
    exact congrArg (fun T : EuclideanSpace ℂ I →ₗ[ℂ] EuclideanSpace ℂ O =>
      T (rightSingularBasis A ⟨j, by have := A.toEuclideanLin.finrank_range_le; simpa using! hr.trans_le this⟩)) he
  · have hz : matrixSingularValues A j=0 := le_antisymm (le_of_not_gt hj) (matrixSingularValues_nonneg A j)
    rw [if_pos hz, zero_smul]
    have hk := adjoint_apply_leftSingularBasis_of_rank_le A j
      (le_of_not_gt (by simpa only [← matrixSingularValues_pos_iff_lt_finrank_range A] using! hj))
    have hkb : Aᴴ*ᵥ(⇑(leftSingularBasis A j))=0 := by
      have h := hk
      rw [← Matrix.toEuclideanLin_conjTranspose_eq_adjoint] at h
      exact congrArg (fun v : EuclideanSpace ℂ I => ⇑v) h
    have hpin := inverse_odd_adjoint_kernel A (fun x => (x:ℂ)⁻¹) _ hkb
    change stateVector ((A*matrixPseudoinverse A)*ᵥ(⇑(leftSingularBasis A j)))=0
    rw [← Matrix.mulVec_mulVec, show matrixPseudoinverse A*ᵥ(⇑(leftSingularBasis A j))=0 from hpin,
      Matrix.mulVec_zero]
    rfl

theorem nativeRange_left_support_error {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A : Matrix O I ℂ) (U : Matrix (O⊕I) (O⊕I) ℂ)
    (κ k : ℕ) (henc : ProjectedUnitaryEncoding A U fitLeft fitRight) (hκ : 0 < κ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i → (κ:ℝ)⁻¹ ≤ matrixSingularValues A i) :
    ‖A*matrixPseudoinverse A - leftSingularTransform A
      (fun x => (((realTarget (nativeRangeCoefficients (explicitInverseCutoff κ (k+2)))).eval x:ℝ):ℂ))‖ ≤
      (1/2:ℝ)^(k+2) := by
  rw [fit_left_support]
  apply leftSingularTransform_error_le A _ _ (by positivity)
  intro j
  by_cases hz : matrixSingularValues A j = 0
  · simp [hz, nativeRangeCoefficients_semantics]
  · have hp : 0 < matrixSingularValues A j :=
      lt_of_le_of_ne (matrixSingularValues_nonneg A j) (Ne.symm hz)
    have hi : j.val < Fintype.card I := by
      by_contra h
      exact hz (matrixSingularValues_of_card_le A (le_of_not_gt h))
    have hg := (computed_range_native_polynomial_and_gap κ k hκ).2.2
      (matrixSingularValues A j) (by rw [abs_of_pos hp]; exact hgap ⟨j,hi⟩ hp)
      (by rw [abs_of_pos hp]; exact (encoded_singularValues_mem_unitInterval henc j.val).2)
    simp only [if_neg hz]
    rw [show (1:ℂ)=((1:ℝ):ℂ) from rfl, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hg

theorem computed_range_actual_word_and_mass
    (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (U B : Matrix (O⊕I) (O⊕I) ℂ) (j : O⊕I) (b : QState O) (κ k : ℕ)
    (henc : ProjectedUnitaryEncoding A U fitLeft fitRight) (hB : B∈Matrix.unitaryGroup (O⊕I) ℂ)
    (hprep : B*ᵥKet j=fitLeft*ᵥb) (hb : Normalized b) (hκ : 0 < κ)
    (hgap : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i → (κ:ℝ)⁻¹ ≤ matrixSingularValues A i) :
    let P := fitProjectionPrepare U B κ k
    let n := explicitInverseCutoff κ (k+2)
    P∈Matrix.unitaryGroup (Bool×(O⊕I)) ℂ ∧
    WellFormedAdjointCircuit (fitProjectionWord (O:=O) (I:=I) κ k) ∧
    adjointQueryCount (fitProjectionWord (O:=O) (I:=I) κ k)=2*n ∧
    adjointGateCount (fitProjectionWord (O:=O) (I:=I) κ k)=2*n+3 ∧
    |MeasureProb (P*ᵥKet (false,j)) (fitOutputEvent O I)-(leastSquaresOverlap A b)^2|≤(1/2:ℝ)^k := by
  (try dsimp only)
  obtain ⟨data,hdata,hlen,hWF,hq,hg,hblock⟩ := computed_range_packet A U κ k henc
  have hW := hWF.evaluate_unitary (parallelOracle_unitary henc.unitary)
  have hP : fitProjectionPrepare U B κ k∈Matrix.unitaryGroup (Bool×(O⊕I)) ℂ :=
    (Matrix.unitaryGroup _ ℂ).mul_mem hW (tensorGate_unitary (by simp) hB)
  refine ⟨hP,hWF,hq,hg,?_⟩
  have htarget := hblock.perturb (by positivity : 0≤(1/2:ℝ)^(k+2))
    (nativeRange_left_support_error A U κ k henc hκ hgap)
  let W := evaluate (parallelOracle U) (fitProjectionWord (O:=O) (I:=I) κ k)
  let v :=
      stateVector (postselectionVector W (coordinatePhaseFrame fitLeft) (coordinatePhaseFrame fitLeft) b)
  let z := stateVector ((A*matrixPseudoinverse A)*ᵥb)
  have herr : ‖v-z‖ ≤ 2*(1/2:ℝ)^(k+2) := by
    have hh :=
        Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_error htarget hb
    simpa only [one_smul, zero_add, norm_sub_rev, ← two_mul] using! hh
  have hv : ‖v‖ ≤ 1 := by
    have hm := postselectionProbability_mem_Icc hW htarget.left_isometry htarget.right_isometry hb
    rw [postselectionProbability_eq_norm_sq htarget.left_isometry] at hm
    have hm1 : ‖v‖^2≤1 := hm.2
    nlinarith [norm_nonneg v]
  have hz : ‖z‖ ≤ 1 := by
    have hh := stateVector_mulVec_norm_le (A*matrixPseudoinverse A) b
    rw [(normalized_iff_stateVector_norm b).mp hb, mul_one] at hh
    exact hh.trans (orthogonalProjector_spectralNorm_le_one (matrixPseudoinverse_projectors A).1)
  rw [fitProjection_mass U B j b κ k hprep]
  change |‖v‖^2-‖z‖^2|≤(1/2:ℝ)^k
  have hab := (abs_norm_sub_norm_le v z).trans herr
  have hsum : ‖v‖+‖z‖≤2 := by linarith
  calc
    _ = |‖v‖-‖z‖| * (‖v‖+‖z‖) := by
      rw [sq_sub_sq, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_comm _ _
    _ ≤ (2*(1/2:ℝ)^(k+2))*2 := mul_le_mul hab hsum (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; norm_num; ring

theorem computed_range_actual_zero_overlap_leakage
    (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
    (A : Matrix O I ℂ) (U B : Matrix (O⊕I) (O⊕I) ℂ) (j : O⊕I) (b : QState O) (κ k : ℕ)
    (henc : ProjectedUnitaryEncoding A U fitLeft fitRight) (hB : B∈Matrix.unitaryGroup (O⊕I) ℂ)
    (hprep : B*ᵥKet j=fitLeft*ᵥb) (_hκ : 0<κ) (ht : leastSquaresOverlap A b=0) :
    MeasureProb (fitProjectionPrepare U B κ k*ᵥKet (false,j)) (fitOutputEvent O I)≤(1/2:ℝ)^(2*(k+2)) := by
  have hb : Normalized b := by
    apply (normalized_iff_stateVector_norm b).mpr
    have hh := (normalized_iff_stateVector_norm _).mp (normalized_applyGate hB (normalized_ket j))
    dsimp only [ApplyGate] at hh
    rw [hprep,
        Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.stateVector_norm henc.left_isometry] at hh
    exact hh
  obtain ⟨_,_,_,_,_,_,hblock⟩ := computed_range_packet A U κ k henc
  have hk :=
      nativeRange_left_kernel A b (explicitInverseCutoff κ (k+2))
      (inverse_overlap_zero_kernel A b ht)
  have hh :=
      Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_error hblock hb
  rw [hk] at hh
  simp only [one_smul, stateVector, WithLp.toLp_zero, zero_sub, norm_neg] at hh
  rw [fitProjection_mass U B j b κ k hprep]
  calc
    _ ≤ ((1/2:ℝ)^(k+2))^2 := pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ = _ := by rw [← pow_mul]; congr 1; omega

end Qatlib.Concepts.QsvtLinearSolve.RangeDataFit
