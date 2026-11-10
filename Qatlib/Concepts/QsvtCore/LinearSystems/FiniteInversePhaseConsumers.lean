/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.FiniteInversePhaseProgram
set_option warningAsError false


open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath
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

theorem nativeInverseScale_square_lower (n : ℕ) (hn : 0 < n) : 1/(16*(n:ℝ)) ≤ (nativeInverseScale n:ℝ)^2 := by
  have hc := (nativeInverseScale_bounds n hn).2.1
  have hs := pow_le_pow_left₀ (show 0 ≤ 1/(4*Real.sqrt (n:ℝ)) by positivity) hc 2
  have he : (1/(4*Real.sqrt (n:ℝ)))^2 = 1/(16*(n:ℝ)) := by
    rw [div_pow,one_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg n)]
    norm_num
  rw [he] at hs
  exact hs

theorem inverse_precision_interval (k : ℕ) : 0 < (1/2:ℝ)^k ∧ (1/2:ℝ)^k ≤ 1 :=
  ⟨by positivity,pow_le_one₀ (by norm_num) (by norm_num)⟩

theorem computed_inverse_actual_minimum_norm_solver : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (kappa k : ℕ) (b : QState O),
  ProjectedUnitaryEncoding A U L R → 0 < kappa → Normalized b →
  (∃ x : QState I, A *ᵥ x=b) →
  (∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
    (kappa:ℝ)⁻¹ ≤ matrixSingularValues A i) →
  let n := explicitInverseCutoff kappa (k+2)
  let cs := finiteInverseWord L R kappa k
  let W := evaluate (parallelOracle U) cs
  postselectionProbability W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b ≥ 1/(64*(n:ℝ)) ∧
  (∃ phi : QState I, postselectionOutput W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b=some phi ∧
    IsMinimumNormSolutionState A b phi ((1/2:ℝ)^k)) ∧
  adjointQueryCount cs=2*n-1 ∧ adjointGateCount cs=2*n+2

 := by
  intro H I O _ _ _ _ _ _ A U L R kappa k b henc hkappa hb hrange hgap
  (try dsimp only)
  let n := explicitInverseCutoff kappa (k+2)
  let c : ℝ := nativeInverseScale n
  let t : ℝ := (1/2)^k
  have hn : 0 < n := (explicit_inverse_cutoff_integer_formula kappa (k+2)).2 hkappa
  have hc : 0 < c := Rat.cast_pos.mpr (nativeInverseScale_bounds n hn).1
  have ht := inverse_precision_interval k
  have hword :=
      computed_full_inverse_actual_encoding_and_cost H I O A U L R kappa k henc hkappa hgap
  have hsource := coordinatePhaseFrame_encoding henc
  have hE : (c/2)*t < c := by nlinarith [ht.2]
  obtain ⟨hprob,hpos,phi,hout,hspec⟩ :=
      scaledPseudoinverse_postselection hsource hword.2.2.1 hb hrange hE
  have hsq := nativeInverseScale_square_lower n hn
  have hbudget : 1/(64*(n:ℝ)) ≤ (c-(c/2)*t)^2 := by
    have hquarter : c/2 ≤ c-(c/2)*t := by nlinarith [ht.2]
    have hh := pow_le_pow_left₀ (show 0 ≤ c/2 by positivity) hquarter 2
    have hdiv := div_le_div_of_nonneg_right hsq (show (0:ℝ) ≤ 4 by norm_num)
    change (1/(16*(n:ℝ)))/4 ≤ c^2/4 at hdiv
    have he : (1/(16*(n:ℝ)))/4 = 1/(64*(n:ℝ)) := by ring
    rw [he] at hdiv
    nlinarith
  have herr : 2*((c/2)*t)/c = t := by field_simp
  refine ⟨hbudget.trans hprob,⟨phi,hout,?_⟩,hword.2.2.2.1,hword.2.2.2.2⟩
  change IsMinimumNormSolutionState A b phi (2*((c/2)*t)/c) at hspec
  rw [herr] at hspec
  exact hspec

theorem inverse_left_columns_factor {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) : leftSingularColumns A = A*basisColumns (rightSingularBasis A)*
      Matrix.diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i:ℂ)⁻¹) := by
  ext o i
  rw [Matrix.mul_diagonal]
  change ((matrixSingularValues A i:ℂ)⁻¹ • A.toEuclideanLin (rightSingularBasis A i)) o =
    (A.toEuclideanLin (rightSingularBasis A i)) o*(matrixSingularValues A i:ℂ)⁻¹
  simp only [PiLp.smul_apply,smul_eq_mul,mul_comm]

theorem inverse_odd_adjoint_kernel {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (f : ℝ → ℂ) (b : QState O) (hb : Aᴴ*ᵥb = 0) :
    (oddSingularTransform A f)ᴴ*ᵥb = 0 := by
  unfold oddSingularTransform
  rw [inverse_left_columns_factor]
  simp only [Matrix.conjTranspose_mul,← Matrix.mulVec_mulVec,hb,Matrix.mulVec_zero]

theorem inverse_overlap_zero_kernel {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A : Matrix O I ℂ) (b : QState O) (ht : leastSquaresOverlap A b = 0) : Aᴴ*ᵥb = 0 := by
  have hx := (leastSquares_overlap_and_zero A b).2.1.mp ht
  have hn := (leastSquares_projection_and_normal A b).1
  rw [hx,Matrix.mulVec_zero,zero_sub,Matrix.mulVec_neg] at hn
  exact neg_eq_zero.mp hn

theorem computed_inverse_actual_kernel_zero
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (kappa k : ℕ) (b : QState O)
    (henc : ProjectedUnitaryEncoding A U L R) (hkappa : 0 < kappa)
    (hkernel : Aᴴ *ᵥ b = 0) :
    let W := evaluate (parallelOracle U) (finiteInverseWord L R kappa k)
    postselectionVector W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b = 0 ∧
    postselectionProbability W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b = 0 ∧
    postselectionOutput W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b = none := by
  (try dsimp only)
  let n := explicitInverseCutoff kappa (k+2)
  let W := evaluate (parallelOracle U) (finiteInverseWord L R kappa k)
  have hn : 0 < n := (explicit_inverse_cutoff_integer_formula kappa (k+2)).2 hkappa
  have hs := native_reciprocal_coefficients_and_scale n hn
  have heps : (0 : ℚ) < nativeInverseTolerance n k := by
    unfold nativeInverseTolerance
    exact mul_pos hs.2.1 (by positivity)
  obtain ⟨data, hdata, _⟩ := finite_rational_phase_synthesis_terminates
    (nativeInverseCoefficients n) (2*n-1) (nativeInverseTolerance n k) heps
    hs.2.2.2.2.2.1 hs.2.2.2.2.2.2.1 hs.2.2.2.2.2.2.2
  have hcorner := finiteInverseWord_actual_odd_corner henc kappa k hkappa data hdata
  have hv : postselectionVector W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b = 0 := by
    unfold postselectionVector
    rw [hcorner]
    exact inverse_odd_adjoint_kernel A _ b hkernel
  refine ⟨hv, ?_, ?_⟩
  · rw [postselectionProbability_eq_norm_sq (coordinatePhaseFrame_isometry henc.right_isometry), hv]
    simp [stateVector]
  · rw [postselectionOutput, hv]
    exact (conditionalState_eq_none_iff (0 : QState I)).mpr rfl

theorem computed_inverse_actual_least_squares_and_zero : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (kappa k : ℕ) (b : QState O),
  ProjectedUnitaryEncoding A U L R → 0 < kappa → Normalized b →
  (∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
    (kappa:ℝ)⁻¹ ≤ matrixSingularValues A i) →
  let n := explicitInverseCutoff kappa (k+2)
  let cs := finiteInverseWord L R kappa k
  let W := evaluate (parallelOracle U) cs
  let tau := leastSquaresOverlap A b
  ((1/2:ℝ)^k < 2*tau →
    postselectionProbability W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b ≥
      (tau-(1/2:ℝ)^k/2)^2/(16*(n:ℝ)) ∧
    (∃ phi : QState I, postselectionOutput W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b=some phi ∧
      IsLeastSquaresSolutionState A b phi (((1/2:ℝ)^k)/tau))) ∧
  (tau=0 → postselectionProbability W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b=0 ∧
    postselectionOutput W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b=none)
 := by
  intro H I O _ _ _ _ _ _ A U L R kappa k b henc hkappa hb hgap
  (try dsimp only)
  let n := explicitInverseCutoff kappa (k+2)
  let c : ℝ := nativeInverseScale n
  let t : ℝ := (1/2)^k
  let tau := leastSquaresOverlap A b
  let cs := finiteInverseWord L R kappa k
  let W := evaluate (parallelOracle U) cs
  have hn : 0 < n := (explicit_inverse_cutoff_integer_formula kappa (k+2)).2 hkappa
  have hc : 0 < c := Rat.cast_pos.mpr (nativeInverseScale_bounds n hn).1
  have hword :=
      computed_full_inverse_actual_encoding_and_cost H I O A U L R kappa k henc hkappa hgap
  have hsource := coordinatePhaseFrame_encoding henc
  refine ⟨?_,?_⟩
  · intro ht
    change t < 2*tau at ht
    have hE : (c/2)*t < c*tau := by nlinarith
    have htau : 0 < tau := by have hp := (inverse_precision_interval k).1; linarith
    obtain ⟨hprob,hpos,phi,hout,hspec⟩ := leastSquares_actual_postselection A (parallelOracle U) W
      (coordinatePhaseFrame L) (coordinatePhaseFrame R) b c 1 ((c/2)*t) hsource hword.2.2.1 hc hb hE
    have hsq := nativeInverseScale_square_lower n hn
    have heprob : ((c*tau-(c/2)*t)/1)^2 = c^2*(tau-t/2)^2 := by ring
    rw [heprob] at hprob
    have hbudget : (tau-t/2)^2/(16*(n:ℝ)) ≤ c^2*(tau-t/2)^2 := by
      have hh := mul_le_mul_of_nonneg_right hsq (sq_nonneg (tau-t/2))
      exact (show (tau-t/2)^2/(16*(n:ℝ)) = (1/(16*(n:ℝ)))*(tau-t/2)^2 by ring).trans_le hh
    have herr : 2*((c/2)*t)/(c*tau) = t/tau := by field_simp
    refine ⟨hbudget.trans hprob,⟨phi,hout,?_⟩⟩
    change IsLeastSquaresSolutionState A b phi (2*((c/2)*t)/(c*tau)) at hspec
    rw [herr] at hspec
    exact hspec
  · intro ht
    exact (computed_inverse_actual_kernel_zero H I O A U L R kappa k b henc hkappa
      (inverse_overlap_zero_kernel A b ht)).2

theorem computed_inverse_actual_noisy_solver : ∀ (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U V : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (kappa k : ℕ) (b : QState O),
  ProjectedUnitaryEncoding A U L R → V ∈ Matrix.unitaryGroup H ℂ → 0 < kappa →
  Normalized b → (∃ x : QState I, A *ᵥ x=b) →
  (∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i →
    (kappa:ℝ)⁻¹ ≤ matrixSingularValues A i) →
  let n := explicitInverseCutoff kappa (k+2)
  let c := (nativeInverseScale n:ℝ)
  let d := 2*n-1
  ‖V-U‖ ≤ c/(4*(d:ℝ))*(1/2:ℝ)^k →
  let cs := finiteInverseWord L R kappa k
  let W := evaluate (parallelOracle V) cs
  BlockEncoding ((c:ℂ) • matrixPseudoinverse A) W
    (coordinatePhaseFrame R) (coordinatePhaseFrame L) 1 ((3*c/4)*(1/2:ℝ)^k) ∧
  postselectionProbability W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b ≥ 1/(256*(n:ℝ)) ∧
  (∃ phi : QState I, postselectionOutput W (coordinatePhaseFrame R) (coordinatePhaseFrame L) b=some phi ∧
    IsMinimumNormSolutionState A b phi ((3/2:ℝ)*(1/2:ℝ)^k)) ∧
  adjointQueryCount cs=d ∧ adjointGateCount cs=d+3
 := by
  intro H I O _ _ _ _ _ _ A U V L R kappa k b henc hV hkappa hb hrange hgap
  (try dsimp only)
  let n := explicitInverseCutoff kappa (k+2)
  let c : ℝ := nativeInverseScale n
  let d := 2*n-1
  let t : ℝ := (1/2)^k
  let cs := finiteInverseWord L R kappa k
  let W := evaluate (parallelOracle V) cs
  let W0 := evaluate (parallelOracle U) cs
  intro hnoise
  change ‖V-U‖ ≤ c/(4*(d:ℝ))*t at hnoise
  have hn : 0 < n := (explicit_inverse_cutoff_integer_formula kappa (k+2)).2 hkappa
  have hd : 0 < d := by dsimp [d]; omega
  have hdR : (0:ℝ) < d := by exact_mod_cast hd
  have hc : 0 < c := Rat.cast_pos.mpr (nativeInverseScale_bounds n hn).1
  have ht := inverse_precision_interval k
  have hword :=
      computed_full_inverse_actual_encoding_and_cost H I O A U L R kappa k henc hkappa hgap
  have hwf : WellFormedAdjointCircuit cs := hword.2.1
  have hbase :
      BlockEncoding ((c:ℂ) • matrixPseudoinverse A) W0 (coordinatePhaseFrame R)
      (coordinatePhaseFrame L) 1 ((c/2)*t) := hword.2.2.1
  have hW : W ∈ Matrix.unitaryGroup (Bool×H) ℂ := hwf.evaluate_unitary (parallelOracle_unitary hV)
  have hdist : ‖W0-W‖ ≤ (c/4)*t := by
    rw [norm_sub_rev]
    have h := evaluate_parallelOracle_oracle_error henc.unitary hV cs hwf
    rw [hword.2.2.2.1] at h
    change ‖W-W0‖ ≤ (d:ℝ)*‖V-U‖ at h
    have hh := mul_le_mul_of_nonneg_left hnoise hdR.le
    have he : (d:ℝ)*(c/(4*(d:ℝ))*t) = (c/4)*t := by field_simp
    exact h.trans (hh.trans_eq he)
  have hnew : BlockEncoding ((c:ℂ) • matrixPseudoinverse A) W (coordinatePhaseFrame R) (coordinatePhaseFrame L) 1 ((3*c/4)*t) := by
    refine ⟨hW,hbase.left_isometry,hbase.right_isometry,by norm_num,by positivity,?_⟩
    rw [one_smul]
    have hb0 : ‖(c:ℂ) • matrixPseudoinverse A-compress (coordinatePhaseFrame R) W0 (coordinatePhaseFrame L)‖ ≤ (c/2)*t := by
      simpa only [one_smul] using hbase.error_le
    have he : ‖compress (coordinatePhaseFrame R) W0 (coordinatePhaseFrame L)-
        compress (coordinatePhaseFrame R) W (coordinatePhaseFrame L)‖ ≤ (c/4)*t :=
      (compress_sub_norm_le hbase.left_isometry hbase.right_isometry W0 W).trans hdist
    calc
      _ = ‖((c:ℂ) • matrixPseudoinverse A-compress (coordinatePhaseFrame R) W0 (coordinatePhaseFrame L))+
        (compress (coordinatePhaseFrame R) W0 (coordinatePhaseFrame L)-compress (coordinatePhaseFrame R) W (coordinatePhaseFrame L))‖ := by congr 1; abel
      _ ≤ (c/2)*t+(c/4)*t := (norm_add_le _ _).trans (add_le_add hb0 he)
      _ = _ := by ring
  have hsource := coordinatePhaseFrame_encoding henc
  have hE : (3*c/4)*t < c := by nlinarith [ht.2]
  obtain ⟨hprob,hpos,phi,hout,hspec⟩ := scaledPseudoinverse_postselection hsource hnew hb hrange hE
  have hsq := nativeInverseScale_square_lower n hn
  have hbudget : 1/(256*(n:ℝ)) ≤ (c-(3*c/4)*t)^2 := by
    have hquarter : c/4 ≤ c-(3*c/4)*t := by nlinarith [ht.2]
    have hh := pow_le_pow_left₀ (show 0 ≤ c/4 by positivity) hquarter 2
    have hdiv := div_le_div_of_nonneg_right hsq (show (0:ℝ) ≤ 16 by norm_num)
    change (1/(16*(n:ℝ)))/16 ≤ c^2/16 at hdiv
    have he : (1/(16*(n:ℝ)))/16 = 1/(256*(n:ℝ)) := by ring
    rw [he] at hdiv
    nlinarith
  have herr : 2*((3*c/4)*t)/c = (3/2)*t := by field_simp; norm_num
  refine ⟨hnew,hbudget.trans hprob,⟨phi,hout,?_⟩,hword.2.2.2.1,?_⟩
  · change IsMinimumNormSolutionState A b phi (2*((3*c/4)*t)/c) at hspec
    rw [herr] at hspec
    exact hspec
  · have hg := hword.2.2.2.2
    change adjointGateCount cs = 2*n+2 at hg
    change adjointGateCount cs = d+3
    dsimp [d]
    omega

end Qatlib.Concepts.QsvtCore.LinearSystems
