/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.CountedThresholdQSVT
import Qatlib.Concepts.BlockEncoding.Postselection
import Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery.NoisyLeastSquaresConsumer

/-!
# Threshold postselection and concrete outputs

`threshold_postselected_subspace_output` converts a noisy threshold-filter approximation into a
nonzero conditional vector, a success-mass lower bound, and a normalized-state error bound when
the target norm exceeds the total error. Its hypotheses impose a gap between squared singular
values and the squared threshold.

The module checks the zero operator, the exact threshold boundary, and the rectangular rank-one
example. These consumers instantiate the singular-value filtering framework of
[GilyenSuLowWiebe2019].

## Main statements

* `threshold_postselected_subspace_output`: obtain output guarantees from the spectral gap and
  noise bound.
* `threshold_exact_boundary_half_response_consumer`: compute the response at the discontinuity.
* `threshold_rank_one_actual_output_consumer`: certify the concrete rank-one output and query
  count.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.WalshMoment.Forrelation

namespace Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery

open Matrix Polynomial
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

section GeneralOutput

variable {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

/-- Under the squared-singular-value gap and oracle-noise bound, if the total filter error `ε`
is below the threshold-projected input norm, the actual vector is nonzero, has mass at least
`(‖x‖ - ε)^2`, and has normalized error at most `2 * ε / ‖x‖`. -/
theorem threshold_postselected_subspace_output (A : Matrix O I ℂ) (U V : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (τ γ δ : ℝ) (k : ℕ) (b : QState I)
    (h : ProjectedUnitaryEncoding A U L R) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), γ ≤ |(matrixSingularValues A i) ^ 2 - τ ^ 2|)
    (hnoise : ‖V - U‖ ≤ δ) (hb : Normalized b) :
    let x := rightThresholdProjection A τ *ᵥ b
    let y := compress (averageFrame R) (evaluate (parallelOracle Vᴴ) (thresholdWord L R τ k))
      (averageFrame R) *ᵥ b
    let ε := signPolynomialError γ k / 2 + (2 * 3 ^ k : ℕ) * δ
    ε < ‖stateVector x‖ → y ≠ 0 ∧
      (‖stateVector x‖ - ε) ^ 2 ≤ MeasureProb y Finset.univ ∧
      ‖stateVector (PostMeasure y Finset.univ) - NormedSpace.normalize (stateVector x)‖ ≤
        2 * ε / ‖stateVector x‖ := by
  intro x y ε hsuccess
  have henc := threshold_actual_noisy_oracle_error A U V L R τ γ δ k h hV hτ hγ hγ1 hgap hnoise
  have hclose : ‖stateVector y - stateVector x‖ ≤ ε := by
    rw [norm_sub_rev]
    simpa only [postselectionVector, one_smul] using!
        Qatlib.Concepts.BlockEncoding.Postselection.Encoding.BlockEncoding.postselection_error henc hb
  obtain ⟨hy, hout⟩ := normalize_error_of_gap hclose hsuccess
  refine ⟨fun hz => hy ((stateVector_eq_zero_iff y).mpr hz), ?_, ?_⟩
  · rw [← stateVector_norm_sq]
    apply pow_le_pow_left₀ (sub_nonneg.mpr hsuccess.le) _ 2
    have hr : ‖stateVector x‖ - ‖stateVector y‖ ≤ ε :=
      (norm_sub_norm_le (stateVector x) (stateVector y)).trans (by
      rw [norm_sub_rev]
      exact hclose)
    linarith
  · rw [stateVector_postMeasure_univ]
    exact hout

/-- For a zero operator and a positive threshold gap, the right threshold projection vanishes
and the compressed filter norm is at most `signPolynomialError γ k / 2`. -/
theorem threshold_zero_operator_full_kernel_consumer (τ γ : ℝ) (k : ℕ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ) (hγτ : γ ≤ τ ^ 2) (hγ1 : γ ≤ 1) :
    rightThresholdProjection (0 : Matrix O I ℂ) τ = 0 ∧
      ∀ (U : Matrix H H ℂ) (L : Matrix H O ℂ) (R : Matrix H I ℂ),
        ProjectedUnitaryEncoding (0 : Matrix O I ℂ) U L R →
        ‖compress (averageFrame R) (evaluate (parallelOracle Uᴴ) (thresholdWord L R τ k))
          (averageFrame R)‖ ≤ signPolynomialError γ k / 2 := by
  refine ⟨rightThresholdProjection_zero τ, ?_⟩
  intro U L R h
  have hgap : ∀ i : Fin (Fintype.card I),
      γ ≤ |(matrixSingularValues (0 : Matrix O I ℂ) i) ^ 2 - τ ^ 2| := by
    intro i
    simpa [matrixSingularValues, LinearMap.singularValues_zero, abs_of_nonneg (sq_nonneg τ)]
      using! hγτ
  have henc := (threshold_actual_word_encoding_and_cost (0 : Matrix O I ℂ) U L R τ γ k
    h hτ hγ hγ1 hgap).2.1
  simpa only [rightThresholdProjection_zero, one_smul, zero_sub, norm_neg] using! henc.error_le

end GeneralOutput

/-- At the exact threshold, the real response is `1 / 2`, whereas the strict threshold indicator
is zero. -/
theorem threshold_exact_boundary_half_response_consumer (τ : ℝ) (k : ℕ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ((responseP (thresholdBase τ k) (thresholdPhases τ k)).eval (τ : ℂ)).re = 1 / 2 ∧
      thresholdIndicator τ τ = 0 := by
  exact ⟨(threshold_phase_word_response τ k hτ).2.2.2 τ |>.trans
    (thresholdPolynomial_eval_threshold τ k), thresholdIndicator_self τ⟩

/-- If `Aᴴ * A` is idempotent, every squared singular value of `A` is zero or one. -/
private theorem squared_singularValues_of_idempotent_gram
    {I O : Type} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]
    (A : Matrix O I ℂ) (hP : (Aᴴ * A) * (Aᴴ * A) = Aᴴ * A)
    (i : Fin (Fintype.card I)) :
    (matrixSingularValues A i) ^ 2 = 0 ∨ (matrixSingularValues A i) ^ 2 = 1 := by
  have hv : rightSingularBasis A i ≠ 0 := by
    intro hz
    have hn := norm_rightSingularBasis A i
    rw [hz, norm_zero] at hn
    norm_num at hn
  have he := congrArg (fun T : Matrix I I ℂ => T.toEuclideanLin (rightSingularBasis A i)) hP
  (try dsimp only at he)
  change (Matrix.toLpLin 2 2 ((Aᴴ * A) * (Aᴴ * A))) (rightSingularBasis A i) = _ at he
  rw [Matrix.toLpLin_mul_same, LinearMap.comp_apply, gram_apply_rightSingularBasis,
    map_smul, gram_apply_rightSingularBasis, smul_smul] at he
  have hh := smul_left_injective ℂ hv he
  have hr : (matrixSingularValues A i) ^ 2 * (matrixSingularValues A i) ^ 2 =
      (matrixSingularValues A i) ^ 2 := by exact_mod_cast hh
  have hm : (matrixSingularValues A i) ^ 2 * ((matrixSingularValues A i) ^ 2 - 1) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hm with h0 | h1
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1)

/-- The Gram matrix of the rectangular rank-one example is idempotent. -/
private theorem lsExample_gram_idempotent :
    (lsExampleAᴴ * lsExampleA) * (lsExampleAᴴ * lsExampleA) = lsExampleAᴴ * lsExampleA := by
  rw [lsExampleA_conjTranspose_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The squared singular values of the rank-one example are separated from the squared threshold
`(1 / 2)^2` by at least `1 / 4`. -/
theorem threshold_rank_one_gap : ∀ i : Fin (Fintype.card (Fin 2)),
    (1 / 4 : ℝ) ≤ |(matrixSingularValues lsExampleA i) ^ 2 - (1 / 2 : ℝ) ^ 2| := by
  intro i
  rcases squared_singularValues_of_idempotent_gram lsExampleA lsExample_gram_idempotent i
    with h0 | h1
  · rw [h0]; norm_num
  · rw [h1]; norm_num

/-- The right threshold projection of the rank-one example at `1 / 2` equals its Gram matrix. -/
theorem threshold_rank_one_projection :
    rightThresholdProjection lsExampleA (1 / 2) = lsExampleAᴴ * lsExampleA := by
  change spectralDiagonal (rightSingularBasis lsExampleA)
    (fun i => (thresholdIndicator (1 / 2) (matrixSingularValues lsExampleA i) : ℂ)) = _
  symm
  apply eq_spectralDiagonal_of_action
  intro i
  rw [gram_apply_rightSingularBasis]
  have hc : (matrixSingularValues lsExampleA i : ℂ) ^ 2 =
      (thresholdIndicator (1 / 2) (matrixSingularValues lsExampleA i) : ℂ) := by
    have hr : (matrixSingularValues lsExampleA i) ^ 2 =
        thresholdIndicator (1 / 2) (matrixSingularValues lsExampleA i) := by
      unfold thresholdIndicator
      rcases squared_singularValues_of_idempotent_gram lsExampleA lsExample_gram_idempotent i
        with h0 | h1
      · rw [h0]; norm_num
      · rw [h1]; norm_num
    exact_mod_cast hr
  rw [hc]

/-- The relabeled Hadamard input has both amplitudes equal to `1 / √2`. -/
private theorem threshold_rank_one_input_amplitudes :
    relabelState boolEquivFin2 (ApplyGate Hadamard (Qatlib.Foundations.PureStateMath.Ket false)) =
      fun _ : Fin 2 => (Real.sqrt 2 : ℂ)⁻¹ := by
  rw [applyGate_hadamard_ket_false]
  funext i
  fin_cases i <;> simp [relabelState, boolEquivFin2, Plus, Hadamard]

/-- The rank-one threshold projection sends the Hadamard input to `1 / √2` times ket zero. -/
private theorem threshold_rank_one_target :
    rightThresholdProjection lsExampleA (1 / 2) *ᵥ
        relabelState boolEquivFin2 (ApplyGate Hadamard (Qatlib.Foundations.PureStateMath.Ket false)) =
      (Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2) := by
  rw [threshold_rank_one_projection, lsExampleA_conjTranspose_mul,
    threshold_rank_one_input_amplitudes]
  funext i
  fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Qatlib.Foundations.PureStateMath.Ket]

/-- The norm of `1 / √2` times ket zero is `1 / √2`. -/
private theorem threshold_rank_one_target_norm :
    ‖stateVector ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))‖ = (Real.sqrt 2)⁻¹ := by
  rw [stateVector_smul_ket_norm, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg 2)]

/-- The normalized state vector of `1 / √2` times ket zero is the state vector of ket zero. -/
private theorem threshold_rank_one_target_direction :
    NormedSpace.normalize (stateVector ((Real.sqrt 2 : ℂ)⁻¹ • Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2))) =
      stateVector (Qatlib.Foundations.PureStateMath.Ket (0 : Fin 2)) := by
  rw [← stateVector_postMeasure_univ, postMeasure_smul_ket]
  have hn : ‖(Real.sqrt 2 : ℂ)⁻¹‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [hn, inv_inv]
  have hs : (↑(Real.sqrt 2) * (Real.sqrt 2 : ℂ)⁻¹) = 1 :=
    mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr
      (Real.sqrt_pos_of_pos (show (0 : ℝ) < 2 by norm_num)).ne')
  rw [hs, one_smul]

/-- The rank-one threshold word has a nonzero output, the stated success-mass and normalized
error bounds relative to ket zero, and exactly `2 * 3^k` adjoint queries. -/
theorem threshold_rank_one_actual_output_consumer (k : ℕ) :
    let ε := signPolynomialError (1 / 4) k / 2
    let b :=
        relabelState boolEquivFin2
        (ApplyGate Hadamard (Qatlib.Foundations.PureStateMath.Ket false))
    let y := compress (averageFrame lsExampleR)
      (evaluate (parallelOracle lsExampleUᴴ) (thresholdWord lsExampleL lsExampleR (1 / 2) k))
      (averageFrame lsExampleR) *ᵥ b
    y ≠ 0 ∧ ((Real.sqrt 2)⁻¹ - ε) ^ 2 ≤ MeasureProb y Finset.univ ∧
      ‖stateVector (PostMeasure y Finset.univ) - stateVector (Qatlib.Foundations.PureStateMath.Ket 0)‖ ≤
        2 * Real.sqrt 2 * ε ∧
      adjointQueryCount (thresholdWord lsExampleL lsExampleR (1 / 2) k) = 2 * 3 ^ k := by
  intro ε b y
  have hdata := leastSquares_rectangular_consumer_data
  have henc := hdata.2.2.2.2.1
  have hb : Normalized b := by
    change Normalized
        (relabelState boolEquivFin2 (ApplyGate Hadamard (Qatlib.Foundations.PureStateMath.Ket false)))
    rw [applyGate_hadamard_ket_false]
    exact normalized_relabelState boolEquivFin2 normalized_plus
  have hτ : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by norm_num
  have hε : ε ≤ (1 / 2 : ℝ) := by
    have hp : (1 - (1 / 4 : ℝ) ^ 2) ^ (2 ^ k) ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    dsimp [ε, signPolynomialError]
    linarith
  have hgap : signPolynomialError (1 / 4) k / 2 + (2 * 3 ^ k : ℕ) * (0 : ℝ) <
      ‖stateVector (rightThresholdProjection lsExampleA (1 / 2) *ᵥ b)‖ := by
    rw [threshold_rank_one_target, threshold_rank_one_target_norm]
    have hs : 0 < Real.sqrt 2 := Real.sqrt_pos_of_pos (by norm_num)
    have hs2 : Real.sqrt 2 < 2 := by nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    have hi : (1 / 2 : ℝ) < (Real.sqrt 2)⁻¹ := by
      rw [inv_eq_one_div]
      exact (lt_div_iff₀ hs).mpr (by nlinarith)
    simpa only [mul_zero, add_zero] using! hε.trans_lt hi
  have hout := threshold_postselected_subspace_output lsExampleA lsExampleU lsExampleU
    lsExampleL lsExampleR (1 / 2) (1 / 4) 0 k b henc hdata.2.1 hτ (by norm_num)
    (by norm_num) threshold_rank_one_gap (by simp) hb hgap
  rw [threshold_rank_one_target, threshold_rank_one_target_norm,
    threshold_rank_one_target_direction] at hout
  simp only [mul_zero, add_zero] at hout
  refine ⟨hout.1, hout.2.1, ?_, ?_⟩
  · have heq : 2 * ε / (Real.sqrt 2)⁻¹ = 2 * Real.sqrt 2 * ε := by
      rw [div_inv_eq_mul]; ring
    have hbound : ‖stateVector (PostMeasure y Finset.univ) - stateVector (Qatlib.Foundations.PureStateMath.Ket 0)‖ ≤
        2 * ε / (Real.sqrt 2)⁻¹ := hout.2.2
    rw [heq] at hbound
    exact hbound
  · exact (threshold_actual_word_encoding_and_cost lsExampleA lsExampleU lsExampleL
      lsExampleR (1 / 2) (1 / 4) k henc hτ (by norm_num) (by norm_num)
      threshold_rank_one_gap).2.2.1

end Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
