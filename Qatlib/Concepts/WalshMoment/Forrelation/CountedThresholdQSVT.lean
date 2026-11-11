/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalshMoment.Forrelation.ThresholdApproximation
import Qatlib.Concepts.QsvtCore.LinearSystems.RealPolynomialCompletionClosed
import Qatlib.Concepts.QsvtCore.LinearSystems.ExplicitNoisyQSVTSolver

/-!
# Counted QSVT words for singular value thresholds

This module chooses phase sequences realizing `thresholdPolynomial` and compiles them into a
real-part QSVT word. For a projected unitary encoding of `A`, the word exactly encodes a
polynomial in `Aᴴ * A`. A gap between squared singular values and `τ^2` then gives an
approximate encoding of `rightThresholdProjection A τ`.

The construction follows the singular value transformation framework of [GilyenSuLowWiebe2019].
The bounds here use the particular threshold polynomial and compiled word defined in the
library.

## Key declarations

* `thresholdBase`, `thresholdPhases`, and `thresholdWord` select and compile the phases.
* `threshold_word_exact_gram_encoding` identifies the exact compressed polynomial.
* `threshold_actual_word_encoding_and_cost` gives error `signPolynomialError γ k / 2`, exactly
  `2 * 3^k` total forward and backward oracle queries, and `2 * 3^k + 1` fixed gates under the
  stated gap assumptions.
* `threshold_actual_noisy_oracle_error` adds at most `(2 * 3^k) * δ` to the error when the
  unitary oracle changes by operator norm at most `δ`.

## References

* [Gilyen et al., 2019][GilyenSuLowWiebe2019]
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
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Matrix Polynomial
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Matrix.Norms.L2Operator

set_option autoImplicit false

/-- For a threshold in `[0, 1]`, there exist unit-modulus base and list phases of length `2 *
3^k` whose response has real part `thresholdPolynomial τ k` on the real line. The response
plus its coefficientwise conjugate is twice that real polynomial embedded into the complex
coefficients. -/
private theorem exists_threshold_phases (τ : ℝ) (k : ℕ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
      zs.length = 2 * 3 ^ k ∧
      responseP base zs + Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial (responseP base zs) =
        C (2 : ℂ) * (thresholdPolynomial τ k).map Complex.ofRealHom ∧
      ∀ x : ℝ, ((responseP base zs).eval (x : ℂ)).re =
        (thresholdPolynomial τ k).eval x := by
  apply Qatlib.Concepts.QsvtCore.LinearSystems.exists_phases_of_bounded
    (degree_le_of_natDegree_le (thresholdPolynomial_natDegree_le τ k))
  · simp [Qatlib.Concepts.QspSimulation.Achievability.HasRealParity, thresholdPolynomial,
      comp_assoc, pow_comp, pow_mul]
  · intro x hx
    have hb := thresholdPolynomial_eval_mem_Icc k hτ (abs_le.mpr hx)
    exact abs_le.mpr ⟨by linarith [hb.1], hb.2⟩

/-- A chosen base phase realizing the threshold polynomial when `τ` lies in `[0, 1]`; it is
defined to be one otherwise. -/
noncomputable def thresholdBase (τ : ℝ) (k : ℕ) : ℂ :=
  if hτ : τ ∈ Set.Icc (0 : ℝ) 1 then
    Classical.choose (exists_threshold_phases τ k hτ) else 1

/-- A chosen phase list realizing the threshold polynomial when `τ` lies in `[0, 1]`; it is the
empty list otherwise. -/
noncomputable def thresholdPhases (τ : ℝ) (k : ℕ) : List ℂ :=
  if hτ : τ ∈ Set.Icc (0 : ℝ) 1 then
    Classical.choose (Classical.choose_spec (exists_threshold_phases τ k hτ)) else []

/-- For `τ` in `[0, 1]`, the chosen base and list entries are phases, the list has length `2 *
3^k`, and its response has real part equal to `thresholdPolynomial τ k` at every real
argument. -/
theorem threshold_phase_word_response (τ : ℝ) (k : ℕ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    IsPhase (thresholdBase τ k) ∧ (∀ z ∈ thresholdPhases τ k, IsPhase z) ∧
      (thresholdPhases τ k).length = 2 * 3 ^ k ∧
      ∀ x : ℝ, ((responseP (thresholdBase τ k) (thresholdPhases τ k)).eval (x : ℂ)).re =
        (thresholdPolynomial τ k).eval x := by
  have hs := Classical.choose_spec (Classical.choose_spec (exists_threshold_phases τ k hτ))
  simp only [thresholdBase, thresholdPhases, dif_pos hτ]
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.2⟩

/-- The adjoint circuit word obtained by compiling real-part QSVT with the range projectors of
`L` and `R` and the chosen threshold phases. -/
noncomputable def thresholdWord {H I O : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (τ : ℝ) (k : ℕ) :
    List (AdjointStep (Bool × H)) :=
  compileRealPartQSVT (rangeProjector L) (rangeProjector R)
    (thresholdBase τ k) (thresholdPhases τ k)

section Encoding

variable {H I O : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
  [Fintype O] [DecidableEq O]

/-- For a projected unitary encoding of `A` and `τ` in `[0, 1]`, the threshold word evaluated
with `parallelOracle Uᴴ` exactly encodes `thresholdFactor τ k` applied to `Aᴴ * A`. Both
encoding frames are `averageFrame R`. -/
theorem threshold_word_exact_gram_encoding (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (τ : ℝ) (k : ℕ)
    (h : ProjectedUnitaryEncoding A U L R) (hτ : τ ∈ Set.Icc (0 : ℝ) 1) :
    ProjectedUnitaryEncoding (aeval (Aᴴ * A) ((thresholdFactor τ k).map Complex.ofRealHom))
      (evaluate (parallelOracle Uᴴ) (thresholdWord L R τ k))
      (averageFrame R) (averageFrame R) := by
  obtain ⟨hb, hzs, hlen, hre⟩ := threshold_phase_word_response τ k hτ
  have heven : (thresholdPhases τ k).length % 2 = 0 := by rw [hlen]; omega
  have hex := realPartQSVT_even_right_projectedEncoding h hb _ hzs heven
  rw [realPartResponse_even_right_eq_singularTransform h _ _ heven] at hex
  have ht : rightSingularTransform A
      (fun x => (((responseP (thresholdBase τ k) (thresholdPhases τ k)).eval (x : ℂ)).re : ℂ)) =
      aeval (Aᴴ * A) ((thresholdFactor τ k).map Complex.ofRealHom) := by
    rw [gram_aeval_eq_rightSingularTransform]
    congr 1
    funext x
    rw [hre, thresholdPolynomial, eval_comp, eval_pow, eval_X, ← Complex.ofReal_pow]
    exact (Polynomial.eval_map_apply (f := Complex.ofRealHom) (x ^ 2)).symm
  rw [ht] at hex
  simpa only [thresholdWord, evaluate_compileRealPartQSVT] using hex

/-- If `τ` is in `[0, 1]` and every squared singular value is separated from `τ^2` by at least
`γ`, with `0 < γ ≤ 1`, the threshold word is well formed and block encodes the right
threshold projection with scale one and error `signPolynomialError γ k / 2`. This library
realization of the threshold-projector framework in [GilyenSuLowWiebe2019] uses exactly `2 *
3^k` total forward and backward oracle queries and `2 * 3^k + 1` fixed gates. -/
theorem threshold_actual_word_encoding_and_cost (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (τ γ : ℝ) (k : ℕ)
    (h : ProjectedUnitaryEncoding A U L R) (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), γ ≤ |(matrixSingularValues A i) ^ 2 - τ ^ 2|) :
    WellFormedAdjointCircuit (thresholdWord L R τ k) ∧
      BlockEncoding (rightThresholdProjection A τ)
        (evaluate (parallelOracle Uᴴ) (thresholdWord L R τ k))
        (averageFrame R) (averageFrame R) 1 (signPolynomialError γ k / 2) ∧
      adjointQueryCount (thresholdWord L R τ k) = 2 * 3 ^ k ∧
      adjointGateCount (thresholdWord L R τ k) = 2 * 3 ^ k + 1 := by
  obtain ⟨hb, hzs, hlen, _⟩ := threshold_phase_word_response τ k hτ
  have hwf : WellFormedAdjointCircuit (thresholdWord L R τ k) :=
    compileRealPartQSVT_wellFormed
      (rangeProjector_isOrthogonalProjector h.left_isometry)
      (rangeProjector_isOrthogonalProjector h.right_isometry) hb _ hzs
  have hA : ‖A‖ ≤ 1 := by
    rw [← h.encoded]
    exact (compress_norm_le h.left_isometry h.right_isometry U).trans
      (unitary_norm_le_one h.unitary)
  have herr := threshold_right_gram_error_le A hτ hγ hγ1 hA hgap k
  have hex :=
      (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (threshold_word_exact_gram_encoding A U L R τ k h hτ))
  have henc := hex.perturb ((norm_nonneg _).trans herr) (by
    rw [norm_sub_rev]
    exact herr)
  have hc := counts_compileRealPartQSVT (rangeProjector L) (rangeProjector R)
    (thresholdBase τ k) (thresholdPhases τ k)
  refine ⟨hwf, by simpa only [zero_add] using henc, ?_, ?_⟩
  · exact hc.1.trans hlen
  · exact hc.2.trans (congrArg (fun n => n + 1) hlen)

/-- Under the threshold and squared-singular-value gap assumptions, replacing the encoding
unitary `U` by a unitary `V` with operator-norm error at most `δ` gives a block encoding of
the same right threshold projection. Its scale is one and its error is at most
`signPolynomialError γ k / 2 + (2 * 3^k) * δ`. -/
theorem threshold_actual_noisy_oracle_error (A : Matrix O I ℂ) (U V : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (τ γ δ : ℝ) (k : ℕ)
    (h : ProjectedUnitaryEncoding A U L R) (hV : V ∈ Matrix.unitaryGroup H ℂ)
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), γ ≤ |(matrixSingularValues A i) ^ 2 - τ ^ 2|)
    (hnoise : ‖V - U‖ ≤ δ) :
    BlockEncoding (rightThresholdProjection A τ)
      (evaluate (parallelOracle Vᴴ) (thresholdWord L R τ k))
      (averageFrame R) (averageFrame R) 1
      (signPolynomialError γ k / 2 + (2 * 3 ^ k : ℕ) * δ) := by
  obtain ⟨hwf, hclean, hq, _⟩ := threshold_actual_word_encoding_and_cost A U L R τ γ k
    h hτ hγ hγ1 hgap
  have hδ : 0 ≤ δ := (norm_nonneg _).trans hnoise
  have hdist : ‖evaluate (parallelOracle Uᴴ) (thresholdWord L R τ k) -
      evaluate (parallelOracle Vᴴ) (thresholdWord L R τ k)‖ ≤ (2 * 3 ^ k : ℕ) * δ := by
    rw [norm_sub_rev]
    calc
      _ ≤ (adjointQueryCount (thresholdWord L R τ k) : ℝ) * ‖Vᴴ - Uᴴ‖ :=
        evaluate_parallelOracle_oracle_error (adjoint_unitary h.unitary) (adjoint_unitary hV) _ hwf
      _ = (2 * 3 ^ k : ℕ) * ‖V - U‖ := by
        rw [hq, ← Matrix.conjTranspose_sub, Matrix.l2_opNorm_conjTranspose]
      _ ≤ (2 * 3 ^ k : ℕ) * δ := mul_le_mul_of_nonneg_left hnoise (by positivity)
  refine ⟨hwf.evaluate_unitary (parallelOracle_unitary (adjoint_unitary hV)),
    hclean.left_isometry, hclean.right_isometry, by norm_num,
    add_nonneg hclean.error_nonneg (mul_nonneg (by positivity) hδ), ?_⟩
  have he := hclean.error_le
  rw [one_smul] at he ⊢
  calc
    _ = ‖(rightThresholdProjection A τ -
          compress (averageFrame R) (evaluate (parallelOracle Uᴴ) (thresholdWord L R τ k))
            (averageFrame R)) +
        (compress (averageFrame R) (evaluate (parallelOracle Uᴴ) (thresholdWord L R τ k))
            (averageFrame R) -
          compress (averageFrame R) (evaluate (parallelOracle Vᴴ) (thresholdWord L R τ k))
            (averageFrame R))‖ := by congr 1; abel
    _ ≤ _ := (norm_add_le _ _).trans (add_le_add he
      ((compress_sub_norm_le hclean.left_isometry hclean.right_isometry _ _).trans hdist))

end Encoding
end Qatlib.Concepts.WalshMoment.Forrelation
