/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.PhaseFrontend.SignPolynomial
import Qatlib.Concepts.WalkSearch.Spectral.Approximation

/-!
# Polynomial approximation of spectral thresholds

`thresholdPolynomial` converts `signPolynomial` into an even approximation of
`thresholdIndicator`, with degree, range, and error bounds away from the squared threshold.
`spectralThresholdProjection`, `rightThresholdProjection`, and `leftThresholdProjection` define
orthogonal threshold projectors. `threshold_right_gram_error_le` and
`threshold_left_gram_error_le` transfer the scalar approximation bounds to polynomial evaluation
on the two Gram matrices.

Spectral projection background appears in [HornJohnson2013], and polynomial singular value
transformations are developed in [Gilyen et al., 2019][GilyenSuLowWiebe2019].

## References

- [Horn and Johnson, 2013][HornJohnson2013].
-/

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.WalshMoment.Forrelation

open Polynomial Matrix Filter
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Topology Matrix.Norms.L2Operator

/-- The indicator of the strict squared threshold `τ ^ 2 < x ^ 2`, taking values zero and one. -/
noncomputable def thresholdIndicator (τ x : ℝ) : ℝ := if τ ^ 2 < x ^ 2 then 1 else 0

/-- The polynomial `(1 + signPolynomial k (X - τ ^ 2)) / 2`, before substituting a squared
variable. -/
noncomputable def thresholdFactor (τ : ℝ) (k : ℕ) : Polynomial ℝ :=
  C (1 / 2) * (1 + (signPolynomial k).comp (X - C (τ ^ 2)))

/-- The even threshold approximation obtained by composing `thresholdFactor τ k` with `X ^ 2`. -/
noncomputable def thresholdPolynomial (τ : ℝ) (k : ℕ) : Polynomial ℝ :=
  (thresholdFactor τ k).comp (X ^ 2)

/-- Evaluating `thresholdPolynomial τ k` at `x` yields `(1 + (signPolynomial k).eval (x ^ 2 - τ
^ 2)) / 2`. -/
theorem thresholdPolynomial_eval (τ : ℝ) (k : ℕ) (x : ℝ) :
    (thresholdPolynomial τ k).eval x = (1 + (signPolynomial k).eval (x ^ 2 - τ ^ 2)) / 2 := by
  simp only [thresholdPolynomial, thresholdFactor, Polynomial.eval_comp,
    Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_sub]
  ring

/-- The threshold polynomial has equal values at `x` and `-x`. -/
theorem thresholdPolynomial_eval_neg (τ : ℝ) (k : ℕ) (x : ℝ) :
    (thresholdPolynomial τ k).eval (-x) = (thresholdPolynomial τ k).eval x := by
  simp only [thresholdPolynomial_eval, neg_sq]

/-- Composing the threshold polynomial with `-X` leaves it unchanged. -/
theorem thresholdPolynomial_comp_neg_X (τ : ℝ) (k : ℕ) :
    (thresholdPolynomial τ k).comp (-X) = thresholdPolynomial τ k := by
  apply Polynomial.funext
  intro x
  simpa using thresholdPolynomial_eval_neg τ k x

/-- The natural degree of `thresholdFactor τ k` is at most `3 ^ k`. -/
theorem thresholdFactor_natDegree_le (τ : ℝ) (k : ℕ) :
    (thresholdFactor τ k).natDegree ≤ 3 ^ k := by
  have hshift : (X - C (τ ^ 2) : Polynomial ℝ).natDegree ≤ 1 := by
    exact (Polynomial.natDegree_sub_le _ _).trans (by simp)
  have hc : ((signPolynomial k).comp (X - C (τ ^ 2))).natDegree ≤ 3 ^ k := by
    calc
      _ ≤ (signPolynomial k).natDegree * (X - C (τ ^ 2) : Polynomial ℝ).natDegree :=
        Polynomial.natDegree_comp_le
      _ ≤ 3 ^ k := by
        rw [signPolynomial_natDegree]
        simpa using Nat.mul_le_mul_left (3 ^ k) hshift
  have ha : (1 + (signPolynomial k).comp (X - C (τ ^ 2))).natDegree ≤ 3 ^ k :=
    (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) hc)
  rw [thresholdFactor, Polynomial.natDegree_C_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)]
  exact ha

/-- The natural degree of the even threshold polynomial is at most `2 * 3 ^ k`. -/
theorem thresholdPolynomial_natDegree_le (τ : ℝ) (k : ℕ) :
    (thresholdPolynomial τ k).natDegree ≤ 2 * 3 ^ k := by
  rw [thresholdPolynomial, Polynomial.natDegree_comp]
  simpa [Nat.mul_comm] using Nat.mul_le_mul_right 2 (thresholdFactor_natDegree_le τ k)

/-- For `τ ∈ [0, 1]` and `|x| ≤ 1`, the shifted square `x ^ 2 - τ ^ 2` lies in `[-1, 1]`. -/
private theorem threshold_argument_mem {τ x : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    (hx : |x| ≤ 1) : x ^ 2 - τ ^ 2 ∈ Set.Icc (-1 : ℝ) 1 := by
  have hxI := abs_le.mp hx
  constructor <;> nlinarith [hxI.1, hxI.2, hτ.1, hτ.2, sq_nonneg x, sq_nonneg τ]

/-- For `τ ∈ [0, 1]` and `|x| ≤ 1`, the threshold polynomial takes values in `[0, 1]`. -/
theorem thresholdPolynomial_eval_mem_Icc (k : ℕ) {τ x : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hx : |x| ≤ 1) :
    (thresholdPolynomial τ k).eval x ∈ Set.Icc (0 : ℝ) 1 := by
  have hs := abs_le.mp (signPolynomial_abs_le_one k (threshold_argument_mem hτ hx))
  rw [thresholdPolynomial_eval]
  constructor <;> linarith [hs.1, hs.2]

/-- The threshold polynomial evaluates to one half at the threshold point `τ`. -/
@[simp] theorem thresholdPolynomial_eval_threshold (τ : ℝ) (k : ℕ) :
    (thresholdPolynomial τ k).eval τ = 1 / 2 := by
  simp [thresholdPolynomial_eval]

/-- The strict threshold indicator is zero at the threshold point itself. -/
@[simp] theorem thresholdIndicator_self (τ : ℝ) : thresholdIndicator τ τ = 0 := by
  simp [thresholdIndicator]

/-- The squared threshold indicator is zero at input zero for every real threshold. -/
@[simp] theorem thresholdIndicator_zero (τ : ℝ) : thresholdIndicator τ 0 = 0 := by
  simp [thresholdIndicator, not_lt.mpr (sq_nonneg τ)]

/-- Away from equality of the squared input and threshold, the threshold indicator equals `(1 +
sign (x ^ 2 - τ ^ 2)) / 2`. -/
private theorem thresholdIndicator_eq_sign {τ x : ℝ} (hne : x ^ 2 - τ ^ 2 ≠ 0) :
    thresholdIndicator τ x = (1 + Real.sign (x ^ 2 - τ ^ 2)) / 2 := by
  by_cases hp : τ ^ 2 < x ^ 2
  · rw [thresholdIndicator, if_pos hp, Real.sign_of_pos (sub_pos.mpr hp)]
    norm_num
  · have hn : x ^ 2 - τ ^ 2 < 0 :=
      lt_of_le_of_ne (sub_nonpos.mpr (le_of_not_gt hp)) hne
    rw [thresholdIndicator, if_neg hp, Real.sign_of_neg hn]
    norm_num

/-- For `τ ∈ [0, 1]` and `|x| ≤ 1` separated from the squared threshold by at least a positive
`γ`, the absolute threshold approximation error is at most `signPolynomialError γ k / 2`. -/
theorem thresholdPolynomial_error_le (k : ℕ) {τ γ x : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ)
    (hgap : γ ≤ |x ^ 2 - τ ^ 2|) (hx : |x| ≤ 1) :
    |thresholdIndicator τ x - (thresholdPolynomial τ k).eval x| ≤
      signPolynomialError γ k / 2 := by
  have hy : |x ^ 2 - τ ^ 2| ≤ 1 := abs_le.mpr (threshold_argument_mem hτ hx)
  have hne : x ^ 2 - τ ^ 2 ≠ 0 := by
    intro he
    rw [he, abs_zero] at hgap
    linarith
  rw [thresholdIndicator_eq_sign hne, thresholdPolynomial_eval]
  rw [show (1 + Real.sign (x ^ 2 - τ ^ 2)) / 2 -
      (1 + (signPolynomial k).eval (x ^ 2 - τ ^ 2)) / 2 =
      (Real.sign (x ^ 2 - τ ^ 2) - (signPolynomial k).eval (x ^ 2 - τ ^ 2)) / 2 by ring,
    abs_div]
  norm_num
  exact div_le_div_of_nonneg_right (signPolynomial_error_le k hγ hgap hy) (by norm_num)

/-- For `τ ∈ [0, 1]` and `0 < γ ≤ 1`, the threshold polynomials eventually achieve any positive
error tolerance uniformly over `|x| ≤ 1` with squared threshold gap at least `γ`. -/
theorem thresholdPolynomial_eventually_error_lt {τ γ ε : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hε : 0 < ε) :
    ∃ K : ℕ, ∀ k ≥ K, ∀ x : ℝ, |x| ≤ 1 → γ ≤ |x ^ 2 - τ ^ 2| →
      |thresholdIndicator τ x - (thresholdPolynomial τ k).eval x| < ε := by
  have ht : Tendsto (fun k : ℕ => signPolynomialError γ k / 2) atTop (𝓝 0) := by
    simpa using (tendsto_signPolynomialError hγ hγ1).div_const 2
  have he : ∀ᶠ k : ℕ in atTop, signPolynomialError γ k / 2 < ε :=
    (tendsto_order.mp ht).2 ε hε
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp he
  exact ⟨K, fun k hk x hx hgap =>
    (thresholdPolynomial_error_le k hτ hγ hgap hx).trans_lt (hK k hk)⟩

section Spectral
variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

/-- The matrix diagonal in the orthonormal basis `b` with diagonal entries `thresholdIndicator τ
(σ j)`. -/
noncomputable def spectralThresholdProjection
    (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) (τ : ℝ) (σ : J → ℝ) : Matrix I I ℂ :=
  spectralDiagonal b (fun j => (thresholdIndicator τ (σ j) : ℂ))

omit [DecidableEq I] in

/-- A spectral threshold projection is an orthogonal projector for every real threshold and real
diagonal parameter family. -/
theorem spectralThresholdProjection_isOrthogonalProjector
    (b : OrthonormalBasis J ℂ (EuclideanSpace ℂ I)) (τ : ℝ) (σ : J → ℝ) :
    IsOrthogonalProjector (spectralThresholdProjection b τ σ) := by
  let d : J → ℂ := fun j => (thresholdIndicator τ (σ j) : ℂ)
  have hd : (diagonal d : Matrix J J ℂ) * diagonal d = diagonal d := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext j
    dsimp [d, thresholdIndicator]
    split_ifs <;> norm_num
  have hda : (diagonal d : Matrix J J ℂ)ᴴ = diagonal d := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [Matrix.conjTranspose_apply, d]
    · simp [Matrix.conjTranspose_apply, hij, Ne.symm hij]
  constructor
  · change (basisColumns b * diagonal d * (basisColumns b)ᴴ) *
        (basisColumns b * diagonal d * (basisColumns b)ᴴ) = _
    calc
      _ = basisColumns b * (diagonal d * ((basisColumns b)ᴴ * basisColumns b) * diagonal d) *
          (basisColumns b)ᴴ := by simp only [Matrix.mul_assoc]
      _ = basisColumns b * diagonal d * (basisColumns b)ᴴ := by
        rw [basisColumns_adjoint_mul, Matrix.mul_one, hd]
  · change (basisColumns b * diagonal d * (basisColumns b)ᴴ)ᴴ =
      basisColumns b * diagonal d * (basisColumns b)ᴴ
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hda, Matrix.mul_assoc]

end Spectral

section Singular
variable {I O : Type*} [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O]

/-- The threshold projection in the right singular basis of `A`, using `matrixSingularValues A`
as the diagonal parameters. -/
noncomputable def rightThresholdProjection (A : Matrix O I ℂ) (τ : ℝ) : Matrix I I ℂ :=
  spectralThresholdProjection (rightSingularBasis A) τ (fun i => matrixSingularValues A i)

/-- The threshold projection in the left singular basis of `A`, using `matrixSingularValues A`
as the diagonal parameters. -/
noncomputable def leftThresholdProjection (A : Matrix O I ℂ) (τ : ℝ) : Matrix O O ℂ :=
  spectralThresholdProjection (leftSingularBasis A) τ (fun i => matrixSingularValues A i)

omit [DecidableEq O] in

/-- The right singular threshold projection of every matrix is an orthogonal projector. -/
theorem rightThresholdProjection_isOrthogonalProjector (A : Matrix O I ℂ) (τ : ℝ) :
    IsOrthogonalProjector (rightThresholdProjection A τ) :=
  spectralThresholdProjection_isOrthogonalProjector _ _ _

omit [DecidableEq O] in

/-- The left singular threshold projection of every matrix is an orthogonal projector. -/
theorem leftThresholdProjection_isOrthogonalProjector (A : Matrix O I ℂ) (τ : ℝ) :
    IsOrthogonalProjector (leftThresholdProjection A τ) :=
  spectralThresholdProjection_isOrthogonalProjector _ _ _

omit [DecidableEq O] in

/-- The right threshold projection of the zero matrix is zero for every real threshold. -/
@[simp] theorem rightThresholdProjection_zero (τ : ℝ) :
    rightThresholdProjection (0 : Matrix O I ℂ) τ = 0 := by
  change rightSingularTransform (0 : Matrix O I ℂ)
    (fun x => (thresholdIndicator τ x : ℂ)) = 0
  rw [rightSingularTransform_zero]
  simp

/-- The left threshold projection of the zero matrix is zero for every real threshold. -/
@[simp] theorem leftThresholdProjection_zero (τ : ℝ) :
    leftThresholdProjection (0 : Matrix O I ℂ) τ = 0 := by
  change leftSingularTransform (0 : Matrix O I ℂ)
    (fun x => (thresholdIndicator τ x : ℂ)) = 0
  rw [leftSingularTransform_zero]
  simp

/-- Evaluating the complex coefficient lift of `thresholdFactor τ k` at `x ^ 2` equals the
complex lift of the real threshold polynomial evaluated at `x`. -/
private theorem thresholdFactor_complex_eval (τ : ℝ) (k : ℕ) (x : ℝ) :
    ((thresholdFactor τ k).map Complex.ofRealHom).eval ((x : ℂ) ^ 2) =
      (((thresholdPolynomial τ k).eval x : ℝ) : ℂ) := by
  rw [← Complex.ofReal_pow]
  calc
    _ = (((thresholdFactor τ k).eval (x ^ 2) : ℝ) : ℂ) :=
      Polynomial.eval_map_apply (f := Complex.ofRealHom) (x ^ 2)
    _ = _ := by simp [thresholdPolynomial]

/-- Under the scalar threshold gap and unit interval hypotheses, the complex norm error of the
lifted threshold factor at `x ^ 2` is at most `signPolynomialError γ k / 2`. -/
private theorem threshold_complex_error (k : ℕ) {τ γ x : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ)
    (hgap : γ ≤ |x ^ 2 - τ ^ 2|) (hx : |x| ≤ 1) :
    ‖((thresholdFactor τ k).map Complex.ofRealHom).eval ((x : ℂ) ^ 2) -
      (thresholdIndicator τ x : ℂ)‖ ≤ signPolynomialError γ k / 2 := by
  rw [thresholdFactor_complex_eval, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    abs_sub_comm]
  exact thresholdPolynomial_error_le k hτ hγ hgap hx

/-- For a matrix of operator norm at most one and `τ ∈ [0, 1]`, if its right singular values
have squared threshold gaps at least `0 < γ ≤ 1`, the lifted threshold factor evaluated on
`Aᴴ * A` approximates `rightThresholdProjection A τ` in operator norm within
`signPolynomialError γ k / 2`. -/
theorem threshold_right_gram_error_le (A : Matrix O I ℂ) {τ γ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hA : ‖A‖ ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card I), γ ≤ |(matrixSingularValues A i) ^ 2 - τ ^ 2|)
    (k : ℕ) :
    ‖aeval (Aᴴ * A) ((thresholdFactor τ k).map Complex.ofRealHom) - rightThresholdProjection A τ‖ ≤
      signPolynomialError γ k / 2 := by
  have hp : rightThresholdProjection A τ =
      rightSingularTransform A (fun x => (thresholdIndicator τ x : ℂ)) := rfl
  rw [gram_aeval_eq_rightSingularTransform, hp]
  apply rightSingularTransform_error_le A
    (fun x => ((thresholdFactor τ k).map Complex.ofRealHom).eval ((x : ℂ) ^ 2))
    (fun x => (thresholdIndicator τ x : ℂ))
    (by
      unfold signPolynomialError
      exact div_nonneg (pow_nonneg (by nlinarith : 0 ≤ 1 - γ ^ 2) _) (by norm_num))
  intro i
  apply threshold_complex_error k hτ hγ (hgap i)
  rw [abs_of_nonneg (matrixSingularValues_nonneg A i)]
  exact (matrixSingularValues_le_spectralNorm A i).trans hA

/-- For a matrix of operator norm at most one and `τ ∈ [0, 1]`, if its left singular values have
squared threshold gaps at least `0 < γ ≤ 1`, the lifted threshold factor evaluated on `A *
Aᴴ` approximates `leftThresholdProjection A τ` in operator norm within `signPolynomialError
γ k / 2`. -/
theorem threshold_left_gram_error_le (A : Matrix O I ℂ) {τ γ : ℝ}
    (hτ : τ ∈ Set.Icc (0 : ℝ) 1) (hγ : 0 < γ) (hγ1 : γ ≤ 1) (hA : ‖A‖ ≤ 1)
    (hgap : ∀ i : Fin (Fintype.card O), γ ≤ |(matrixSingularValues A i) ^ 2 - τ ^ 2|)
    (k : ℕ) :
    ‖aeval (A * Aᴴ) ((thresholdFactor τ k).map Complex.ofRealHom) - leftThresholdProjection A τ‖ ≤
      signPolynomialError γ k / 2 := by
  have hp : leftThresholdProjection A τ =
      leftSingularTransform A (fun x => (thresholdIndicator τ x : ℂ)) := rfl
  rw [leftGram_aeval_eq_leftSingularTransform, hp]
  apply leftSingularTransform_error_le A
    (fun x => ((thresholdFactor τ k).map Complex.ofRealHom).eval ((x : ℂ) ^ 2))
    (fun x => (thresholdIndicator τ x : ℂ))
    (by
      unfold signPolynomialError
      exact div_nonneg (pow_nonneg (by nlinarith : 0 ≤ 1 - γ ^ 2) _) (by norm_num))
  intro i
  apply threshold_complex_error k hτ hγ (hgap i)
  rw [abs_of_nonneg (matrixSingularValues_nonneg A i)]
  exact (matrixSingularValues_le_spectralNorm A i).trans hA

end Singular
end Qatlib.Concepts.WalshMoment.Forrelation
