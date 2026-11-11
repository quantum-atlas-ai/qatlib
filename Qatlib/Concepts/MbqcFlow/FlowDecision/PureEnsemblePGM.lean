/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurement
import Qatlib.Concepts.MbqcFlow.FlowDecision.GramSquareRootBound

/-!
# Pretty-good measurement probabilities for pure ensembles

Computes the Born probabilities of `prettyGoodPOVM W` on normalized columns of `W`. The
complementary outcome has probability zero, and the labeled probabilities are squared moduli of
entries of the Gram square root.

The theorem `pure_ensemble_pgm_born_and_row_failure` also bounds the probability of an incorrect
label by the sum of squared off-diagonal Gram entries in the input row. The pure-state
measurement setting is described in [Watrous2018].

## Main statements

* `pure_ensemble_pgm_born_and_row_failure`: exact labeled probabilities and an overlap bound on
  failure.

## References

* [Watrous, 2018][Watrous2018]
-/

open Qatlib.Foundations.PureStateMath
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.MbqcFlow.FlowDecision

open Matrix
open scoped ComplexOrder MatrixOrder

/-- The real trace of the product of two pure outer products equals the squared modulus of the
vectors' inner product. -/
private theorem trace_outer_products_re {D : ℕ}
    (φ ψ : QState (Fin D)) :
    (Matrix.trace (outerProduct φ * outerProduct ψ)).re =
      Complex.normSq (∑ d, star (φ d) * ψ d) := by
  have hconj : (∑ d, φ d * star (ψ d)) =
      (starRingEnd ℂ) (∑ d, star (φ d) * ψ d) := by
    rw [map_sum (starRingEnd ℂ) (fun d => star (φ d) * ψ d) Finset.univ]
    apply Finset.sum_congr rfl
    intro d _
    rw [map_mul]
    change φ d * star (ψ d) = star (star (φ d)) * star (ψ d)
    rw [star_star]
  have htrace : Matrix.trace (outerProduct φ * outerProduct ψ) =
      ((Complex.normSq (∑ d, star (φ d) * ψ d) : ℝ) : ℂ) := by
    calc
      Matrix.trace (outerProduct φ * outerProduct ψ) =
          (∑ d, φ d * star (ψ d)) * (∑ e, star (φ e) * ψ e) := by
        simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
          outerProduct_apply, Finset.sum_mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        apply Finset.sum_congr rfl
        intro e _
        change (φ d * star (φ e)) * (ψ e * star (ψ d)) =
          (φ d * star (ψ d)) * (star (φ e) * ψ e)
        ring
      _ = (starRingEnd ℂ) (∑ d, star (φ d) * ψ d) *
          (∑ d, star (φ d) * ψ d) := by rw [hconj]
      _ = ((Complex.normSq (∑ d, star (φ d) * ψ d) : ℝ) : ℂ) := by
        rw [mul_comm, Complex.mul_conj]
  rw [htrace]
  rfl

/-- A normalized column of `W` gives diagonal Gram entry one. -/
private theorem normalized_ensemble_gram_diagonal
    {I : Type} [Fintype I] [DecidableEq I] {D : ℕ}
    (W : Matrix (Fin D) I ℂ) (i : I)
    (hi : Normalized (fun d => W d i)) :
    (ensembleGram W).mat i i = 1 := by
  have hterm : ∀ d : Fin D,
      (starRingEnd ℂ) (W d i) * W d i = ((‖W d i‖ ^ 2 : ℝ) : ℂ) := by
    intro d
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
  change (Wᴴ * W) i i = 1
  calc
    (Wᴴ * W) i i = ((∑ d, ‖W d i‖ ^ 2 : ℝ) : ℂ) := by
      rw [Matrix.mul_apply, Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro d _
      exact hterm d
    _ = 1 := by exact_mod_cast hi

/-- If a Gram diagonal entry is one, the squared moduli in the corresponding Gram-square-root
column sum to one. -/
private theorem normalized_ensemble_sqrt_column_sum
    {I : Type} [Fintype I] [DecidableEq I] {D : ℕ}
    (W : Matrix (Fin D) I ℂ) (i : I)
    (hi : (ensembleGram W).mat i i = 1) :
    ∑ j : I, Complex.normSq ((ensembleGram W).sqrt.mat j i) = 1 := by
  have hsq : (ensembleGram W).sqrt.matᴴ * (ensembleGram W).sqrt.mat =
      (ensembleGram W).mat := by
    rw [HermitianMat.conjTranspose_mat]
    exact HermitianMat.sqrt_sq (ensembleGram_nonneg W)
  have hsum : ((∑ j : I, Complex.normSq ((ensembleGram W).sqrt.mat j i) : ℝ) : ℂ) =
      1 := by
    calc
      ((∑ j : I, Complex.normSq ((ensembleGram W).sqrt.mat j i) : ℝ) : ℂ) =
          ((ensembleGram W).sqrt.matᴴ * (ensembleGram W).sqrt.mat) i i := by
        rw [Complex.ofReal_sum, Matrix.mul_apply]
        apply Finset.sum_congr rfl
        intro j _
        change ((Complex.normSq ((ensembleGram W).sqrt.mat j i) : ℝ) : ℂ) =
          (starRingEnd ℂ) ((ensembleGram W).sqrt.mat j i) *
            (ensembleGram W).sqrt.mat j i
        exact Complex.normSq_eq_conj_mul_self
      _ = (ensembleGram W).mat i i := congrArg (fun A => A i i) hsq
      _ = 1 := hi
  simpa only [Complex.ofReal_re, Complex.one_re] using congrArg Complex.re hsum

/-- For normalized ensemble columns, proves that the input outer product is a density operator,
the complementary PGM outcome has zero probability, and labeled Born probabilities are
squared Gram-square-root entries. The failure probability is bounded by the sum of squared
off-diagonal Gram entries in the input row. -/
theorem pure_ensemble_pgm_born_and_row_failure
    (I : Type) [Fintype I] [DecidableEq I] (D : ℕ)
    (W : Matrix (Fin D) I ℂ)
    (hW : ∀ i : I, Normalized (fun d => W d i)) (i : I) :
    let ρ := outerProduct (fun d => W d i)
    let J := Instrument.ofPOVM (prettyGoodPOVM W)
    IsDensityOperator ρ ∧ instrumentProb J ρ none = 0 ∧
      (∀ j : I, instrumentProb J ρ (some j) =
        Complex.normSq ((ensembleGram W).sqrt.mat j i)) ∧
      1 - instrumentProb J ρ (some i) ≤
        ∑ j ∈ Finset.univ.erase i, Complex.normSq ((ensembleGram W).mat i j) := by
  let ρ := outerProduct (fun d => W d i)
  let J := Instrument.ofPOVM (prettyGoodPOVM W)
  have hρ : IsDensityOperator ρ := isDensityOperator_outerProduct (hW i)
  have hdiag : (ensembleGram W).mat i i = 1 :=
    normalized_ensemble_gram_diagonal W i (hW i)
  have hborn : ∀ j : I, instrumentProb J ρ (some j) =
      Complex.normSq ((ensembleGram W).sqrt.mat j i) := by
    intro j
    rw [instrumentProb_ofPOVM]
    change (Matrix.trace (outerProduct (fun d => prettyGoodFrame W d j) *
      outerProduct (fun d => W d i))).re = _
    rw [trace_outer_products_re]
    have hentry : (∑ d, star (prettyGoodFrame W d j) * W d i) =
        (ensembleGram W).sqrt.mat j i := by
      simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply] using
        congrArg (fun A => A j i) (pretty_good_frame_support_contract I D W).1
    rw [hentry]
  have hconclusive : ∑ j : I, instrumentProb J ρ (some j) = 1 := by
    simpa only [hborn] using normalized_ensemble_sqrt_column_sum W i hdiag
  have htotal := sum_instrumentProb_isDensityOperator J hρ
  rw [Fintype.sum_option, hconclusive] at htotal
  have hreject : instrumentProb J ρ none = 0 := by linarith
  have hfailure : 1 - instrumentProb J ρ (some i) ≤
      ∑ j ∈ Finset.univ.erase i, Complex.normSq ((ensembleGram W).mat i j) := by
    rw [hborn]
    exact gram_square_root_row_failure_bound I (ensembleGram W)
      (ensembleGram_nonneg W) i hdiag
  exact ⟨hρ, hreject, hborn, hfailure⟩

end Qatlib.Concepts.MbqcFlow.FlowDecision
