/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreRefined
public import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtModulusTransport
public import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation

@[expose] public section

/-!
# Corollary 21 for polynomial singular-value responses

Corollary 21 of [GilyenSuLowWiebe2019] controls the singular-value
transformation of an even or odd function in terms of a modulus of
continuity and the logarithmic factor
`4 * (log (2 / δ + 1) + 1)^2`.  The public development proves the statement
for continuous responses under a rank-dependent adequacy threshold, and
separately proves the printed factor for polynomial responses on Hermitian
contractions.  This module combines those pieces into an unconditional
instance of the source corollary for real polynomial responses of even or
odd parity, using the Hermitian dilation and its block decomposition.  The
coefficient weight `polynomialResponseModulus p` is the explicit linear
modulus of continuity of the polynomial response.  The norms are the matrix
L2 operator norms, equivalently the operator norms on the corresponding
Euclidean spaces.

The general continuous-modulus statement with an arbitrary modulus `ω`
remains an open obligation: the present result covers the polynomial class,
for which the real-log factor is discharged without a rank threshold.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.QsVtStability

open Matrix Polynomial
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open scoped Matrix.Norms.L2Operator

/-- The complex-valued response induced by a real polynomial. -/
noncomputable def realPolynomialResponse (p : Polynomial ℝ) : ℝ → ℂ :=
  fun x => ((p.eval x : ℝ) : ℂ)

/-- An even real polynomial, in the unnormalised parity convention used by the
source split, induces an even complex response. -/
theorem realPolynomialResponse_even {p : Polynomial ℝ}
    (h : p.comp (-Polynomial.X) = p) :
    IsEvenFunction (realPolynomialResponse p) := by
  intro x
  have hx : p.eval (-x) = p.eval x := by
    have h' := congrArg (fun q : Polynomial ℝ => q.eval x) h
    simpa [Polynomial.eval_comp] using h'
  simp [realPolynomialResponse, hx]

/-- An odd real polynomial induces an odd complex response. -/
theorem realPolynomialResponse_odd {p : Polynomial ℝ}
    (h : p.comp (-Polynomial.X) = -p) :
    IsOddFunction (realPolynomialResponse p) := by
  intro x
  have hx : p.eval (-x) = -p.eval x := by
    have h' := congrArg (fun q : Polynomial ℝ => q.eval x) h
    simpa [Polynomial.eval_comp] using h'
  simp [realPolynomialResponse, hx]

/-- The logarithmic robustness factor is antitone on positive distances. -/
theorem modulusRobustnessFactor_antitone {δ δ₀ : ℝ} (hδ₀ : 0 < δ₀) (h : δ₀ ≤ δ) :
    modulusRobustnessFactor δ ≤ modulusRobustnessFactor δ₀ := by
  have hδ : 0 < δ := lt_of_lt_of_le hδ₀ h
  have hquot : 2 / δ ≤ 2 / δ₀ :=
    div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2) hδ₀ h
  have harg : 2 / δ + 1 ≤ 2 / δ₀ + 1 := by linarith
  have hargpos : 0 < 2 / δ + 1 := by
    have : 0 ≤ 2 / δ := div_nonneg (by norm_num) (le_of_lt hδ)
    linarith
  have hlog : Real.log (2 / δ + 1) ≤ Real.log (2 / δ₀ + 1) :=
    Real.log_le_log hargpos harg
  have hnonnegδ : 0 ≤ 2 / δ := div_nonneg (by norm_num) (le_of_lt hδ)
  have hnonnegδ₀ : 0 ≤ 2 / δ₀ := div_nonneg (by norm_num) (le_of_lt hδ₀)
  have hleft : 0 ≤ Real.log (2 / δ + 1) + 1 := by
    have : 0 ≤ Real.log (2 / δ + 1) :=
      Real.log_nonneg (by linarith)
    linarith
  have hright : 0 ≤ Real.log (2 / δ₀ + 1) + 1 := by
    have : 0 ≤ Real.log (2 / δ₀ + 1) :=
      Real.log_nonneg (by linarith)
    linarith
  have hsq : (Real.log (2 / δ + 1) + 1) ^ 2 ≤
      (Real.log (2 / δ₀ + 1) + 1) ^ 2 := by
    exact (sq_le_sq₀ hleft hright).mpr (by linarith)
  unfold modulusRobustnessFactor
  nlinarith

/-- **Corollary 21, even polynomial case.**  For an even real polynomial and
two contractions of the same rectangular shape, the right singular transforms
differ by at most the printed logarithmic factor times the polynomial response
modulus.  The constant is fixed pointwise by the input distance; no rank
threshold or adequacy hypothesis is needed. -/
theorem corollary21_evenPolynomial
    {I O : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (A B : Matrix O I ℂ) (p : Polynomial ℝ)
    (heven : p.comp (-Polynomial.X) = p)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) :
    ‖rightSingularTransform A (realPolynomialResponse p) -
        rightSingularTransform B (realPolynomialResponse p)‖ ≤
      modulusRobustnessFactor ‖A - B‖ * polynomialResponseModulus p ‖A - B‖ := by
  have hf : IsEvenFunction (realPolynomialResponse p) :=
    realPolynomialResponse_even heven
  have h22A : (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A)
      (realPolynomialResponse p)).toBlocks₂₂ =
      rightSingularTransform A (realPolynomialResponse p) := by
    rw [hermitianDilation_even_fromBlocks A (realPolynomialResponse p) hf]
    simp
  have h22B : (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B)
      (realPolynomialResponse p)).toBlocks₂₂ =
      rightSingularTransform B (realPolynomialResponse p) := by
    rw [hermitianDilation_even_fromBlocks B (realPolynomialResponse p) hf]
    simp
  rw [← h22A, ← h22B]
  have hle := dilation_block22_sub_norm_le
    (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A)
      (realPolynomialResponse p))
    (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B)
      (realPolynomialResponse p))
  have hnormA : ‖hermitianDilation A‖ ≤ 1 := by
    rw [hermitianDilation_norm]
    exact hA1
  have hnormB : ‖hermitianDilation B‖ ≤ 1 := by
    rw [hermitianDilation_norm]
    exact hB1
  have hth := hermitianFunction_polynomial_printed
    (hermitianDilation A) (hermitianDilation B)
    (hermitianDilation_adjoint A) (hermitianDilation_adjoint B) hnormA hnormB p
  rw [hermitianDilation_sub_norm] at hth
  exact hle.trans hth

/-- **Corollary 21, odd polynomial case.**  The odd singular transform obeys
the same printed bound for odd real polynomial responses. -/
theorem corollary21_oddPolynomial
    {I O : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (A B : Matrix O I ℂ) (p : Polynomial ℝ)
    (hodd : p.comp (-Polynomial.X) = -p)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) :
    ‖oddSingularTransform A (realPolynomialResponse p) -
        oddSingularTransform B (realPolynomialResponse p)‖ ≤
      modulusRobustnessFactor ‖A - B‖ * polynomialResponseModulus p ‖A - B‖ := by
  have hf : IsOddFunction (realPolynomialResponse p) :=
    realPolynomialResponse_odd hodd
  change ‖oddSingularTransform A (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) -
      oddSingularTransform B (fun x : ℝ => ((p.eval x : ℝ) : ℂ))‖ ≤
    modulusRobustnessFactor ‖A - B‖ * polynomialResponseModulus p ‖A - B‖
  exact oddSingularTransform_polynomial_printed A B p hf hA1 hB1

/-- The even/odd dichotomy of Corollary 21 packaged for a single polynomial.
The two branches are the right singular transform for even parity and the odd
singular transform for odd parity. -/
theorem corollary21_polynomialResponse
    {I O : Type} [Fintype I] [DecidableEq I] [Nonempty I]
    [Fintype O] [DecidableEq O] [Nonempty O]
    (A B : Matrix O I ℂ) (p : Polynomial ℝ)
    (_hparity : p.comp (-Polynomial.X) = p ∨ p.comp (-Polynomial.X) = -p)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) :
    (p.comp (-Polynomial.X) = p →
      ‖rightSingularTransform A (realPolynomialResponse p) -
          rightSingularTransform B (realPolynomialResponse p)‖ ≤
        modulusRobustnessFactor ‖A - B‖ * polynomialResponseModulus p ‖A - B‖) ∧
    (p.comp (-Polynomial.X) = -p →
      ‖oddSingularTransform A (realPolynomialResponse p) -
          oddSingularTransform B (realPolynomialResponse p)‖ ≤
        modulusRobustnessFactor ‖A - B‖ * polynomialResponseModulus p ‖A - B‖) := by
  refine ⟨fun heven => corollary21_evenPolynomial A B p heven hA1 hB1, ?_⟩
  exact fun hodd => corollary21_oddPolynomial A B p hodd hA1 hB1

/-- **Uniform-constant form of the even polynomial Corollary 21.** A fixed polynomial
and positive lower distance bound determine a constant that works for all matrix
dimensions and operators satisfying the stated hypotheses. -/
theorem corollary21_evenPolynomial_uniform
    (p : Polynomial ℝ) {δ₀ : ℝ} (hδ₀ : 0 < δ₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {I O : Type} [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
        [Nonempty I] [Nonempty O]
        (A B : Matrix O I ℂ),
        p.comp (-Polynomial.X) = p → ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → δ₀ ≤ ‖A - B‖ →
        ‖rightSingularTransform A (realPolynomialResponse p) -
            rightSingularTransform B (realPolynomialResponse p)‖ ≤ C * ‖A - B‖ := by
  refine ⟨1 + modulusRobustnessFactor δ₀ * polynomialLipschitzWeight p, ?_, ?_⟩
  · have hfac : 0 < modulusRobustnessFactor δ₀ :=
      lt_of_lt_of_le (by norm_num) (four_le_modulusRobustnessFactor (le_of_lt hδ₀))
    have hw : 0 ≤ polynomialLipschitzWeight p := polynomialLipschitzWeight_nonneg p
    nlinarith [mul_nonneg (le_of_lt hfac) hw]
  · intro I O _ _ _ _ _ _ A B heven hA1 hB1 hδ
    have hmain := corollary21_evenPolynomial A B p heven hA1 hB1
    have hfac := modulusRobustnessFactor_antitone hδ₀ hδ
    have hw : 0 ≤ polynomialLipschitzWeight p := polynomialLipschitzWeight_nonneg p
    have hdist : 0 ≤ ‖A - B‖ := norm_nonneg _
    have hstep : modulusRobustnessFactor ‖A - B‖ *
        polynomialResponseModulus p ‖A - B‖ ≤
        (1 + modulusRobustnessFactor δ₀ * polynomialLipschitzWeight p) * ‖A - B‖ := by
      unfold polynomialResponseModulus
      have hmono :
          modulusRobustnessFactor ‖A - B‖ * polynomialLipschitzWeight p ≤
            modulusRobustnessFactor δ₀ * polynomialLipschitzWeight p :=
        mul_le_mul_of_nonneg_right hfac hw
      have hrewrite :
          modulusRobustnessFactor ‖A - B‖ * (polynomialLipschitzWeight p * ‖A - B‖) =
            (modulusRobustnessFactor ‖A - B‖ * polynomialLipschitzWeight p) * ‖A - B‖ := by
        ring
      rw [hrewrite]
      refine (mul_le_mul_of_nonneg_right hmono hdist).trans ?_
      apply mul_le_mul_of_nonneg_right _ hdist
      linarith
    exact hmain.trans hstep

end Qatlib.Papers.QSingValue19.QsVtStability
