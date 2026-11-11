/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreDefs
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtModulusTransport

/-!
# Polynomial transport and rectangle approximation bounds

This module proves scalar and matrix perturbation bounds for polynomial responses using
`polynomialLipschitzWeight`. It transfers these bounds through Hermitian dilations and odd
singular-value transforms and proves that two translated sign approximations satisfy
`RectangleBand`. Background and related constructions are discussed in [GilyenSuLowWiebe2019].

## Main statements

* `abs_polynomial_eval_sub_le`: a scalar Lipschitz bound on the unit interval.
* `oddSingularTransform_polynomial_transport`: a polynomial perturbation bound for contractions.
* `rectangle_from_sign`: derives rectangle bands from a sign approximation.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QsvtCore.PhaseExistence

namespace Qatlib.Concepts.QsvtCore.ApproxToolkit

open Polynomial
open scoped Classical BigOperators
open Qatlib.Concepts.QsvtCore.ApproxToolkit

open scoped Matrix.Norms.L2Operator

open Qatlib
open Qatlib
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.PhaseExistence.GslwSourceQsvt.GslwSourceQsvt
open Qatlib.Concepts.QsvtCore.ApproxToolkit
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
set_option warningAsError false

/-- The coefficient-weighted polynomial Lipschitz bound is nonnegative. -/
theorem polynomialLipschitzWeight_nonneg (p : Polynomial ℝ) :
    0 ≤ polynomialLipschitzWeight p := by
  unfold polynomialLipschitzWeight
  exact Finset.sum_nonneg fun k hk =>
    mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)

/-- For real `x` and `y` in [−1, 1], the difference of their `k`th powers has absolute value at
most k|x − y|. -/
theorem abs_pow_sub_le (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) (k : ℕ) :
    |x ^ k - y ^ k| ≤ (k : ℝ) * |x - y| := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hkey : x ^ (k + 1) - y ^ (k + 1) = (x ^ k - y ^ k) * x + y ^ k * (x - y) := by
      rw [pow_succ, pow_succ]
      ring
    rw [hkey]
    refine (abs_add_le _ _).trans ?_
    have h1 : |(x ^ k - y ^ k) * x| ≤ (k : ℝ) * |x - y| := by
      rw [abs_mul]
      calc |x ^ k - y ^ k| * |x| ≤ (k : ℝ) * |x - y| * |x| :=
            mul_le_mul_of_nonneg_right ih (abs_nonneg _)
        _ ≤ (k : ℝ) * |x - y| := by
            have hstep : |x| * ((k : ℝ) * |x - y|) ≤ 1 * ((k : ℝ) * |x - y|) :=
              mul_le_mul_of_nonneg_right hx (mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
            calc (k : ℝ) * |x - y| * |x| = |x| * ((k : ℝ) * |x - y|) := by ring
              _ ≤ 1 * ((k : ℝ) * |x - y|) := hstep
              _ = (k : ℝ) * |x - y| := by ring
    have h2 : |y ^ k * (x - y)| ≤ |x - y| := by
      rw [abs_mul]
      have hyk : |y ^ k| ≤ 1 := by
        rw [abs_pow]
        exact pow_le_one₀ (by simpa using! hy.le) (by simpa using! hy)
      have hstep : |y ^ k| * |x - y| ≤ 1 * |x - y| :=
        mul_le_mul_of_nonneg_right hyk (abs_nonneg _)
      simpa only [one_mul] using! hstep
    have h3 : (k : ℝ) * |x - y| + |x - y| = ((k + 1 : ℕ) : ℝ) * |x - y| := by
      push_cast
      ring
    exact (add_le_add h1 h2).trans (le_of_eq h3)

/-- On [−1, 1], the difference of two polynomial values is bounded by `polynomialLipschitzWeight
p` times the distance between the inputs. -/
theorem abs_polynomial_eval_sub_le (p : Polynomial ℝ) (x y : ℝ) (hx : |x| ≤ 1) (hy : |y| ≤ 1) :
    |p.eval x - p.eval y| ≤ polynomialLipschitzWeight p * |x - y| := by
  have hexp : p.eval x - p.eval y =
      ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (x ^ k - y ^ k) := by
    rw [Polynomial.eval_eq_sum_range, Polynomial.eval_eq_sum_range, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun k hk => by rw [mul_sub])
  have hsum : ‖∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (x ^ k - y ^ k)‖ ≤
      ∑ k ∈ Finset.range (p.natDegree + 1), ‖p.coeff k * (x ^ k - y ^ k)‖ :=
    norm_sum_le _ _
  have hterm (k : ℕ) (hk : k ∈ Finset.range (p.natDegree + 1)) :
      ‖p.coeff k * (x ^ k - y ^ k)‖ ≤ (k : ℝ) * |p.coeff k| * |x - y| := by
    simp only [norm_mul, Real.norm_eq_abs]
    have h1 := abs_pow_sub_le x y hx hy k
    calc |p.coeff k| * |x ^ k - y ^ k| ≤ |p.coeff k| * ((k : ℝ) * |x - y|) :=
            mul_le_mul_of_nonneg_left (abs_pow_sub_le x y hx hy k) (abs_nonneg _)
      _ = (k : ℝ) * |p.coeff k| * |x - y| := by ring
  have hfin : (∑ k ∈ Finset.range (p.natDegree + 1), (k : ℝ) * |p.coeff k| * |x - y|) =
      polynomialLipschitzWeight p * |x - y| := by
    unfold polynomialLipschitzWeight
    calc (∑ k ∈ Finset.range (p.natDegree + 1), (k : ℝ) * |p.coeff k| * |x - y|)
        = (∑ k ∈ Finset.range (p.natDegree + 1), (k : ℝ) * |p.coeff k|) * |x - y| := by
          rw [Finset.sum_mul]
      _ = polynomialLipschitzWeight p * |x - y| := rfl
  rw [hexp]
  exact hsum.trans ((Finset.sum_le_sum fun k hk => hterm k hk).trans (le_of_eq hfin))

/-- The function `polynomialResponseModulus p` is a modulus of continuity for the complex-valued
cast of the real polynomial response. -/
theorem polynomial_response_modulus (p : Polynomial ℝ) :
    ModulusOfContinuity (fun x : ℝ => ((p.eval x : ℝ) : ℂ))
      (polynomialResponseModulus p) := by
  have hw : 0 ≤ polynomialLipschitzWeight p := polynomialLipschitzWeight_nonneg p
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    exact mul_le_mul_of_nonneg_left hab hw
  · unfold polynomialResponseModulus
    simp
  · intro x y hx hy
    rw [← Complex.ofReal_sub, Complex.norm_real]
    refine (abs_polynomial_eval_sub_le p x y ?_ ?_).trans ?_
    · rcases Set.mem_Icc.mp hx with ⟨hx1, hx2⟩
      exact abs_le.mpr ⟨hx1, hx2⟩
    · rcases Set.mem_Icc.mp hy with ⟨hy1, hy2⟩
      exact abs_le.mpr ⟨hy1, hy2⟩
    · unfold polynomialResponseModulus
      exact le_rfl

/-- For contraction matrices `A` and `B`, polynomial functional calculus on their Hermitian
dilations differs in operator norm by at most `polynomialLipschitzWeight p * ‖A - B‖`. -/
theorem dilationPolynomialResponseTransport {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A B : Matrix O I ℂ) (p : Polynomial ℝ)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) :
    ‖hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A)
        (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) -
      hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B)
        (fun x : ℝ => ((p.eval x : ℝ) : ℂ))‖ ≤
      polynomialLipschitzWeight p * ‖A - B‖ := by
  have hpoly := polynomial_sub_norm_le (hermitianDilation A) (hermitianDilation B)
    (hermitianDilation_adjoint A) (hermitianDilation_adjoint B)
    (by rw [hermitianDilation_norm]; exact hA1)
    (by rw [hermitianDilation_norm]; exact hB1) p
  rw [hermitianDilation_sub_norm] at hpoly
  exact hpoly

/-- For an odd real polynomial response and contraction matrices `A` and `B`, the odd singular
transforms differ by at most `polynomialLipschitzWeight p * ‖A - B‖`. -/
theorem oddSingularTransform_polynomial_transport {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A B : Matrix O I ℂ) (p : Polynomial ℝ)
    (hodd : IsOddFunction (fun x : ℝ => ((p.eval x : ℝ) : ℂ)))
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) :
    ‖oddSingularTransform A (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) -
      oddSingularTransform B (fun x : ℝ => ((p.eval x : ℝ) : ℂ))‖ ≤
      polynomialLipschitzWeight p * ‖A - B‖ := by
  set f : ℝ → ℂ := fun x : ℝ => ((p.eval x : ℝ) : ℂ) with hfdef
  have h12A : (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f).toBlocks₁₂
      = oddSingularTransform A f := by
    rw [hermitianDilation_odd_fromBlocks A f hodd]
    simp
  have h12B : (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f).toBlocks₁₂
      = oddSingularTransform B f := by
    rw [hermitianDilation_odd_fromBlocks B f hodd]
    simp
  rw [← h12A, ← h12B]
  have hle := dilation_block12_sub_norm_le
    (hermitianFunction (hermitianDilation A) (hermitianDilation_adjoint A) f)
    (hermitianFunction (hermitianDilation B) (hermitianDilation_adjoint B) f)
  have htr := dilationPolynomialResponseTransport A B p hA1 hB1
  simpa [hfdef] using! hle.trans htr

/-- For Hermitian contractions, the polynomial functional-calculus difference is bounded by
`modulusRobustnessFactor` times `polynomialResponseModulus`, both evaluated at the input
distance. -/
theorem hermitianFunction_polynomial_printed {I : Type} [Fintype I] [DecidableEq I]
    (A B : Matrix I I ℂ) (hA : A.IsHermitian) (hB : B.IsHermitian)
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) (p : Polynomial ℝ) :
    ‖hermitianFunction A hA (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) -
      hermitianFunction B hB (fun x : ℝ => ((p.eval x : ℝ) : ℂ))‖ ≤
      modulusRobustnessFactor ‖A - B‖ * polynomialResponseModulus p ‖A - B‖ := by
  have hpoly := polynomial_sub_norm_le A B hA hB hA1 hB1 p
  have hw : 0 ≤ polynomialLipschitzWeight p := polynomialLipschitzWeight_nonneg p
  have hfac : (1 : ℝ) ≤ modulusRobustnessFactor ‖A - B‖ :=
    le_trans (le_of_lt (by norm_num)) (four_le_modulusRobustnessFactor (norm_nonneg _))
  have hmain : polynomialLipschitzWeight p * ‖A - B‖ ≤
      modulusRobustnessFactor ‖A - B‖ * (polynomialLipschitzWeight p * ‖A - B‖) := by
    have hnonneg : (0 : ℝ) ≤ polynomialLipschitzWeight p * ‖A - B‖ :=
      mul_nonneg hw (norm_nonneg _)
    calc polynomialLipschitzWeight p * ‖A - B‖ =
        (polynomialLipschitzWeight p * ‖A - B‖) * 1 := by ring
      _ ≤ (polynomialLipschitzWeight p * ‖A - B‖) * modulusRobustnessFactor ‖A - B‖ :=
        mul_le_mul_of_nonneg_left hfac hnonneg
      _ = modulusRobustnessFactor ‖A - B‖ * (polynomialLipschitzWeight p * ‖A - B‖) := by ring
  have hlast : modulusRobustnessFactor ‖A - B‖ *
      (polynomialLipschitzWeight p * ‖A - B‖) =
      modulusRobustnessFactor ‖A - B‖ * polynomialResponseModulus p ‖A - B‖ := by
    unfold polynomialResponseModulus
    ring
  exact hpoly.trans (hmain.trans (le_of_eq hlast))

/-- For an odd polynomial response on contractions, the odd singular-transform difference
satisfies the product bound given by `modulusRobustnessFactor` and
`polynomialResponseModulus` at the input distance. -/
theorem oddSingularTransform_polynomial_printed {O I : Type} [Fintype O] [Fintype I]
    [DecidableEq O] [DecidableEq I] (A B : Matrix O I ℂ) (p : Polynomial ℝ)
    (hodd : IsOddFunction (fun x : ℝ => ((p.eval x : ℝ) : ℂ)))
    (hA1 : ‖A‖ ≤ 1) (hB1 : ‖B‖ ≤ 1) :
    ‖oddSingularTransform A (fun x : ℝ => ((p.eval x : ℝ) : ℂ)) -
      oddSingularTransform B (fun x : ℝ => ((p.eval x : ℝ) : ℂ))‖ ≤
      modulusRobustnessFactor ‖A - B‖ * polynomialResponseModulus p ‖A - B‖ := by
  have htr := oddSingularTransform_polynomial_transport A B p hodd hA1 hB1
  have hw : 0 ≤ polynomialLipschitzWeight p := polynomialLipschitzWeight_nonneg p
  have hfac : (1 : ℝ) ≤ modulusRobustnessFactor ‖A - B‖ :=
    le_trans (le_of_lt (by norm_num)) (four_le_modulusRobustnessFactor (norm_nonneg _))
  have hmain : polynomialLipschitzWeight p * ‖A - B‖ ≤
      modulusRobustnessFactor ‖A - B‖ * (polynomialLipschitzWeight p * ‖A - B‖) := by
    have hnonneg : (0 : ℝ) ≤ polynomialLipschitzWeight p * ‖A - B‖ :=
      mul_nonneg hw (norm_nonneg _)
    calc polynomialLipschitzWeight p * ‖A - B‖ =
        (polynomialLipschitzWeight p * ‖A - B‖) * 1 := by ring
      _ ≤ (polynomialLipschitzWeight p * ‖A - B‖) * modulusRobustnessFactor ‖A - B‖ :=
        mul_le_mul_of_nonneg_left hfac hnonneg
      _ = modulusRobustnessFactor ‖A - B‖ * (polynomialLipschitzWeight p * ‖A - B‖) := by ring
  have hlast : modulusRobustnessFactor ‖A - B‖ *
      (polynomialLipschitzWeight p * ‖A - B‖) =
      modulusRobustnessFactor ‖A - B‖ * polynomialResponseModulus p ‖A - B‖ := by
    unfold polynomialResponseModulus
    ring
  exact htr.trans (hmain.trans (le_of_eq hlast))

/-- Evaluating the rectangle polynomial yields ((1 − ε₀)/2)(S(x + t) + S(t − x)) + ε₀. -/
theorem rectanglePolynomial_eval (S : Polynomial ℝ) (ε₀ t x : ℝ) :
    (rectanglePolynomial S ε₀ t).eval x =
      ((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x)) + ε₀ := by
  simp only [rectanglePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C]
  rw [Polynomial.eval_comp, Polynomial.eval_comp]
  simp only [Polynomial.eval_add, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X]

/-- The rectangle polynomial response is even for every input polynomial and all real
parameters. -/
theorem rectanglePolynomial_even (S : Polynomial ℝ) (ε₀ t x : ℝ) :
    (rectanglePolynomial S ε₀ t).eval (-x) = (rectanglePolynomial S ε₀ t).eval x := by
  rw [rectanglePolynomial_eval, rectanglePolynomial_eval]
  congr 1
  ring

/-- A sign approximation takes values in [1 − σ, 1 + σ] at positive points in [−2, 2] outside
the gap. -/
theorem signApprox_pos {S : Polynomial ℝ} {δ σ : ℝ} (hS : SignApproximation S δ σ)
    {y : ℝ} (hy2 : |y| ≤ 2) (hyδ : δ ≤ |y|) (hypos : 0 < y) :
    1 - σ ≤ S.eval y ∧ S.eval y ≤ 1 + σ := by
  have h := hS.2.1 y hy2 hyδ
  rw [Real.sign_of_pos hypos] at h
  have h' := abs_le.mp h
  constructor <;> linarith

/-- A sign approximation takes values in [−1 − σ, −1 + σ] at negative points in [−2, 2] outside
the gap. -/
theorem signApprox_neg {S : Polynomial ℝ} {δ σ : ℝ} (hS : SignApproximation S δ σ)
    {y : ℝ} (hy2 : |y| ≤ 2) (hyδ : δ ≤ |y|) (hyneg : y < 0) :
    -1 - σ ≤ S.eval y ∧ S.eval y ≤ -1 + σ := by
  have h := hS.2.1 y hy2 hyδ
  rw [Real.sign_of_neg hyneg] at h
  have h' := abs_le.mp h
  constructor <;> linarith

/-- For 0 < ε₀ < 1, positive gap, and 0 ≤ t with t + δ ≤ 1, two translated sign approximations
satisfy `RectangleBand` with band error (1 − ε₀)σ. -/
theorem rectangle_from_sign {S : Polynomial ℝ} {ε₀ δ t σ : ℝ}
    (hε0 : 0 < ε₀) (hε01 : ε₀ < 1) (hδ : 0 < δ) (ht : 0 ≤ t) (htδ : t + δ ≤ 1)
    (hS : SignApproximation S δ σ) :
    RectangleBand (rectanglePolynomial S ε₀ t) ε₀ δ t ((1 - ε₀) * σ) := by
  have htn : t ≤ 1 := by linarith
  have hc : 0 ≤ (1 - ε₀) / 2 := by linarith
  have hmul_lo : ((1 - ε₀) / 2) * (-2 * σ) = -((1 - ε₀) * σ) := by ring
  have hmul_hi : ((1 - ε₀) / 2) * (2 * σ) = (1 - ε₀) * σ := by ring
  have ht2 : |t| ≤ 2 := by
    rw [abs_le]
    constructor <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rw [rectanglePolynomial_eval]
    have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
    have hxt : |x + t| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    have htx : |t - x| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith
    have h1 : |S.eval (x + t)| ≤ 1 := hS.1 (x + t) hxt
    have h2 : |S.eval (t - x)| ≤ 1 := hS.1 (t - x) htx
    calc |((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x)) + ε₀|
        ≤ |((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x))| + |ε₀| := abs_add_le _ _
      _ = |(1 - ε₀) / 2| * |S.eval (x + t) + S.eval (t - x)| + |ε₀| := by rw [abs_mul]
      _ ≤ ((1 - ε₀) / 2) * (|S.eval (x + t)| + |S.eval (t - x)|) + ε₀ := by
          rw [abs_of_nonneg hc, abs_of_nonneg (le_of_lt hε0)]
          exact add_le_add (mul_le_mul_of_nonneg_left (abs_add_le _ _) hc) (le_refl _)
      _ ≤ (1 - ε₀) + ε₀ := by
          have hsum : |S.eval (x + t)| + |S.eval (t - x)| ≤ 2 := by linarith
          calc ((1 - ε₀) / 2) * (|S.eval (x + t)| + |S.eval (t - x)|) + ε₀
              ≤ ((1 - ε₀) / 2) * 2 + ε₀ := by
                  exact add_le_add (mul_le_mul_of_nonneg_left hsum hc) (le_refl _)
            _ = (1 - ε₀) + ε₀ := by ring
      _ = 1 := by ring
  · intro x hx hband
    rw [rectanglePolynomial_eval]
    have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
    rcases hband with hleft | hright
    · have hxtneg : x + t < 0 := by linarith
      have hxtδ : δ ≤ |x + t| := by
        rw [abs_of_nonpos (le_of_lt hxtneg)]
        linarith
      have htxpos : 0 < t - x := by linarith
      have htxδ : δ ≤ |t - x| := by
        rw [abs_of_nonneg (le_of_lt htxpos)]
        linarith
      have h1 := signApprox_neg hS (by
        rw [abs_le]; constructor <;> linarith) hxtδ hxtneg
      have h2 := signApprox_pos hS (by
        rw [abs_le]; constructor <;> linarith) htxδ htxpos
      have hsumlo : -2 * σ ≤ S.eval (x + t) + S.eval (t - x) := by linarith
      have hsumhi : S.eval (x + t) + S.eval (t - x) ≤ 2 * σ := by linarith
      have hlo : ((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x)) ≥ -((1 - ε₀) * σ) := by
        rw [← hmul_lo]
        exact mul_le_mul_of_nonneg_left hsumlo hc
      have hhi : ((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x)) ≤ (1 - ε₀) * σ := by
        rw [← hmul_hi]
        exact mul_le_mul_of_nonneg_left hsumhi hc
      constructor <;> linarith
    · have htxneg : t - x < 0 := by linarith
      have htxδ : δ ≤ |t - x| := by
        rw [abs_of_nonpos (le_of_lt htxneg)]
        linarith
      have hxtpos : 0 < x + t := by linarith
      have hxtδ : δ ≤ |x + t| := by
        rw [abs_of_nonneg (le_of_lt hxtpos)]
        linarith
      have h1 := signApprox_pos hS (by
        rw [abs_le]; constructor <;> linarith) hxtδ hxtpos
      have h2 := signApprox_neg hS (by
        rw [abs_le]; constructor <;> linarith) htxδ htxneg
      have hsumlo : -2 * σ ≤ S.eval (x + t) + S.eval (t - x) := by linarith
      have hsumhi : S.eval (x + t) + S.eval (t - x) ≤ 2 * σ := by linarith
      have hlo : ((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x)) ≥ -((1 - ε₀) * σ) := by
        rw [← hmul_lo]
        exact mul_le_mul_of_nonneg_left hsumlo hc
      have hhi : ((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x)) ≤ (1 - ε₀) * σ := by
        rw [← hmul_hi]
        exact mul_le_mul_of_nonneg_left hsumhi hc
      constructor <;> linarith
  · intro x hx hband
    rw [rectanglePolynomial_eval]
    have hx' : -1 ≤ x ∧ x ≤ 1 := abs_le.mp hx
    have hxtpos : 0 < x + t := by linarith
    have hxtδ : δ ≤ |x + t| := by
      rw [abs_of_nonneg (le_of_lt hxtpos)]
      linarith
    have htxpos : 0 < t - x := by linarith
    have htxδ : δ ≤ |t - x| := by
      rw [abs_of_nonneg (le_of_lt htxpos)]
      linarith
    have h1 := signApprox_pos hS (by
      rw [abs_le]; constructor <;> linarith) hxtδ hxtpos
    have h2 := signApprox_pos hS (by
      rw [abs_le]; constructor <;> linarith) htxδ htxpos
    have hsumlo : 2 - 2 * σ ≤ S.eval (x + t) + S.eval (t - x) := by linarith
    have hsumhi : S.eval (x + t) + S.eval (t - x) ≤ 2 + 2 * σ := by linarith
    have hlo : ((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x)) ≥ (1 - ε₀) - ((1 - ε₀) * σ) := by
      calc (1 - ε₀) / 2 * (S.eval (x + t) + S.eval (t - x))
          ≥ (1 - ε₀) / 2 * (2 - 2 * σ) := mul_le_mul_of_nonneg_left hsumlo hc
        _ = (1 - ε₀) - ((1 - ε₀) * σ) := by ring
    have hhi : ((1 - ε₀) / 2) * (S.eval (x + t) + S.eval (t - x)) ≤ (1 - ε₀) + ((1 - ε₀) * σ) := by
      calc (1 - ε₀) / 2 * (S.eval (x + t) + S.eval (t - x))
          ≤ (1 - ε₀) / 2 * (2 + 2 * σ) := mul_le_mul_of_nonneg_left hsumhi hc
        _ = (1 - ε₀) + ((1 - ε₀) * σ) := by ring
    constructor <;> linarith

end Qatlib.Concepts.QsvtCore.ApproxToolkit
