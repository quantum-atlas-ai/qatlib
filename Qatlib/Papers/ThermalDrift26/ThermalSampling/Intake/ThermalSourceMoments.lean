/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.ThermalSourceExponential

/-!
# Thermal Source Sign Laws and Moments

This module computes the one-step sign law and operator moments of the thermal source in
[JiangEtAl2026]. `reflectionExpectation` evaluates a reflection in the input density, and
`bornLaw_sign_thermal` shows that the sign bias at index `j` is `Real.tanh tau` times that
expectation.

The signed operator increment `logStep` has the explicit mean `logDrift` and square `tau^2*1`.
Centering by this drift gives zero mean and the operator covariance identity used for subsequent
path calculations.

## Main statements

* `bornLaw_sign_given_index` gives the conditional sign law at an index with nonzero
  probability.
* `bornLaw_logStep_mean` and `bornLaw_logStep_square_mean` compute the first two operator
  moments.
* `bornLaw_centered_mean` and `bornLaw_logStep_covariance` compute the centered mean and second
  moment.

## References

* [Jiang et al., 2026][JiangEtAl2026], *Thermal-Drift Sampling: Generating Thermal Ensembles for
  Learning Many-Body Systems*.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix
open scoped BigOperators

/-- The real part of `trace(sigma_j * rho)`, giving the reflection expectation at index `j` in
the input density. -/
def reflectionExpectation {L d : ℕ} (F : ReflectionFamily L d) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (j : Fin L) : ℝ :=
  (Matrix.trace (F.sigma j * rho.val)).re

/-- The square of a weak-reflection operator is `(1+a^2)*I + 2*sign*a*sigma_j`, with positive
sign for `false` and negative sign for `true`. -/
private theorem weakOperator_square {L d : ℕ} (F : ReflectionFamily L d) (a : ℝ)
    (j : Fin L) (b : Bool) :
    weakOperator F a j b * weakOperator F a j b =
      ((1 + a ^ 2 : ℝ) : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) +
        ((2 * (if b then -a else a) : ℝ) : ℂ) • F.sigma j := by
  cases b <;>
    simp only [weakOperator, Bool.false_eq_true, reduceIte, Matrix.add_mul, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, F.square]
  all_goals
    ext i k
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    push_cast
    ring

/-- The real trace of the weak-reflection sandwich of a density is `1+a^2 +
2*sign*a*reflectionExpectation`, with sign determined by the Boolean outcome. -/
private theorem weakOperator_trace {L d : ℕ} (F : ReflectionFamily L d) (a : ℝ)
    (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (j : Fin L) (b : Bool) :
    (Matrix.trace (weakOperator F a j b * rho.val * weakOperator F a j b)).re =
      1 + a ^ 2 + 2 * (if b then -a else a) * reflectionExpectation F rho j := by
  rw [Matrix.trace_mul_comm (weakOperator F a j b * rho.val), ← Matrix.mul_assoc,
    weakOperator_square]
  simp only [Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.trace_add,
    Matrix.trace_smul, rho.property.2, smul_eq_mul, mul_one, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rfl

/-- The probability of outcome `(j,b)` is `p_j/(2*(1+a^2))` times `1+a^2 +
2*sign*a*reflectionExpectation F rho j`, with negative sign exactly when `b` is true. -/
theorem bornLaw_sign_weak {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (a : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (j : Fin L) (b : Bool) :
    (bornLaw F p a rho).prob (j,b) =
      p.prob j / (2 * (1 + a ^ 2)) *
        (1 + a ^ 2 + 2 * (if b then -a else a) * reflectionExpectation F rho j) := by
  change Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb (idealInstrument F p a) rho.val
      (j,b) = _
  rw [Qatlib.Concepts.AdaptiveCP.BranchTrace.instrumentProb, idealInstrument_branch_weak,
      Matrix.trace_smul]
  simp only [smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  rw [weakOperator_trace]

/-- The hyperbolic identity `2*tanh(tau/2)/(1+tanh(tau/2)^2) = tanh(tau)` converts the weak-step
sign bias into the thermal one. -/
theorem thermal_sign_bias (tau : ℝ) :
    2 * Real.tanh (tau / 2) / (1 + Real.tanh (tau / 2) ^ 2) = Real.tanh tau := by
  have hc : Real.cosh (tau / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hd : Real.cosh (tau / 2) ^ 2 + Real.sinh (tau / 2) ^ 2 ≠ 0 := by
    positivity
  have ht : tau = 2 * (tau / 2) := by ring
  conv_rhs => rw [ht, Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

/-- For weak parameter `tanh(tau/2)`, the outcome probability is `p_j/2 * (1 +
sign*tanh(tau)*reflectionExpectation F rho j)`, with sign `-1` for `true` and `1` for
`false`. -/
theorem bornLaw_sign_thermal {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (j : Fin L) (b : Bool) :
    (bornLaw F p (Real.tanh (tau / 2)) rho).prob (j,b) =
      p.prob j / 2 * (1 + (if b then -1 else 1) * Real.tanh tau * reflectionExpectation F rho j) := by
  rw [bornLaw_sign_weak, ← thermal_sign_bias tau]
  have hd : 1 + Real.tanh (tau / 2) ^ 2 ≠ 0 := by positivity
  cases b <;> simp only [Bool.false_eq_true, reduceIte]
  all_goals field_simp

/-- The signed operator increment `tau*sigma_j` for a `false` outcome and `-tau*sigma_j` for a
`true` outcome. -/
def logStep {L d : ℕ} (F : ReflectionFamily L d) (tau : ℝ) (o : Fin L × Bool) : Qatlib.Foundations.PureStateMath.Operator d :=
  ((if o.2 then -tau else tau : ℝ) : ℂ) • F.sigma o.1

/-- Under the thermal Born law, the mean signed increment is `tau*tanh(tau)` times the sum of
`p_j*reflectionExpectation F rho j*sigma_j` over indices. -/
theorem bornLaw_logStep_mean {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    ∑ o : Fin L × Bool, ((bornLaw F p (Real.tanh (tau / 2)) rho).prob o : ℂ) • logStep F tau o =
      ((tau * Real.tanh tau : ℝ) : ℂ) •
        (∑ j : Fin L, ((p.prob j * reflectionExpectation F rho j : ℝ) : ℂ) • F.sigma j) := by
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Fintype.sum_bool, bornLaw_sign_thermal, bornLaw_sign_thermal]
  simp only [logStep, reduceIte, smul_smul, ← add_smul]
  congr 1
  push_cast
  ring

/-- At an index with nonzero probability, dividing the thermal joint outcome probability by
`p_j` gives `(1 + sign*tanh(tau)*reflectionExpectation F rho j)/2`. -/
theorem bornLaw_sign_given_index {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (j : Fin L) (b : Bool) (hj : p.prob j ≠ 0) :
    (bornLaw F p (Real.tanh (tau / 2)) rho).prob (j,b) / p.prob j =
      (1 + (if b then -1 else 1) * Real.tanh tau * reflectionExpectation F rho j) / 2 := by
  rw [bornLaw_sign_thermal]
  field_simp

/-- Every signed logarithmic step squares to `tau^2` times the identity, independently of the
selected index and sign. -/
theorem logStep_square {L d : ℕ} (F : ReflectionFamily L d) (tau : ℝ) (o : Fin L × Bool) :
    logStep F tau o * logStep F tau o = ((tau ^ 2 : ℝ) : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) := by
  unfold logStep
  simp only [Matrix.smul_mul, Matrix.mul_smul, F.square, smul_smul]
  congr 1
  cases o.2 <;> simp <;> ring

/-- The thermal Born expectation of `logStep*logStep` equals `tau^2` times the identity. -/
theorem bornLaw_logStep_square_mean {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    ∑ o : Fin L × Bool, ((bornLaw F p (Real.tanh (tau / 2)) rho).prob o : ℂ) •
      (logStep F tau o * logStep F tau o) = ((tau ^ 2 : ℝ) : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) := by
  simp only [logStep_square, smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_mul, ← Complex.ofReal_sum,
    (bornLaw F p (Real.tanh (tau / 2)) rho).sum_one, Complex.ofReal_one, one_mul]

/-- The state-dependent operator drift `tau*tanh(tau)` times the reflection-family sum weighted
by `p_j*reflectionExpectation F rho j`. -/
def logDrift {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : Qatlib.Foundations.PureStateMath.Operator d :=
  ((tau * Real.tanh tau : ℝ) : ℂ) •
    (∑ j : Fin L, ((p.prob j * reflectionExpectation F rho j : ℝ) : ℂ) • F.sigma j)

/-- Subtracting `logDrift` from each signed increment gives zero mean under the thermal Born
law. -/
theorem bornLaw_centered_mean {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    ∑ o : Fin L × Bool, ((bornLaw F p (Real.tanh (tau / 2)) rho).prob o : ℂ) •
      (logStep F tau o - logDrift F p tau rho) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum,
    (bornLaw F p (Real.tanh (tau / 2)) rho).sum_one, Complex.ofReal_one, one_smul,
    bornLaw_logStep_mean]
  exact sub_self _

/-- Under the thermal Born law, the mean square of the centered operator increment is `tau^2*I -
D*D`, where `D = logDrift F p tau rho`. -/
theorem bornLaw_logStep_covariance {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    ∑ o : Fin L × Bool, ((bornLaw F p (Real.tanh (tau / 2)) rho).prob o : ℂ) •
      ((logStep F tau o - logDrift F p tau rho) * (logStep F tau o - logDrift F p tau rho)) =
        ((tau ^ 2 : ℝ) : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) - logDrift F p tau rho * logDrift F p tau rho := by
  let law := bornLaw F p (Real.tanh (tau / 2)) rho
  let D := logDrift F p tau rho
  have hm : (∑ o, (law.prob o : ℂ) • logStep F tau o) = D := bornLaw_logStep_mean F p tau rho
  have he (o : Fin L × Bool) :
      (law.prob o : ℂ) • ((logStep F tau o - D) * (logStep F tau o - D)) =
        (law.prob o : ℂ) • (logStep F tau o * logStep F tau o) -
          ((law.prob o : ℂ) • logStep F tau o) * D -
          D * ((law.prob o : ℂ) • logStep F tau o) + (law.prob o : ℂ) • (D * D) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, smul_sub, Matrix.smul_mul, Matrix.mul_smul]
    abel
  change (∑ o, (law.prob o : ℂ) • ((logStep F tau o - D) * (logStep F tau o - D))) = _
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, hm, ← Finset.sum_smul, ← Complex.ofReal_sum, law.sum_one,
    Complex.ofReal_one, one_smul, bornLaw_logStep_square_mean]
  dsimp only [D]
  abel

end Qatlib.Papers.ThermalDrift26.ThermalSampling
