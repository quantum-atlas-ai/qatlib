/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ThermalDrift26.ThermalSampling.Intake.ThermalSourceExponential
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option warningAsError false
noncomputable section
namespace Qatlib.Papers.ThermalDrift26.ThermalSampling
open Qatlib Matrix
open scoped BigOperators

def reflectionExpectation {L d : ℕ} (F : ReflectionFamily L d) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (j : Fin L) : ℝ :=
  (Matrix.trace (F.sigma j * rho.val)).re

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

theorem thermal_sign_bias (tau : ℝ) :
    2 * Real.tanh (tau / 2) / (1 + Real.tanh (tau / 2) ^ 2) = Real.tanh tau := by
  have hc : Real.cosh (tau / 2) ≠ 0 := ne_of_gt (Real.cosh_pos _)
  have hd : Real.cosh (tau / 2) ^ 2 + Real.sinh (tau / 2) ^ 2 ≠ 0 := by
    positivity
  have ht : tau = 2 * (tau / 2) := by ring
  conv_rhs => rw [ht, Real.tanh_eq_sinh_div_cosh, Real.sinh_two_mul, Real.cosh_two_mul]
  rw [Real.tanh_eq_sinh_div_cosh]
  field_simp

theorem bornLaw_sign_thermal {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (j : Fin L) (b : Bool) :
    (bornLaw F p (Real.tanh (tau / 2)) rho).prob (j,b) =
      p.prob j / 2 * (1 + (if b then -1 else 1) * Real.tanh tau * reflectionExpectation F rho j) := by
  rw [bornLaw_sign_weak, ← thermal_sign_bias tau]
  have hd : 1 + Real.tanh (tau / 2) ^ 2 ≠ 0 := by positivity
  cases b <;> simp only [Bool.false_eq_true, reduceIte]
  all_goals field_simp

def logStep {L d : ℕ} (F : ReflectionFamily L d) (tau : ℝ) (o : Fin L × Bool) : Qatlib.Foundations.PureStateMath.Operator d :=
  ((if o.2 then -tau else tau : ℝ) : ℂ) • F.sigma o.1

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

theorem bornLaw_sign_given_index {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) (j : Fin L) (b : Bool) (hj : p.prob j ≠ 0) :
    (bornLaw F p (Real.tanh (tau / 2)) rho).prob (j,b) / p.prob j =
      (1 + (if b then -1 else 1) * Real.tanh tau * reflectionExpectation F rho j) / 2 := by
  rw [bornLaw_sign_thermal]
  field_simp

theorem logStep_square {L d : ℕ} (F : ReflectionFamily L d) (tau : ℝ) (o : Fin L × Bool) :
    logStep F tau o * logStep F tau o = ((tau ^ 2 : ℝ) : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) := by
  unfold logStep
  simp only [Matrix.smul_mul, Matrix.mul_smul, F.square, smul_smul]
  congr 1
  cases o.2 <;> simp <;> ring

theorem bornLaw_logStep_square_mean {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    ∑ o : Fin L × Bool, ((bornLaw F p (Real.tanh (tau / 2)) rho).prob o : ℂ) •
      (logStep F tau o * logStep F tau o) = ((tau ^ 2 : ℝ) : ℂ) • (1 : Qatlib.Foundations.PureStateMath.Operator d) := by
  simp only [logStep_square, smul_smul]
  rw [← Finset.sum_smul, ← Finset.sum_mul, ← Complex.ofReal_sum,
    (bornLaw F p (Real.tanh (tau / 2)) rho).sum_one, Complex.ofReal_one, one_mul]

def logDrift {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) : Qatlib.Foundations.PureStateMath.Operator d :=
  ((tau * Real.tanh tau : ℝ) : ℂ) •
    (∑ j : Fin L, ((p.prob j * reflectionExpectation F rho j : ℝ) : ℂ) • F.sigma j)

theorem bornLaw_centered_mean {L d : ℕ} (F : ReflectionFamily L d) (p : Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist (Fin L))
    (tau : ℝ) (rho : Qatlib.Foundations.PureStateMath.DensityOperator d) :
    ∑ o : Fin L × Bool, ((bornLaw F p (Real.tanh (tau / 2)) rho).prob o : ℂ) •
      (logStep F tau o - logDrift F p tau rho) = 0 := by
  simp only [smul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_smul, ← Complex.ofReal_sum,
    (bornLaw F p (Real.tanh (tau / 2)) rho).sum_one, Complex.ofReal_one, one_smul,
    bornLaw_logStep_mean]
  exact sub_self _

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
