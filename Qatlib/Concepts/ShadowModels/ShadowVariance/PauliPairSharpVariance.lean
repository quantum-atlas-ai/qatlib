/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ShadowModels.ShadowChannel.PauliRealMoments

/-!
# Sharp variance bounds for Pauli pair shadows

This module bounds the conditional and kernel variances of Pauli pair shadow estimators using
their two support sizes and observable norm. It supplies the variance estimates used for
quadratic classical-shadow sample budgets [HuangKuengPreskill2020].

## Main statements

* `pauli_pair_conditional_variance_sharp`: conditional variance controlled by the larger
  support.
* `pauli_pair_raw_second_moment_bound`: second-moment bound for the unsymmetrized kernel.
* `pauli_pair_sharp_variances`: the combined bounds under the norm lower bound.

## References

* [Huang, Kueng, and Preskill, 2020][HuangKuengPreskill2020]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Concepts.ShadowModels.FairBitRecords
open Qatlib.Concepts.ShadowModels.ShadowChannel
open Qatlib.Concepts.ShadowModels.UStatBackend
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace Qatlib.Concepts.ShadowModels.ShadowVariance
open Matrix Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Taking the state expectation in either register of a Pauli pair observable yields a real
sparse Pauli observable whose norm is at most the original norm. -/
theorem pauli_pair_partial_norm (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ) :
    ‖realSparsePauliObservable (fun j => (ww j).1)
      (fun j => (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).2 * ρ)).re)‖ ≤
      ‖pauliPairObservable n q ww c‖ ∧
    ‖realSparsePauliObservable (fun j => (ww j).2)
      (fun j => (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).1 * ρ)).re)‖ ≤
      ‖pauliPairObservable n q ww c‖ := by
  have hreal (w : Fin n → Option (Fin 3)) :
      ((Matrix.trace (tensorPauliWord n w * ρ)).re : ℂ) =
        Matrix.trace (tensorPauliWord n w * ρ) := by
    apply Complex.ext
    · rfl
    · simp only [Complex.ofReal_im,
        pauli_pair_hermitian_trace_real _ _ (pauli_pair_word_hermitian _ _) hρ.1.isHermitian]
  constructor
  · apply hermitian_norm_le_of_pure_trace _ (realSparsePauliObservable_hermitian _ _)
      _ (norm_nonneg _)
    intro v hv
    have htrace : Matrix.trace
        (realSparsePauliObservable (fun j => (ww j).1)
          (fun j => (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).2 * ρ)).re) * outerProduct v) =
        Matrix.trace (pauliPairObservable n q ww c * TensorGate (outerProduct v) ρ) := by
      rw [pauli_pair_complex_estimand]
      simp only [realSparsePauliObservable, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
        Matrix.trace_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ratCast, hreal]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [htrace]
    apply abs_trace_density_le_norm _ _
      (Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate (outerProduct_density hv).1 hρ.1)
    rw [Qatlib.Foundations.PureStateMath.BornBridge.trace_tensorGate, (outerProduct_density hv).2,
        hρ.2, mul_one]
  · apply hermitian_norm_le_of_pure_trace _ (realSparsePauliObservable_hermitian _ _)
      _ (norm_nonneg _)
    intro v hv
    have htrace : Matrix.trace
        (realSparsePauliObservable (fun j => (ww j).2)
          (fun j => (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).1 * ρ)).re) * outerProduct v) =
        Matrix.trace (pauliPairObservable n q ww c * TensorGate ρ (outerProduct v)) := by
      rw [pauli_pair_complex_estimand]
      simp only [realSparsePauliObservable, Matrix.sum_mul, Matrix.smul_mul, Matrix.trace_sum,
        Matrix.trace_smul, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_ratCast, hreal]
    rw [htrace]
    apply abs_trace_density_le_norm _ _
      (Qatlib.Foundations.PureStateMath.BornBridge.posSemidef_tensorGate hρ.1 (outerProduct_density hv).1)
    rw [Qatlib.Foundations.PureStateMath.BornBridge.trace_tensorGate, hρ.2,
        (outerProduct_density hv).2, mul_one]

/-- The conditional mean of the quadratic Pauli pair kernel is the average of the two sparse
Pauli estimators obtained by contracting the opposite register with the state. -/
theorem pauli_pair_conditional_value (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) (ρ : Operator (2^n)) (hρ : IsDensityOperator ρ)
    (a : Fin n → Fin 3 × Bool) :
    (∑ b, (tensorPauliLaw n ρ hρ).prob b *
      quadraticShadowKernel n (pauliPairObservable n q ww c) a b) =
    (realSparsePauliValue (fun j => (ww j).1)
        (fun j => (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).2 * ρ)).re) a +
      realSparsePauliValue (fun j => (ww j).2)
        (fun j => (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).1 * ρ)).re) a) / 2 := by
  rw [quadraticShadowKernel_conditional, quadratic_symmetric_trace,
    pauli_pair_complex_estimand, pauli_pair_complex_estimand]
  simp only [tensorPauliValue_trace, Complex.add_re, Complex.mul_re, Complex.mul_im,
    Complex.re_sum, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  norm_num
  simp only [realSparsePauliValue, ← Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The conditional variance of a pair kernel is at most the second moment of its conditional
mean. -/
theorem pair_conditional_variance_le_second {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → ℝ) :
    pairConditionalVariance p h ≤ ∑ a, p.prob a * (∑ b, p.prob b * h a b)^2 := by
  simpa only [pairConditionalVariance, pairKernelMean, Finset.mul_sum, mul_assoc] using!
    finite_pair_variance_le_second p (fun a => ∑ b, p.prob b * h a b)

/-- For supported Pauli pairs, the conditional variance is at most four to the larger support
size times the squared observable norm. -/
theorem pauli_pair_conditional_variance_sharp (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) (S₁ S₂ : Finset (Fin n)) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (hs : pauliPairSupported S₁ S₂ ww c) :
    pairConditionalVariance (tensorPauliLaw n ρ hρ)
      (quadraticShadowKernel n (pauliPairObservable n q ww c)) ≤
      (4 : ℝ)^(max S₁.card S₂.card) * ‖pauliPairObservable n q ww c‖^2 := by
  let p := tensorPauliLaw n ρ hρ
  let d₁ := fun j : Fin q => (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).2 * ρ)).re
  let d₂ := fun j : Fin q => (c j : ℝ) * (Matrix.trace (tensorPauliWord n (ww j).1 * ρ)).re
  let x := realSparsePauliValue (fun j => (ww j).1) d₁
  let y := realSparsePauliValue (fun j => (ww j).2) d₂
  let B := (4 : ℝ)^(max S₁.card S₂.card) * ‖pauliPairObservable n q ww c‖^2
  have hs₁ : realShadowSupported S₁ (fun j => (ww j).1) d₁ := by
    intro j hj
    have hc : c j ≠ 0 := by intro hc; simp [d₁, hc] at hj
    exact (hs j hc).1
  have hs₂ : realShadowSupported S₂ (fun j => (ww j).2) d₂ := by
    intro j hj
    have hc : c j ≠ 0 := by intro hc; simp [d₂, hc] at hj
    exact (hs j hc).2
  have hnorm := pauli_pair_partial_norm n q ww c ρ hρ
  have hx : p.expect (fun a => x a ^ 2) ≤ B := by
    apply (real_pauli_second_moment_bound n q S₁ (fun j => (ww j).1) d₁ ρ hρ hs₁).trans
    apply mul_le_mul
    · exact pow_le_pow_right₀ (by norm_num) (le_max_left _ _)
    · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm.1
    · exact sq_nonneg _
    · positivity
  have hy : p.expect (fun a => y a ^ 2) ≤ B := by
    apply (real_pauli_second_moment_bound n q S₂ (fun j => (ww j).2) d₂ ρ hρ hs₂).trans
    apply mul_le_mul
    · exact pow_le_pow_right₀ (by norm_num) (le_max_right _ _)
    · exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm.2
    · exact sq_nonneg _
    · positivity
  apply (pair_conditional_variance_le_second p _).trans
  calc
    _ ≤ ∑ a, p.prob a * ((x a)^2 + (y a)^2) / 2 := by
      apply Finset.sum_le_sum
      intro a _
      rw [pauli_pair_conditional_value]
      have he : ((x a + y a) / 2)^2 ≤ ((x a)^2 + (y a)^2) / 2 := by
        nlinarith [sq_nonneg (x a - y a)]
      simpa only [mul_div_assoc] using! mul_le_mul_of_nonneg_left he (p.nonneg a)
    _ = (p.expect (fun a => x a ^ 2) + p.expect (fun a => y a ^ 2)) / 2 := by
      simp only [FinDist.expect, mul_add, Finset.sum_add_distrib, ← Finset.sum_div]
    _ ≤ B := by linarith

/-- The coefficient-weighted sum of products of the first-word estimate on `a` and the
second-word estimate on `b`. -/
def pauliPairRawValue {n q : ℕ} (ww : Fin q → pauliPairWord n) (c : Fin q → ℚ)
    (a b : Fin n → Fin 3 × Bool) : ℝ :=
  ∑ j, (c j : ℝ) * tensorPauliValue (ww j).1 a * tensorPauliValue (ww j).2 b

/-- The second moment of the unsymmetrized Pauli pair estimator is at most four to the sum of
the support sizes times the squared observable norm. -/
theorem pauli_pair_raw_second_moment_bound (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) (S₁ S₂ : Finset (Fin n)) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (hs : pauliPairSupported S₁ S₂ ww c) :
    (∑ a, ∑ b, (tensorPauliLaw n ρ hρ).prob a * (tensorPauliLaw n ρ hρ).prob b *
      pauliPairRawValue ww c a b ^ 2) ≤
      (4 : ℝ)^(S₁.card + S₂.card) * ‖pauliPairObservable n q ww c‖^2 := by
  let p := tensorPauliLaw n ρ hρ
  let d := fun a (j : Fin q) => (c j : ℝ) * tensorPauliValue (ww j).1 a
  let cv := fun (v : Fin n → Option (Fin 3)) (j : Fin q) => if (ww j).2 = v then c j else 0
  have hF (a b) : pauliPairRawValue ww c a b =
      realSparsePauliValue (fun j => (ww j).2) (d a) b := rfl
  have hs₂ (a) : realShadowSupported S₂ (fun j => (ww j).2) (d a) := by
    intro j hj
    have hc : c j ≠ 0 := by intro hc; simp [d, hc] at hj
    exact (hs j hc).2
  have hrow (a) : p.expect (fun b => pauliPairRawValue ww c a b ^ 2) ≤
      (4 : ℝ)^S₂.card * ∑ v, realShadowCoefficient (fun j => (ww j).2) (d a) v ^ 2 := by
    simp_rw [hF]
    exact realShadow_second_le_coefficient S₂ (fun j => (ww j).2) (d a) ρ hρ (hs₂ a)
  have hcoeff (a) (v : Fin n → Option (Fin 3)) :
      realShadowCoefficient (fun j => (ww j).2) (d a) v =
        sparsePauliValue (fun j => (ww j).1) (cv v) a := by
    simp only [realShadowCoefficient, sparsePauliValue, d, cv]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  have hmerged (u v : Fin n → Option (Fin 3)) :
      localShadowCoefficient (fun j => (ww j).1) (cv v) u = pauliPairCoefficient ww c (u, v) := by
    simp only [localShadowCoefficient, pauliPairCoefficient, cv]
    apply Finset.sum_congr rfl
    intro j _
    have he : ww j = (u, v) ↔ (ww j).1 = u ∧ (ww j).2 = v := Prod.ext_iff
    by_cases h1 : (ww j).1 = u <;> by_cases h2 : (ww j).2 = v <;>
      simp [he, h1, h2]
  have hs₁ (v) : localShadowSupported S₁ (fun j => (ww j).1) (cv v) := by
    intro j hj
    have hc : c j ≠ 0 := by intro hc; simp [cv, hc] at hj
    exact (hs j hc).1
  have hcol (v) : p.expect (fun a =>
      realShadowCoefficient (fun j => (ww j).2) (d a) v ^ 2) ≤
        (4 : ℝ)^S₁.card * ∑ u, pauliPairCoefficient ww c (u, v)^2 := by
    simp_rw [hcoeff]
    have h := localShadow_second_le_coefficient S₁ (fun j => (ww j).1) (cv v) ρ hρ (hs₁ v)
    simpa only [hmerged] using! h
  calc
    _ = ∑ a, p.prob a * p.expect (fun b => pauliPairRawValue ww c a b ^ 2) := by
      simp only [FinDist.expect, Finset.mul_sum, mul_assoc]
      rfl
    _ ≤ ∑ a, p.prob a * ((4 : ℝ)^S₂.card *
        ∑ v, realShadowCoefficient (fun j => (ww j).2) (d a) v ^ 2) :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hrow a) (p.nonneg a)
    _ = (4 : ℝ)^S₂.card * ∑ v, p.expect (fun a =>
        realShadowCoefficient (fun j => (ww j).2) (d a) v ^ 2) := by
      simp only [FinDist.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      simp only [mul_left_comm]
    _ ≤ (4 : ℝ)^S₂.card * ∑ v, ((4 : ℝ)^S₁.card * ∑ u, pauliPairCoefficient ww c (u, v)^2) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => hcol v) (by positivity)
    _ = (4 : ℝ)^(S₁.card + S₂.card) * ∑ u : pauliPairWord n, pauliPairCoefficient ww c u ^ 2 := by
      have hsum : (∑ z : pauliPairWord n, pauliPairCoefficient ww c z ^ 2) =
          ∑ u, ∑ v, pauliPairCoefficient ww c (u, v) ^ 2 := by
        change (∑ z : (Fin n → Option (Fin 3)) × (Fin n → Option (Fin 3)),
          pauliPairCoefficient ww c z ^ 2) = _
        exact Fintype.sum_prod_type _
      rw [hsum, ← Finset.mul_sum, Finset.sum_comm, pow_add]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (pauli_pair_coefficient_mass_le ww c) (by positivity)

/-- The quadratic shadow kernel is the average of the raw Pauli pair estimator in the two record
orders. -/
theorem pauli_pair_kernel_raw_average (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) (a b : Fin n → Fin 3 × Bool) :
    quadraticShadowKernel n (pauliPairObservable n q ww c) a b =
      (pauliPairRawValue ww c a b + pauliPairRawValue ww c b a) / 2 := by
  rw [pauli_pair_kernel_formula]
  simp only [pauliPairRawValue, mul_add, Finset.sum_add_distrib, mul_assoc]
  ring

/-- The law of two independent samples from the finite distribution `p`. -/
noncomputable def shadowPairRecordLaw {X : Type} [Fintype X] (p : FinDist X) : FinDist (X × X) where
  prob z := p.prob z.1 * p.prob z.2
  nonneg z := mul_nonneg (p.nonneg _) (p.nonneg _)
  sum_one := by simp only [Fintype.sum_prod_type, ← Finset.mul_sum, p.sum_one, mul_one]

/-- The kernel variance is at most the second moment of the kernel under two independent
samples. -/
theorem pair_kernel_variance_le_second {X : Type} [Fintype X] (p : FinDist X)
    (h : X → X → ℝ) :
    pairKernelVariance p h ≤ ∑ a, ∑ b, p.prob a * p.prob b * h a b ^ 2 := by
  simpa only [pairKernelVariance, pairKernelMean, Fintype.sum_prod_type, shadowPairRecordLaw] using!
    finite_pair_variance_le_second (shadowPairRecordLaw p) (fun z => h z.1 z.2)

/-- Averaging a kernel with its argument-swapped version does not increase its second moment
under identical independent sample laws. -/
theorem pair_average_second_le {X : Type} [Fintype X] (p : FinDist X) (f : X → X → ℝ) :
    (∑ a, ∑ b, p.prob a * p.prob b * ((f a b + f b a) / 2)^2) ≤
      ∑ a, ∑ b, p.prob a * p.prob b * f a b ^ 2 := by
  have hswap : (∑ a, ∑ b, p.prob a * p.prob b * f b a ^ 2) =
      ∑ a, ∑ b, p.prob a * p.prob b * f a b ^ 2 := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  calc
    _ ≤ ∑ a, ∑ b, p.prob a * p.prob b * (f a b ^ 2 + f b a ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      have he : ((f a b + f b a) / 2)^2 ≤ (f a b ^ 2 + f b a ^ 2) / 2 := by
        nlinarith [sq_nonneg (f a b - f b a)]
      simpa only [mul_div_assoc] using! mul_le_mul_of_nonneg_left he
        (mul_nonneg (p.nonneg _) (p.nonneg _))
    _ = _ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_div]
      rw [hswap]
      ring

/-- If the observable norm is at least one, both the conditional variance and the square root of
the kernel variance are bounded by four to the larger support size times the squared
observable norm. -/
theorem pauli_pair_sharp_variances (n q : ℕ) (ww : Fin q → pauliPairWord n)
    (c : Fin q → ℚ) (S₁ S₂ : Finset (Fin n)) (ρ : Operator (2^n))
    (hρ : IsDensityOperator ρ) (hs : pauliPairSupported S₁ S₂ ww c)
    (hnorm : 1 ≤ ‖pauliPairObservable n q ww c‖) :
    pairConditionalVariance (tensorPauliLaw n ρ hρ)
      (quadraticShadowKernel n (pauliPairObservable n q ww c)) ≤
      (4 : ℝ)^(max S₁.card S₂.card) * ‖pauliPairObservable n q ww c‖^2 ∧
    Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ)
      (quadraticShadowKernel n (pauliPairObservable n q ww c))) ≤
      (4 : ℝ)^(max S₁.card S₂.card) * ‖pauliPairObservable n q ww c‖^2 := by
  refine ⟨pauli_pair_conditional_variance_sharp n q ww c S₁ S₂ ρ hρ hs, ?_⟩
  have hraw := pauli_pair_raw_second_moment_bound n q ww c S₁ S₂ ρ hρ hs
  have hsecond := pair_average_second_le (tensorPauliLaw n ρ hρ) (pauliPairRawValue ww c)
  have hvar := pair_kernel_variance_le_second (tensorPauliLaw n ρ hρ)
    (quadraticShadowKernel n (pauliPairObservable n q ww c))
  simp_rw [pauli_pair_kernel_raw_average] at hvar
  have hK := (hvar.trans hsecond).trans hraw
  have hpow : (4 : ℝ)^(S₁.card + S₂.card) ≤ ((4 : ℝ)^max S₁.card S₂.card)^2 := by
    rw [← pow_mul]
    apply pow_le_pow_right₀ (by norm_num)
    omega
  have hK' : pairKernelVariance (tensorPauliLaw n ρ hρ)
      (quadraticShadowKernel n (pauliPairObservable n q ww c)) ≤
        ((4 : ℝ)^max S₁.card S₂.card)^2 * ‖pauliPairObservable n q ww c‖^2 :=
    hK.trans (mul_le_mul_of_nonneg_right hpow (sq_nonneg _))
  have hsqrt : Real.sqrt (pairKernelVariance (tensorPauliLaw n ρ hρ)
      (quadraticShadowKernel n (pauliPairObservable n q ww c))) ≤
        (4 : ℝ)^max S₁.card S₂.card * ‖pauliPairObservable n q ww c‖ := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    simpa only [mul_pow] using! hK'
  exact hsqrt.trans (mul_le_mul_of_nonneg_left (by nlinarith) (by positivity))

end Qatlib.Concepts.ShadowModels.ShadowVariance
