/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.FormAlgebra.ParentWeightedForm
public import Qatlib.Concepts.GibbsSource.CkgBounds.ParentResidual
public import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ParentBridge
public import Qatlib.Foundations.DirichletForm.KmsDirichlet.Basic
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
public import Mathlib.LinearAlgebra.Vandermonde

@[expose] public section


/-! Gaussian CKG kernels, source weights, and weighted Gram operators.
The proofs retain frequency cross terms and the physical half; positive definiteness
requires the stated frequency or temperature assumptions, never a target gap. -/
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.DirichletForm.KmsDirichlet Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GibbsSource.FormAlgebra Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Foundations.DirichletForm.KmsDirichlet

namespace Qatlib.Concepts.GibbsSource.CkgBounds

open Matrix MeasureTheory

open scoped MeasureTheory

noncomputable def ckgC : ℝ := Real.exp (-(1 : ℝ) / 4) / (2 * Real.sqrt 2)

/-- The CKG normalization constant `ckgC` is strictly positive. -/
theorem ckgC_pos : 0 < ckgC :=
  div_pos (Real.exp_pos _) (mul_pos two_pos (Real.sqrt_pos.2 two_pos))

noncomputable def ckgWeight (β ν ν' : ℝ) : ℝ :=
  ckgC * Real.exp (-(β * (ν + ν')) / 4 - (β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2))

/-- The CKG weight is strictly positive for all real parameters. -/
theorem ckgWeight_pos (β ν ν' : ℝ) : 0 < ckgWeight β ν ν' :=
  mul_pos ckgC_pos (Real.exp_pos _)

/-- The CKG weight is symmetric in its two frequency arguments. -/
theorem ckgWeight_symm (β ν ν' : ℝ) : ckgWeight β ν ν' = ckgWeight β ν' ν := by
  rw [ckgWeight, ckgWeight]
  have h1 : β * (ν + ν') = β * (ν' + ν) := by ring
  have h2 : 3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2
      = 3 * ν' ^ 2 - 2 * ν' * ν + 3 * ν ^ 2 := by ring
  rw [h1, h2]

/-- Decomposes the CKG quadratic exponent into the squared frequency difference plus twice each
squared frequency. -/
theorem ckgQuad_eq (ν ν' : ℝ) :
    3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2 = (ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2 := by
  ring

/-- Factors the CKG weight into separate linear exponential terms and a Gaussian term with a
sum-of-squares exponent. -/
theorem ckgWeight_eq_factor (β ν ν' : ℝ) :
    ckgWeight β ν ν' = ckgC * Real.exp (-(β * ν) / 4) * Real.exp (-(β * ν') / 4)
      * Real.exp (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2)) := by
  have hE : (-(β * (ν + ν')) / 4 - (β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2))
      = -(β * ν) / 4 + (-(β * ν') / 4)
        + (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2)) := by
    rw [ckgQuad_eq ν ν']
    ring
  rw [ckgWeight, hE, Real.exp_add, Real.exp_add]
  ring

/-- The CKG weight is bounded above by its prefactor with the nonpositive quadratic exponential
omitted. -/
theorem ckgWeight_le (β ν ν' : ℝ) :
    ckgWeight β ν ν' ≤ ckgC * Real.exp (-(β * (ν + ν')) / 4) := by
  have hQ : 0 ≤ (β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2) := by positivity
  have h1 : Real.exp (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2)) ≤ 1 := by
    have h2 : Real.exp (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2))
        ≤ Real.exp (0 : ℝ) := Real.exp_le_exp.mpr (by linarith)
    simpa [Real.exp_zero] using h2
  have hnn : 0 ≤ ckgC * Real.exp (-(β * ν) / 4) * Real.exp (-(β * ν') / 4) :=
    mul_nonneg (mul_nonneg ckgC_pos.le (Real.exp_nonneg _)) (Real.exp_nonneg _)
  calc ckgWeight β ν ν'
      = ckgC * Real.exp (-(β * ν) / 4) * Real.exp (-(β * ν') / 4)
          * Real.exp (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2)) :=
        ckgWeight_eq_factor β ν ν'
    _ ≤ ckgC * Real.exp (-(β * ν) / 4) * Real.exp (-(β * ν') / 4) * 1 :=
        mul_le_mul_of_nonneg_left h1 hnn
    _ = ckgC * Real.exp (-(β * (ν + ν')) / 4) := by
        have hE : (-(β * ν) / 4) + (-(β * ν') / 4) = -(β * (ν + ν')) / 4 := by ring
        have hassoc : ckgC * Real.exp (-(β * ν) / 4) * Real.exp (-(β * ν') / 4)
            = ckgC * (Real.exp (-(β * ν) / 4) * Real.exp (-(β * ν') / 4)) := by ring
        rw [mul_one, hassoc, ← Real.exp_add, hE]

/-- At zero inverse temperature, the CKG weight equals `ckgC`. -/
theorem ckgWeight_zero (ν ν' : ℝ) : ckgWeight 0 ν ν' = ckgC := by
  rw [ckgWeight]
  norm_num [Real.exp_zero]

/-- The CKG weight tends to `ckgC` as the inverse temperature tends to zero. -/
theorem ckgWeight_tendsto_zero (ν ν' : ℝ) :
    Filter.Tendsto (fun β => ckgWeight β ν ν') (nhds 0) (nhds ckgC) := by
  have hcont : Continuous (fun β => ckgWeight β ν ν') := by
    simp only [ckgWeight]
    fun_prop
  have hthis := hcont.tendsto (0 : ℝ)
  rwa [ckgWeight_zero] at hthis

/-- The integral of a shifted real Gaussian with positive precision is the square root of the
ratio of pi to that precision. -/
theorem integral_shifted_gaussian {a μ : ℝ} :
    ∫ ω : ℝ, Real.exp (-a * (ω - μ) ^ 2) = Real.sqrt (Real.pi / a) := by
  have hmp : MeasurePreserving (fun ω : ℝ => ω - μ) volume volume := by
    refine (measurePreserving_add_left volume (-μ)).congr
      (measurable_id.sub measurable_const) ?_
    filter_upwards with ω
    ring
  have key := hmp.integral_comp (measurableEmbedding_subRight μ)
    (fun y : ℝ => Real.exp (-a * y ^ 2))
  rw [key, integral_gaussian]

noncomputable def ckgFilter (β ω : ℝ) : ℝ := Real.exp (-((β * ω + 1) ^ 2) / 2)

noncomputable def ckgBumpNorm (β : ℝ) : ℝ := Real.sqrt (β / (2 * Real.sqrt (2 * Real.pi)))

noncomputable def ckgBump (β ν ω : ℝ) : ℝ :=
  ckgBumpNorm β * Real.exp (-(β ^ 2) * (ω - ν) ^ 2 / 4)

/-- For positive inverse temperature, the filtered integral of two CKG bumps equals their CKG
weight. -/
theorem ckgWeight_eq_integral {β : ℝ} (hβ : 0 < β) (ν ν' : ℝ) :
    ∫ ω : ℝ, ckgFilter β ω * ckgBump β ν ω * ckgBump β ν' ω = ckgWeight β ν ν' := by

  have hint : ∀ ω : ℝ, ckgFilter β ω * ckgBump β ν ω * ckgBump β ν' ω
      = ckgBumpNorm β * ckgBumpNorm β
          * (Real.exp (-(β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2)
                - β * (ν + ν') / 4 - 1 / 4)
            * Real.exp (-β ^ 2 * (ω - (β * (ν + ν') - 2) / (4 * β)) ^ 2)) := by
    intro ω
    rw [ckgFilter, ckgBump, ckgBump]
    have h1 : Real.exp (-((β * ω + 1) ^ 2) / 2)
          * (ckgBumpNorm β * Real.exp (-(β ^ 2) * (ω - ν) ^ 2 / 4))
          * (ckgBumpNorm β * Real.exp (-(β ^ 2) * (ω - ν') ^ 2 / 4))
        = ckgBumpNorm β * ckgBumpNorm β
            * (Real.exp (-((β * ω + 1) ^ 2) / 2) * Real.exp (-(β ^ 2) * (ω - ν) ^ 2 / 4)
              * Real.exp (-(β ^ 2) * (ω - ν') ^ 2 / 4)) := by
      ring
    have hE : -((β * ω + 1) ^ 2) / 2 + (-(β ^ 2) * (ω - ν) ^ 2 / 4)
          + (-(β ^ 2) * (ω - ν') ^ 2 / 4)
        = -(β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2) - β * (ν + ν') / 4 - 1 / 4
            + -β ^ 2 * (ω - (β * (ν + ν') - 2) / (4 * β)) ^ 2 := by
      field_simp
      ring
    rw [h1, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hE, Real.exp_add]
  simp only [hint]
  rw [integral_const_mul, integral_const_mul,
    integral_shifted_gaussian (a := β ^ 2)]

  have hsqrt : Real.sqrt (Real.pi / β ^ 2) = Real.sqrt Real.pi / β := by
    rw [Real.sqrt_div Real.pi_pos.le (β ^ 2), Real.sqrt_sq (le_of_lt hβ)]
  rw [hsqrt]

  have hsnn : 0 ≤ β / (2 * Real.sqrt (2 * Real.pi)) := by positivity
  have hcc : ckgBumpNorm β * ckgBumpNorm β * (Real.sqrt Real.pi / β)
      = 1 / (2 * Real.sqrt 2) := by
    rw [ckgBumpNorm, Real.mul_self_sqrt hsnn, Real.sqrt_mul two_pos.le]
    field_simp

  have hassoc2 : ckgBumpNorm β * ckgBumpNorm β
        * (Real.exp (-(β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2)
            - β * (ν + ν') / 4 - 1 / 4) * (Real.sqrt Real.pi / β))
      = (ckgBumpNorm β * ckgBumpNorm β * (Real.sqrt Real.pi / β))
          * Real.exp (-(β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2)
            - β * (ν + ν') / 4 - 1 / 4) := by
    ring
  rw [hassoc2, hcc]

  have hK : (-(β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2) - β * (ν + ν') / 4 - 1 / 4)
      = -(1 : ℝ) / 4 + (-(β * (ν + ν')) / 4
          - (β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2)) := by
    ring
  have hsq2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt two_pos.le
  rw [hK, Real.exp_add, ckgWeight, ckgC]
  field_simp [hsq2]

section Instantiation

variable {D : ℕ} {ι : Type*} [Fintype ι]

noncomputable def ckgDampedForm (β : ℝ) (ρ : Operator D) (ν : ι → ℝ)
    (A : ι → Operator D) (X : Operator D) : ℂ :=
  wdampedForm (fun a b => ckgWeight β (ν a) (ν b)) β ρ ν A X

noncomputable def ckgPlainForm (β : ℝ) (ρ : Operator D) (ν : ι → ℝ)
    (A : ι → Operator D) (X : Operator D) : ℂ :=
  wplainForm (fun a b => ckgWeight β (ν a) (ν b)) ρ A X

/-- When all frequencies coincide, the CKG damped form equals the CKG plain form. -/
theorem ckgDampedForm_of_const_freq {β : ℝ} {ρ : Operator D} {ν : ι → ℝ} {A : ι → Operator D}
    (hν : ∀ a b, ν a = ν b) (X : Operator D) :
    ckgDampedForm β ρ ν A X = ckgPlainForm β ρ ν A X :=
  wdampedForm_of_const_freq hν A X

def ckgDomination (β : ℝ) (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D) : Prop :=
  ∀ X : Operator D, Complex.re (ckgDampedForm β ρ ν A X)
    ≤ 3 / 2 * Complex.re (ckgPlainForm β ρ ν A X)

end Instantiation

noncomputable def ckgKappa (β ν ν' : ℝ) : ℝ :=
  ckgWeight β ν ν' * (1 / 2 - phaseKernel β (ν - ν'))

/-- The CKG kappa kernel is nonnegative. -/
theorem ckgKappa_nonneg (β ν ν' : ℝ) : 0 ≤ ckgKappa β ν ν' :=
  mul_nonneg (ckgWeight_pos β ν ν').le (by
    have h := phaseKernel_le_half β (ν - ν')
    linarith)

/-- The CKG kappa kernel vanishes when its two frequencies coincide. -/
theorem ckgKappa_self (β ν : ℝ) : ckgKappa β ν ν = 0 := by
  rw [ckgKappa, sub_self, phaseKernel_self β]
  ring

/-- The CKG kappa kernel is symmetric in its frequency arguments. -/
theorem ckgKappa_symm (β ν ν' : ℝ) : ckgKappa β ν ν' = ckgKappa β ν' ν := by
  rw [ckgKappa, ckgKappa, ckgWeight_symm]
  have he : phaseKernel β (ν' - ν) = phaseKernel β (ν - ν') := by
    rw [show ν' - ν = -(ν - ν') from by ring, phaseKernel_neg]
  rw [he]

variable {D : ℕ} {ι : Type*} [Fintype ι]

/-- The CKG filter is strictly positive. -/
theorem ckgFilter_pos (β ω : ℝ) : 0 < ckgFilter β ω := Real.exp_pos _

/-- A shifted Gaussian with positive precision and an arbitrary constant exponent offset is
integrable. -/
theorem integrable_exp_shifted_gauss {a μ c : ℝ} (ha : 0 < a) :
    Integrable (fun ω : ℝ => Real.exp (-a * (ω - μ) ^ 2 + c)) := by
  refine (((integrable_exp_neg_mul_sq ha).comp_sub_right μ).const_mul (Real.exp c)).congr ?_
  filter_upwards with ω
  rw [Real.exp_add]
  ring_nf

/-- The product of the CKG filter with two CKG bumps is integrable for positive inverse
temperature. -/
theorem integrable_ckgFilter_mul_bump {β ν ν' : ℝ} (hβ : 0 < β) :
    Integrable (fun ω : ℝ => ckgFilter β ω * ckgBump β ν ω * ckgBump β ν' ω) := by
  have hβ2 : 0 < β ^ 2 := by positivity
  refine ((integrable_exp_shifted_gauss (a := β ^ 2)
      (μ := (β * (ν + ν') - 2) / (4 * β))
      (c := -(β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2) - β * (ν + ν') / 4 - 1 / 4)
      hβ2).const_mul
    (ckgBumpNorm β * ckgBumpNorm β)).congr ?_
  filter_upwards with ω
  have h1 : Real.exp (-((β * ω + 1) ^ 2) / 2)
      * (ckgBumpNorm β * Real.exp (-(β ^ 2) * (ω - ν) ^ 2 / 4))
      * (ckgBumpNorm β * Real.exp (-(β ^ 2) * (ω - ν') ^ 2 / 4))
      = ckgBumpNorm β * ckgBumpNorm β
          * (Real.exp (-((β * ω + 1) ^ 2) / 2) * Real.exp (-(β ^ 2) * (ω - ν) ^ 2 / 4)
            * Real.exp (-(β ^ 2) * (ω - ν') ^ 2 / 4)) := by
    ring
  have hE : -((β * ω + 1) ^ 2) / 2 + (-(β ^ 2) * (ω - ν) ^ 2 / 4)
      + (-(β ^ 2) * (ω - ν') ^ 2 / 4)
      = -β ^ 2 * (ω - (β * (ν + ν') - 2) / (4 * β)) ^ 2
          + (-(β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2)
            - β * (ν + ν') / 4 - 1 / 4) := by
    field_simp
    ring
  have hsumexp : Real.exp (-((β * ω + 1) ^ 2) / 2) * Real.exp (-(β ^ 2) * (ω - ν) ^ 2 / 4)
        * Real.exp (-(β ^ 2) * (ω - ν') ^ 2 / 4)
      = Real.exp (-β ^ 2 * (ω - (β * (ν + ν') - 2) / (4 * β)) ^ 2
          + (-(β ^ 2 / 16) * (3 * ν ^ 2 - 2 * ν * ν' + 3 * ν' ^ 2)
            - β * (ν + ν') / 4 - 1 / 4)) := by
    rw [← Real.exp_add, ← Real.exp_add, hE]
  rw [ckgFilter, ckgBump, ckgBump, h1, hsumexp]

/-- The CKG-weighted contraction of an operator Gram matrix is nonnegative for positive inverse
temperature. -/
theorem ckgWeightedGram_nonneg {β : ℝ} (hβ : 0 < β) (ν : ι → ℝ) (B : ι → Operator D) :
    0 ≤ ∑ a, ∑ b, ckgWeight β (ν a) (ν b) * (hsInner (B a) (B b)).re := by
  classical
  have hint : ∀ a b : ι, ckgWeight β (ν a) (ν b) * (hsInner (B a) (B b)).re
      = ∫ ω : ℝ, (hsInner (B a) (B b)).re
          * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω) := by
    intro a b
    rw [integral_const_mul, ← ckgWeight_eq_integral hβ]
    ring
  have hswap : (∫ ω : ℝ, ∑ a, ∑ b, (hsInner (B a) (B b)).re
          * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω))
      = ∑ a, ∑ b, ∫ ω : ℝ, (hsInner (B a) (B b)).re
          * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω) := by
    rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ
      (fun b _ => ((integrable_ckgFilter_mul_bump (ν := ν a) (ν' := ν b) hβ).const_mul
        ((hsInner (B a) (B b)).re))))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum Finset.univ (fun b _ =>
      ((integrable_ckgFilter_mul_bump (ν := ν a) (ν' := ν b) hβ).const_mul
        ((hsInner (B a) (B b)).re)))]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hint a b, ← hswap]

  have hcongr : ∀ ω : ℝ, (∑ a, ∑ b, (hsInner (B a) (B b)).re
        * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω))
      = ckgFilter β ω * (hsInner (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • B a)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • B b)).re := by
    intro ω
    have hγ : ∀ a b : ι, (hsInner (B a) (B b)).re
          * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω)
        = ckgFilter β ω * (ckgBump β (ν a) ω * ckgBump β (ν b) ω
            * (hsInner (B a) (B b)).re) := fun a b => by ring
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hγ a b]
    simp only [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hsInner_re_bilinear_sum (fun a => ckgBump β (ν a) ω)
      (fun b => ckgBump β (ν b) ω) B B]
  have hcf : Continuous (ckgFilter β) := by
    show Continuous (fun ω : ℝ => Real.exp (-((β * ω + 1) ^ 2) / 2))
    fun_prop
  have hcb : ∀ x : ι, Continuous (fun ω : ℝ => ckgBump β (ν x) ω) := fun x => by
    show Continuous (fun ω : ℝ => ckgBumpNorm β * Real.exp (-(β ^ 2) * (ω - ν x) ^ 2 / 4))
    fun_prop
  have hsum : Continuous (fun ω : ℝ => ∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • B a) := by
    refine continuous_finsetSum Finset.univ (fun a _ => ?_)
    exact (Complex.continuous_ofReal.comp (hcb a)).smul continuous_const
  have hhs : Continuous (fun ω : ℝ => hsInner (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • B a)
      (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • B b)) := by
    show Continuous (fun ω : ℝ => ((∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • B a)ᴴ
      * (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • B b)).trace)
    have htr : Continuous (fun X : Operator D => X.trace) := by fun_prop
    exact htr.comp ((Continuous.star hsum).mul hsum)
  have hmeas : AEStronglyMeasurable (fun ω : ℝ => ckgFilter β ω * (hsInner
      (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • B a)
      (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • B b)).re) volume :=
    Continuous.aestronglyMeasurable (hcf.mul (Complex.continuous_re.comp hhs))
  have hnn : ∀ ω : ℝ, 0 ≤ ckgFilter β ω * (hsInner
      (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • B a)
      (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • B b)).re := fun ω =>
    mul_nonneg (ckgFilter_pos β ω).le (hsInner_self_nonneg _)
  have hint2 : (∫ ω : ℝ, ∑ a, ∑ b, (hsInner (B a) (B b)).re
        * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω))
      = ∫ ω : ℝ, ckgFilter β ω * (hsInner (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • B a)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • B b)).re :=
    integral_congr_ae (ae_of_all volume hcongr)
  rw [hint2]
  exact integral_nonneg (fun ω => hnn ω)

/-- Real exponential functions with distinct real rates are linearly independent. -/
theorem exp_linearIndependent {m : ℕ} (lam : Fin m → ℝ) (hlam : Function.Injective lam) :
    LinearIndependent ℝ (fun i : Fin m => (fun ω : ℝ => Real.exp (lam i * ω))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have heval : ∀ k : ℕ, ∑ j, c j * (Real.exp (lam j)) ^ k = 0 := by
    intro k
    have h := congrFun hc (k : ℝ)
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    have hterm : ∀ j : Fin m, c j * Real.exp (lam j * (k : ℝ))
        = c j * (Real.exp (lam j)) ^ k := fun j => by
      rw [mul_comm (lam j), Real.exp_nat_mul, ← Real.rpow_natCast]
    rw [Finset.sum_congr rfl fun j _ => hterm j] at h
    exact h
  exact fun i => congrFun (Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero
    (fun a b hab => hlam (Real.exp_injective hab)) (fun k => heval k)) i

/-- Factors a CKG bump into its normalization, a common Gaussian in the integration variable,
and frequency-dependent exponential factors. -/
theorem ckgBump_factor (β ν ω : ℝ) :
    ckgBump β ν ω = ckgBumpNorm β * Real.exp (-(β ^ 2) * ω ^ 2 / 4)
      * (Real.exp ((β ^ 2 / 2) * ν * ω) * Real.exp (-(β ^ 2) * ν ^ 2 / 4)) := by
  rw [ckgBump]
  rw [show (-(β ^ 2) * (ω - ν) ^ 2 / 4 : ℝ)
      = (-(β ^ 2) * ω ^ 2 / 4) + ((β ^ 2 / 2) * ν * ω + -(β ^ 2) * ν ^ 2 / 4) from by
    field_simp
    ring]
  rw [Real.exp_add, Real.exp_add]
  ring

/-- CKG bumps at distinct frequencies are linearly independent for positive inverse temperature. -/
theorem ckgBump_linearIndependent {β : ℝ} (hβ : 0 < β) {m : ℕ} (ν : Fin m → ℝ)
    (hν : Function.Injective ν) :
    LinearIndependent ℝ (fun i : Fin m => (fun ω : ℝ => ckgBump β (ν i) ω)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hCc : (0 : ℝ) < ckgBumpNorm β := Real.sqrt_pos.mpr
    (div_pos hβ (mul_pos two_pos (Real.sqrt_pos.2 Real.two_pi_pos)))
  have hE : ∀ ω : ℝ, (0 : ℝ) < Real.exp (-(β ^ 2) * ω ^ 2 / 4) := fun ω => Real.exp_pos _
  have hscale : ∀ ω : ℝ, ∑ a, (c a * Real.exp (-(β ^ 2) * (ν a) ^ 2 / 4))
      * Real.exp ((β ^ 2 / 2) * (ν a) * ω) = 0 := by
    intro ω
    have h := congrFun hc ω
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply] at h
    rw [Finset.sum_congr rfl fun a _ => by rw [ckgBump_factor β (ν a) ω]] at h
    have hpos : (0 : ℝ) < ckgBumpNorm β * Real.exp (-(β ^ 2) * ω ^ 2 / 4) :=
      mul_pos hCc (hE ω)

    have hdiv : ∀ a : Fin m, c a * (ckgBumpNorm β * Real.exp (-(β ^ 2) * ω ^ 2 / 4)
          * (Real.exp ((β ^ 2 / 2) * (ν a) * ω)
            * Real.exp (-(β ^ 2) * (ν a) ^ 2 / 4)))
        = (ckgBumpNorm β * Real.exp (-(β ^ 2) * ω ^ 2 / 4))
          * ((c a * Real.exp (-(β ^ 2) * (ν a) ^ 2 / 4))
            * Real.exp ((β ^ 2 / 2) * (ν a) * ω)) := fun a => by ring
    rw [Finset.sum_congr rfl fun a _ => hdiv a] at h
    simp only [← Finset.mul_sum] at h
    have := (mul_eq_zero.mp h).resolve_left (ne_of_gt hpos)
    exact this
  have hd : ∀ i : Fin m, c i * Real.exp (-(β ^ 2) * (ν i) ^ 2 / 4) = 0 := by
    have hli := exp_linearIndependent (fun a => (β ^ 2 / 2) * (ν a))
      (fun a b hab => hν (mul_left_cancel₀
        (ne_of_gt (by positivity : (0:ℝ) < β ^ 2 / 2)) hab))
    rw [Fintype.linearIndependent_iff] at hli
    exact hli (fun a => c a * Real.exp (-(β ^ 2) * (ν a) ^ 2 / 4))
      (funext fun ω => by
        simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply]
        exact hscale ω)
  intro i
  have ki : (0:ℝ) < Real.exp (-(β ^ 2) * (ν i) ^ 2 / 4) := Real.exp_pos _
  exact (mul_eq_zero.mp (hd i)).resolve_right (ne_of_gt ki)

/-- The CKG weight matrix at distinct frequencies has a strictly positive quadratic form on
every nonzero real coefficient vector. -/
theorem ckgWeight_posDef {β : ℝ} (hβ : 0 < β) {m : ℕ} (ν : Fin m → ℝ)
    (hν : Function.Injective ν) (c : Fin m → ℝ) (hc : c ≠ 0) :
    0 < ∑ a, ∑ b, ckgWeight β (ν a) (ν b) * (c a * c b) := by
  classical

  have hsq : ∀ ω : ℝ, ckgFilter β ω * (∑ a, c a * ckgBump β (ν a) ω) ^ 2
      = ∑ a, ∑ b, (c a * c b)
          * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω) := by
    intro ω
    rw [pow_two, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

  have hnn : 0 ≤ (fun ω : ℝ => ckgFilter β ω * (∑ a, c a * ckgBump β (ν a) ω) ^ 2) :=
    fun ω => mul_nonneg (ckgFilter_pos β ω).le (sq_nonneg _)

  have hint : Integrable
      (fun ω : ℝ => ckgFilter β ω * (∑ a, c a * ckgBump β (ν a) ω) ^ 2) := by
    have hexp : (fun ω : ℝ => ckgFilter β ω * (∑ a, c a * ckgBump β (ν a) ω) ^ 2)
        = fun ω => ∑ a, ∑ b, (c a * c b)
            * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω) := by
      funext ω; exact hsq ω
    rw [hexp]
    exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
      ((integrable_ckgFilter_mul_bump (ν := ν a) (ν' := ν b) hβ).const_mul (c a * c b))))

  have hquad : (∫ ω : ℝ, ckgFilter β ω * (∑ a, c a * ckgBump β (ν a) ω) ^ 2)
      = ∑ a, ∑ b, ckgWeight β (ν a) (ν b) * (c a * c b) := by
    have hexp : (fun ω : ℝ => ckgFilter β ω * (∑ a, c a * ckgBump β (ν a) ω) ^ 2)
        = fun ω => ∑ a, ∑ b, (c a * c b)
            * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω) := by
      funext ω; exact hsq ω
    rw [hexp]
    rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ
      (fun b _ => ((integrable_ckgFilter_mul_bump (ν := ν a) (ν' := ν b) hβ).const_mul
        (c a * c b))))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum Finset.univ (fun b _ =>
      ((integrable_ckgFilter_mul_bump (ν := ν a) (ν' := ν b) hβ).const_mul
        (c a * c b)))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [integral_const_mul, ckgWeight_eq_integral hβ]
    ring

  obtain ⟨ω₀, hω₀⟩ : ∃ ω₀, (∑ a, c a * ckgBump β (ν a) ω₀) ≠ 0 := by
    by_contra hall
    push Not at hall

    apply hc
    have hli := Fintype.linearIndependent_iff.mp (ckgBump_linearIndependent hβ ν hν)
    have hzero_fn : ∑ i, c i • (fun ω => ckgBump β (ν i) ω) = 0 := by
      funext ω
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hall ω
    exact funext fun i => hli c hzero_fn i

  have hcb : ∀ i : Fin m, Continuous (fun ω : ℝ => ckgBump β (ν i) ω) := fun i => by
    unfold ckgBump; fun_prop
  have hcont : Continuous (fun ω => ∑ a, c a * ckgBump β (ν a) ω) :=
    continuous_finsetSum _ (fun a _ => (continuous_const).mul (hcb a))
  have hopen : IsOpen {ω : ℝ | (∑ a, c a * ckgBump β (ν a) ω) ≠ 0} :=
    isOpen_ne.preimage hcont
  have hpos : 0 < volume {ω : ℝ | (∑ a, c a * ckgBump β (ν a) ω) ≠ 0} :=
    IsOpen.measure_pos volume hopen ⟨ω₀, hω₀⟩

  have hsub : {ω : ℝ | (∑ a, c a * ckgBump β (ν a) ω) ≠ 0}
      ⊆ Function.support (fun ω : ℝ => ckgFilter β ω * (∑ a, c a * ckgBump β (ν a) ω) ^ 2) := by
    intro ω hw
    exact mul_ne_zero (ne_of_gt (ckgFilter_pos β ω)) (pow_ne_zero 2 hw)

  rw [← hquad]
  rw [integral_pos_iff_support_of_nonneg hnn hint]
  exact lt_of_lt_of_le hpos (measure_mono hsub)

/-- If a linear combination of distinct-frequency CKG bumps with operator coefficients vanishes
identically, every coefficient operator is zero. -/
theorem matrixSum_eq_zero_of_bumpLI {β : ℝ} (hβ : 0 < β) {m : ℕ} (ν : Fin m → ℝ)
    (hν : Function.Injective ν) (M : Fin m → Operator D)
    (h : ∀ ω : ℝ, ∑ a, (ckgBump β (ν a) ω : ℂ) • M a = 0) :
    ∀ a, M a = 0 := by
  classical
  have hentry : ∀ i j : Fin D, ∀ ω : ℝ,
      ∑ a, (ckgBump β (ν a) ω : ℂ) * M a i j = 0 := by
    intro i j ω
    have hsum := h ω
    have h₀ : ((∑ a, (ckgBump β (ν a) ω : ℂ) • M a) : Operator D) i j
        = (0 : Operator D) i j := by rw [hsum]
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply] at h₀
    exact h₀
  have hsum_re : ∀ (s : Finset (Fin m)) (f : Fin m → ℂ),
      (∑ a ∈ s, f a).re = ∑ a ∈ s, (f a).re := by
    intro s f
    induction s using Finset.induction with
    | empty => simp
    | insert x sx hx ih => simp [Finset.sum_insert hx, ih, Complex.add_re]
  have hsum_im : ∀ (s : Finset (Fin m)) (f : Fin m → ℂ),
      (∑ a ∈ s, f a).im = ∑ a ∈ s, (f a).im := by
    intro s f
    induction s using Finset.induction with
    | empty => simp
    | insert x sx hx ih => simp [Finset.sum_insert hx, ih, Complex.add_im]
  have hre_entry : ∀ i j : Fin D, ∀ ω : ℝ,
      ∑ a, ckgBump β (ν a) ω * (M a i j).re = 0 := by
    intro i j ω
    have h1 : (∑ a, (ckgBump β (ν a) ω : ℂ) * M a i j).re = 0 := by
      rw [hentry i j ω]; rfl
    rw [hsum_re] at h1
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] at h1
    exact h1
  have him_entry : ∀ i j : Fin D, ∀ ω : ℝ,
      ∑ a, ckgBump β (ν a) ω * (M a i j).im = 0 := by
    intro i j ω
    have h1 : (∑ a, (ckgBump β (ν a) ω : ℂ) * M a i j).im = 0 := by
      rw [hentry i j ω]; rfl
    rw [hsum_im] at h1
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] at h1
    exact h1
  have hli := Fintype.linearIndependent_iff.mp (ckgBump_linearIndependent hβ ν hν)
  intro a₀
  ext i j
  have hre_zero : (M a₀ i j).re = 0 :=
    hli (fun a => (M a i j).re) (by
      funext ω
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact (Finset.sum_congr rfl fun a _ => mul_comm _ _).trans (hre_entry i j ω)) a₀
  have him_zero : (M a₀ i j).im = 0 :=
    hli (fun a => (M a i j).im) (by
      funext ω
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact (Finset.sum_congr rfl fun a _ => mul_comm _ _).trans (him_entry i j ω)) a₀
  exact Complex.ext hre_zero him_zero

/-- A continuous nonnegative integrable real function with integral zero is identically zero. -/
theorem continuous_nonneg_integral_eq_zero {f : ℝ → ℝ} (hc : Continuous f) (hnn : 0 ≤ f)
    (hint : Integrable f) (h₀ : ∫ x, f x = 0) : f = 0 := by
  by_contra hf
  obtain ⟨x₀, hx₀⟩ := Function.ne_iff.mp hf
  have hpos : 0 < f x₀ := lt_of_le_of_ne (hnn x₀) (Ne.symm hx₀)
  have hopen : IsOpen {x : ℝ | f x₀ / 2 < f x} := isOpen_lt continuous_const hc
  have hne : {x : ℝ | f x₀ / 2 < f x}.Nonempty := ⟨x₀, half_lt_self hpos⟩
  have hmeas : 0 < volume {x : ℝ | f x₀ / 2 < f x} := IsOpen.measure_pos volume hopen hne
  have hsub : {x : ℝ | f x₀ / 2 < f x} ⊆ Function.support f := fun x hx =>
    ne_of_gt (lt_trans (div_pos hpos two_pos) hx)
  have hsup : 0 < volume (Function.support f) := lt_of_lt_of_le hmeas (measure_mono hsub)
  have hpos_int : 0 < ∫ x, f x := (integral_pos_iff_support_of_nonneg hnn hint).mpr hsup
  linarith

/-- An operator whose Hilbert-Schmidt squared norm has real part zero is zero. -/
theorem hsInner_self_re_zero_iff {M : Operator D} (h : (hsInner M M).re = 0) : M = 0 := by
  ext i j
  rw [hsInner_self_re_sum] at h
  have hterm : Complex.normSq (M i j) = 0 := by
    by_contra hne
    have hlt : 0 < Complex.normSq (M i j) :=
      lt_of_le_of_ne (Complex.normSq_nonneg _) (Ne.symm hne)
    have hpi : 0 < ∑ j', Complex.normSq (M i j') :=
      Finset.sum_pos' (fun j' _ => Complex.normSq_nonneg _) ⟨j, Finset.mem_univ _, hlt⟩
    have hpo : 0 < ∑ i', ∑ j', Complex.normSq (M i' j') :=
      Finset.sum_pos' (fun i' _ => Finset.sum_nonneg fun j' _ => Complex.normSq_nonneg _)
        ⟨i, Finset.mem_univ _, hpi⟩
    rw [h] at hpo; exact absurd hpo (by simp)
  have him2 : 0 ≤ (M i j).im * (M i j).im := mul_self_nonneg _

  have hnn_re : (M i j).re * (M i j).re ≥ 0 := mul_self_nonneg _
  have hnn_im : (M i j).im * (M i j).im ≥ 0 := mul_self_nonneg _
  have hsum : (M i j).re * (M i j).re + (M i j).im * (M i j).im = 0 := hterm
  have hre_sq : (M i j).re * (M i j).re = 0 := by linarith
  have him_sq : (M i j).im * (M i j).im = 0 := by linarith
  exact Complex.ext
    ((mul_eq_zero.mp hre_sq).elim id id) ((mul_eq_zero.mp him_sq).elim id id)

/-- Expresses the CKG-weighted Gram contraction as the filtered integral of the Hilbert-Schmidt
squared norm of the bump-weighted operator sum. -/
theorem ckgWeightedGram_eq_integral {β : ℝ} (hβ : 0 < β) (ν : ι → ℝ) (B : ι → Operator D) :
    ∑ a, ∑ b, ckgWeight β (ν a) (ν b) * (hsInner (B a) (B b)).re
      = ∫ ω : ℝ, ckgFilter β ω * (hsInner
          (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • B a)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • B b)).re := by
  classical
  have hint : ∀ a b : ι, ckgWeight β (ν a) (ν b) * (hsInner (B a) (B b)).re
      = ∫ ω : ℝ, (hsInner (B a) (B b)).re
          * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω) := by
    intro a b
    rw [integral_const_mul, ← ckgWeight_eq_integral hβ]
    ring
  have hswap : ∑ a, ∑ b, ∫ ω : ℝ, (hsInner (B a) (B b)).re
          * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω)
      = ∫ ω : ℝ, ∑ a, ∑ b, (hsInner (B a) (B b)).re
          * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω) := by
    rw [integral_finsetSum Finset.univ (fun a _ => integrable_finsetSum Finset.univ
      (fun b _ => ((integrable_ckgFilter_mul_bump (ν := ν a) (ν' := ν b) hβ).const_mul
        ((hsInner (B a) (B b)).re))))]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [integral_finsetSum Finset.univ (fun b _ =>
      ((integrable_ckgFilter_mul_bump (ν := ν a) (ν' := ν b) hβ).const_mul
        ((hsInner (B a) (B b)).re)))]
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hint a b, hswap]
  have hsimp : ∀ ω : ℝ, (∑ a, ∑ b, (hsInner (B a) (B b)).re
          * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω))
      = ckgFilter β ω * (hsInner (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • B a)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • B b)).re := by
    intro ω
    rw [hsInner_re_bilinear_sum (fun a => ckgBump β (ν a) ω)
      (fun b => ckgBump β (ν b) ω) B B]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [integral_congr_ae (ae_of_all _ fun ω => hsimp ω)]

def complexReAddMonoidHom : ℂ →+ ℝ where
  toFun z := z.re
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The real part of the weighted plain form is a sum of parent-factor Gram entries with weights
divided by two. -/
theorem wplainForm_re (w : ι → ι → ℝ) (ρ : Operator D)
    (A : ι → Operator D) (X : Operator D) :
    (wplainForm w ρ A X).re = ∑ a, ∑ b, (w a b / 2) *
      (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re := by
  rw [wplainForm]

  have h1 : (∑ a : ι, ∑ b : ι, (↑(w a b / 2) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re
      = ∑ a : ι, (∑ b : ι, (↑(w a b / 2) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re :=
    map_sum complexReAddMonoidHom (fun a => ∑ b : ι, (↑(w a b / 2) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)) Finset.univ
  rw [h1]
  refine Finset.sum_congr rfl fun a _ => ?_

  have h2 : (∑ b : ι, (↑(w a b / 2) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re
      = ∑ b : ι, ((↑(w a b / 2) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re :=
    map_sum complexReAddMonoidHom (fun b : ι => (↑(w a b / 2) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)) Finset.univ
  rw [h2]
  exact Finset.sum_congr rfl fun b _ => by
    simp [Complex.mul_re]

/-- The real part of the weighted plain form is half the weighted sum of real parent-factor Gram
entries. -/
theorem wplainForm_re_eq (w : ι → ι → ℝ) (ρ : Operator D)
    (A : ι → Operator D) (X : Operator D) :
    (wplainForm w ρ A X).re = (∑ a, ∑ b, w a b *
      (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re) / 2 := by
  rw [wplainForm_re]
  have h1 : ∀ a b : ι, (w a b / 2) *
      (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re
      = (w a b * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re) / 2 := by
    intro a b; ring
  rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => h1 a b]
  rw [Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_div]]
  rw [← Finset.sum_div]

/-- At distinct frequencies and positive inverse temperature, the real CKG-weighted plain form
vanishes exactly when every parent factor vanishes. -/
theorem ckgWplainForm_eq_zero_iff {β : ℝ} (hβ : 0 < β) {m : ℕ} (ν : Fin m → ℝ)
    (hν : Function.Injective ν) (ρ : Operator D) (A : Fin m → Operator D)
    (O : Operator D) :
    (wplainForm (fun a b => ckgWeight β (ν a) (ν b)) ρ A O).re = 0
      ↔ ∀ a, parentFactor ρ (A a) O = 0 := by
  classical
  constructor
  · intro hE0

    rw [wplainForm_re_eq] at hE0
    have hE0_sum : ∑ a, ∑ b, ckgWeight β (ν a) (ν b)
        * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re = 0 :=
      (div_eq_zero_iff.mp hE0).resolve_right (by norm_num)

    have hintegral : (∫ ω : ℝ, ckgFilter β ω * (hsInner
          (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • parentFactor ρ (A a) O)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • parentFactor ρ (A b) O)).re) = 0 := by
      rw [← ckgWeightedGram_eq_integral hβ ν (fun a => parentFactor ρ (A a) O)]
      exact hE0_sum

    have hnn : 0 ≤ (fun ω : ℝ => ckgFilter β ω * (hsInner
          (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • parentFactor ρ (A a) O)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • parentFactor ρ (A b) O)).re) := fun ω =>
      mul_nonneg (ckgFilter_pos β ω).le (hsInner_self_nonneg _)
    have hinteg : Integrable (fun ω : ℝ => ckgFilter β ω * (hsInner
          (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • parentFactor ρ (A a) O)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • parentFactor ρ (A b) O)).re) := by
      have hexp : (fun ω : ℝ => ckgFilter β ω * (hsInner
          (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • parentFactor ρ (A a) O)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • parentFactor ρ (A b) O)).re)
          = fun ω => ∑ a, ∑ b, (hsInner (parentFactor ρ (A a) O)
              (parentFactor ρ (A b) O)).re
              * (ckgFilter β ω * ckgBump β (ν a) ω * ckgBump β (ν b) ω) := by
        funext ω
        rw [hsInner_re_bilinear_sum (fun a => ckgBump β (ν a) ω)
          (fun b => ckgBump β (ν b) ω)
          (fun a => parentFactor ρ (A a) O) (fun b => parentFactor ρ (A b) O)]
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun b _ => by ring
      rw [hexp]
      exact integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ =>
        ((integrable_ckgFilter_mul_bump (ν := ν a) (ν' := ν b) hβ).const_mul
          ((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re))))
    have hF0 : (fun ω : ℝ => ckgFilter β ω * (hsInner
          (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • parentFactor ρ (A a) O)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • parentFactor ρ (A b) O)).re) = 0 := by
      have hcb : ∀ i : Fin m, Continuous (fun ω : ℝ => ckgBump β (ν i) ω) := fun i => by
        unfold ckgBump; fun_prop
      have hsum : Continuous (fun ω : ℝ => ∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ)
          • parentFactor ρ (A a) O) := by
        refine continuous_finsetSum _ fun a _ => ?_
        exact (Complex.continuous_ofReal.comp (hcb a)).smul continuous_const
      have htr : Continuous (fun M : Operator D => M.trace) := by
        unfold Matrix.trace; fun_prop
      have hinner : Continuous (fun ω : ℝ => (hsInner
          (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • parentFactor ρ (A a) O)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • parentFactor ρ (A b) O)).re) := by
        unfold hsInner
        exact Complex.continuous_re.comp (htr.comp ((Continuous.star hsum).mul hsum))
      have hcont : Continuous (fun ω : ℝ => ckgFilter β ω * (hsInner
          (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • parentFactor ρ (A a) O)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • parentFactor ρ (A b) O)).re) := by
        refine Continuous.mul ?_ hinner
        unfold ckgFilter; fun_prop
      exact continuous_nonneg_integral_eq_zero hcont hnn hinteg hintegral

    have hM0 : ∀ ω : ℝ, (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ)
        • parentFactor ρ (A a) O) = 0 := by
      intro ω
      have hF0ω := congrFun hF0 ω
      have hnorm_zero : (hsInner
          (∑ a, ((ckgBump β (ν a) ω : ℝ) : ℂ) • parentFactor ρ (A a) O)
          (∑ b, ((ckgBump β (ν b) ω : ℝ) : ℂ) • parentFactor ρ (A b) O)).re = 0 :=
        (mul_eq_zero.mp hF0ω).resolve_left (ne_of_gt (ckgFilter_pos β ω))
      exact hsInner_self_re_zero_iff hnorm_zero

    exact matrixSum_eq_zero_of_bumpLI hβ ν hν (fun a => parentFactor ρ (A a) O) hM0
  · intro hall
    rw [wplainForm]
    simp only [hall]
    simp only [hsInner, Matrix.trace_zero,
      Matrix.conjTranspose_zero, mul_zero, Finset.sum_const_zero, Complex.zero_re]

/-- Expands the Hilbert-Schmidt inner product as the sum of conjugated entry products. -/
theorem hsInner_eq_sum (U V : Operator D) :
    hsInner U V = ∑ i, ∑ j, star (U i j) * V i j := by
  simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

/-- Expands the real Hilbert-Schmidt inner product using the real and imaginary matrix entries. -/
theorem hsInner_re_sum (U V : Operator D) :
    (hsInner U V).re = ∑ i, ∑ j,
      ((U i j).re * (V i j).re + (U i j).im * (V i j).im) := by
  rw [hsInner_eq_sum]
  have h1 : (∑ i : Fin D, ∑ j : Fin D, star (U i j) * V i j).re
      = ∑ i : Fin D, (∑ j : Fin D, star (U i j) * V i j).re :=
    map_sum complexReAddMonoidHom
      (fun i => ∑ j : Fin D, star (U i j) * V i j) Finset.univ
  rw [h1]
  have h2 : ∀ i : Fin D, (∑ j : Fin D, star (U i j) * V i j).re
      = ∑ j : Fin D, (star (U i j) * V i j).re :=
    fun i => map_sum complexReAddMonoidHom
      (fun j : Fin D => star (U i j) * V i j) Finset.univ
  rw [funext h2]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

/-- Interchanges the two pairs of indices in a fourfold finite real sum. -/
theorem sum_swap4 {α β γ δ : Type*} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ]
    (F : α → β → γ → δ → ℝ) :
    (∑ a, ∑ b, ∑ i, ∑ j, F a b i j) = (∑ i, ∑ j, ∑ a, ∑ b, F a b i j) := by
  calc (∑ a, ∑ b, ∑ i, ∑ j, F a b i j)
      = ∑ a, ∑ i, ∑ b, ∑ j, F a b i j :=
        Finset.sum_congr rfl fun a _ =>
          Finset.sum_comm (f := fun b i => ∑ j, F a b i j)
    _ = ∑ i, ∑ a, ∑ b, ∑ j, F a b i j :=
        Finset.sum_comm (f := fun a i => ∑ b, ∑ j, F a b i j)
    _ = ∑ i, ∑ a, ∑ j, ∑ b, F a b i j :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_comm (f := fun b j => F a b i j)
    _ = ∑ i, ∑ j, ∑ a, ∑ b, F a b i j :=
        Finset.sum_congr rfl fun i _ =>
          Finset.sum_comm (f := fun a j => ∑ b, F a b i j)

/-- Writes a double sum defining a real quadratic form as a dot product with a matrix-vector
product. -/
theorem quad_eq_dotProduct_mulVec {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (u : Fin m → ℝ) :
    ∑ a, ∑ b, M a b * (u a * u b) = u ⬝ᵥ (M *ᵥ u) := by
  have h1 : (∑ a, ∑ b, M a b * (u a * u b))
      = ∑ a, (u a * (∑ b, M a b * u b)) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum Finset.univ (fun b => M a b * u b) (u a)]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h1]
  rfl

/-- Contracting a positive semidefinite real matrix with an operator Gram matrix yields a
nonnegative real number. -/
theorem gramContraction_nonneg {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.PosSemidef)
    (B : Fin m → Operator D) :
    0 ≤ ∑ a, ∑ b, M a b * (hsInner (B a) (B b)).re := by
  have e1 : ∀ a b : Fin m, M a b * (hsInner (B a) (B b)).re
      = ∑ i : Fin D, ∑ j : Fin D, M a b *
          ((B a i j).re * (B b i j).re + (B a i j).im * (B b i j).im) := by
    intro a b
    rw [hsInner_re_sum, Finset.mul_sum Finset.univ _ (M a b)]
    exact Finset.sum_congr rfl fun i _ => Finset.mul_sum Finset.univ _ (M a b)
  have e2 : ∑ a, ∑ b, M a b * (hsInner (B a) (B b)).re
      = ∑ i, ∑ j, ∑ a, ∑ b, M a b *
          ((B a i j).re * (B b i j).re + (B a i j).im * (B b i j).im) := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => e1 a b]
    exact sum_swap4 (fun a b i j => M a b *
      ((B a i j).re * (B b i j).re + (B a i j).im * (B b i j).im))
  rw [e2]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have e3 : (∑ a, ∑ b, M a b *
        ((B a i j).re * (B b i j).re + (B a i j).im * (B b i j).im))
      = (∑ a, ∑ b, M a b * ((B a i j).re * (B b i j).re))
        + (∑ a, ∑ b, M a b * ((B a i j).im * (B b i j).im)) := by
    simp only [mul_add, Finset.sum_add_distrib]
  rw [e3, quad_eq_dotProduct_mulVec M (fun a => (B a i j).re),
    quad_eq_dotProduct_mulVec M (fun a => (B a i j).im)]
  exact add_nonneg (hM.dotProduct_mulVec_nonneg _) (hM.dotProduct_mulVec_nonneg _)

noncomputable def ckgDiagControlMat {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => ckgWeight β (ν a) (ν b) / 2
    - (if a = b then 2 * kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a else 0)

/-- Expands each entry of `ckgDiagControlMat` into half the CKG weight minus its diagonal
kappa-row correction. -/
theorem ckgDiagControlMat_apply {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) (a b : Fin m) :
    ckgDiagControlMat β ν a b
      = ckgWeight β (ν a) (ν b) / 2
        - (if a = b then 2 * kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a else 0) :=
  rfl

/-- Positive semidefiniteness of the diagonal control matrix bounds twice the kappa-weighted
parent-factor norm sum by the real plain form. -/
theorem ckgDiagControl {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hM : (ckgDiagControlMat β ν).PosSemidef)
    (ρ : Operator D) (A : Fin m → Operator D) (O : Operator D) :
    2 * (∑ a, kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a
      * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re)
      ≤ (wplainForm (fun a b => ckgWeight β (ν a) (ν b)) ρ A O).re := by
  have hE0 : (wplainForm (fun a b => ckgWeight β (ν a) (ν b)) ρ A O).re
      = (∑ a, ∑ b, ckgWeight β (ν a) (ν b)
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re) / 2 :=
    wplainForm_re_eq _ ρ A O
  have hcon : 0 ≤ ∑ a, ∑ b, (ckgDiagControlMat β ν) a b
      * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re :=
    gramContraction_nonneg _ hM _

  have hterm : ∀ a b : Fin m, (ckgWeight β (ν a) (ν b) / 2)
        * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re
      = (ckgDiagControlMat β ν) a b
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re
        + (if a = b then 2 * kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a else 0)
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re := by
    intro a b
    rw [ckgDiagControlMat_apply β ν a b]
    by_cases hab : a = b
    · simp only [ite_eq_left hab]; ring
    · simp only [ite_eq_right hab]; ring
  have hsumsplit : (∑ a, ∑ b, (ckgWeight β (ν a) (ν b) / 2)
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re)
      = (∑ a, ∑ b, (ckgDiagControlMat β ν) a b
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re)
        + (∑ a, ∑ b, (if a = b then
            2 * kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a else 0)
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re) := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => hterm a b]
    simp only [Finset.sum_add_distrib]

  have hcollapse : (∑ a, ∑ b, (if a = b then
            2 * kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a else 0)
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re)
      = ∑ a, (2 * kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    have key : ∀ b : Fin m, (if a = b then
          2 * kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a else 0)
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re
        = if a = b then (2 * kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a
            * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re) else 0 := by
      intro b; split_ifs <;> ring
    rw [Finset.sum_congr rfl fun b _ => key b]
    rw [Finset.sum_ite_eq Finset.univ a (fun b => 2 * kappaRow
      (fun x y => ckgWeight β (ν x) (ν y)) β ν a
      * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re)]
    simp

  have hhalf : (∑ a, ∑ b, (ckgWeight β (ν a) (ν b) / 2)
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re)
      = (∑ a, ∑ b, ckgWeight β (ν a) (ν b)
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re) / 2 := by
    rw [Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      show (ckgWeight β (ν a) (ν b) / 2)
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re
        = (ckgWeight β (ν a) (ν b)
            * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re) / 2 from by
        ring]
    rw [Finset.sum_congr rfl fun a _ => by rw [← Finset.sum_div]]
    rw [← Finset.sum_div]

  have hT : ∑ a, (2 * kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a
        * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re)
      = 2 * (∑ a, kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a
        * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re) := by
    rw [Finset.sum_congr rfl fun a _ => show (2 * kappaRow
      (fun x y => ckgWeight β (ν x) (ν y)) β ν a
      * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re)
      = 2 * (kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a
        * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re) from by ring]
    exact (Finset.mul_sum Finset.univ (fun a => kappaRow
      (fun x y => ckgWeight β (ν x) (ν y)) β ν a
      * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re) 2).symm
  linarith [hE0, hcon, hsumsplit, hcollapse, hhalf, hT]

/-- Positive semidefiniteness of `ckgDiagControlMat` implies CKG domination for any operator
family. -/
theorem ckgDomination_of_mpsd {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hM : (ckgDiagControlMat β ν).PosSemidef)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgDomination β ρ ν A := by
  intro X
  exact domination_of_diag_control (fun a b => (ckgWeight_pos β (ν a) (ν b)).le) β ρ ν A
    (fun O' => ckgDiagControl β ν hM ρ A O') X

/-- Rewrites a sum with one erased index as a full sum whose contribution at that index is zero. -/
theorem sum_erase_eq_ite {m : ℕ} (a : Fin m) (f : Fin m → ℝ) :
    ∑ b ∈ Finset.univ.erase a, f b = ∑ b, (if a = b then 0 else f b) := by
  classical
  have step1 : ∑ b ∈ Finset.univ.erase a, f b
      = ∑ b ∈ Finset.univ.erase a, (if a = b then 0 else f b) :=
    Finset.sum_congr rfl fun b hb => by
      have hne : a ≠ b := fun h => (Finset.mem_erase.mp hb).1 h.symm
      simp [hne]
  have step2 : ∑ b ∈ Finset.univ.erase a, (if a = b then 0 else f b)
      = ∑ b : Fin m, (if a = b then 0 else f b) :=
    Finset.sum_subset (Finset.erase_subset a Finset.univ) fun b _ hb => by
      have hba : b = a := by
        by_contra h
        exact hb (Finset.mem_erase.mpr ⟨h, Finset.mem_univ b⟩)
      simp [hba]
  rw [step1, step2]

/-- Exchanges the indices of a double sum restricted to unequal indices. -/
theorem sum_erase_swap {m : ℕ} (F : Fin m → Fin m → ℝ) :
    ∑ a, ∑ b ∈ Finset.univ.erase a, F a b
      = ∑ b, ∑ a ∈ Finset.univ.erase b, F a b := by
  have eL : ∑ a, ∑ b ∈ Finset.univ.erase a, F a b
      = ∑ a, ∑ b, (if a = b then 0 else F a b) :=
    Finset.sum_congr rfl fun a _ => sum_erase_eq_ite a (fun b => F a b)
  have eR : ∀ b : Fin m, (∑ a ∈ Finset.univ.erase b, F a b)
      = ∑ a, (if a = b then 0 else F a b) := by
    intro b
    rw [sum_erase_eq_ite b (fun a => F a b)]
    refine Finset.sum_congr rfl fun a _ => ?_
    by_cases h : a = b
    · simp [h]
    · simp [h, Ne.symm h]
  rw [eL, Finset.sum_congr rfl fun b _ => eR b, Finset.sum_comm]

/-- Splits a finite sum into its value at one index and the sum over the remaining indices. -/
theorem sum_univ_diag_add_erase {m : ℕ} (a : Fin m) (f : Fin m → ℝ) :
    ∑ b, f b = f a + ∑ b ∈ Finset.univ.erase a, f b := by
  rw [← Finset.sum_insert (fun h => (Finset.mem_erase.mp h).1 rfl),
    Finset.insert_erase (Finset.mem_univ a)]

/-- A symmetric real matrix with each diagonal entry dominating the sum of absolute off-diagonal
entries is positive semidefinite. -/
theorem gramDiagDominance_posSemidef {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ)
    (hsymm : ∀ a b, M a b = M b a)
    (hdom : ∀ a, ∑ b ∈ Finset.univ.erase a, |M a b| ≤ M a a) :
    M.PosSemidef := by
  classical
  have hherm : M.IsHermitian := by
    ext a b
    simp [Matrix.conjTranspose_apply, hsymm a b]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm ?_
  intro x
  show 0 ≤ x ⬝ᵥ (M *ᵥ x)

  have hsplit : ∀ a : Fin m, (∑ b, M a b * (x a * x b))
      = M a a * x a ^ 2 + ∑ b ∈ Finset.univ.erase a, M a b * (x a * x b) := by
    intro a
    rw [pow_two]
    exact sum_univ_diag_add_erase a (fun b => M a b * (x a * x b))
  have hquad : x ⬝ᵥ (M *ᵥ x)
      = ∑ a, M a a * x a ^ 2 + ∑ a, ∑ b ∈ Finset.univ.erase a, M a b * (x a * x b) := by
    rw [← quad_eq_dotProduct_mulVec M x,
      Finset.sum_congr rfl fun a _ => hsplit a, Finset.sum_add_distrib]
  rw [hquad]

  have hamgm : ∀ a b : Fin m,
      -((|M a b| / 2) * (x a ^ 2 + x b ^ 2)) ≤ M a b * (x a * x b) := by
    intro a b
    have hsq : (|x a| - |x b|) ^ 2 ≥ 0 := sq_nonneg _
    have hexp : (|x a| - |x b|) ^ 2
        = x a ^ 2 - 2 * (|x a| * |x b|) + x b ^ 2 := by
      have h1 : (|x a| - |x b|) ^ 2
          = |x a| ^ 2 - 2 * (|x a| * |x b|) + |x b| ^ 2 := by ring
      rw [h1, sq_abs, sq_abs]
    rw [hexp] at hsq
    have h3 : |M a b * (x a * x b)| = |M a b| * (|x a| * |x b|) := by
      rw [abs_mul, abs_mul]
    have h4 : M a b * (x a * x b) ≥ -|M a b * (x a * x b)| := neg_abs_le _
    rw [h3] at h4
    have h5 : |M a b| * (|x a| * |x b|) ≤ |M a b| * ((x a ^ 2 + x b ^ 2) / 2) := by
      have h2 : |x a| * |x b| ≤ (x a ^ 2 + x b ^ 2) / 2 := by linarith
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have h6 : |M a b| * ((x a ^ 2 + x b ^ 2) / 2) = (|M a b| / 2) * (x a ^ 2 + x b ^ 2) := by
      ring
    rw [h6] at h5
    linarith

  have hbound : -(∑ a, ∑ b ∈ Finset.univ.erase a, (|M a b| / 2) * (x a ^ 2 + x b ^ 2))
      ≤ ∑ a, ∑ b ∈ Finset.univ.erase a, M a b * (x a * x b) := by
    have hper : ∀ a : Fin m,
        -(∑ b ∈ Finset.univ.erase a, (|M a b| / 2) * (x a ^ 2 + x b ^ 2))
        ≤ ∑ b ∈ Finset.univ.erase a, M a b * (x a * x b) := by
      intro a
      have h := Finset.sum_le_sum (s := Finset.univ.erase a) fun b _ => hamgm a b
      rw [Finset.sum_neg_distrib] at h
      exact h
    have hsum := Finset.sum_le_sum (s := Finset.univ) fun a _ => hper a
    rw [Finset.sum_neg_distrib] at hsum
    exact hsum

  have hkey : (∑ a, ∑ b ∈ Finset.univ.erase a, (|M a b| / 2) * (x a ^ 2 + x b ^ 2))
      ≤ ∑ a, M a a * x a ^ 2 := by
    have hsplit2 : ∀ a : Fin m, (∑ b ∈ Finset.univ.erase a,
          (|M a b| / 2) * (x a ^ 2 + x b ^ 2))
        = (∑ b ∈ Finset.univ.erase a, |M a b| / 2 * x a ^ 2)
          + (∑ b ∈ Finset.univ.erase a, |M a b| / 2 * x b ^ 2) := by
      intro a
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    rw [Finset.sum_congr rfl fun a _ => hsplit2 a, Finset.sum_add_distrib]

    have hT1 : ∑ a, ∑ b ∈ Finset.univ.erase a, |M a b| / 2 * x a ^ 2
        ≤ (∑ a, M a a * x a ^ 2) / 2 := by
      have e1 : ∑ a, ∑ b ∈ Finset.univ.erase a, |M a b| / 2 * x a ^ 2
          = ∑ a, (∑ b ∈ Finset.univ.erase a, |M a b|) * x a ^ 2 / 2 := by
        refine Finset.sum_congr rfl fun a _ => ?_
        have hmul : (∑ b ∈ Finset.univ.erase a, |M a b| / 2) * x a ^ 2
            = ∑ b ∈ Finset.univ.erase a, |M a b| / 2 * x a ^ 2 :=
          Finset.sum_mul (Finset.univ.erase a) (fun b => |M a b| / 2) (x a ^ 2)
        have hdiv : (∑ b ∈ Finset.univ.erase a, |M a b| / 2)
            = (∑ b ∈ Finset.univ.erase a, |M a b|) / 2 :=
          (Finset.sum_div (Finset.univ.erase a) (fun b => |M a b|) 2).symm
        rw [← hmul, hdiv]
        ring
      rw [e1]
      have hle : ∀ a : Fin m, (∑ b ∈ Finset.univ.erase a, |M a b|) * x a ^ 2 / 2
          ≤ M a a * x a ^ 2 / 2 := by
        intro a
        calc (∑ b ∈ Finset.univ.erase a, |M a b|) * x a ^ 2 / 2
            = (∑ b ∈ Finset.univ.erase a, |M a b|) * (x a ^ 2 / 2) := by ring
          _ ≤ M a a * (x a ^ 2 / 2) :=
              mul_le_mul_of_nonneg_right (hdom a) (by positivity)
          _ = M a a * x a ^ 2 / 2 := by ring
      have hsum1 : ∑ a, (∑ b ∈ Finset.univ.erase a, |M a b|) * x a ^ 2 / 2
          ≤ ∑ a, M a a * x a ^ 2 / 2 :=
        Finset.sum_le_sum fun a _ => hle a
      rw [Finset.sum_div]
      exact hsum1

    have hT2 : ∑ a, ∑ b ∈ Finset.univ.erase a, |M a b| / 2 * x b ^ 2
        ≤ (∑ a, M a a * x a ^ 2) / 2 := by
      rw [sum_erase_swap (fun a b => |M a b| / 2 * x b ^ 2)]
      have eswap : ∀ b : Fin m, (∑ a ∈ Finset.univ.erase b, |M a b| / 2 * x b ^ 2)
          = (∑ a ∈ Finset.univ.erase b, |M a b|) * x b ^ 2 / 2 := by
        intro b
        have hmul : (∑ a ∈ Finset.univ.erase b, |M a b| / 2) * x b ^ 2
            = ∑ a ∈ Finset.univ.erase b, |M a b| / 2 * x b ^ 2 :=
          Finset.sum_mul (Finset.univ.erase b) (fun a => |M a b| / 2) (x b ^ 2)
        have hdiv : (∑ a ∈ Finset.univ.erase b, |M a b| / 2)
            = (∑ a ∈ Finset.univ.erase b, |M a b|) / 2 :=
          (Finset.sum_div (Finset.univ.erase b) (fun a => |M a b|) 2).symm
        rw [← hmul, hdiv]
        ring
      have hsymm' : ∀ b : Fin m, (∑ a ∈ Finset.univ.erase b, |M a b|)
          = ∑ a ∈ Finset.univ.erase b, |M b a| :=
        fun b => Finset.sum_congr rfl fun a _ => congrArg abs (hsymm a b)
      have hconv2 : ∀ b : Fin m, (∑ a ∈ Finset.univ.erase b, |M a b|) * x b ^ 2 / 2
          = (∑ a ∈ Finset.univ.erase b, |M b a|) * x b ^ 2 / 2 :=
        fun b => by rw [hsymm' b]
      rw [Finset.sum_congr rfl fun b _ => eswap b,
        Finset.sum_congr rfl fun b _ => hconv2 b]
      have hsum2 : ∑ b, (∑ a ∈ Finset.univ.erase b, |M b a|) * x b ^ 2 / 2
          ≤ ∑ b, M b b * x b ^ 2 / 2 :=
        Finset.sum_le_sum fun b _ => by
          calc (∑ a ∈ Finset.univ.erase b, |M b a|) * x b ^ 2 / 2
              = (∑ a ∈ Finset.univ.erase b, |M b a|) * (x b ^ 2 / 2) := by ring
            _ ≤ M b b * (x b ^ 2 / 2) :=
                mul_le_mul_of_nonneg_right (hdom b) (by positivity)
            _ = M b b * x b ^ 2 / 2 := by ring
      rw [Finset.sum_div]
      exact hsum2
    linarith

  linarith [hkey, hbound]

/-- Expands the CKG kappa row as the sum of CKG weights times the difference between one half
and the phase kernel. -/
theorem kappaRow_ckg {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) (a : Fin m) :
    kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a
      = ∑ b, ckgWeight β (ν a) (ν b) * (1 / 2 - phaseKernel β (ν a - ν b)) := by
  have hEq := kappaRow_eq (fun x y => ckgWeight β (ν x) (ν y)) β ν a
  have h2 : (∑ b, ckgWeight β (ν b) (ν a)
        * (1 / 2 - phaseKernel β (ν b - ν a)))
      = ∑ b, ckgWeight β (ν a) (ν b) * (1 / 2 - phaseKernel β (ν a - ν b)) := by
    refine Finset.sum_congr rfl fun b _ => ?_
    have hne : ν a - ν b = -(ν b - ν a) := by ring
    rw [ckgWeight_symm β (ν b) (ν a), hne, phaseKernel_neg β (ν b - ν a)]
  rw [hEq, h2]
  ring

/-- Expands the CKG kappa row as an off-diagonal sum, omitting the vanishing diagonal
contribution. -/
theorem kappaRow_ckg_erase {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) (a : Fin m) :
    kappaRow (fun x y => ckgWeight β (ν x) (ν y)) β ν a
      = ∑ b ∈ Finset.univ.erase a,
          ckgWeight β (ν a) (ν b) * (1 / 2 - phaseKernel β (ν a - ν b)) := by
  rw [kappaRow_ckg β ν a, sum_univ_diag_add_erase a
    (fun b => ckgWeight β (ν a) (ν b) * (1 / 2 - phaseKernel β (ν a - ν b))),
    sub_self, phaseKernel_self β, sub_self, mul_zero, zero_add]

/-- The stated CKG row-dominance inequalities imply positive semidefiniteness of the diagonal
control matrix. -/
theorem ckgDiagControlMat_posSemidef_of_rowdom {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hrow : ∀ a, ∑ b ∈ Finset.univ.erase a, ckgWeight β (ν a) (ν b)
        * (3 - 4 * phaseKernel β (ν a - ν b)) ≤ ckgWeight β (ν a) (ν a)) :
    (ckgDiagControlMat β ν).PosSemidef := by

  have hsymm : ∀ a b : Fin m,
      (ckgDiagControlMat β ν) a b = (ckgDiagControlMat β ν) b a := by
    intro a b
    rw [ckgDiagControlMat_apply β ν a b, ckgDiagControlMat_apply β ν b a]
    by_cases hab : a = b
    · simp [hab]
    · rw [ite_eq_right hab, ite_eq_right (Ne.symm hab), ckgWeight_symm β (ν a) (ν b)]

  have hoff : ∀ a b : Fin m, b ∈ Finset.univ.erase a →
      |(ckgDiagControlMat β ν) a b| = ckgWeight β (ν a) (ν b) / 2 := by
    intro a b hb
    have hne : a ≠ b := Ne.symm (Finset.mem_erase.mp hb).1
    rw [ckgDiagControlMat_apply β ν a b, ite_eq_right hne, sub_zero]
    exact abs_of_pos (div_pos (ckgWeight_pos β (ν a) (ν b)) two_pos)

  have hdom : ∀ a : Fin m, ∑ b ∈ Finset.univ.erase a, |(ckgDiagControlMat β ν) a b|
      ≤ (ckgDiagControlMat β ν) a a := by
    intro a
    have hsumabs : ∑ b ∈ Finset.univ.erase a, |(ckgDiagControlMat β ν) a b|
        = ∑ b ∈ Finset.univ.erase a, ckgWeight β (ν a) (ν b) / 2 :=
      Finset.sum_congr rfl fun b hb => hoff a b hb
    rw [hsumabs, ckgDiagControlMat_apply β ν a a, ite_eq_left (rfl : a = a),
      kappaRow_ckg_erase β ν a]

    have hconv : 2 * (∑ b ∈ Finset.univ.erase a, ckgWeight β (ν a) (ν b) / 2)
        + 4 * ∑ b ∈ Finset.univ.erase a, ckgWeight β (ν a) (ν b)
            * (1 / 2 - phaseKernel β (ν a - ν b))
        = ∑ b ∈ Finset.univ.erase a, ckgWeight β (ν a) (ν b)
            * (3 - 4 * phaseKernel β (ν a - ν b)) := by
      rw [Finset.mul_sum (Finset.univ.erase a) _ 2, Finset.mul_sum (Finset.univ.erase a) _ 4,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by ring
    linarith [hrow a, hconv]
  exact gramDiagDominance_posSemidef _ hsymm hdom

/-- The stated CKG row-dominance inequalities imply CKG domination for any operator family. -/
theorem ckgDomination_of_rowdom {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hrow : ∀ a, ∑ b ∈ Finset.univ.erase a, ckgWeight β (ν a) (ν b)
        * (3 - 4 * phaseKernel β (ν a - ν b)) ≤ ckgWeight β (ν a) (ν a))
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgDomination β ρ ν A :=
  ckgDomination_of_mpsd β ν (ckgDiagControlMat_posSemidef_of_rowdom β ν hrow) ρ A

/-- The hyperbolic sine of a nonnegative real number is nonnegative. -/
theorem sinh_nonneg' {x : ℝ} (hx : 0 ≤ x) : 0 ≤ Real.sinh x := by
  rw [Real.sinh_eq]
  have h3 : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  exact div_nonneg (sub_nonneg.2 h3) zero_le_two

/-- For nonnegative `t`, the hyperbolic sine is at most `t` times the hyperbolic cosine. -/
theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) : Real.sinh t ≤ t * Real.cosh t := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => y * Real.cosh y - Real.sinh y)
      (x * Real.sinh x) x := by
    intro x
    have h1 := (hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)
    have h2 := h1.sub (Real.hasDerivAt_sinh x)
    convert! h2 using 1; (try simp only [id_eq, one_mul]); ring
  have hcont : ContinuousOn (fun y : ℝ => y * Real.cosh y - Real.sinh y) (Set.Ici 0) :=
    (by fun_prop : Continuous (fun y : ℝ => y * Real.cosh y - Real.sinh y)).continuousOn
  have hdw : ∀ x ∈ interior (Set.Ici 0), HasDerivWithinAt
      (fun y : ℝ => y * Real.cosh y - Real.sinh y)
      (x * Real.sinh x) (interior (Set.Ici 0)) x :=
    fun x _ => (hd x).hasDerivWithinAt
  have hnn : ∀ x ∈ interior (Set.Ici 0), 0 ≤ x * Real.sinh x := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt (by simpa using hx)
    exact mul_nonneg hx0 (sinh_nonneg' hx0)
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont hdw hnn
  have hle := hmono (Set.mem_Ici.2 (le_refl 0)) (Set.mem_Ici.2 ht) ht
  simp only [Real.cosh_zero, Real.sinh_zero, sub_zero] at hle
  simpa using hle

/-- For nonnegative `t`, three minus twice the reciprocal hyperbolic cosine is bounded by the
exponential of the square. -/
theorem three_sub_two_div_cosh_le_exp_sq {t : ℝ} (ht : 0 ≤ t) :
    3 - 2 / Real.cosh t ≤ Real.exp (t ^ 2) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun y : ℝ => Real.exp (y ^ 2) + 2 / Real.cosh y - 3)
      (2 * x * Real.exp (x ^ 2) - 2 * Real.sinh x / Real.cosh x ^ 2) x := by
    intro x
    have hp : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have he : HasDerivAt (fun y : ℝ => Real.exp (y ^ 2))
        (Real.exp (x ^ 2) * (2 * x)) x := hp.exp
    have hdiv := (hasDerivAt_const x (2:ℝ)).div (Real.hasDerivAt_cosh x)
      (ne_of_gt (Real.cosh_pos x))
    have h3 := (he.add hdiv).sub (hasDerivAt_const x (3:ℝ))
    convert! h3 using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun y : ℝ => Real.exp (y ^ 2) + 2 / Real.cosh y - 3)
      (Set.Ici 0) :=
    (by
      refine Continuous.sub (Continuous.add ?_ ?_) continuous_const
      · exact Real.continuous_exp.comp (by fun_prop)
      · exact continuous_const.div Real.continuous_cosh
          (fun x => ne_of_gt (Real.cosh_pos x)) :
      Continuous (fun y : ℝ => Real.exp (y ^ 2) + 2 / Real.cosh y - 3)).continuousOn
  have hdw : ∀ x ∈ interior (Set.Ici 0), HasDerivWithinAt
      (fun y : ℝ => Real.exp (y ^ 2) + 2 / Real.cosh y - 3)
      (2 * x * Real.exp (x ^ 2) - 2 * Real.sinh x / Real.cosh x ^ 2)
      (interior (Set.Ici 0)) x :=
    fun x _ => (hd x).hasDerivWithinAt
  have hnn : ∀ x ∈ interior (Set.Ici 0),
      0 ≤ 2 * x * Real.exp (x ^ 2) - 2 * Real.sinh x / Real.cosh x ^ 2 := by
    intro x hx
    have hx0 : 0 ≤ x := le_of_lt (by simpa using hx)
    have hc1 : 1 ≤ Real.cosh x := Real.one_le_cosh x
    have hc2 : 0 < Real.cosh x := lt_of_lt_of_le zero_lt_one hc1
    have step1 : Real.sinh x / Real.cosh x ^ 2 ≤ x / Real.cosh x := by
      rw [div_le_div_iff₀ (pow_pos hc2 2) hc2]
      calc Real.sinh x * Real.cosh x
          ≤ x * Real.cosh x * Real.cosh x :=
            mul_le_mul_of_nonneg_right (sinh_le_mul_cosh hx0) (le_of_lt hc2)
        _ = x * Real.cosh x ^ 2 := by ring
    have step2 : x / Real.cosh x ≤ x := div_le_self hx0 hc1
    have h2 : 2 * (Real.sinh x / Real.cosh x ^ 2) ≤ 2 * x :=
      mul_le_mul_of_nonneg_left (le_trans step1 step2) zero_le_two
    have hxe : (2:ℝ) * x ≤ 2 * x * Real.exp (x ^ 2) := by
      have h := mul_le_mul_of_nonneg_left (Real.one_le_exp (sq_nonneg x))
        (mul_nonneg zero_le_two hx0)
      simpa only [mul_one] using h
    have hsplit : 2 * Real.sinh x / Real.cosh x ^ 2
        = 2 * (Real.sinh x / Real.cosh x ^ 2) := by ring
    rw [hsplit]
    linarith
  have hmono := monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0) hcont hdw hnn
  have hle : Real.exp ((0:ℝ) ^ 2) + 2 / Real.cosh 0 - 3
      ≤ Real.exp (t ^ 2) + 2 / Real.cosh t - 3 :=
    hmono (Set.mem_Ici.2 (le_refl 0)) (Set.mem_Ici.2 ht) ht
  have hz : Real.exp ((0:ℝ) ^ 2) + 2 / Real.cosh 0 - 3 = 0 := by
    norm_num [Real.cosh_zero]
  rw [hz] at hle
  linarith

/-- Expresses an off-diagonal CKG weight as the corresponding diagonal weight times an explicit
exponential ratio. -/
theorem ckgWeight_ratio {β : ℝ} (x y : ℝ) :
    ckgWeight β x y = ckgWeight β x x * Real.exp
      (-(β * (y - x) / 4 + (β ^ 2 / 16) * ((y - x) ^ 2 + 2 * y ^ 2 - 2 * x ^ 2))) := by
  rw [ckgWeight, ckgWeight]
  have hsplit : (-(β * (x + y)) / 4 - (β ^ 2 / 16) * (3 * x ^ 2 - 2 * x * y + 3 * y ^ 2))
      = (-(β * (x + x)) / 4 - (β ^ 2 / 16) * (3 * x ^ 2 - 2 * x * x + 3 * x ^ 2))
        + (-(β * (y - x) / 4 + (β ^ 2 / 16) * ((y - x) ^ 2 + 2 * y ^ 2 - 2 * x ^ 2))) := by
    ring
  rw [hsplit, Real.exp_add]
  ring

/-- CKG domination holds for two frequencies symmetric about minus the reciprocal inverse
temperature. -/
theorem ckgDomination_pair_bohrCenter {β : ℝ} (hβ : 0 < β) (s : ℝ) (hs : 0 ≤ s)
    (ρ : Operator D) (A : Fin 2 → Operator D) :
    ckgDomination β ρ ![-1 / β - s, -1 / β + s] A := by
  have hβne : β ≠ 0 := ne_of_gt hβ
  set ν : Fin 2 → ℝ := ![-1 / β - s, -1 / β + s] with hνdef
  have hν0 : ν 0 = -1 / β - s := by simp [hνdef]
  have hν1 : ν 1 = -1 / β + s := by simp [hνdef]
  have htpos : 0 ≤ β * s / 2 := by positivity

  have hab01 : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> try exact absurd rfl hab
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩

  have hpair : ∀ a b : Fin 2, a ≠ b → (ν a = -1 / β - s ∧ ν b = -1 / β + s)
      ∨ (ν a = -1 / β + s ∧ ν b = -1 / β - s) := by
    intro a b hab
    rcases hab01 a b hab with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · subst a; subst b; exact Or.inl ⟨hν0, hν1⟩
    · subst a; subst b; exact Or.inr ⟨hν1, hν0⟩

  have hratio : ∀ a b : Fin 2, a ≠ b → ckgWeight β (ν a) (ν b)
      = ckgWeight β (ν a) (ν a) * Real.exp (-((β * s / 2) ^ 2)) := by
    intro a b hab
    rcases hpair a b hab with ⟨hax, hby⟩ | ⟨hax, hby⟩
    · rw [hax, hby, ckgWeight_ratio]
      congr 1
      field_simp
      ring
    · rw [hax, hby, ckgWeight_ratio]
      congr 1
      field_simp
      ring

  have hpk : ∀ a b : Fin 2, a ≠ b → (3 - 4 * phaseKernel β (ν a - ν b))
      = 3 - 2 / Real.cosh (β * s / 2) := by
    intro a b hab
    rcases hpair a b hab with ⟨hax, hby⟩ | ⟨hax, hby⟩
    · have harg : β * ((-1 / β - s) - (-1 / β + s)) / 4 = -(β * s / 2) := by
        field_simp
        ring
      rw [hax, hby, phaseKernel, harg, Real.cosh_neg]
      ring
    · have harg : β * ((-1 / β + s) - (-1 / β - s)) / 4 = β * s / 2 := by
        field_simp
        ring
      rw [hax, hby, phaseKernel, harg]
      ring

  have key : Real.exp (-((β * s / 2) ^ 2)) * (3 - 2 / Real.cosh (β * s / 2)) ≤ 1 := by
    calc Real.exp (-((β * s / 2) ^ 2)) * (3 - 2 / Real.cosh (β * s / 2))
        ≤ Real.exp (-((β * s / 2) ^ 2)) * Real.exp ((β * s / 2) ^ 2) :=
          mul_le_mul_of_nonneg_left (three_sub_two_div_cosh_le_exp_sq htpos)
            (by positivity)
      _ = 1 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]

  refine ckgDomination_of_rowdom β ν (fun a => ?_) ρ A
  have hother : ∀ a : Fin 2, ∃ b : Fin 2, b ≠ a ∧ ∀ c : Fin 2, c ≠ a → c = b := by
    intro a
    by_cases ha : a = 0
    · refine ⟨1, by rw [ha]; decide, fun c hc => ?_⟩
      rcases hab01 c a hc with ⟨_, h1⟩ | ⟨h0, _⟩
      · exact absurd h1 (by rw [ha]; decide)
      · exact h0
    · refine ⟨0, Ne.symm ha, fun c hc => ?_⟩
      rcases hab01 c a hc with ⟨h01, _⟩ | ⟨_, h1⟩
      · exact h01
      · exact absurd h1 ha
  obtain ⟨b, hbne, hbuniq⟩ := hother a
  have hsum : ∑ c ∈ Finset.univ.erase a, (fun c => ckgWeight β (ν a) (ν c)
        * (3 - 4 * phaseKernel β (ν a - ν c))) c
      = ckgWeight β (ν a) (ν b) * (3 - 4 * phaseKernel β (ν a - ν b)) :=
    Finset.sum_eq_single_of_mem b (by
      simp only [Finset.mem_erase, Finset.mem_univ]
      exact ⟨hbne, trivial⟩) (fun c hcm hcn => by
      have hcb : c = b := hbuniq c (fun h => (Finset.mem_erase.mp hcm).1 h)
      exact absurd hcb hcn)
  rw [hsum, hratio a b (Ne.symm hbne), hpk a b (Ne.symm hbne)]
  calc ckgWeight β (ν a) (ν a) * Real.exp (-((β * s / 2) ^ 2))
        * (3 - 2 / Real.cosh (β * s / 2))
      = ckgWeight β (ν a) (ν a)
        * (Real.exp (-((β * s / 2) ^ 2)) * (3 - 2 / Real.cosh (β * s / 2))) := by
        ring
    _ ≤ ckgWeight β (ν a) (ν a) * 1 :=
        mul_le_mul_of_nonneg_left key (ckgWeight_pos β (ν a) (ν a)).le
    _ = ckgWeight β (ν a) (ν a) := mul_one _

/-- The real weighted damped form is a parent-factor Gram sum weighted by the phase kernel. -/
theorem wdampedForm_re {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (β : ℝ) (ρ : Operator D)
    (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D) :
    (wdampedForm w β ρ ν A X).re = ∑ a, ∑ b, (w a b * phaseKernel β (ν a - ν b)) *
      (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re := by
  rw [wdampedForm]
  have h1 : (∑ a : ι, ∑ b : ι, (↑(w a b * phaseKernel β (ν a - ν b)) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re
      = ∑ a : ι, (∑ b : ι, (↑(w a b * phaseKernel β (ν a - ν b)) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re :=
    map_sum complexReAddMonoidHom (fun a => ∑ b : ι,
      (↑(w a b * phaseKernel β (ν a - ν b)) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)) Finset.univ
  rw [h1]
  have h2 : ∀ a : ι, (∑ b : ι, (↑(w a b * phaseKernel β (ν a - ν b)) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re
      = ∑ b : ι, ((↑(w a b * phaseKernel β (ν a - ν b)) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re :=
    fun a => map_sum complexReAddMonoidHom (fun b : ι =>
      (↑(w a b * phaseKernel β (ν a - ν b)) : ℂ) *
      hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)) Finset.univ
  rw [funext h2]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
    simp [Complex.mul_re]

noncomputable def ckgDomKernel {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => ckgWeight β (ν a) (ν b) * (3 / 4 - phaseKernel β (ν a - ν b))

/-- Each entry of `ckgDomKernel` is the CKG weight times the difference between three quarters
and the phase kernel. -/
theorem ckgDomKernel_apply {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) (a b : Fin m) :
    ckgDomKernel β ν a b
      = ckgWeight β (ν a) (ν b) * (3 / 4 - phaseKernel β (ν a - ν b)) :=
  rfl

/-- Positive semidefiniteness of `ckgDomKernel` implies CKG domination for any operator family. -/
theorem ckgDomination_of_kernelPSD {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hN : (ckgDomKernel β ν).PosSemidef)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgDomination β ρ ν A := by
  intro X
  set w : Fin m → Fin m → ℝ := fun a b => ckgWeight β (ν a) (ν b) with hwdef
  have key : 3 / 2 * (wplainForm w ρ A X).re - (wdampedForm w β ρ ν A X).re
      = ∑ a, ∑ b, (ckgDomKernel β ν) a b
          * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re := by
    rw [wplainForm_re_eq w ρ A X, wdampedForm_re w β ρ ν A X]
    have hinner : ∀ a : Fin m, (∑ b, w a b
            * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re) / 2
        = ∑ b, (w a b / 2)
            * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re := by
      intro a
      rw [Finset.sum_div Finset.univ _ (2:ℝ)]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hdiv : (∑ a, ∑ b, w a b
          * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re) / 2
        = ∑ a, ∑ b, (w a b / 2)
            * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re := by
      rw [Finset.sum_div Finset.univ _ (2:ℝ)]
      exact Finset.sum_congr rfl fun a _ => hinner a
    have hm : (3 / 2 : ℝ) * (∑ a, ∑ b, (w a b / 2)
          * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re)
        = ∑ a, ∑ b, (3 / 2 : ℝ) * ((w a b / 2)
            * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re) := by
      rw [Finset.mul_sum Finset.univ _ (3 / 2 : ℝ)]
      exact Finset.sum_congr rfl fun a _ => Finset.mul_sum Finset.univ _ (3 / 2 : ℝ)
    rw [hdiv, hm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by
      rw [ckgDomKernel_apply β ν a b]
      ring
  have hcon : 0 ≤ ∑ a, ∑ b, (ckgDomKernel β ν) a b
      * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re :=
    gramContraction_nonneg _ hN _
  rw [← key] at hcon
  have hE0 : (wplainForm w ρ A X).re = (ckgPlainForm β ρ ν A X).re := rfl
  have hEg : (wdampedForm w β ρ ν A X).re = (ckgDampedForm β ρ ν A X).re := rfl
  rw [hE0, hEg] at hcon
  linarith

/-- A symmetric real two-by-two matrix is positive semidefinite when its diagonal entries and
determinant are nonnegative. -/
theorem posSemidef_two_two {N : Matrix (Fin 2) (Fin 2) ℝ}
    (hsymm : ∀ a b : Fin 2, N a b = N b a)
    (hd0 : 0 ≤ N 0 0) (hd1 : 0 ≤ N 1 1)
    (hdet : N 0 1 * N 0 1 ≤ N 0 0 * N 1 1) :
    N.PosSemidef := by
  have hherm : N.IsHermitian := by
    ext a b
    simp [Matrix.conjTranspose_apply, hsymm a b]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hherm ?_
  intro x
  show 0 ≤ x ⬝ᵥ (N *ᵥ x)
  have hexp : x ⬝ᵥ (N *ᵥ x)
      = N 0 0 * x 0 ^ 2 + 2 * N 0 1 * (x 0 * x 1) + N 1 1 * x 1 ^ 2 := by
    rw [← quad_eq_dotProduct_mulVec N x]
    simp only [Fin.sum_univ_two, hsymm 1 0]
    ring
  rw [hexp]

  have hn : |N 0 1| ≤ Real.sqrt (N 0 0 * N 1 1) :=
    le_trans (le_of_eq (Real.sqrt_mul_self_eq_abs (N 0 1)).symm)
      (Real.sqrt_le_sqrt hdet)

  have hchain : 2 * Real.sqrt (N 0 0 * N 1 1) * |x 0| * |x 1|
      ≤ N 0 0 * x 0 ^ 2 + N 1 1 * x 1 ^ 2 := by
    have hsq : 0 ≤ (Real.sqrt (N 0 0) * |x 0| - Real.sqrt (N 1 1) * |x 1|) ^ 2 :=
      sq_nonneg _
    have hexp2 : (Real.sqrt (N 0 0) * |x 0| - Real.sqrt (N 1 1) * |x 1|) ^ 2
        = N 0 0 * x 0 ^ 2 + N 1 1 * x 1 ^ 2
          - 2 * (Real.sqrt (N 0 0) * Real.sqrt (N 1 1)) * |x 0| * |x 1| := by
      have h1 : (Real.sqrt (N 0 0) * |x 0| - Real.sqrt (N 1 1) * |x 1|) ^ 2
          = (Real.sqrt (N 0 0)) ^ 2 * |x 0| ^ 2
              - 2 * (Real.sqrt (N 0 0) * Real.sqrt (N 1 1)) * |x 0| * |x 1|
              + (Real.sqrt (N 1 1)) ^ 2 * |x 1| ^ 2 := by ring
      rw [h1, Real.sq_sqrt hd0, Real.sq_sqrt hd1, sq_abs (x 0), sq_abs (x 1),
        ← Real.sqrt_mul hd0 (N 1 1)]
      ring
    rw [Real.sqrt_mul hd0 (N 1 1)]
    linarith [hsq, hexp2]
  have hamgm : 2 * |N 0 1| * |x 0 * x 1| ≤ N 0 0 * x 0 ^ 2 + N 1 1 * x 1 ^ 2 := by
    calc 2 * |N 0 1| * |x 0 * x 1|
        = 2 * |N 0 1| * |x 0| * |x 1| := by rw [abs_mul]; ring
      _ ≤ 2 * Real.sqrt (N 0 0 * N 1 1) * |x 0| * |x 1| := by
          have hnn : 0 ≤ 2 * |x 0| * |x 1| := by positivity
          calc 2 * |N 0 1| * |x 0| * |x 1|
              = (2 * |x 0| * |x 1|) * |N 0 1| := by ring
            _ ≤ (2 * |x 0| * |x 1|) * Real.sqrt (N 0 0 * N 1 1) :=
                mul_le_mul_of_nonneg_left hn hnn
            _ = 2 * Real.sqrt (N 0 0 * N 1 1) * |x 0| * |x 1| := by ring
      _ ≤ N 0 0 * x 0 ^ 2 + N 1 1 * x 1 ^ 2 := hchain
  have habs : |2 * N 0 1 * (x 0 * x 1)| = 2 * |N 0 1| * |x 0 * x 1| := by
    rw [abs_mul (2 * N 0 1) (x 0 * x 1), abs_mul 2 (N 0 1), abs_of_nonneg zero_le_two]
  have hl : -|2 * N 0 1 * (x 0 * x 1)| ≤ 2 * N 0 1 * (x 0 * x 1) := neg_abs_le _
  have hr : 2 * N 0 1 * (x 0 * x 1) ≤ |2 * N 0 1 * (x 0 * x 1)| := le_abs_self _
  rw [habs] at hl hr
  linarith

/-- CKG domination holds for every pair of real frequencies and every operator family. -/
theorem ckgDomination_pair {β : ℝ} (ν : Fin 2 → ℝ)
    (ρ : Operator D) (A : Fin 2 → Operator D) :
    ckgDomination β ρ ν A := by
  refine ckgDomination_of_kernelPSD β ν ?_ ρ A

  have hs : ∀ a b : Fin 2, ckgDomKernel β ν a b = ckgDomKernel β ν b a := by
    intro a b
    rw [ckgDomKernel_apply β ν a b, ckgDomKernel_apply β ν b a,
      ckgWeight_symm β (ν a) (ν b), show ν b - ν a = -(ν a - ν b) from by ring,
      phaseKernel_neg β (ν a - ν b)]

  have hd : ∀ a : Fin 2, 0 ≤ ckgDomKernel β ν a a := by
    intro a
    rw [ckgDomKernel_apply β ν a a, sub_self, phaseKernel_self β]
    have hc : (3 : ℝ) / 4 - 1 / 2 = 1 / 4 := by norm_num
    rw [hc]
    exact mul_nonneg (ckgWeight_pos β (ν a) (ν a)).le (by norm_num : (0:ℝ) ≤ 1 / 4)

  have hdet : ckgDomKernel β ν 0 1 * ckgDomKernel β ν 0 1
      ≤ ckgDomKernel β ν 0 0 * ckgDomKernel β ν 1 1 := by

    have E1 := ckgWeight_ratio (β := β) (ν 0) (ν 1)
    have E2 := ckgWeight_ratio (β := β) (ν 1) (ν 0)
    have hprod : ckgWeight β (ν 0) (ν 1) * ckgWeight β (ν 0) (ν 1)
        = ckgWeight β (ν 0) (ν 0) * ckgWeight β (ν 1) (ν 1)
          * Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 8)) := by
      have hcomm : ckgWeight β (ν 0) (ν 1) * ckgWeight β (ν 0) (ν 1)
          = ckgWeight β (ν 0) (ν 1) * ckgWeight β (ν 1) (ν 0) := by
        rw [ckgWeight_symm β (ν 1) (ν 0)]
      rw [hcomm, E1, E2]
      rw [show -(β ^ 2 * (ν 0 - ν 1) ^ 2 / 8)
          = -(β * (ν 1 - ν 0) / 4
              + β ^ 2 / 16 * ((ν 1 - ν 0) ^ 2 + 2 * ν 1 ^ 2 - 2 * ν 0 ^ 2))
            + -(β * (ν 0 - ν 1) / 4
              + β ^ 2 / 16 * ((ν 0 - ν 1) ^ 2 + 2 * ν 0 ^ 2 - 2 * ν 1 ^ 2)) from by ring,
        Real.exp_add]
      ring

    have hg : Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
        * (3 - 4 * phaseKernel β (ν 0 - ν 1)) ≤ 1 := by
      have hph : 4 * phaseKernel β (ν 0 - ν 1)
          = 2 / Real.cosh (β * (ν 0 - ν 1) / 4) := by
        rw [phaseKernel]
        field_simp
        ring
      rw [hph]
      by_cases hT : 0 ≤ β * (ν 0 - ν 1) / 4
      · have hkey := three_sub_two_div_cosh_le_exp_sq hT
        calc Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
              * (3 - 2 / Real.cosh (β * (ν 0 - ν 1) / 4))
            ≤ Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
              * Real.exp ((β * (ν 0 - ν 1) / 4) ^ 2) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
          _ = 1 := by
              have hzero : -(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16)
                  + (β * (ν 0 - ν 1) / 4) ^ 2 = 0 := by
                field_simp
                ring
              rw [← Real.exp_add, hzero, Real.exp_zero]
      · have hT' : 0 ≤ -(β * (ν 0 - ν 1) / 4) := by linarith
        have hkey := three_sub_two_div_cosh_le_exp_sq hT'
        have hcos : Real.cosh (β * (ν 0 - ν 1) / 4)
            = Real.cosh (-(β * (ν 0 - ν 1) / 4)) := (Real.cosh_neg _).symm
        rw [hcos]
        calc Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
              * (3 - 2 / Real.cosh (-(β * (ν 0 - ν 1) / 4)))
            ≤ Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
              * Real.exp ((-(β * (ν 0 - ν 1) / 4)) ^ 2) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
          _ = 1 := by
              have hzero : -(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16)
                  + (-(β * (ν 0 - ν 1) / 4)) ^ 2 = 0 := by
                rw [neg_sq]
                field_simp
                ring
              rw [← Real.exp_add, hzero, Real.exp_zero]

    have hgsq : Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 8))
        * (3 - 4 * phaseKernel β (ν 0 - ν 1)) ^ 2 ≤ 1 := by
      have hexp2 : Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
          * Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
          = Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 8)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hnn : 0 ≤ 3 - 4 * phaseKernel β (ν 0 - ν 1) := by
        have hle := phaseKernel_le_half β (ν 0 - ν 1)
        linarith
      have h2 := mul_le_mul hg hg (mul_nonneg (by positivity) hnn) zero_le_one
      rw [mul_one] at h2
      calc Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 8))
            * (3 - 4 * phaseKernel β (ν 0 - ν 1)) ^ 2
          = (Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
              * (3 - 4 * phaseKernel β (ν 0 - ν 1)))
            * (Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
              * (3 - 4 * phaseKernel β (ν 0 - ν 1))) := by
            have hrr : (Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
                * (3 - 4 * phaseKernel β (ν 0 - ν 1)))
                * (Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
                * (3 - 4 * phaseKernel β (ν 0 - ν 1)))
                = Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
                  * Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 16))
                  * (3 - 4 * phaseKernel β (ν 0 - ν 1)) ^ 2 := by
              rw [sq]
              ring
            rw [hrr, hexp2]
        _ ≤ 1 := h2

    have hA0 : 0 < ckgWeight β (ν 0) (ν 0) := ckgWeight_pos _ _ _
    have hA1 : 0 < ckgWeight β (ν 1) (ν 1) := ckgWeight_pos _ _ _
    rw [ckgDomKernel_apply β ν 0 1, ckgDomKernel_apply β ν 0 0,
      ckgDomKernel_apply β ν 1 1]
    simp only [sub_self, phaseKernel_self β]

    have hc4 : ∀ x : ℝ, 3 / 4 - x = (3 - 4 * x) / 4 := fun x => by ring
    rw [hc4, hc4]

    rw [show ckgWeight β (ν 0) (ν 1) * ((3 - 4 * phaseKernel β (ν 0 - ν 1)) / 4)
          * (ckgWeight β (ν 0) (ν 1) * ((3 - 4 * phaseKernel β (ν 0 - ν 1)) / 4))
        = (ckgWeight β (ν 0) (ν 1) * ckgWeight β (ν 0) (ν 1))
          * ((3 - 4 * phaseKernel β (ν 0 - ν 1)) / 4
            * ((3 - 4 * phaseKernel β (ν 0 - ν 1)) / 4)) from by ring,
      hprod]
    have hsplit : (3 - 4 * phaseKernel β (ν 0 - ν 1)) / 4
        * ((3 - 4 * phaseKernel β (ν 0 - ν 1)) / 4)
        = (3 - 4 * phaseKernel β (ν 0 - ν 1)) ^ 2 / 16 := by ring
    rw [hsplit]
    have hA : (0:ℝ) ≤ ckgWeight β (ν 0) (ν 0) * ckgWeight β (ν 1) (ν 1) :=
      mul_nonneg (ckgWeight_pos _ _ _).le (ckgWeight_pos _ _ _).le
    have hnum : ckgWeight β (ν 0) (ν 0) * ckgWeight β (ν 1) (ν 1)
        * (Real.exp (-(β ^ 2 * (ν 0 - ν 1) ^ 2 / 8))
          * (3 - 4 * phaseKernel β (ν 0 - ν 1)) ^ 2 / 16)
        ≤ ckgWeight β (ν 0) (ν 0) * ckgWeight β (ν 1) (ν 1) * ((1:ℝ) / 16) := by
      exact mul_le_mul_of_nonneg_left
        ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 16)).mpr hgsq) hA
    have hdiag : ckgWeight β (ν 0) (ν 0) * ((3 - 4 * ((1:ℝ) / 2)) / 4)
          * (ckgWeight β (ν 1) (ν 1) * ((3 - 4 * ((1:ℝ) / 2)) / 4))
        = ckgWeight β (ν 0) (ν 0) * ckgWeight β (ν 1) (ν 1) * ((1:ℝ) / 16) := by
      norm_num
      ring
    rw [hdiag]
    linarith [hnum]
  exact posSemidef_two_two hs (hd 0) (hd 1) hdet

/-- The CKG domination kernel for any pair of real frequencies is positive semidefinite. -/
theorem ckgDomKernel_pair_posSemidef (β : ℝ) (x y : ℝ) :
    (ckgDomKernel β ![x, y]).PosSemidef := by
  have hs : ∀ a b : Fin 2, ckgDomKernel β ![x, y] a b = ckgDomKernel β ![x, y] b a := by
    intro a b
    rw [ckgDomKernel_apply β _ a b, ckgDomKernel_apply β _ b a,
      ckgWeight_symm β (![x, y] a) (![x, y] b),
      show (![x, y] b - ![x, y] a) = -(![x, y] a - ![x, y] b) from by ring,
      phaseKernel_neg β (![x, y] a - ![x, y] b)]
  have hd : ∀ a : Fin 2, 0 ≤ ckgDomKernel β ![x, y] a a := by
    intro a
    rw [ckgDomKernel_apply β _ a a]
    fin_cases a <;> simp only [sub_self, phaseKernel_self β] <;>
      exact mul_nonneg (ckgWeight_pos _ _ _).le (by norm_num : (0:ℝ) ≤ 3 / 4 - 1 / 2)
  have hdet : ckgDomKernel β ![x, y] 0 1 * ckgDomKernel β ![x, y] 0 1
      ≤ ckgDomKernel β ![x, y] 0 0 * ckgDomKernel β ![x, y] 1 1 := by
    have E1 := ckgWeight_ratio (β := β) x y
    have E2 := ckgWeight_ratio (β := β) y x
    have hprod : ckgWeight β x y * ckgWeight β x y
        = ckgWeight β x x * ckgWeight β y y * Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8)) := by
      have hcomm : ckgWeight β x y * ckgWeight β x y
          = ckgWeight β x y * ckgWeight β y x := by
        rw [ckgWeight_symm β y x]
      rw [hcomm, E1, E2]
      rw [show -(β ^ 2 * (x - y) ^ 2 / 8)
          = -(β * (y - x) / 4 + β ^ 2 / 16 * ((y - x) ^ 2 + 2 * y ^ 2 - 2 * x ^ 2))
            + -(β * (x - y) / 4 + β ^ 2 / 16 * ((x - y) ^ 2 + 2 * x ^ 2 - 2 * y ^ 2)) from by
          ring,
        Real.exp_add]
      ring

    have hg : Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
        * (3 - 4 * phaseKernel β (x - y)) ≤ 1 := by
      have hph : 4 * phaseKernel β (x - y) = 2 / Real.cosh (β * (x - y) / 4) := by
        rw [phaseKernel]
        field_simp
        ring
      rw [hph]
      by_cases hT : 0 ≤ β * (x - y) / 4
      · have hkey := three_sub_two_div_cosh_le_exp_sq hT
        calc Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
              * (3 - 2 / Real.cosh (β * (x - y) / 4))
            ≤ Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
              * Real.exp ((β * (x - y) / 4) ^ 2) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
          _ = 1 := by
              have hzero : -(β ^ 2 * (x - y) ^ 2 / 16)
                  + (β * (x - y) / 4) ^ 2 = 0 := by
                field_simp
                ring
              rw [← Real.exp_add, hzero, Real.exp_zero]
      · have hT' : 0 ≤ -(β * (x - y) / 4) := by linarith
        have hkey := three_sub_two_div_cosh_le_exp_sq hT'
        have hcos : Real.cosh (β * (x - y) / 4)
            = Real.cosh (-(β * (x - y) / 4)) := (Real.cosh_neg _).symm
        rw [hcos]
        calc Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
              * (3 - 2 / Real.cosh (-(β * (x - y) / 4)))
            ≤ Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
              * Real.exp ((-(β * (x - y) / 4)) ^ 2) :=
              mul_le_mul_of_nonneg_left hkey (by positivity)
          _ = 1 := by
              have hzero : -(β ^ 2 * (x - y) ^ 2 / 16)
                  + (-(β * (x - y) / 4)) ^ 2 = 0 := by
                rw [neg_sq]
                field_simp
                ring
              rw [← Real.exp_add, hzero, Real.exp_zero]
    have hgsq : Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8))
        * (3 - 4 * phaseKernel β (x - y)) ^ 2 ≤ 1 := by
      have hexp2 : Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
          * Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
          = Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      have hnn : 0 ≤ 3 - 4 * phaseKernel β (x - y) := by
        have hle := phaseKernel_le_half β (x - y)
        linarith
      have h2 := mul_le_mul hg hg (mul_nonneg (by positivity) hnn) zero_le_one
      rw [mul_one] at h2
      calc Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8))
            * (3 - 4 * phaseKernel β (x - y)) ^ 2
          = (Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
              * (3 - 4 * phaseKernel β (x - y)))
            * (Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
              * (3 - 4 * phaseKernel β (x - y))) := by
            have hrr : (Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
                * (3 - 4 * phaseKernel β (x - y)))
                * (Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
                * (3 - 4 * phaseKernel β (x - y)))
                = Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
                  * Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
                  * (3 - 4 * phaseKernel β (x - y)) ^ 2 := by
              rw [sq]
              ring
            rw [hrr, hexp2]
        _ ≤ 1 := h2

    have hA : (0:ℝ) ≤ ckgWeight β x x * ckgWeight β y y :=
      mul_nonneg (ckgWeight_pos _ _ _).le (ckgWeight_pos _ _ _).le
    rw [ckgDomKernel_apply β _ 0 1, ckgDomKernel_apply β _ 0 0,
      ckgDomKernel_apply β _ 1 1]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_self, phaseKernel_self β]
    have hc4 : ∀ w : ℝ, 3 / 4 - w = (3 - 4 * w) / 4 := fun w => by ring
    rw [hc4, hc4]
    rw [show (ckgWeight β x y * ((3 - 4 * phaseKernel β (x - y)) / 4))
          * (ckgWeight β x y * ((3 - 4 * phaseKernel β (x - y)) / 4))
        = (ckgWeight β x y * ckgWeight β x y)
          * ((3 - 4 * phaseKernel β (x - y)) / 4
            * ((3 - 4 * phaseKernel β (x - y)) / 4)) from by ring,
      hprod]
    have hsplit : (3 - 4 * phaseKernel β (x - y)) / 4
        * ((3 - 4 * phaseKernel β (x - y)) / 4)
        = (3 - 4 * phaseKernel β (x - y)) ^ 2 / 16 := by ring
    rw [hsplit]
    have hnum : ckgWeight β x x * ckgWeight β y y
        * (Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8))
          * (3 - 4 * phaseKernel β (x - y)) ^ 2 / 16)
        ≤ ckgWeight β x x * ckgWeight β y y * ((1:ℝ) / 16) := by
      exact mul_le_mul_of_nonneg_left
        ((div_le_div_iff_of_pos_right (by norm_num : (0:ℝ) < 16)).mpr hgsq) hA
    have hdiag : ckgWeight β x x * ((3 - 4 * ((1:ℝ) / 2)) / 4)
          * (ckgWeight β y y * ((3 - 4 * ((1:ℝ) / 2)) / 4))
        = ckgWeight β x x * ckgWeight β y y * ((1:ℝ) / 16) := by
      norm_num
      ring
    rw [hdiag]
    linarith [hnum]
  exact posSemidef_two_two hs (hd 0) (hd 1) hdet

/-- CKG domination holds when the frequency family takes at most two prescribed values. -/
theorem ckgDomination_twoFreq {m : ℕ} {β : ℝ} (x y : ℝ) (ν : Fin m → ℝ)
    (hν : ∀ a, ν a = x ∨ ν a = y)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgDomination β ρ ν A := by
  classical

  set s : Fin m → Fin 2 := fun a => if ν a = x then 0 else 1 with hsdef
  have hclass : ∀ a : Fin m, ν a = ![x, y] (s a) := by
    intro a
    show ν a = ![x, y] (if ν a = x then (0:Fin 2) else 1)
    rcases hν a with ha | ha
    · rw [ite_eq_left ha, ha]
      rfl
    · by_cases hxy : x = y
      · rw [ite_eq_left (ha.trans hxy.symm), ha, hxy]
        rfl
      · rw [ite_eq_right (fun h => hxy (h.symm.trans ha)), ha]
        rfl

  have hentry : ∀ a b : Fin m, ckgDomKernel β ν a b
      = ckgDomKernel β ![x, y] (s a) (s b) := by
    intro a b
    rw [ckgDomKernel_apply β ν a b, ckgDomKernel_apply β ![x, y] (s a) (s b),
      hclass a, hclass b]

  have hN : ckgDomKernel β ν
      = (Matrix.of fun i a => if s a = i then (1:ℝ) else 0)ᵀ
          * (ckgDomKernel β ![x, y])
          * Matrix.of fun i a => if s a = i then (1:ℝ) else 0 := by
    ext a b
    rw [hentry a b]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Fin.sum_univ_two, mul_ite, mul_zero, mul_one]
    generalize hsa : s a = i
    generalize hsb : s b = j
    fin_cases i <;> fin_cases j <;> simp [ckgDomKernel_apply]
  refine ckgDomination_of_kernelPSD β ν ?_ ρ A
  rw [hN]
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same
    (ckgDomKernel_pair_posSemidef β x y) _

/-- Factors the CKG weight into separate frequency factors and a Gaussian depending only on the
frequency difference. -/
theorem ckgWeight_eq_diff (β : ℝ) (x y : ℝ) :
    ckgWeight β x y = Real.exp (-(β * x / 4 + β ^ 2 * x ^ 2 / 8))
      * (ckgC * Real.exp (-(β ^ 2 / 16) * (x - y) ^ 2))
      * Real.exp (-(β * y / 4 + β ^ 2 * y ^ 2 / 8)) := by
  have hmerge3 : ∀ p q r : ℝ,
      Real.exp p * Real.exp q * Real.exp r = Real.exp (p + q + r) := by
    intro p q r
    rw [← Real.exp_add, ← Real.exp_add]
  rw [ckgWeight_eq_factor β x y,
    show ckgC * Real.exp (-(β * x) / 4) * Real.exp (-(β * y) / 4)
        * Real.exp (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))
      = ckgC * (Real.exp (-(β * x) / 4) * Real.exp (-(β * y) / 4)
          * Real.exp (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))) from by ring,
    show Real.exp (-(β * x / 4 + β ^ 2 * x ^ 2 / 8))
        * (ckgC * Real.exp (-(β ^ 2 / 16) * (x - y) ^ 2))
        * Real.exp (-(β * y / 4 + β ^ 2 * y ^ 2 / 8))
      = ckgC * (Real.exp (-(β * x / 4 + β ^ 2 * x ^ 2 / 8))
          * Real.exp (-(β ^ 2 / 16) * (x - y) ^ 2)
          * Real.exp (-(β * y / 4 + β ^ 2 * y ^ 2 / 8))) from by ring,
    hmerge3, hmerge3]
  congr 1
  ring

noncomputable def ckgDomKernelDiff {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
    * (3 / 4 - phaseKernel β (ν a - ν b))

/-- Expands the difference kernel entry as a Gaussian in the frequency difference times the
phase-kernel correction. -/
theorem ckgDomKernelDiff_apply {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) (a b : Fin m) :
    ckgDomKernelDiff β ν a b
      = ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 - phaseKernel β (ν a - ν b)) :=
  rfl

/-- The CKG domination kernel is a diagonal congruence of the difference kernel. -/
theorem ckgDomKernel_eq_diag_conj {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) :
    ckgDomKernel β ν
      = (Matrix.diagonal fun a => Real.exp (-(β * ν a / 4 + β ^ 2 * ν a ^ 2 / 8)))ᴴ
          * ckgDomKernelDiff β ν
          * Matrix.diagonal fun a => Real.exp (-(β * ν a / 4 + β ^ 2 * ν a ^ 2 / 8)) := by
  have hDstar : (((Matrix.diagonal fun a => Real.exp (-(β * ν a / 4 + β ^ 2 * ν a ^ 2 / 8)))ᴴ)
      : Matrix (Fin m) (Fin m) ℝ)
      = Matrix.diagonal fun a => Real.exp (-(β * ν a / 4 + β ^ 2 * ν a ^ 2 / 8)) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : j = i
    · rw [ite_eq_left h, ite_eq_left h.symm, h, star_trivial]
    · rw [ite_eq_right h, ite_eq_right (fun hh : i = j => h hh.symm), star_zero]
  ext a b
  rw [hDstar, Matrix.mul_diagonal, Matrix.diagonal_mul,
    ckgDomKernel_apply β ν a b, ckgDomKernelDiff_apply β ν a b,
    ckgWeight_eq_diff β (ν a) (ν b)]
  ring

/-- The stated row-dominance condition on the difference kernel implies CKG domination. -/
theorem ckgDomination_of_diffRowdom {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hrow : ∀ a, ∑ b ∈ Finset.univ.erase a,
        ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
          * (3 / 4 - phaseKernel β (ν a - ν b)) ≤ ckgC / 4)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgDomination β ρ ν A := by

  have hsymm : ∀ a b : Fin m, ckgDomKernelDiff β ν a b = ckgDomKernelDiff β ν b a := by
    intro a b
    rw [ckgDomKernelDiff_apply β ν a b, ckgDomKernelDiff_apply β ν b a,
      show ν b - ν a = -(ν a - ν b) from by ring, neg_sq,
      phaseKernel_neg β (ν a - ν b)]

  have hdiag : ∀ a : Fin m, ckgDomKernelDiff β ν a a = ckgC / 4 := by
    intro a
    rw [ckgDomKernelDiff_apply β ν a a, sub_self, phaseKernel_self β]
    norm_num
    ring

  have hoff : ∀ a b : Fin m, b ∈ Finset.univ.erase a →
      |ckgDomKernelDiff β ν a b|
        = ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
          * (3 / 4 - phaseKernel β (ν a - ν b)) := by
    intro a b hb
    rw [ckgDomKernelDiff_apply β ν a b]
    refine abs_of_pos (mul_pos (mul_pos ckgC_pos (Real.exp_pos _)) ?_)
    have hle := phaseKernel_le_half β (ν a - ν b)
    linarith

  have hdiff : (ckgDomKernelDiff β ν).PosSemidef := by
    refine gramDiagDominance_posSemidef _ hsymm ?_
    intro a
    rw [Finset.sum_congr rfl (fun b hb => hoff a b hb), hdiag a]
    exact hrow a

  have hN : (ckgDomKernel β ν).PosSemidef := by
    rw [ckgDomKernel_eq_diag_conj β ν]
    exact Matrix.PosSemidef.conjTranspose_mul_mul_same hdiff _
  exact ckgDomination_of_kernelPSD β ν hN ρ A

/-- A uniform Gaussian frequency-separation bound implies CKG domination for families with at
least two indices. -/
theorem ckgDomination_of_spacing {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hm : 2 ≤ m)
    (hsp : ∀ a b : Fin m, a ≠ b →
        Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) ≤ 1 / (3 * ((m : ℝ) - 1)))
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgDomination β ρ ν A := by
  have hm1 : 1 ≤ m := Nat.le_of_succ_le hm
  have hcard : ∀ a : Fin m, (Finset.univ.erase a).card = m - 1 := fun a => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
  refine ckgDomination_of_diffRowdom β ν (fun a => ?_) ρ A

  have hsum : ∑ b ∈ Finset.univ.erase a, Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
      ≤ ((m : ℝ) - 1) * (1 / (3 * ((m : ℝ) - 1))) := by
    have h1 : ∑ b ∈ Finset.univ.erase a, Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        ≤ ∑ b ∈ Finset.univ.erase a, 1 / (3 * ((m : ℝ) - 1)) :=
      Finset.sum_le_sum fun b hb => by
        have hbne := (Finset.mem_erase.mp hb).1
        rw [show (ν a - ν b) ^ 2 = (ν b - ν a) ^ 2 from by
          rw [show ν b - ν a = -(ν a - ν b) from by ring, neg_sq]]
        exact hsp b a hbne
    rw [Finset.sum_const, hcard a, nsmul_eq_mul, Nat.cast_sub hm1, Nat.cast_one] at h1
    exact h1

  have hle : ∀ b : Fin m, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 - phaseKernel β (ν a - ν b))
      ≤ ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) * (3 / 4 : ℝ) := by
    intro b
    exact mul_le_mul_of_nonneg_left
      (sub_le_self (3 / 4) (phaseKernel_pos β (ν a - ν b)).le)
      (mul_nonneg ckgC_pos.le (Real.exp_nonneg _))
  have hne : ((m : ℝ) - 1) ≠ 0 := by
    have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    exact ne_of_gt h1
  calc ∑ b ∈ Finset.univ.erase a, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 - phaseKernel β (ν a - ν b))
      ≤ ∑ b ∈ Finset.univ.erase a, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
          * (3 / 4 : ℝ) := Finset.sum_le_sum fun b _ => hle b
    _ = (∑ b ∈ Finset.univ.erase a, Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2))
          * (ckgC * (3 / 4 : ℝ)) := by
          have hpull : ∀ b : Fin m, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
              * (3 / 4 : ℝ)
              = Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) * (ckgC * (3 / 4 : ℝ)) := by
            intro b
            ring
          rw [Finset.sum_congr rfl (fun b _ => hpull b),
            ← Finset.sum_mul _ _ (ckgC * (3 / 4 : ℝ))]
    _ ≤ (((m : ℝ) - 1) * (1 / (3 * ((m : ℝ) - 1)))) * (ckgC * (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hsum (mul_nonneg ckgC_pos.le (by norm_num))
    _ = ckgC / 4 := by
          field_simp

/-- CKG domination follows when each off-diagonal Gaussian overlap sum is at most one third. -/
theorem ckgDomination_of_expSpacing {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hsum : ∀ a, ∑ b ∈ Finset.univ.erase a,
        Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) ≤ 1 / 3)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgDomination β ρ ν A := by
  refine ckgDomination_of_diffRowdom β ν (fun a => ?_) ρ A
  have hterm : ∀ b : Fin m, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 - phaseKernel β (ν a - ν b))
      ≤ ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) * (3 / 4 : ℝ) :=
    fun b => mul_le_mul_of_nonneg_left
      (sub_le_self (3 / 4) (phaseKernel_pos β (ν a - ν b)).le)
      (mul_nonneg ckgC_pos.le (Real.exp_nonneg _))
  have hpull : ∀ b : Fin m, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 : ℝ)
      = Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) * (ckgC * (3 / 4 : ℝ)) :=
    fun b => by ring
  calc ∑ b ∈ Finset.univ.erase a, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 - phaseKernel β (ν a - ν b))
      ≤ ∑ b ∈ Finset.univ.erase a, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
          * (3 / 4 : ℝ) := Finset.sum_le_sum fun b _ => hterm b
    _ = (∑ b ∈ Finset.univ.erase a, Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2))
          * (ckgC * (3 / 4 : ℝ)) := by
          rw [Finset.sum_congr rfl (fun b _ => hpull b),
            ← Finset.sum_mul _ _ (ckgC * (3 / 4 : ℝ))]
    _ ≤ (1 / 3) * (ckgC * (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right (hsum a) (mul_nonneg ckgC_pos.le (by norm_num))
    _ = ckgC / 4 := by
          field_simp

/-- CKG domination holds when every frequency is either zero or the specified gap `g`. -/
theorem ckgDomination_bohrTwoLevel {m : ℕ} {β : ℝ} (g : ℝ) (ν : Fin m → ℝ)
    (hν : ∀ a, ν a = 0 ∨ ν a = g)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgDomination β ρ ν A :=
  ckgDomination_twoFreq (β := β) 0 g ν hν ρ A

noncomputable def ckgSourceWeight (β ν ν' : ℝ) : ℝ :=
  ckgC * Real.exp (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2))

/-- The CKG source weight is strictly positive. -/
theorem ckgSourceWeight_pos (β ν ν' : ℝ) : 0 < ckgSourceWeight β ν ν' :=
  mul_pos ckgC_pos (Real.exp_pos _)

/-- The CKG source weight is symmetric in its two frequencies. -/
theorem ckgSourceWeight_symm (β ν ν' : ℝ) :
    ckgSourceWeight β ν ν' = ckgSourceWeight β ν' ν := by
  rw [ckgSourceWeight, ckgSourceWeight]
  congr 2
  ring

/-- On the diagonal, the CKG source weight equals `ckgC` times the stated Gaussian frequency
factor. -/
theorem ckgSourceWeight_self (β ν : ℝ) :
    ckgSourceWeight β ν ν = ckgC * Real.exp (-(β ^ 2 / 4) * ν ^ 2) := by
  rw [ckgSourceWeight]
  congr 2
  ring

/-- The CKG source weight equals the CKG weight multiplied by the exponential of one quarter of
the inverse temperature times the frequency sum. -/
theorem ckgSourceWeight_eq (β ν ν' : ℝ) :
    ckgSourceWeight β ν ν'
      = ckgWeight β ν ν' * Real.exp (β * (ν + ν') / 4) := by
  rw [ckgSourceWeight, ckgWeight_eq_factor β ν ν']

  have hmerge : (-(β * ν) / 4) + (-(β * ν') / 4)
      + (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2))
      + (β * (ν + ν') / 4)
      = -(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2) := by ring
  rw [show ckgC * Real.exp (-(β * ν) / 4) * Real.exp (-(β * ν') / 4)
      * Real.exp (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2))
      * Real.exp (β * (ν + ν') / 4)
    = ckgC * (Real.exp (-(β * ν) / 4) * Real.exp (-(β * ν') / 4)
      * Real.exp (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2))
      * Real.exp (β * (ν + ν') / 4)) from by ring,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add, hmerge]

/-- Factors the CKG source weight into Gaussian terms in the frequency sum and frequency
difference. -/
theorem ckgSourceWeight_eq_center (β ν ν' : ℝ) :
    ckgSourceWeight β ν ν' = ckgC
      * Real.exp (-(β ^ 2 / 16) * (ν + ν') ^ 2)
      * Real.exp (-(β ^ 2 / 8) * (ν - ν') ^ 2) := by
  rw [ckgSourceWeight]
  have hsplit : (-(β ^ 2 / 16) * ((ν - ν') ^ 2 + 2 * ν ^ 2 + 2 * ν' ^ 2))
      = (-(β ^ 2 / 16) * (ν + ν') ^ 2) + (-(β ^ 2 / 8) * (ν - ν') ^ 2) := by ring
  rw [hsplit, Real.exp_add]
  ring

/-- The CKG source weight at two zero frequencies equals `ckgC`. -/
theorem ckgSourceWeight_zero_zero (β : ℝ) :
    ckgSourceWeight β 0 0 = ckgC := by
  rw [ckgSourceWeight]
  norm_num

/-- Evaluates the CKG source weight when both frequencies equal `g`. -/
theorem ckgSourceWeight_gg (β g : ℝ) :
    ckgSourceWeight β g g = ckgC * Real.exp (-(β ^ 2 * g ^ 2 / 4)) := by
  rw [ckgSourceWeight]
  congr 2
  ring

/-- Evaluates the CKG source weight at frequencies zero and `g`. -/
theorem ckgSourceWeight_zero_g (β g : ℝ) :
    ckgSourceWeight β 0 g = ckgC * Real.exp (-(β ^ 2 * 3 * g ^ 2 / 16)) := by
  rw [ckgSourceWeight]
  congr 2
  ring

noncomputable def ckgSourceKernel {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) :
    Matrix (Fin m) (Fin m) ℝ :=
  Matrix.of fun a b => ckgSourceWeight β (ν a) (ν b)
    * (3 / 4 - phaseKernel β (ν a - ν b))

/-- Each CKG source kernel entry is the source weight times the difference between three
quarters and the phase kernel. -/
theorem ckgSourceKernel_apply {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) (a b : Fin m) :
    ckgSourceKernel β ν a b
      = ckgSourceWeight β (ν a) (ν b)
        * (3 / 4 - phaseKernel β (ν a - ν b)) :=
  rfl

/-- The stated Gaussian factor times the hyperbolic-secant correction is bounded above by one. -/
theorem sech_kernel_bound (β g : ℝ) :
    Real.exp (-(β * g / 4) ^ 2) * (3 - 2 / Real.cosh (β * g / 4)) ≤ 1 := by
  by_cases hT : 0 ≤ β * g / 4
  · have hkey := three_sub_two_div_cosh_le_exp_sq hT
    calc Real.exp (-(β * g / 4) ^ 2) * (3 - 2 / Real.cosh (β * g / 4))
        ≤ Real.exp (-(β * g / 4) ^ 2) * Real.exp ((β * g / 4) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 1 := by
          rw [← Real.exp_add]
          have hz : -(β * g / 4) ^ 2 + (β * g / 4) ^ 2 = 0 := by ring
          rw [hz, Real.exp_zero]
  · have hT' : 0 ≤ -(β * g / 4) := by linarith
    have hkey := three_sub_two_div_cosh_le_exp_sq hT'
    have hcos : Real.cosh (β * g / 4) = Real.cosh (-(β * g / 4)) :=
      (Real.cosh_neg _).symm
    calc Real.exp (-(β * g / 4) ^ 2) * (3 - 2 / Real.cosh (β * g / 4))
        = Real.exp (-(-(β * g / 4)) ^ 2) * (3 - 2 / Real.cosh (-(β * g / 4))) := by
          rw [hcos, neg_sq]
      _ ≤ Real.exp (-(-(β * g / 4)) ^ 2) * Real.exp ((-(β * g / 4)) ^ 2) :=
          mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 1 := by
          rw [← Real.exp_add]
          have hz : -(-(β * g / 4)) ^ 2 + (-(β * g / 4)) ^ 2 = 0 := by ring
          rw [hz, Real.exp_zero]

/-- The contraction of a positive semidefinite real matrix with an operator Gram matrix is
nonnegative. -/
theorem ckgSourceKernelContraction_nonneg {m : ℕ}
    (M : Matrix (Fin m) (Fin m) ℝ) (hM : M.PosSemidef)
    (B : Fin m → Operator D) :
    0 ≤ ∑ a, ∑ b, M a b * (hsInner (B a) (B b)).re :=
  gramContraction_nonneg M hM B

/-- The first diagonal entry of the source kernel for frequencies zero and `g` is one quarter of
`ckgC`. -/
theorem ckgSourceKernel_diag00 (β g : ℝ) :
    ckgSourceKernel β ![0, g] 0 0 = ckgC * (1 / 4) := by
  rw [ckgSourceKernel_apply β _ 0 0]
  simp only [Matrix.cons_val_zero, sub_self, phaseKernel_self β]
  rw [ckgSourceWeight_zero_zero β]
  norm_num

/-- The second diagonal entry of the source kernel for frequencies zero and `g` is one quarter
of the diagonal Gaussian source weight. -/
theorem ckgSourceKernel_diag11 (β g : ℝ) :
    ckgSourceKernel β ![0, g] 1 1
      = ckgC * Real.exp (-(β ^ 2 * g ^ 2 / 4)) * (1 / 4) := by
  rw [ckgSourceKernel_apply β _ 1 1]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_self,
    phaseKernel_self β]
  rw [ckgSourceWeight_gg β g]
  norm_num

/-- Expands the off-diagonal source kernel entry for frequencies zero and `g`. -/
theorem ckgSourceKernel_off01 (β g : ℝ) :
    ckgSourceKernel β ![0, g] 0 1
      = ckgC * Real.exp (-(β ^ 2 * 3 * g ^ 2 / 16))
        * (3 / 4 - phaseKernel β (0 - g)) := by
  rw [ckgSourceKernel_apply β _ 0 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ckgSourceWeight_zero_g β g]

/-- The Gaussian frequency factor times three minus four times the phase kernel is at most one. -/
theorem sech_bound_phaseKernel (β g : ℝ) :
    Real.exp (-(β ^ 2 * g ^ 2 / 16)) * (3 - 4 * phaseKernel β g) ≤ 1 := by
  have hraw := sech_kernel_bound β g
  have hph : 2 / Real.cosh (β * g / 4) = 4 * phaseKernel β g := by
    rw [phaseKernel]
    field_simp
    ring
  have hexp : (β * g / 4) ^ 2 = β ^ 2 * g ^ 2 / 16 := by
    field_simp
    ring
  rw [hph, hexp] at hraw
  exact hraw

/-- The stated factorization and scalar bound imply that the squared off-diagonal term is at
most the product of the two diagonal terms. -/
theorem det_le_of_sq {C E3 E4 E8 T : ℝ} (hC : 0 ≤ C) (hE4 : 0 ≤ E4)
    (hff : E3 * E3 = E4 * E8) (hkey : E8 * T * T ≤ 1) :
    (C * E3 * (T / 4)) * (C * E3 * (T / 4)) ≤ C * (1 / 4) * (C * E4 * (1 / 4)) := by
  have hsplit : (C * E3 * (T / 4)) * (C * E3 * (T / 4))
      = C * C * (E3 * E3) * (T * T) / (4 * 4) := by ring
  have hrhs : C * (1 / 4) * (C * E4 * (1 / 4)) = C * C * E4 / (4 * 4) := by ring
  have hsplit2 : C * C * (E4 * E8) * (T * T) / (4 * 4)
      = (C * C * E4 / (4 * 4)) * (E8 * T * T) := by ring
  rw [hsplit, hff, hrhs, hsplit2]
  have hnn2 : 0 ≤ C * C * E4 / (4 * 4) := by
    apply div_nonneg _ (by norm_num : (0:ℝ) ≤ 4 * 4)
    exact mul_nonneg (mul_nonneg hC hC) hE4
  have hfin := mul_le_mul_of_nonneg_left hkey hnn2
  rw [mul_one] at hfin
  exact hfin

/-- Evaluates the first diagonal source kernel entry for an arbitrary pair of frequencies. -/
theorem ckgSourceKernel_pair00 (β x y : ℝ) :
    ckgSourceKernel β ![x, y] 0 0
      = ckgC * Real.exp (-(β ^ 2 / 4) * x ^ 2) * (1 / 4) := by
  rw [ckgSourceKernel_apply β _ 0 0]
  simp only [Matrix.cons_val_zero, sub_self, phaseKernel_self β]
  rw [ckgSourceWeight_self β x]
  norm_num

/-- Evaluates the second diagonal source kernel entry for an arbitrary pair of frequencies. -/
theorem ckgSourceKernel_pair11 (β x y : ℝ) :
    ckgSourceKernel β ![x, y] 1 1
      = ckgC * Real.exp (-(β ^ 2 / 4) * y ^ 2) * (1 / 4) := by
  rw [ckgSourceKernel_apply β _ 1 1]
  simp only [Matrix.cons_val_one, Matrix.cons_val_zero, sub_self, phaseKernel_self β]
  rw [ckgSourceWeight_self β y]
  norm_num

/-- Expands the off-diagonal source kernel entry for an arbitrary pair of frequencies. -/
theorem ckgSourceKernel_pair01 (β x y : ℝ) :
    ckgSourceKernel β ![x, y] 0 1
      = ckgC * Real.exp (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))
        * (3 / 4 - phaseKernel β (x - y)) := by
  rw [ckgSourceKernel_apply β _ 0 1]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [ckgSourceWeight]

/-- The CKG source kernel for every pair of real frequencies is positive semidefinite. -/
theorem ckgSourceKernel_pair_posSemidef (β x y : ℝ) :
    (ckgSourceKernel β ![x, y]).PosSemidef := by

  have hs : ∀ a b : Fin 2, ckgSourceKernel β ![x, y] a b
      = ckgSourceKernel β ![x, y] b a := by
    intro a b
    rw [ckgSourceKernel_apply β _ a b, ckgSourceKernel_apply β _ b a,
      ckgSourceWeight_symm β (![x, y] a) (![x, y] b),
      show (![x, y] b - (![x, y] a)) = -(![x, y] a - (![x, y] b)) from by ring,
      phaseKernel_neg β (![x, y] a - (![x, y] b))]

  have hd0 : 0 ≤ ckgSourceKernel β ![x, y] 0 0 := by
    rw [ckgSourceKernel_pair00]
    exact mul_nonneg (mul_nonneg ckgC_pos.le (Real.exp_pos _).le) (by norm_num)
  have hd1 : 0 ≤ ckgSourceKernel β ![x, y] 1 1 := by
    rw [ckgSourceKernel_pair11]
    exact mul_nonneg (mul_nonneg ckgC_pos.le (Real.exp_pos _).le) (by norm_num)

  have hdet : ckgSourceKernel β ![x, y] 0 1 * ckgSourceKernel β ![x, y] 0 1
      ≤ ckgSourceKernel β ![x, y] 0 0 * ckgSourceKernel β ![x, y] 1 1 := by
    rw [ckgSourceKernel_pair01 β x y, ckgSourceKernel_pair00 β x y,
      ckgSourceKernel_pair11 β x y]
    have hc : (3:ℝ) / 4 - phaseKernel β (x - y)
        = (3 - 4 * phaseKernel β (x - y)) / 4 := by ring
    rw [hc]

    have hnn : 0 ≤ 3 - 4 * phaseKernel β (x - y) := by
      have hle : phaseKernel β (x - y) ≤ 1 / 2 := phaseKernel_le_half β (x - y)
      linarith

    have hkey1 := sech_bound_phaseKernel β (x - y)
    have hkeysq : (Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
          * (3 - 4 * phaseKernel β (x - y)))
        * (Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
          * (3 - 4 * phaseKernel β (x - y))) ≤ 1 * 1 :=
      mul_le_mul hkey1 hkey1 (mul_nonneg (Real.exp_nonneg _) hnn) zero_le_one
    rw [mul_one] at hkeysq

    have hexp2 : Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
        * Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
        = Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8)) := by
      have he : (-(β ^ 2 * (x - y) ^ 2 / 16)) + (-(β ^ 2 * (x - y) ^ 2 / 16))
          = -(β ^ 2 * (x - y) ^ 2 / 8) := by ring
      rw [← Real.exp_add, he]
    have hkey : Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8))
        * (3 - 4 * phaseKernel β (x - y))
        * (3 - 4 * phaseKernel β (x - y)) ≤ 1 := by
      rw [show Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8))
            * (3 - 4 * phaseKernel β (x - y))
            * (3 - 4 * phaseKernel β (x - y))
          = Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
            * (3 - 4 * phaseKernel β (x - y))
            * (Real.exp (-(β ^ 2 * (x - y) ^ 2 / 16))
              * (3 - 4 * phaseKernel β (x - y))) from by
          rw [← hexp2]
          ring]
      exact hkeysq

    have hff : Real.exp (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))
        * Real.exp (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))
        = Real.exp (-(β ^ 2 / 4) * x ^ 2) * Real.exp (-(β ^ 2 / 4) * y ^ 2)
          * Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8)) := by
      have hL : Real.exp (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))
          * Real.exp (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))
          = Real.exp (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2)
            + (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))) :=
        (Real.exp_add _ _).symm
      have hR : Real.exp (-(β ^ 2 / 4) * x ^ 2) * Real.exp (-(β ^ 2 / 4) * y ^ 2)
          * Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8))
          = Real.exp (-(β ^ 2 / 4) * x ^ 2 + -(β ^ 2 / 4) * y ^ 2
            + -(β ^ 2 * (x - y) ^ 2 / 8)) := by
        rw [← Real.exp_add, ← Real.exp_add]
      have hE : (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))
          + (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2))
          = -(β ^ 2 / 4) * x ^ 2 + -(β ^ 2 / 4) * y ^ 2
            + -(β ^ 2 * (x - y) ^ 2 / 8) := by ring
      rw [hL, hR, hE]

    rw [show ckgC * Real.exp (-(β ^ 2 / 4) * x ^ 2) * (1 / 4)
          * (ckgC * Real.exp (-(β ^ 2 / 4) * y ^ 2) * (1 / 4))
        = ckgC * (1 / 4)
          * (ckgC * (Real.exp (-(β ^ 2 / 4) * x ^ 2)
            * Real.exp (-(β ^ 2 / 4) * y ^ 2)) * (1 / 4)) from by ring]
    exact det_le_of_sq (C := ckgC)
      (E3 := Real.exp (-(β ^ 2 / 16) * ((x - y) ^ 2 + 2 * x ^ 2 + 2 * y ^ 2)))
      (E4 := Real.exp (-(β ^ 2 / 4) * x ^ 2) * Real.exp (-(β ^ 2 / 4) * y ^ 2))
      (E8 := Real.exp (-(β ^ 2 * (x - y) ^ 2 / 8)))
      (T := 3 - 4 * phaseKernel β (x - y))
      ckgC_pos.le (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _)) hff hkey
  exact posSemidef_two_two hs hd0 hd1 hdet

/-- The CKG source kernel for frequencies zero and `g` is positive semidefinite. -/
theorem ckgSourceKernel_two_posSemidef (β g : ℝ) :
    (ckgSourceKernel β ![0, g]).PosSemidef :=
  ckgSourceKernel_pair_posSemidef β 0 g

noncomputable def ckgSourceDampedForm (β : ℝ) (ρ : Operator D) (ν : ι → ℝ)
    (A : ι → Operator D) (X : Operator D) : ℂ :=
  wdampedForm (fun a b => ckgSourceWeight β (ν a) (ν b)) β ρ ν A X

noncomputable def ckgSourcePlainForm (β : ℝ) (ρ : Operator D) (ν : ι → ℝ)
    (A : ι → Operator D) (X : Operator D) : ℂ :=
  wplainForm (fun a b => ckgSourceWeight β (ν a) (ν b)) ρ A X

def ckgSourceDomination (β : ℝ) (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D) : Prop :=
  ∀ X : Operator D, Complex.re (ckgSourceDampedForm β ρ ν A X)
    ≤ 3 / 2 * Complex.re (ckgSourcePlainForm β ρ ν A X)

/-- Positive semidefiniteness of the CKG source kernel implies CKG source domination. -/
theorem ckgSourceDomination_of_kernelPSD {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hN : (ckgSourceKernel β ν).PosSemidef)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgSourceDomination β ρ ν A := by
  intro X
  set w : Fin m → Fin m → ℝ := fun a b => ckgSourceWeight β (ν a) (ν b) with hwdef
  have key : 3 / 2 * (wplainForm w ρ A X).re - (wdampedForm w β ρ ν A X).re
      = ∑ a, ∑ b, (ckgSourceKernel β ν) a b
          * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re := by
    rw [wplainForm_re_eq w ρ A X, wdampedForm_re w β ρ ν A X]
    have hinner : ∀ a : Fin m, (∑ b, w a b
            * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re) / 2
        = ∑ b, (w a b / 2)
            * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re := by
      intro a
      rw [Finset.sum_div Finset.univ _ (2:ℝ)]
      exact Finset.sum_congr rfl fun b _ => by ring
    have hdiv : (∑ a, ∑ b, w a b
          * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re) / 2
        = ∑ a, ∑ b, (w a b / 2)
            * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re := by
      rw [Finset.sum_div Finset.univ _ (2:ℝ)]
      exact Finset.sum_congr rfl fun a _ => hinner a
    have hm : (3 / 2 : ℝ) * (∑ a, ∑ b, (w a b / 2)
          * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re)
        = ∑ a, ∑ b, (3 / 2 : ℝ) * ((w a b / 2)
            * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re) := by
      rw [Finset.mul_sum Finset.univ _ (3 / 2 : ℝ)]
      exact Finset.sum_congr rfl fun a _ => Finset.mul_sum Finset.univ _ (3 / 2 : ℝ)
    rw [hdiv, hm, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun b _ => by
      rw [ckgSourceKernel_apply β ν a b]
      ring
  have hcon : 0 ≤ ∑ a, ∑ b, (ckgSourceKernel β ν) a b
      * (hsInner (parentFactor ρ (A a) X) (parentFactor ρ (A b) X)).re :=
    gramContraction_nonneg _ hN _
  rw [← key] at hcon
  have hE0 : (wplainForm w ρ A X).re = (ckgSourcePlainForm β ρ ν A X).re := rfl
  have hEg : (wdampedForm w β ρ ν A X).re = (ckgSourceDampedForm β ρ ν A X).re := rfl
  rw [hE0, hEg] at hcon
  linarith

/-- CKG source domination holds when the frequency family takes at most two prescribed values. -/
theorem ckgSourceDomination_twoFreq {m : ℕ} {β : ℝ} (x y : ℝ) (ν : Fin m → ℝ)
    (hν : ∀ a, ν a = x ∨ ν a = y)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgSourceDomination β ρ ν A := by
  classical
  set s : Fin m → Fin 2 := fun a => if ν a = x then 0 else 1 with hsdef
  have hclass : ∀ a : Fin m, ν a = ![x, y] (s a) := by
    intro a
    show ν a = ![x, y] (if ν a = x then (0:Fin 2) else 1)
    rcases hν a with ha | ha
    · rw [ite_eq_left ha, ha]
      rfl
    · by_cases hxy : x = y
      · rw [ite_eq_left (ha.trans hxy.symm), ha, hxy]
        rfl
      · rw [ite_eq_right (fun h => hxy (h.symm.trans ha)), ha]
        rfl
  have hentry : ∀ a b : Fin m, ckgSourceKernel β ν a b
      = ckgSourceKernel β ![x, y] (s a) (s b) := by
    intro a b
    rw [ckgSourceKernel_apply β ν a b, ckgSourceKernel_apply β ![x, y] (s a) (s b),
      hclass a, hclass b]
  have hN : ckgSourceKernel β ν
      = (Matrix.of fun i a => if s a = i then (1:ℝ) else 0)ᵀ
          * (ckgSourceKernel β ![x, y])
          * Matrix.of fun i a => if s a = i then (1:ℝ) else 0 := by
    ext a b
    rw [hentry a b]
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Fin.sum_univ_two, mul_ite, mul_zero, mul_one]
    generalize hsa : s a = i
    generalize hsb : s b = j
    fin_cases i <;> fin_cases j <;> simp [ckgSourceKernel_apply]
  refine ckgSourceDomination_of_kernelPSD β ν ?_ ρ A
  rw [hN]
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same
    (ckgSourceKernel_pair_posSemidef β x y) _

/-- CKG source domination holds for frequencies restricted to zero and the specified gap. -/
theorem ckgDomination_source_twoLevel {m : ℕ} {β g : ℝ} (ν : Fin m → ℝ)
    (hν : ∀ a, ν a = 0 ∨ ν a = g)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgSourceDomination β ρ ν A :=
  ckgSourceDomination_twoFreq 0 g ν hν ρ A

/-- For a two-level frequency family, a source damped form gap of at least `r` implies a source
plain form gap of at least two thirds of `r`. -/
theorem ckgSourceFormGap_twoLevel {m : ℕ} {β g : ℝ} (ν : Fin m → ℝ)
    (hν : ∀ a, ν a = 0 ∨ ν a = g)
    (ρ : Operator D) (A : Fin m → Operator D) {W : Operator D} {r : ℝ}
    (hgap : FormGapAtLeast (fun X => (ckgSourceDampedForm β ρ ν A X).re) W r) :
    FormGapAtLeast (fun X => (ckgSourcePlainForm β ρ ν A X).re) W (2 * r / 3) := by
  have h := formGap_transfer (α := 3 / 2) (by norm_num)
    (ckgDomination_source_twoLevel ν hν ρ A) hgap
  intro X
  have hX := h X
  rw [show r / (3 / 2) = 2 * r / 3 from by field_simp] at hX
  exact hX

/-- Factors the source weight into separate Gaussian frequency factors and the common Gaussian
difference kernel. -/
theorem ckgSourceWeight_eq_diff (β x y : ℝ) :
    ckgSourceWeight β x y
      = Real.exp (-(β ^ 2 / 8) * x ^ 2)
        * (ckgC * Real.exp (-(β ^ 2 / 16) * (x - y) ^ 2))
        * Real.exp (-(β ^ 2 / 8) * y ^ 2) := by
  rw [ckgSourceWeight_eq_center β x y]
  have he : (-(β ^ 2 / 16) * (x + y) ^ 2) + (-(β ^ 2 / 8) * (x - y) ^ 2)
      = (-(β ^ 2 / 8) * x ^ 2) + (-(β ^ 2 / 16) * (x - y) ^ 2)
        + (-(β ^ 2 / 8) * y ^ 2) := by ring
  calc ckgC * Real.exp (-(β ^ 2 / 16) * (x + y) ^ 2)
        * Real.exp (-(β ^ 2 / 8) * (x - y) ^ 2)
      = ckgC * (Real.exp (-(β ^ 2 / 16) * (x + y) ^ 2)
          * Real.exp (-(β ^ 2 / 8) * (x - y) ^ 2)) := by ring
    _ = ckgC * Real.exp (-(β ^ 2 / 16) * (x + y) ^ 2
          + -(β ^ 2 / 8) * (x - y) ^ 2) := by rw [← Real.exp_add]
    _ = ckgC * Real.exp (-(β ^ 2 / 8) * x ^ 2 + -(β ^ 2 / 16) * (x - y) ^ 2
          + -(β ^ 2 / 8) * y ^ 2) := by rw [he]
    _ = Real.exp (-(β ^ 2 / 8) * x ^ 2)
          * (ckgC * Real.exp (-(β ^ 2 / 16) * (x - y) ^ 2))
          * Real.exp (-(β ^ 2 / 8) * y ^ 2) := by
          rw [Real.exp_add, Real.exp_add]
          ring

/-- The CKG source kernel is a diagonal congruence of the difference kernel. -/
theorem ckgSourceKernel_eq_diag_conj {m : ℕ} (β : ℝ) (ν : Fin m → ℝ) :
    ckgSourceKernel β ν
      = (Matrix.diagonal fun a => Real.exp (-(β ^ 2 / 8) * (ν a) ^ 2))ᴴ
          * ckgDomKernelDiff β ν
          * Matrix.diagonal fun a => Real.exp (-(β ^ 2 / 8) * (ν a) ^ 2) := by
  have hDstar : (((Matrix.diagonal fun a => Real.exp (-(β ^ 2 / 8) * (ν a) ^ 2)))ᴴ
      : Matrix (Fin m) (Fin m) ℝ)
      = Matrix.diagonal fun a => Real.exp (-(β ^ 2 / 8) * (ν a) ^ 2) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : j = i
    · rw [ite_eq_left h, ite_eq_left h.symm, h, star_trivial]
    · rw [ite_eq_right h, ite_eq_right (fun hh : i = j => h hh.symm), star_zero]
  ext a b
  rw [hDstar, Matrix.mul_diagonal, Matrix.diagonal_mul,
    ckgSourceKernel_apply β ν a b, ckgDomKernelDiff_apply β ν a b,
    ckgSourceWeight_eq_diff β (ν a) (ν b)]
  ring

/-- Positive semidefiniteness of the difference kernel implies positive semidefiniteness of the
source kernel. -/
theorem ckgSourceKernel_of_diffPosSemidef {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hdiff : (ckgDomKernelDiff β ν).PosSemidef) :
    (ckgSourceKernel β ν).PosSemidef := by
  rw [ckgSourceKernel_eq_diag_conj β ν]
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same hdiff _

/-- The stated row-dominance inequalities imply positive semidefiniteness of the difference
kernel. -/
theorem ckgDomKernelDiff_posSemidef_of_rowdom {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hrow : ∀ a, ∑ b ∈ Finset.univ.erase a,
        ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
          * (3 / 4 - phaseKernel β (ν a - ν b)) ≤ ckgC / 4) :
    (ckgDomKernelDiff β ν).PosSemidef := by
  have hsymm : ∀ a b : Fin m, ckgDomKernelDiff β ν a b = ckgDomKernelDiff β ν b a := by
    intro a b
    rw [ckgDomKernelDiff_apply β ν a b, ckgDomKernelDiff_apply β ν b a,
      show ν b - ν a = -(ν a - ν b) from by ring, neg_sq,
      phaseKernel_neg β (ν a - ν b)]
  have hdiag : ∀ a : Fin m, ckgDomKernelDiff β ν a a = ckgC / 4 := by
    intro a
    rw [ckgDomKernelDiff_apply β ν a a, sub_self, phaseKernel_self β]
    norm_num
    ring
  have hoff : ∀ a b : Fin m, b ∈ Finset.univ.erase a →
      |ckgDomKernelDiff β ν a b|
        = ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
          * (3 / 4 - phaseKernel β (ν a - ν b)) := by
    intro a b hb
    rw [ckgDomKernelDiff_apply β ν a b]
    refine abs_of_pos (mul_pos (mul_pos ckgC_pos (Real.exp_pos _)) ?_)
    have hle := phaseKernel_le_half β (ν a - ν b)
    linarith
  refine gramDiagDominance_posSemidef _ hsymm ?_
  intro a
  rw [Finset.sum_congr rfl (fun b hb => hoff a b hb), hdiag a]
  exact hrow a

/-- Row dominance of the difference kernel implies CKG source domination. -/
theorem ckgSourceDomination_of_diffRowdom {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hrow : ∀ a, ∑ b ∈ Finset.univ.erase a,
        ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
          * (3 / 4 - phaseKernel β (ν a - ν b)) ≤ ckgC / 4)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgSourceDomination β ρ ν A := by
  refine ckgSourceDomination_of_kernelPSD β ν ?_ ρ A
  rw [ckgSourceKernel_eq_diag_conj β ν]
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same
    (ckgDomKernelDiff_posSemidef_of_rowdom β ν hrow) _

/-- The uniform Gaussian frequency-separation bound implies CKG source domination for families
with at least two indices. -/
theorem ckgSourceDomination_of_spacing {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hm : 2 ≤ m)
    (hsp : ∀ a b : Fin m, a ≠ b →
        Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) ≤ 1 / (3 * ((m : ℝ) - 1)))
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgSourceDomination β ρ ν A := by
  have hm1 : 1 ≤ m := Nat.le_of_succ_le hm
  have hcard : ∀ a : Fin m, (Finset.univ.erase a).card = m - 1 := fun a => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
  refine ckgSourceDomination_of_diffRowdom β ν (fun a => ?_) ρ A
  have hsum : ∑ b ∈ Finset.univ.erase a, Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
      ≤ ((m : ℝ) - 1) * (1 / (3 * ((m : ℝ) - 1))) := by
    have h1 : ∑ b ∈ Finset.univ.erase a, Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        ≤ ∑ b ∈ Finset.univ.erase a, 1 / (3 * ((m : ℝ) - 1)) :=
      Finset.sum_le_sum fun b hb => by
        have hbne := (Finset.mem_erase.mp hb).1
        rw [show (ν a - ν b) ^ 2 = (ν b - ν a) ^ 2 from by
          rw [show ν b - ν a = -(ν a - ν b) from by ring, neg_sq]]
        exact hsp b a hbne
    rw [Finset.sum_const, hcard a, nsmul_eq_mul, Nat.cast_sub hm1, Nat.cast_one] at h1
    exact h1
  have hle : ∀ b : Fin m, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 - phaseKernel β (ν a - ν b))
      ≤ ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) * (3 / 4 : ℝ) := by
    intro b
    exact mul_le_mul_of_nonneg_left
      (sub_le_self (3 / 4) (phaseKernel_pos β (ν a - ν b)).le)
      (mul_nonneg ckgC_pos.le (Real.exp_nonneg _))
  have hne : ((m : ℝ) - 1) ≠ 0 := by
    have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    have h1 : (0 : ℝ) < (m : ℝ) - 1 := by linarith
    exact ne_of_gt h1
  calc ∑ b ∈ Finset.univ.erase a, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 - phaseKernel β (ν a - ν b))
      ≤ ∑ b ∈ Finset.univ.erase a, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
          * (3 / 4 : ℝ) := Finset.sum_le_sum fun b _ => hle b
    _ = (∑ b ∈ Finset.univ.erase a, Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2))
          * (ckgC * (3 / 4 : ℝ)) := by
          have hpull : ∀ b : Fin m, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
              * (3 / 4 : ℝ)
              = Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) * (ckgC * (3 / 4 : ℝ)) := by
            intro b
            ring
          rw [Finset.sum_congr rfl (fun b _ => hpull b),
            ← Finset.sum_mul _ _ (ckgC * (3 / 4 : ℝ))]
    _ ≤ (((m : ℝ) - 1) * (1 / (3 * ((m : ℝ) - 1)))) * (ckgC * (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right hsum (mul_nonneg ckgC_pos.le (by norm_num))
    _ = ckgC / 4 := by
          field_simp

/-- CKG source domination follows when each off-diagonal Gaussian overlap sum is at most one
third. -/
theorem ckgSourceDomination_of_expSpacing {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hsum : ∀ a, ∑ b ∈ Finset.univ.erase a,
        Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) ≤ 1 / 3)
    (ρ : Operator D) (A : Fin m → Operator D) :
    ckgSourceDomination β ρ ν A := by
  refine ckgSourceDomination_of_diffRowdom β ν (fun a => ?_) ρ A
  have hterm : ∀ b : Fin m, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 - phaseKernel β (ν a - ν b))
      ≤ ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) * (3 / 4 : ℝ) :=
    fun b => mul_le_mul_of_nonneg_left
      (sub_le_self (3 / 4) (phaseKernel_pos β (ν a - ν b)).le)
      (mul_nonneg ckgC_pos.le (Real.exp_nonneg _))
  have hpull : ∀ b : Fin m, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 : ℝ)
      = Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) * (ckgC * (3 / 4 : ℝ)) :=
    fun b => by ring
  calc ∑ b ∈ Finset.univ.erase a, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
        * (3 / 4 - phaseKernel β (ν a - ν b))
      ≤ ∑ b ∈ Finset.univ.erase a, ckgC * Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2)
          * (3 / 4 : ℝ) := Finset.sum_le_sum fun b _ => hterm b
    _ = (∑ b ∈ Finset.univ.erase a, Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2))
          * (ckgC * (3 / 4 : ℝ)) := by
          rw [Finset.sum_congr rfl (fun b _ => hpull b),
            ← Finset.sum_mul _ _ (ckgC * (3 / 4 : ℝ))]
    _ ≤ (1 / 3) * (ckgC * (3 / 4 : ℝ)) :=
        mul_le_mul_of_nonneg_right (hsum a) (mul_nonneg ckgC_pos.le (by norm_num))
    _ = ckgC / 4 := by
          field_simp

/-- Under the uniform frequency-separation bound, a source damped form gap transfers to a source
plain form gap with a factor of two thirds. -/
theorem ckgSourceFormGap_of_spacing {m : ℕ} (β : ℝ) (ν : Fin m → ℝ)
    (hm : 2 ≤ m)
    (hsp : ∀ a b : Fin m, a ≠ b →
        Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) ≤ 1 / (3 * ((m : ℝ) - 1)))
    (ρ : Operator D) (A : Fin m → Operator D) {W : Operator D} {r : ℝ}
    (hgap : FormGapAtLeast (fun X => (ckgSourceDampedForm β ρ ν A X).re) W r) :
    FormGapAtLeast (fun X => (ckgSourcePlainForm β ρ ν A X).re) W (2 * r / 3) := by
  have h := formGap_transfer (α := 3 / 2) (by norm_num)
    (ckgSourceDomination_of_spacing β ν hm hsp ρ A) hgap
  intro X
  have hX := h X
  rw [show r / (3 / 2) = 2 * r / 3 from by field_simp] at hX
  exact hX

/-- Under the Gaussian overlap-sum bound, a source damped form gap transfers to a source plain
form gap with a factor of two thirds. -/
theorem ckgSourceFormGap_of_expSpacing {m : ℕ} {β : ℝ} (ν : Fin m → ℝ)
    (hsum : ∀ a, ∑ b ∈ Finset.univ.erase a,
        Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) ≤ 1 / 3)
    (ρ : Operator D) (A : Fin m → Operator D) {W : Operator D} {r : ℝ}
    (hgap : FormGapAtLeast (fun X => (ckgSourceDampedForm β ρ ν A X).re) W r) :
    FormGapAtLeast (fun X => (ckgSourcePlainForm β ρ ν A X).re) W (2 * r / 3) := by
  have h := formGap_transfer (α := 3 / 2) (by norm_num)
    (ckgSourceDomination_of_expSpacing β ν hsum ρ A) hgap
  intro X
  have hX := h X
  rw [show r / (3 / 2) = 2 * r / 3 from by field_simp] at hX
  exact hX

/-- Pointwise equal weight functions give equal weighted damped forms. -/
theorem wdampedForm_congr {ι : Type*} [Fintype ι] {w w' : ι → ι → ℝ} (β : ℝ)
    (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D)
    (h : ∀ a b, w a b = w' a b) :
    wdampedForm w β ρ ν A X = wdampedForm w' β ρ ν A X := by
  simp only [wdampedForm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [h a b]

/-- Pointwise equal weight functions give equal weighted plain forms. -/
theorem wplainForm_congr {ι : Type*} [Fintype ι] {w w' : ι → ι → ℝ}
    (ρ : Operator D) (A : ι → Operator D) (X : Operator D)
    (h : ∀ a b, w a b = w' a b) :
    wplainForm w ρ A X = wplainForm w' ρ A X := by
  simp only [wplainForm]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by rw [h a b]

/-- Real scaling of each operator in a weighted damped form can be absorbed into the two
corresponding weight indices. -/
theorem wdampedForm_smul_real {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (c : ι → ℝ)
    (β : ℝ) (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D) :
    wdampedForm w β ρ ν (fun a => ((c a : ℝ) : ℂ) • A a) X
      = wdampedForm (fun a b => c a * w a b * c b) β ρ ν A X := by
  simp only [wdampedForm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [parentFactor_smul, parentFactor_smul,
    hsInner_smul_left, hsInner_smul_right]
  have hst : star (((c a : ℝ) : ℂ)) = ((c a : ℝ) : ℂ) := by
    simp
  rw [hst]
  push_cast
  ring

/-- Real scaling of each operator in a weighted plain form can be absorbed into the two
corresponding weight indices. -/
theorem wplainForm_smul_real {ι : Type*} [Fintype ι] (w : ι → ι → ℝ) (c : ι → ℝ)
    (ρ : Operator D) (A : ι → Operator D) (X : Operator D) :
    wplainForm w ρ (fun a => ((c a : ℝ) : ℂ) • A a) X
      = wplainForm (fun a b => c a * w a b * c b) ρ A X := by
  simp only [wplainForm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [parentFactor_smul, parentFactor_smul,
    hsInner_smul_left, hsInner_smul_right]
  have hst : star (((c a : ℝ) : ℂ)) = ((c a : ℝ) : ℂ) := by
    simp
  rw [hst]
  push_cast
  ring

/-- The CKG source damped form equals the ordinary CKG damped form of the exponentially rescaled
operator family. -/
theorem ckgSourceDampedForm_eq_smulFamily {m : ℕ} (β : ℝ) (ρ : Operator D)
    (ν : Fin m → ℝ) (A : Fin m → Operator D) (X : Operator D) :
    ckgSourceDampedForm β ρ ν A X
      = ckgDampedForm β ρ ν
          (fun a => ((Real.exp (β * ν a / 4) : ℝ) : ℂ) • A a) X := by
  rw [ckgSourceDampedForm, ckgDampedForm,
    wdampedForm_smul_real (fun a b => ckgWeight β (ν a) (ν b))
      (fun a => Real.exp (β * ν a / 4)) β ρ ν A X]
  refine wdampedForm_congr β ρ ν A X ?_
  intro a b
  rw [ckgSourceWeight_eq β (ν a) (ν b)]
  have hexp : Real.exp (β * ν a / 4) * ckgWeight β (ν a) (ν b)
        * Real.exp (β * ν b / 4)
      = ckgWeight β (ν a) (ν b) * Real.exp (β * (ν a + ν b) / 4) := by
    have he : (β * ν a / 4) + (β * ν b / 4) = β * (ν a + ν b) / 4 := by ring
    calc Real.exp (β * ν a / 4) * ckgWeight β (ν a) (ν b)
          * Real.exp (β * ν b / 4)
        = (Real.exp (β * ν a / 4) * Real.exp (β * ν b / 4))
            * ckgWeight β (ν a) (ν b) := by ring
      _ = Real.exp ((β * ν a / 4) + (β * ν b / 4))
            * ckgWeight β (ν a) (ν b) := by rw [← Real.exp_add]
      _ = Real.exp (β * (ν a + ν b) / 4) * ckgWeight β (ν a) (ν b) := by rw [he]
      _ = ckgWeight β (ν a) (ν b) * Real.exp (β * (ν a + ν b) / 4) := by ring
  exact hexp.symm

/-- The CKG source plain form equals the CKG-weighted plain form of the exponentially rescaled
operator family. -/
theorem ckgSourcePlainForm_eq_smulFamily {m : ℕ} (β : ℝ) (ρ : Operator D)
    (ν : Fin m → ℝ) (A : Fin m → Operator D) (X : Operator D) :
    ckgSourcePlainForm β ρ ν A X
      = wplainForm (fun a b => ckgWeight β (ν a) (ν b)) ρ
          (fun a => ((Real.exp (β * ν a / 4) : ℝ) : ℂ) • A a) X := by
  rw [ckgSourcePlainForm,
    wplainForm_smul_real (fun a b => ckgWeight β (ν a) (ν b))
      (fun a => Real.exp (β * ν a / 4)) ρ A X]
  refine wplainForm_congr ρ A X ?_
  intro a b
  rw [ckgSourceWeight_eq β (ν a) (ν b)]
  have hexp : Real.exp (β * ν a / 4) * ckgWeight β (ν a) (ν b)
        * Real.exp (β * ν b / 4)
      = ckgWeight β (ν a) (ν b) * Real.exp (β * (ν a + ν b) / 4) := by
    have he : (β * ν a / 4) + (β * ν b / 4) = β * (ν a + ν b) / 4 := by ring
    calc Real.exp (β * ν a / 4) * ckgWeight β (ν a) (ν b)
          * Real.exp (β * ν b / 4)
        = (Real.exp (β * ν a / 4) * Real.exp (β * ν b / 4))
            * ckgWeight β (ν a) (ν b) := by ring
      _ = Real.exp ((β * ν a / 4) + (β * ν b / 4))
            * ckgWeight β (ν a) (ν b) := by rw [← Real.exp_add]
      _ = Real.exp (β * (ν a + ν b) / 4) * ckgWeight β (ν a) (ν b) := by rw [he]
      _ = ckgWeight β (ν a) (ν b) * Real.exp (β * (ν a + ν b) / 4) := by ring
  exact hexp.symm

/-- Flattening a matrix unit for a diagonal Gibbs state multiplies it by the exponential of one
quarter of its inverse-temperature energy difference. -/
theorem flat_matUnit (lam : Fin D → ℝ) (β : ℝ) (i j : Fin D) (c : ℂ) :
    flat (gibbsDiag lam β) (matUnit i j c)
      = ((Real.exp (β * (lam i - lam j) / 4) : ℝ) : ℂ) • matUnit i j c := by
  classical
  set Z := ∑ k' : Fin D, Real.exp (-(β * lam k')) with hZdef
  have hZ : 0 < Z := Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨i, Finset.mem_univ i⟩
  set g : Fin D → ℝ := fun k => Real.exp (-(β * lam k)) / Z with hgdef
  have hgnn : ∀ k, 0 ≤ g k := fun k => div_nonneg (le_of_lt (Real.exp_pos _)) hZ.le
  have hgpos : ∀ k, 0 < g k := fun k => div_pos (Real.exp_pos _) hZ
  have hR : fourthRoot (gibbsDiag lam β)
      = Matrix.diagonal fun k => ((Real.sqrt (Real.sqrt (g k)) : ℝ) : ℂ) := by
    rw [gibbsDiag, hgdef]
    exact fourthRoot_diagonal g hgnn
  have hreal : Real.sqrt (Real.sqrt (g j)) * (Real.sqrt (Real.sqrt (g i)))⁻¹
      = Real.exp (β * (lam i - lam j) / 4) := by
    have hgi : g i = Real.exp (-(β * lam i)) / Z := rfl
    have hgj : g j = Real.exp (-(β * lam j)) / Z := rfl
    have hdiv : g j / g i = Real.exp (β * (lam i - lam j)) := by
      rw [hgj, hgi,
        show (Real.exp (-(β * lam j)) / Z) / (Real.exp (-(β * lam i)) / Z)
            = Real.exp (-(β * lam j)) / Real.exp (-(β * lam i)) from by field_simp,
        ← Real.exp_sub]
      congr 1
      ring
    have key : Real.sqrt (Real.sqrt (g j)) / Real.sqrt (Real.sqrt (g i))
        = Real.sqrt (Real.sqrt (g j / g i)) := by
      rw [← Real.sqrt_div (Real.sqrt_nonneg (g j)) (Real.sqrt (g i)),
        ← Real.sqrt_div (hgpos j).le (g i)]
    rw [← div_eq_mul_inv, key, hdiv, sqrt_exp, sqrt_exp]
    congr 1
    field_simp
    ring
  have hd0 : ∀ k, ((Real.sqrt (Real.sqrt (g k)) : ℝ) : ℂ) ≠ 0 :=
    fun k => Complex.ofReal_ne_zero.mpr
      (ne_of_gt (Real.sqrt_pos.mpr (Real.sqrt_pos.mpr (hgpos k))))
  have hRinv : (Matrix.diagonal fun k => ((Real.sqrt (Real.sqrt (g k)) : ℝ) : ℂ))⁻¹
      = Matrix.diagonal fun k => (((Real.sqrt (Real.sqrt (g k)) : ℝ) : ℂ))⁻¹ :=
    diagonal_inv_eq _ hd0
  rw [flat, hR, hRinv, Matrix.mul_assoc, matUnit_mul_diagonal,
    Matrix.mul_smul, diagonal_mul_matUnit, smul_smul]
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hreal]

open scoped MatrixOrder ComplexOrder

/-- The fourth root of an operator is Hermitian. -/
theorem fourthRoot_isHermitian (ρ : Operator D) :
    (fourthRoot ρ)ᴴ = fourthRoot ρ :=
  (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian

/-- The Hilbert-Schmidt inner product distributes over subtraction in its first argument. -/
theorem hsInner_sub_left (U V W : Operator D) :
    hsInner (U - V) W = hsInner U W - hsInner V W := by
  simp [hsInner, Matrix.conjTranspose_sub, Matrix.trace_sub, sub_mul]

/-- Expands the Hilbert-Schmidt inner product of two differences into four terms. -/
theorem hsInner_sub_sub (A1 A2 W1 W2 : Operator D) :
    hsInner (A1 - A2) (W1 - W2)
      = hsInner A1 W1 - hsInner A1 W2 - hsInner A2 W1 + hsInner A2 W2 := by
  rw [hsInner_sub_left, hsInner_sub_right, hsInner_sub_right]
  ring

/-- The KMS inner product equals the Hilbert-Schmidt inner product after conjugating both
operators by the fourth root of the state. -/
theorem kmsInner_eq_hsInner_conj (ρ U V : Operator D) :
    kmsInner ρ U V
      = hsInner (fourthRoot ρ * U * fourthRoot ρ)
          (fourthRoot ρ * V * fourthRoot ρ) := by
  have hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ := fourthRoot_isHermitian ρ
  have hSS : fourthRoot ρ * fourthRoot ρ = CFC.sqrt ρ := fourthRoot_mul_self ρ
  show Matrix.trace (Uᴴ * CFC.sqrt ρ * V * CFC.sqrt ρ)
      = Matrix.trace ((fourthRoot ρ * U * fourthRoot ρ)ᴴ
          * (fourthRoot ρ * V * fourthRoot ρ))
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hRsa]
  have key : Matrix.trace ((fourthRoot ρ * (Uᴴ * fourthRoot ρ))
        * (fourthRoot ρ * V * fourthRoot ρ))
      = Matrix.trace (Uᴴ * CFC.sqrt ρ * V * CFC.sqrt ρ) := by
    have e1 : (fourthRoot ρ * (Uᴴ * fourthRoot ρ)) * (fourthRoot ρ * V * fourthRoot ρ)
        = fourthRoot ρ * (Uᴴ * (fourthRoot ρ
            * (fourthRoot ρ * V * fourthRoot ρ))) := by
      simp only [Matrix.mul_assoc]
    rw [e1, Matrix.trace_mul_comm (fourthRoot ρ)
      (Uᴴ * (fourthRoot ρ * (fourthRoot ρ * V * fourthRoot ρ))), ← hSS]
    simp only [Matrix.mul_assoc]
  rw [key]

/-- Expands the inner product of two parent factors into four terms involving `sharp` and
`flat`. -/
theorem hsInner_parentFactor_eq (ρ B C X : Operator D) :
    hsInner (parentFactor ρ B X) (parentFactor ρ C X)
      = hsInner (sharp ρ B * X) (sharp ρ C * X)
        - hsInner (sharp ρ B * X) (X * flat ρ C)
        - hsInner (X * flat ρ B) (sharp ρ C * X)
        + hsInner (X * flat ρ B) (X * flat ρ C) := by
  rw [parentFactor_apply, parentFactor_apply, hsInner_sub_sub]

/-- If `sharp` and `flat` act on `B` by scalars, its parent factor is the corresponding
difference of scaled left and right products. -/
theorem parentFactor_apply_of_sharp_flat {ρ B X : Operator D} {c1 c2 : ℂ}
    (h1 : sharp ρ B = c1 • B) (h2 : flat ρ B = c2 • B) :
    parentFactor ρ B X = c1 • (B * X) - c2 • (X * B) := by
  rw [parentFactor_apply, h1, h2, Matrix.smul_mul, Matrix.mul_smul]

/-- For scalar `sharp` and `flat` actions, expands the parent-factor inner product using the
four scalar-weighted product inner products. -/
theorem hsInner_parentFactor_bohr {ρ B C X : Operator D} {c1 c2 d1 d2 : ℂ}
    (h1 : sharp ρ B = c1 • B) (h2 : flat ρ B = c2 • B)
    (h3 : sharp ρ C = d1 • C) (h4 : flat ρ C = d2 • C) :
    hsInner (parentFactor ρ B X) (parentFactor ρ C X)
      = star c1 * d1 * hsInner (B * X) (C * X)
        - star c1 * d2 * hsInner (B * X) (X * C)
        - star c2 * d1 * hsInner (X * B) (C * X)
        + star c2 * d2 * hsInner (X * B) (X * C) := by
  rw [parentFactor_apply_of_sharp_flat h1 h2,
    parentFactor_apply_of_sharp_flat h3 h4, hsInner_sub_sub]
  simp only [hsInner_smul_left, hsInner_smul_right]
  ring

/-- For a positive definite state, the family KMS Dirichlet form is the sum of squared
Hilbert-Schmidt norms of fourth-root-conjugated commutators. -/
theorem kmsDirichletFam_eq_hsGram {ρ : Operator D} (hρ : ρ.PosDef)
    {ι : Type*} [Fintype ι] (A : ι → Operator D) (X : Operator D) :
    kmsDirichlet ρ (kmsGeneratorFam ρ A) X
      = ∑ i, (hsInner (fourthRoot ρ * (A i * X - X * A i) * fourthRoot ρ)
          (fourthRoot ρ * (A i * X - X * A i) * fourthRoot ρ)).re := by
  rw [kmsGeneratorFam_dirichlet_self hρ A X]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [kmsNorm, Real.sq_sqrt (kmsInner_re_self_nonneg ρ _),
    kmsInner_eq_hsInner_conj]

set_option maxHeartbeats 1000000

/-- The real part of a Hilbert-Schmidt self-inner-product is nonnegative. -/
theorem hsInner_re_self_nonneg (U : Operator D) : 0 ≤ (hsInner U U).re := by
  have h1 : (∑ i, ∑ j, (star (U i j) * U i j : ℂ)).re
      = ∑ i, (∑ j, (star (U i j) * U i j : ℂ)).re :=
    map_sum complexReAddMonoidHom
      (fun i => ∑ j, (star (U i j) * U i j : ℂ)) Finset.univ
  have h2 : ∀ i, (∑ j, (star (U i j) * U i j : ℂ)).re
      = ∑ j, ((star (U i j) * U i j : ℂ)).re :=
    fun i => map_sum complexReAddMonoidHom
      (fun j => star (U i j) * U i j) Finset.univ
  rw [hsInner_eq U U, h1, funext h2]
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  have hz : (star (U i j) * U i j : ℂ) = ↑(Complex.normSq (U i j)) := by
    have h := Complex.normSq_eq_conj_mul_self (z := U i j)
    rw [h]
    simp
  rw [hz]
  exact Complex.normSq_nonneg _

open scoped MatrixOrder ComplexOrder

/-- The real trace of a matrix multiplied on the right by a real scalar identity is that scalar
times the real trace. -/
private theorem re_trace_smul_one_right (M : Operator D) (r : ℝ) :
    (Matrix.trace (M * (r • 1))).re = r * (Matrix.trace M).re := by
  have e : M * (r • 1) = (r : ℝ) • M := by
    rw [Matrix.mul_smul, Matrix.mul_one]
  rw [e, Matrix.trace_smul, Complex.real_smul]
  simp [Complex.mul_re]

/-- The real trace of a matrix multiplied on the left by a real scalar identity is that scalar
times the real trace. -/
private theorem re_trace_smul_one_left (M : Operator D) (r : ℝ) :
    (Matrix.trace ((r • 1) * M)).re = r * (Matrix.trace M).re := by
  have e : (r • 1) * M = (r : ℝ) • M := by
    rw [Matrix.smul_mul, Matrix.one_mul]
  rw [e, Matrix.trace_smul, Complex.real_smul]
  simp [Complex.mul_re]

variable {D : ℕ}

/-- For positive semidefinite weights, the real weighted trace equals the squared
Hilbert-Schmidt norm after multiplication by their square roots. -/
theorem re_trace_eq_hsInner_sq {W S C : Operator D}
    (hW : W.PosSemidef) (hS : S.PosSemidef) :
    (Matrix.trace (Cᴴ * W * C * S)).re
      = (hsInner (CFC.sqrt W * C * CFC.sqrt S)
          (CFC.sqrt W * C * CFC.sqrt S)).re := by
  have hWsa : (CFC.sqrt W)ᴴ = CFC.sqrt W :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  have hSsa : (CFC.sqrt S)ᴴ = CFC.sqrt S :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)).isHermitian
  have hWW : CFC.sqrt W * CFC.sqrt W = W :=
    CFC.sqrt_mul_sqrt_self W (Matrix.PosSemidef.nonneg hW)
  have hSS : CFC.sqrt S * CFC.sqrt S = S :=
    CFC.sqrt_mul_sqrt_self S (Matrix.PosSemidef.nonneg hS)
  show (Matrix.trace (Cᴴ * W * C * S)).re
      = (Matrix.trace ((CFC.sqrt W * C * CFC.sqrt S)ᴴ
          * (CFC.sqrt W * C * CFC.sqrt S))).re
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hSsa, hWsa]
  have key : Matrix.trace ((CFC.sqrt S * (Cᴴ * CFC.sqrt W))
        * (CFC.sqrt W * C * CFC.sqrt S))
      = Matrix.trace (Cᴴ * W * C * S) := by
    have harg : (CFC.sqrt S * (Cᴴ * CFC.sqrt W)) * (CFC.sqrt W * C * CFC.sqrt S)
        = CFC.sqrt S * ((Cᴴ * W) * (C * CFC.sqrt S)) := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (CFC.sqrt W) (CFC.sqrt W) (C * CFC.sqrt S), hWW]
    rw [harg, Matrix.trace_mul_comm (CFC.sqrt S)
      ((Cᴴ * W) * (C * CFC.sqrt S))]
    simp only [Matrix.mul_assoc]
    rw [hSS]
  rw [key]

/-- The real trace weighted on both sides by positive semidefinite matrices is nonnegative. -/
theorem re_trace_weighted_nonneg {W S C : Operator D}
    (hW : W.PosSemidef) (hS : S.PosSemidef) :
    0 ≤ (Matrix.trace (Cᴴ * W * C * S)).re := by
  rw [re_trace_eq_hsInner_sq hW hS]
  exact hsInner_re_self_nonneg _

/-- The real weighted trace is monotone in the left weight when the right weight is positive
semidefinite. -/
theorem re_trace_weighted_mono_left {W₁ W₂ S C : Operator D}
    (h : W₁ ≤ W₂) (hS : S.PosSemidef) :
    (Matrix.trace (Cᴴ * W₁ * C * S)).re
      ≤ (Matrix.trace (Cᴴ * W₂ * C * S)).re := by
  have hP : (W₂ - W₁).PosSemidef := Matrix.le_iff.mp h
  have hsub : Matrix.trace (Cᴴ * W₂ * C * S) - Matrix.trace (Cᴴ * W₁ * C * S)
      = Matrix.trace (Cᴴ * (W₂ - W₁) * C * S) := by
    rw [← Matrix.trace_sub, ← Matrix.sub_mul, ← Matrix.sub_mul, ← Matrix.mul_sub]
  have hnn : 0 ≤ (Matrix.trace (Cᴴ * (W₂ - W₁) * C * S)).re :=
    re_trace_weighted_nonneg hP hS
  have hre : (Matrix.trace (Cᴴ * W₂ * C * S)).re
      - (Matrix.trace (Cᴴ * W₁ * C * S)).re
      = (Matrix.trace (Cᴴ * (W₂ - W₁) * C * S)).re := by
    rw [show (Matrix.trace (Cᴴ * W₂ * C * S)).re
          - (Matrix.trace (Cᴴ * W₁ * C * S)).re
        = (Matrix.trace (Cᴴ * W₂ * C * S)
          - Matrix.trace (Cᴴ * W₁ * C * S)).re from by
        simp [Complex.sub_re],
      hsub]
  linarith

/-- The real weighted trace is monotone in the right weight when the left weight is positive
semidefinite. -/
theorem re_trace_weighted_mono_right {W S₁ S₂ C : Operator D}
    (hW : W.PosSemidef) (h : S₁ ≤ S₂) :
    (Matrix.trace (Cᴴ * W * C * S₁)).re
      ≤ (Matrix.trace (Cᴴ * W * C * S₂)).re := by
  have hP : (S₂ - S₁).PosSemidef := Matrix.le_iff.mp h
  have hsub : Matrix.trace (Cᴴ * W * C * S₂) - Matrix.trace (Cᴴ * W * C * S₁)
      = Matrix.trace (Cᴴ * W * C * (S₂ - S₁)) := by
    rw [← Matrix.trace_sub, ← Matrix.mul_sub]
  have hnn : 0 ≤ (Matrix.trace (Cᴴ * W * C * (S₂ - S₁))).re :=
    re_trace_weighted_nonneg hW hP
  have hre : (Matrix.trace (Cᴴ * W * C * S₂)).re
      - (Matrix.trace (Cᴴ * W * C * S₁)).re
      = (Matrix.trace (Cᴴ * W * C * (S₂ - S₁))).re := by
    rw [show (Matrix.trace (Cᴴ * W * C * S₂)).re
          - (Matrix.trace (Cᴴ * W * C * S₁)).re
        = (Matrix.trace (Cᴴ * W * C * S₂)
          - Matrix.trace (Cᴴ * W * C * S₁)).re from by
        simp [Complex.sub_re],
      hsub]
  linarith

section Bounds

variable {ρ U : Operator D} {s t : ℝ}

/-- Scalar lower and upper bounds on the state square root give squared-scalar bounds comparing
KMS and Hilbert-Schmidt squared norms. -/
theorem kmsInner_re_bounds (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hlo : s • 1 ≤ CFC.sqrt ρ) (hhi : CFC.sqrt ρ ≤ t • 1) :
    s * s * (hsInner U U).re ≤ (kmsInner ρ U U).re
      ∧ (kmsInner ρ U U).re ≤ t * t * (hsInner U U).re := by
  have hSnn : (CFC.sqrt ρ).PosSemidef :=
    Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)
  have hmo : ∀ M : Operator D, Matrix.trace (M * 1) = Matrix.trace M := fun M => by
    rw [Matrix.mul_one]

  have hup1 : (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * CFC.sqrt ρ)).re
      ≤ (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * (t • 1))).re :=
    re_trace_weighted_mono_right hSnn hhi
  have ht1 : (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * (t • 1))).re
      = t * (Matrix.trace (Uᴴ * CFC.sqrt ρ * U)).re :=
    re_trace_smul_one_right _ _
  have hup2' : (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * 1)).re
      ≤ (Matrix.trace (Uᴴ * (t • 1) * U * 1)).re :=
    re_trace_weighted_mono_left hhi Matrix.PosSemidef.one
  have hup2 : (Matrix.trace (Uᴴ * CFC.sqrt ρ * U)).re
      ≤ (Matrix.trace (Uᴴ * (t • 1) * U)).re := by
    rw [← hmo (Uᴴ * CFC.sqrt ρ * U), ← hmo (Uᴴ * (t • 1) * U)]
    exact hup2'
  have ht2 : (Matrix.trace (Uᴴ * (t • 1) * U)).re = t * (hsInner U U).re := by
    rw [Matrix.trace_mul_cycle, re_trace_smul_one_right,
      Matrix.trace_mul_comm, hsInner]

  have hlo2 : (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * (s • 1))).re
      ≤ (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * CFC.sqrt ρ)).re :=
    re_trace_weighted_mono_right hSnn hlo
  have hs1 : (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * (s • 1))).re
      = s * (Matrix.trace (Uᴴ * CFC.sqrt ρ * U)).re :=
    re_trace_smul_one_right _ _
  have hlo2' : (Matrix.trace (Uᴴ * (s • 1) * U * 1)).re
      ≤ (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * 1)).re :=
    re_trace_weighted_mono_left hlo Matrix.PosSemidef.one
  have hlo1 : (Matrix.trace (Uᴴ * (s • 1) * U)).re
      ≤ (Matrix.trace (Uᴴ * CFC.sqrt ρ * U)).re := by
    rw [← hmo (Uᴴ * (s • 1) * U), ← hmo (Uᴴ * CFC.sqrt ρ * U)]
    exact hlo2'
  have hs2 : (Matrix.trace (Uᴴ * (s • 1) * U)).re = s * (hsInner U U).re := by
    rw [Matrix.trace_mul_cycle, re_trace_smul_one_right,
      Matrix.trace_mul_comm, hsInner]
  show s * s * (hsInner U U).re ≤ (kmsInner ρ U U).re
      ∧ (kmsInner ρ U U).re ≤ t * t * (hsInner U U).re
  constructor
  · show s * s * (hsInner U U).re
        ≤ (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * CFC.sqrt ρ)).re
    calc s * s * (hsInner U U).re
        = s * (s * (hsInner U U).re) := by ring
      _ = s * (Matrix.trace (Uᴴ * (s • 1) * U)).re := by rw [hs2]
      _ ≤ s * (Matrix.trace (Uᴴ * CFC.sqrt ρ * U)).re :=
          mul_le_mul_of_nonneg_left hlo1 hs
      _ = (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * (s • 1))).re := hs1.symm
      _ ≤ (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * CFC.sqrt ρ)).re := hlo2
  · show (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * CFC.sqrt ρ)).re
        ≤ t * t * (hsInner U U).re
    calc (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * CFC.sqrt ρ)).re
        ≤ (Matrix.trace (Uᴴ * CFC.sqrt ρ * U * (t • 1))).re := hup1
      _ = t * (Matrix.trace (Uᴴ * CFC.sqrt ρ * U)).re := ht1
      _ ≤ t * (Matrix.trace (Uᴴ * (t • 1) * U)).re :=
          mul_le_mul_of_nonneg_left hup2 ht
      _ = t * (t * (hsInner U U).re) := by rw [ht2]
      _ = t * t * (hsInner U U).re := by ring

/-- Scalar bounds on the state square root bound the family KMS Dirichlet form by the
corresponding multiples of the commutator squared-norm sum. -/
theorem kmsDirichletFam_bounds {ρ : Operator D} (hρ : ρ.PosDef) {s t : ℝ}
    (hs : 0 ≤ s) (ht : 0 ≤ t)
    (hlo : s • 1 ≤ CFC.sqrt ρ) (hhi : CFC.sqrt ρ ≤ t • 1)
    {ι : Type*} [Fintype ι] (A : ι → Operator D) (X : Operator D) :
    s * s * ∑ i, (hsInner (A i * X - X * A i) (A i * X - X * A i)).re
      ≤ kmsDirichlet ρ (kmsGeneratorFam ρ A) X
      ∧ kmsDirichlet ρ (kmsGeneratorFam ρ A) X
        ≤ t * t * ∑ i, (hsInner (A i * X - X * A i) (A i * X - X * A i)).re := by
  have hkey : ∀ i, (kmsNorm ρ (A i * X - X * A i)) ^ 2
      = (kmsInner ρ (A i * X - X * A i) (A i * X - X * A i)).re := by
    intro i
    rw [kmsNorm, Real.sq_sqrt (kmsInner_re_self_nonneg ρ _)]
  have hlo' := fun i =>
    (kmsInner_re_bounds (ρ := ρ) (U := A i * X - X * A i) hs ht hlo hhi).1
  have hhi' := fun i =>
    (kmsInner_re_bounds (ρ := ρ) (U := A i * X - X * A i) hs ht hlo hhi).2
  rw [kmsGeneratorFam_dirichlet_self hρ A X]
  constructor
  · calc s * s * ∑ i, (hsInner (A i * X - X * A i) (A i * X - X * A i)).re
        = ∑ i, s * s * (hsInner (A i * X - X * A i) (A i * X - X * A i)).re := by
          rw [Finset.mul_sum]
      _ ≤ ∑ i, (kmsNorm ρ (A i * X - X * A i)) ^ 2 :=
          Finset.sum_le_sum fun i _ => by rw [hkey i]; exact hlo' i
  · calc ∑ i, (kmsNorm ρ (A i * X - X * A i)) ^ 2
        ≤ ∑ i, t * t * (hsInner (A i * X - X * A i) (A i * X - X * A i)).re :=
          Finset.sum_le_sum fun i _ => by rw [hkey i]; exact hhi' i
      _ = t * t * ∑ i, (hsInner (A i * X - X * A i) (A i * X - X * A i)).re := by
          rw [Finset.mul_sum]

end Bounds

/-- A chain of Dirichlet form comparisons transfers a KMS gap from `Kg` to `K₀`, divided by the
positive comparison constant. -/
theorem kmsGap_of_formDomination {ρ : Operator D}
    {Kg K₀ : Operator D →ₗ[ℂ] Operator D} {Eg E0 : Operator D → ℝ} {α : ℝ}
    (hα : 0 < α)
    (h₁ : ∀ X, kmsDirichlet ρ Kg X ≤ Eg X)
    (h₂ : ∀ X, Eg X ≤ α * E0 X)
    (h₃ : ∀ X, E0 X ≤ kmsDirichlet ρ K₀ X)
    {r : ℝ} (hgap : KmsGapAtLeast ρ Kg r) :
    KmsGapAtLeast ρ K₀ (r / α) := by
  refine kmsGap_transfer hα ?_ hgap
  intro O
  calc kmsDirichlet ρ Kg O ≤ Eg O := h₁ O
    _ ≤ α * E0 O := h₂ O
    _ ≤ α * kmsDirichlet ρ K₀ O := mul_le_mul_of_nonneg_left (h₃ O) hα.le

/-- A Dirichlet form comparison with constant three halves transfers a KMS gap with a factor of
two thirds. -/
theorem kmsGap_twoThirds_of_formBounds {ρ : Operator D}
    {Kg K₀ : Operator D →ₗ[ℂ] Operator D} {Eg E0 : Operator D → ℝ} {r : ℝ}
    (h₁ : ∀ X, kmsDirichlet ρ Kg X ≤ Eg X)
    (h₂ : ∀ X, Eg X ≤ (3 / 2 : ℝ) * E0 X)
    (h₃ : ∀ X, E0 X ≤ kmsDirichlet ρ K₀ X)
    (hgap : KmsGapAtLeast ρ Kg r) :
    KmsGapAtLeast ρ K₀ (2 * r / 3) := by
  have h := kmsGap_of_formDomination (α := 3 / 2) (by norm_num) h₁ h₂ h₃ hgap
  intro O
  have hO := h O
  rw [show r / (3 / 2 : ℝ) = 2 * r / 3 from by field_simp] at hO
  exact hO

/-- For scalar `sharp` and `flat` actions, expands a parent-factor squared norm into two
squared-norm terms and a real cross term. -/
theorem hsInner_parentFactor_bohr_self {ρ B X : Operator D} {c1 c2 : ℂ}
    (h1 : sharp ρ B = c1 • B) (h2 : flat ρ B = c2 • B) :
    (hsInner (parentFactor ρ B X) (parentFactor ρ B X)).re
      = Complex.normSq c1 * (hsInner (B * X) (B * X)).re
        - 2 * (star c1 * c2 * hsInner (B * X) (X * B)).re
        + Complex.normSq c2 * (hsInner (X * B) (X * B)).re := by
  have h4 : hsInner (parentFactor ρ B X) (parentFactor ρ B X)
      = star c1 * c1 * hsInner (B * X) (B * X)
        - star c1 * c2 * hsInner (B * X) (X * B)
        - star c2 * c1 * hsInner (X * B) (B * X)
        + star c2 * c2 * hsInner (X * B) (X * B) :=
    hsInner_parentFactor_bohr h1 h2 h1 h2
  have hcross : star c2 * c1 * hsInner (X * B) (B * X)
      = star (star c1 * c2 * hsInner (B * X) (X * B)) := by
    rw [hsInner_conj_swap (X * B) (B * X), star_mul, star_mul, star_star]
    ring
  have hd1 : (star c1 * c1 * hsInner (B * X) (B * X)).re
      = Complex.normSq c1 * (hsInner (B * X) (B * X)).re := by
    simp [Complex.normSq]
    ring
    simp
  have hd2 : (star c2 * c2 * hsInner (X * B) (X * B)).re
      = Complex.normSq c2 * (hsInner (X * B) (X * B)).re := by
    simp [Complex.normSq]
    ring
    simp
  have hst : ∀ w : ℂ, (star w).re = w.re := fun w => by simp
  rw [h4, hcross]
  simp only [Complex.sub_re, Complex.add_re, hd1, hd2, hst]
  ring

/-- A commuting product with distinct `sharp` and `flat` scaling factors has nonzero parent
factor whenever the product is nonzero. -/
theorem parentFactor_ne_zero_of_comm {ρ B X : Operator D} {c1 c2 : ℂ}
    (h1 : sharp ρ B = c1 • B) (h2 : flat ρ B = c2 • B)
    (hne : c1 ≠ c2) (hcomm : B * X = X * B) (hBX : B * X ≠ 0) :
    parentFactor ρ B X ≠ 0 := by
  rw [parentFactor_apply_of_sharp_flat h1 h2, hcomm, ← sub_smul]
  exact smul_ne_zero (sub_ne_zero.mpr hne) (fun h => hBX (by rw [hcomm, h]))

/-- The Hilbert-Schmidt inner product with zero in its first argument is zero. -/
theorem hsInner_zero_left (V : Operator D) : hsInner 0 V = 0 := by
  show Matrix.trace ((0 : Operator D)ᴴ * V) = 0
  rw [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.trace_zero]

/-- The weighted plain form vanishes on the square root of a positive definite state. -/
theorem wplainForm_sqrt_eq_zero {ι : Type*} [Fintype ι] {ρ : Operator D}
    (hρ : ρ.PosDef) (w : ι → ι → ℝ) (A : ι → Operator D) :
    wplainForm w ρ A (CFC.sqrt ρ) = 0 := by
  simp only [wplainForm]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [parentFactor_sqrt hρ, hsInner_zero_left, mul_zero]

/-- The weighted damped form vanishes on the square root of a positive definite state. -/
theorem wdampedForm_sqrt_eq_zero {ι : Type*} [Fintype ι] {ρ : Operator D}
    (hρ : ρ.PosDef) (w : ι → ι → ℝ) (β : ℝ) (ν : ι → ℝ) (A : ι → Operator D) :
    wdampedForm w β ρ ν A (CFC.sqrt ρ) = 0 := by
  simp only [wdampedForm]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [parentFactor_sqrt hρ, hsInner_zero_left, mul_zero]

/-- The CKG source plain form vanishes on the square root of a positive definite state. -/
theorem ckgSourcePlainForm_sqrt_eq_zero {m : ℕ} {ρ : Operator D} (hρ : ρ.PosDef)
    (β : ℝ) (ν : Fin m → ℝ) (A : Fin m → Operator D) :
    ckgSourcePlainForm β ρ ν A (CFC.sqrt ρ) = 0 :=
  wplainForm_sqrt_eq_zero hρ _ _

/-- The CKG source damped form vanishes on the square root of a positive definite state. -/
theorem ckgSourceDampedForm_sqrt_eq_zero {m : ℕ} {ρ : Operator D} (hρ : ρ.PosDef)
    (β : ℝ) (ν : Fin m → ℝ) (A : Fin m → Operator D) :
    ckgSourceDampedForm β ρ ν A (CFC.sqrt ρ) = 0 :=
  wdampedForm_sqrt_eq_zero hρ _ _ _ _

/-- Expands the Hilbert-Schmidt squared norm after subtracting a scalar multiple of `W`. -/
theorem hsInner_sub_smul_self (X W : Operator D) (c : ℂ) :
    hsInner (X - c • W) (X - c • W)
      = hsInner X X - star c * hsInner W X - c * star (hsInner W X)
        + star c * c * hsInner W W := by
  rw [hsInner_sub_left, hsInner_sub_right, hsInner_sub_right,
    hsInner_smul_left, hsInner_smul_right, hsInner_smul_right, hsInner_smul_left,
    hsInner_conj_swap X W]
  ring

/-- The Hilbert-Schmidt variance relative to a nonzero `W` is at most the squared distance to
any scalar multiple of `W`. -/
theorem hsInner_sub_normSq_ge (X W : Operator D)
    (hW : 0 < (hsInner W W).re) (c : ℂ) :
    hsVar W X ≤ (hsInner (X - c • W) (X - c • W)).re := by
  have hw0 : (hsInner W W).re ≠ 0 := ne_of_gt hW

  have hsq : Complex.normSq (hsInner W X - c * ((hsInner W W).re : ℂ))
      = Complex.normSq (hsInner W X)
        - 2 * (hsInner W W).re * (star c * hsInner W X).re
        + Complex.normSq c * (hsInner W W).re * (hsInner W W).re := by
    rw [Complex.normSq_sub]
    simp [Complex.mul_re, Complex.normSq]
    ring
  have hsqnn : 0 ≤ Complex.normSq (hsInner W X - c * ((hsInner W W).re : ℂ)) :=
    Complex.normSq_nonneg _

  have hmid : (c * star (hsInner W X)).re = (star c * hsInner W X).re := by
    have hE : c * star (hsInner W X) = star (star c * hsInner W X) := by
      rw [star_mul, star_star]
      ring
    rw [hE]
    simp
  have hsmul : (star c * c * hsInner W W).re
      = Complex.normSq c * (hsInner W W).re := by
    have hc : star c * c = ((Complex.normSq c : ℝ) : ℂ) := by
      apply Complex.ext
      · simp [Complex.mul_re, Complex.normSq]
      · simp [Complex.mul_im, Complex.normSq]
        ring
    rw [hc]
    simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  have hexp : (hsInner (X - c • W) (X - c • W)).re
      = (hsInner X X).re - 2 * (star c * hsInner W X).re
        + Complex.normSq c * (hsInner W W).re := by
    rw [hsInner_sub_smul_self]
    simp only [Complex.sub_re, Complex.add_re]
    rw [hmid, hsmul]
    ring

  have hkey : Complex.normSq (hsInner W X)
      ≥ 2 * (hsInner W W).re * (star c * hsInner W X).re
        - Complex.normSq c * (hsInner W W).re * (hsInner W W).re := by
    linarith [hsq, hsqnn]
  have h1 : Complex.normSq (hsInner W X) / (hsInner W W).re
      ≥ 2 * (star c * hsInner W X).re - Complex.normSq c * (hsInner W W).re := by
    rw [ge_iff_le, le_div_iff₀ hW]
    linarith [hkey]
  rw [hsVar, hexp]
  linarith

/-- The Hilbert-Schmidt variance of the fourth-root-conjugated observable relative to the state
square root is bounded by its KMS variance. -/
theorem kmsVariance_ge_hsVar_conj {ρ : Operator D}
    (O : Operator D) (hpos : 0 < (hsInner (CFC.sqrt ρ) (CFC.sqrt ρ)).re) :
    hsVar (CFC.sqrt ρ) (fourthRoot ρ * O * fourthRoot ρ) ≤ kmsVariance ρ O := by
  have h1 : kmsVariance ρ O
      = (kmsInner ρ (kmsCenter ρ O) (kmsCenter ρ O)).re := by
    rw [kmsVariance, kmsNorm, Real.sq_sqrt (kmsInner_re_self_nonneg ρ _)]
  rw [h1, kmsInner_eq_hsInner_conj]
  have hconj : fourthRoot ρ * kmsCenter ρ O * fourthRoot ρ
      = fourthRoot ρ * O * fourthRoot ρ
        - (Matrix.trace (ρ * O)) • CFC.sqrt ρ := by
    rw [kmsCenter, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul, fourthRoot_mul_self]
  rw [hconj]
  exact hsInner_sub_normSq_ge _ _ hpos _

/-- For two-level frequencies, a source damped form gap relative to the state square root
transfers to the source plain form with a factor of two thirds. -/
theorem ckgSourceFormGap_sqrt_twoLevel {m : ℕ} {β g : ℝ} (ν : Fin m → ℝ)
    (hν : ∀ a, ν a = 0 ∨ ν a = g) {ρ : Operator D} (A : Fin m → Operator D)
    {r : ℝ}
    (hgap : FormGapAtLeast (fun X => (ckgSourceDampedForm β ρ ν A X).re)
      (CFC.sqrt ρ) r) :
    FormGapAtLeast (fun X => (ckgSourcePlainForm β ρ ν A X).re)
      (CFC.sqrt ρ) (2 * r / 3) :=
  ckgSourceFormGap_twoLevel ν hν ρ A hgap

/-- Moves left multiplication across the Hilbert-Schmidt inner product by taking the conjugate
transpose. -/
theorem hsInner_mulLeft (C U V : Operator D) :
    hsInner (C * U) V = hsInner U (Cᴴ * V) := by
  show Matrix.trace ((C * U)ᴴ * V) = Matrix.trace (Uᴴ * (Cᴴ * V))
  rw [Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- Moves right multiplication across the Hilbert-Schmidt inner product by taking the conjugate
transpose. -/
theorem hsInner_mulRight (U C V : Operator D) :
    hsInner (U * C) V = hsInner U (V * Cᴴ) := by
  show Matrix.trace ((U * C)ᴴ * V) = Matrix.trace (Uᴴ * (V * Cᴴ))
  rw [Matrix.conjTranspose_mul, Matrix.trace_mul_cycle, ← Matrix.mul_assoc,
    Matrix.trace_mul_cycle]

/-- The conjugate transpose of `sharp` applied to `B` equals `flat` applied to the conjugate
transpose of `B` when the fourth root is Hermitian. -/
theorem sharp_conj {ρ : Operator D} (B : Operator D)
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) :
    (sharp ρ B)ᴴ = flat ρ Bᴴ := by
  rw [sharp, flat, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, hRsa, Matrix.mul_assoc]

/-- The conjugate transpose of `flat` applied to `B` equals `sharp` applied to the conjugate
transpose of `B` when the fourth root is Hermitian. -/
theorem flat_conj {ρ : Operator D} (B : Operator D)
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) :
    (flat ρ B)ᴴ = sharp ρ Bᴴ := by
  rw [sharp, flat, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_nonsing_inv, hRsa, Matrix.mul_assoc]

noncomputable def parentFactorAdj (ρ B : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  LinearMap.mulLeft ℂ (flat ρ Bᴴ) - LinearMap.mulRight ℂ (sharp ρ Bᴴ)

/-- Expands `parentFactorAdj` as the difference of left multiplication by the flattened adjoint
and right multiplication by the sharpened adjoint. -/
theorem parentFactorAdj_apply (ρ B Y : Operator D) :
    parentFactorAdj ρ B Y = flat ρ Bᴴ * Y - Y * sharp ρ Bᴴ := rfl

/-- For a Hermitian fourth root, `parentFactorAdj` is the adjoint of `parentFactor` for the
Hilbert-Schmidt inner product. -/
theorem hsInner_parentFactor_adjoint {ρ : Operator D}
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) (B X Y : Operator D) :
    hsInner (parentFactor ρ B X) Y
      = hsInner X (parentFactorAdj ρ B Y) := by
  rw [parentFactor_apply, parentFactorAdj_apply,
    hsInner_sub_left,
    hsInner_mulLeft, hsInner_mulRight,
    ← sharp_conj B hRsa, ← flat_conj B hRsa, ← hsInner_sub_right]

noncomputable def parentGramOp (ρ B : Operator D) : Operator D →ₗ[ℂ] Operator D :=
  (parentFactorAdj ρ B).comp (parentFactor ρ B)

/-- The parent Gram operator is the composition of the parent factor with its adjoint. -/
theorem parentGramOp_apply (ρ B X : Operator D) :
    parentGramOp ρ B X = parentFactorAdj ρ B (parentFactor ρ B X) := rfl

/-- The squared norm of a parent factor equals the real quadratic form of its parent Gram
operator. -/
theorem hsInner_parentFactor_self_eq {ρ : Operator D}
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) (B X : Operator D) :
    (hsInner (parentFactor ρ B X) (parentFactor ρ B X)).re
      = (hsInner X (parentGramOp ρ B X)).re := by
  rw [parentGramOp_apply, hsInner_parentFactor_adjoint hRsa]

/-- The real quadratic form of the parent Gram operator is nonnegative. -/
theorem parentGramOp_nonneg {ρ : Operator D}
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) (B X : Operator D) :
    0 ≤ (hsInner X (parentGramOp ρ B X)).re := by
  rw [← hsInner_parentFactor_self_eq hRsa]
  exact hsInner_re_self_nonneg _

/-- The parent Gram operator annihilates the square root of a positive definite state. -/
theorem parentGramOp_sqrt_eq_zero {ρ : Operator D} (hρ : ρ.PosDef) (B : Operator D) :
    parentGramOp ρ B (CFC.sqrt ρ) = 0 := by
  rw [parentGramOp_apply, parentFactor_sqrt hρ, map_zero]

noncomputable def parentGramFamOp {ι : Type*} [Fintype ι] (w : ι → ι → ℝ)
    (ρ : Operator D) (A : ι → Operator D) : Operator D →ₗ[ℂ] Operator D :=
  ∑ a, ∑ b, ((w a b / 2 : ℝ) : ℂ)
    • ((parentFactorAdj ρ (A a)).comp (parentFactor ρ (A b)))

/-- Expands the weighted family parent Gram operator as the double sum of parent-factor adjoint
compositions. -/
theorem parentGramFamOp_apply {ι : Type*} [Fintype ι] (w : ι → ι → ℝ)
    (ρ : Operator D) (A : ι → Operator D) (X : Operator D) :
    parentGramFamOp w ρ A X
      = ∑ a, ∑ b, ((w a b / 2 : ℝ) : ℂ)
        • parentFactorAdj ρ (A a) (parentFactor ρ (A b) X) := by
  rw [parentGramFamOp]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.coe_comp, Function.comp_apply]

/-- The real weighted plain form equals the real quadratic form of the weighted family parent
Gram operator. -/
theorem wplainForm_eq_parentGramFamOp {ι : Type*} [Fintype ι] {ρ : Operator D}
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) (w : ι → ι → ℝ)
    (A : ι → Operator D) (X : Operator D) :
    (wplainForm w ρ A X).re
      = (hsInner X (parentGramFamOp w ρ A X)).re := by
  set Y : ι → ι → Operator D :=
    fun a b => parentFactorAdj ρ (A a) (parentFactor ρ (A b) X) with hYdef
  rw [wplainForm_re w ρ A X, parentGramFamOp_apply]

  have hpush : (hsInner X (∑ a, ∑ b, ((w a b / 2 : ℝ) : ℂ) • Y a b)).re
      = ∑ a, ∑ b, (w a b / 2) * (hsInner X (Y a b)).re := by
    rw [hsInner_sum_right X (fun a => ∑ b, ((w a b / 2 : ℝ) : ℂ) • Y a b)]
    have h1 : (∑ a, (hsInner X (∑ b, ((w a b / 2 : ℝ) : ℂ) • Y a b) : ℂ)).re
        = ∑ a, (hsInner X (∑ b, ((w a b / 2 : ℝ) : ℂ) • Y a b)).re :=
      map_sum complexReAddMonoidHom
        (fun a => hsInner X (∑ b, ((w a b / 2 : ℝ) : ℂ) • Y a b)) Finset.univ
    rw [h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsInner_sum_right X (fun b => ((w a b / 2 : ℝ) : ℂ) • Y a b)]
    have h2 : (∑ b, (hsInner X (((w a b / 2 : ℝ) : ℂ) • Y a b) : ℂ)).re
        = ∑ b, (hsInner X (((w a b / 2 : ℝ) : ℂ) • Y a b)).re :=
      map_sum complexReAddMonoidHom
        (fun b => hsInner X (((w a b / 2 : ℝ) : ℂ) • Y a b)) Finset.univ
    rw [h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsInner_smul_right]
    simp [Complex.mul_re]
  rw [hpush]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hsInner_parentFactor_adjoint hRsa]

/-- The real weighted damped form equals twice the real family parent Gram quadratic form with
phase-modified weights. -/
theorem wdampedForm_eq_parentGramFamOp {ι : Type*} [Fintype ι] {ρ : Operator D}
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) (w : ι → ι → ℝ) (β : ℝ)
    (ν : ι → ℝ) (A : ι → Operator D) (X : Operator D) :
    (wdampedForm w β ρ ν A X).re
      = 2 * (hsInner X (parentGramFamOp
          (fun a b => w a b * phaseKernel β (ν a - ν b)) ρ A X)).re := by
  set c : ι → ι → ℝ :=
    fun a b => w a b * phaseKernel β (ν a - ν b) with hcdef
  set Y : ι → ι → Operator D :=
    fun a b => parentFactorAdj ρ (A a) (parentFactor ρ (A b) X) with hYdef
  rw [wdampedForm_re w β ρ ν A X, parentGramFamOp_apply]
  have hpush : (hsInner X (∑ a, ∑ b, ((c a b / 2 : ℝ) : ℂ) • Y a b)).re
      = ∑ a, ∑ b, (c a b / 2) * (hsInner X (Y a b)).re := by
    rw [hsInner_sum_right X (fun a => ∑ b, ((c a b / 2 : ℝ) : ℂ) • Y a b)]
    have h1 : (∑ a, (hsInner X (∑ b, ((c a b / 2 : ℝ) : ℂ) • Y a b) : ℂ)).re
        = ∑ a, (hsInner X (∑ b, ((c a b / 2 : ℝ) : ℂ) • Y a b)).re :=
      map_sum complexReAddMonoidHom
        (fun a => hsInner X (∑ b, ((c a b / 2 : ℝ) : ℂ) • Y a b)) Finset.univ
    rw [h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsInner_sum_right X (fun b => ((c a b / 2 : ℝ) : ℂ) • Y a b)]
    have h2 : (∑ b, (hsInner X (((c a b / 2 : ℝ) : ℂ) • Y a b) : ℂ)).re
        = ∑ b, (hsInner X (((c a b / 2 : ℝ) : ℂ) • Y a b)).re :=
      map_sum complexReAddMonoidHom
        (fun b => hsInner X (((c a b / 2 : ℝ) : ℂ) • Y a b)) Finset.univ
    rw [h2]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hsInner_smul_right]
    simp [Complex.mul_re]
  rw [hpush]
  have h2 : 2 * ∑ a, ∑ b, (c a b / 2) * (hsInner X (Y a b)).re
      = ∑ a, ∑ b, 2 * ((c a b / 2) * (hsInner X (Y a b)).re) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ =>
      Finset.mul_sum Finset.univ (fun b => (c a b / 2) * (hsInner X (Y a b)).re) 2
  rw [h2]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hsInner_parentFactor_adjoint hRsa]
  ring

/-- The real CKG source plain form is the family parent Gram quadratic form with source weights. -/
theorem ckgSourcePlainForm_eq_parentGramFamOp {m : ℕ} {ρ : Operator D}
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) (β : ℝ) (ν : Fin m → ℝ)
    (A : Fin m → Operator D) (X : Operator D) :
    (ckgSourcePlainForm β ρ ν A X).re
      = (hsInner X (parentGramFamOp
          (fun a b => ckgSourceWeight β (ν a) (ν b)) ρ A X)).re :=
  wplainForm_eq_parentGramFamOp hRsa (fun a b => ckgSourceWeight β (ν a) (ν b)) A X

/-- The real CKG source damped form is twice the family parent Gram quadratic form with
phase-modified source weights. -/
theorem ckgSourceDampedForm_eq_parentGramFamOp {m : ℕ} {ρ : Operator D}
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) (β : ℝ) (ν : Fin m → ℝ)
    (A : Fin m → Operator D) (X : Operator D) :
    (ckgSourceDampedForm β ρ ν A X).re
      = 2 * (hsInner X (parentGramFamOp
          (fun a b => ckgSourceWeight β (ν a) (ν b)
            * phaseKernel β (ν a - ν b)) ρ A X)).re :=
  wdampedForm_eq_parentGramFamOp hRsa
    (fun a b => ckgSourceWeight β (ν a) (ν b)) β ν A X

/-- A positive semidefinite weight matrix makes the real weighted plain form nonnegative. -/
theorem wplainForm_nonneg_of_weightPSD {m : ℕ} {ρ : Operator D}
    (w : Fin m → Fin m → ℝ) (hW : (Matrix.of w).PosSemidef)
    (A : Fin m → Operator D) (X : Operator D) :
    0 ≤ (wplainForm w ρ A X).re := by
  rw [wplainForm_re_eq w ρ A X]
  have hcon := gramContraction_nonneg (Matrix.of w) hW
    (fun a => parentFactor ρ (A a) X)
  simp only [Matrix.of_apply] at hcon
  exact div_nonneg hcon (by norm_num)

/-- A variance lower bound for the family parent Gram quadratic form gives the same gap for the
weighted plain form. -/
theorem formGap_of_parentGramFamOp {ι : Type*} [Fintype ι] {ρ : Operator D}
    (hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ) (w : ι → ι → ℝ)
    (A : ι → Operator D) {W : Operator D} {r : ℝ}
    (hgap : ∀ X, r * hsVar W X
      ≤ (hsInner X (parentGramFamOp w ρ A X)).re) :
    FormGapAtLeast (fun X => (wplainForm w ρ A X).re) W r := by
  intro X
  show r * hsVar W X ≤ (wplainForm w ρ A X).re
  rw [wplainForm_eq_parentGramFamOp hRsa w A X]
  exact hgap X

/-- The CKG weight matrix at distinct frequencies is positive semidefinite for positive inverse
temperature. -/
theorem ckgWeightMatrix_posSemidef {β : ℝ} (hβ : 0 < β) {m : ℕ} (ν : Fin m → ℝ)
    (hν : Function.Injective ν) :
    (Matrix.of fun a b => ckgWeight β (ν a) (ν b)).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext a b
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply]
    rw [star_trivial, ckgWeight_symm]
  · have hconv : ∀ y : Fin m → ℝ,
        y ⬝ᵥ ((Matrix.of fun a b => ckgWeight β (ν a) (ν b)) *ᵥ y)
          = ∑ a, ∑ b, ckgWeight β (ν a) (ν b) * (y a * y b) := by
      intro y
      simp [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    intro x
    show 0 ≤ x ⬝ᵥ ((Matrix.of fun a b => ckgWeight β (ν a) (ν b)) *ᵥ x)
    by_cases hx : x = 0
    · subst hx
      simp
    · rw [hconv x]
      exact le_of_lt (ckgWeight_posDef hβ ν hν x hx)

/-- The CKG source weight matrix is a diagonal congruence of the ordinary CKG weight matrix. -/
theorem ckgSourceWeightMatrix_eq_diag_conj (β : ℝ) {m : ℕ} (ν : Fin m → ℝ) :
    (Matrix.of fun a b => ckgSourceWeight β (ν a) (ν b))
      = (Matrix.diagonal fun a => Real.exp (β * ν a / 4))ᴴ
          * (Matrix.of fun a b => ckgWeight β (ν a) (ν b))
          * Matrix.diagonal fun a => Real.exp (β * ν a / 4) := by
  have hDstar : (((Matrix.diagonal fun a => Real.exp (β * ν a / 4)))ᴴ
      : Matrix (Fin m) (Fin m) ℝ)
      = Matrix.diagonal fun a => Real.exp (β * ν a / 4) := by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.diagonal_apply]
    by_cases h : j = i
    · rw [ite_eq_left h, ite_eq_left h.symm, h, star_trivial]
    · rw [ite_eq_right h, ite_eq_right (fun hh : i = j => h hh.symm), star_zero]
  ext a b
  rw [hDstar, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.of_apply, Matrix.of_apply, ckgSourceWeight_eq β (ν a) (ν b),
    show β * (ν a + ν b) / 4 = β * ν a / 4 + β * ν b / 4 from by ring,
    Real.exp_add]
  ring

/-- The CKG source weight matrix at distinct frequencies is positive semidefinite for positive
inverse temperature. -/
theorem ckgSourceWeightMatrix_posSemidef {β : ℝ} (hβ : 0 < β) {m : ℕ}
    (ν : Fin m → ℝ) (hν : Function.Injective ν) :
    (Matrix.of fun a b => ckgSourceWeight β (ν a) (ν b)).PosSemidef := by
  rw [ckgSourceWeightMatrix_eq_diag_conj β ν]
  exact Matrix.PosSemidef.conjTranspose_mul_mul_same
    (ckgWeightMatrix_posSemidef hβ ν hν) _

/-- The real CKG source plain form is nonnegative at distinct frequencies and positive inverse
temperature. -/
theorem ckgSourcePlainForm_nonneg {β : ℝ} (hβ : 0 < β) {m : ℕ}
    (ν : Fin m → ℝ) (hν : Function.Injective ν)
    (ρ : Operator D) (A : Fin m → Operator D) (X : Operator D) :
    0 ≤ (ckgSourcePlainForm β ρ ν A X).re :=
  wplainForm_nonneg_of_weightPSD _
    (ckgSourceWeightMatrix_posSemidef hβ ν hν) _ _

/-- The weighted family parent Gram operator annihilates the square root of a positive definite
state. -/
theorem parentGramFamOp_sqrt_eq_zero {ι : Type*} [Fintype ι] {ρ : Operator D}
    (hρ : ρ.PosDef) (w : ι → ι → ℝ) (A : ι → Operator D) :
    parentGramFamOp w ρ A (CFC.sqrt ρ) = 0 := by
  rw [parentGramFamOp_apply]
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  rw [parentFactor_sqrt hρ, map_zero, smul_zero]

/-- For two-level frequencies, transfers the phase-weighted parent Gram variance bound to the
source-weighted bound with a factor of two thirds. -/
theorem ckgSourceFormGap_op_twoLevel {m : ℕ} {β g : ℝ} (ν : Fin m → ℝ)
    (hν : ∀ a, ν a = 0 ∨ ν a = g) {ρ : Operator D} (A : Fin m → Operator D)
    {r : ℝ}
    (hgap : ∀ X, r * hsVar (CFC.sqrt ρ) X
      ≤ 2 * (hsInner X (parentGramFamOp
        (fun a b => ckgSourceWeight β (ν a) (ν b)
          * phaseKernel β (ν a - ν b)) ρ A X)).re) :
    ∀ X, (2 * r / 3) * hsVar (CFC.sqrt ρ) X
      ≤ (hsInner X (parentGramFamOp
          (fun a b => ckgSourceWeight β (ν a) (ν b)) ρ A X)).re := by
  have hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ := fourthRoot_isHermitian ρ
  have hd : FormGapAtLeast (fun X => (ckgSourceDampedForm β ρ ν A X).re)
      (CFC.sqrt ρ) r := by
    intro X'
    show r * hsVar (CFC.sqrt ρ) X' ≤ (ckgSourceDampedForm β ρ ν A X').re
    rw [ckgSourceDampedForm_eq_parentGramFamOp hRsa β ν A X']
    exact hgap X'
  have h := ckgSourceFormGap_sqrt_twoLevel (ρ := ρ) ν hν A hd
  intro X
  have hX : (2 * r / 3) * hsVar (CFC.sqrt ρ) X
      ≤ (ckgSourcePlainForm β ρ ν A X).re := h X
  rw [ckgSourcePlainForm_eq_parentGramFamOp hRsa β ν A X] at hX
  exact hX

/-- Under the Gaussian overlap-sum condition, transfers the phase-weighted parent Gram variance
bound to the source-weighted bound with a factor of two thirds. -/
theorem ckgSourceFormGap_op_expSpacing {m : ℕ} {β : ℝ} (ν : Fin m → ℝ)
    (hsum : ∀ a, ∑ b ∈ Finset.univ.erase a,
        Real.exp (-(β ^ 2 / 16) * (ν a - ν b) ^ 2) ≤ 1 / 3)
    {ρ : Operator D} (A : Fin m → Operator D) {r : ℝ}
    (hgap : ∀ X, r * hsVar (CFC.sqrt ρ) X
      ≤ 2 * (hsInner X (parentGramFamOp
        (fun a b => ckgSourceWeight β (ν a) (ν b)
          * phaseKernel β (ν a - ν b)) ρ A X)).re) :
    ∀ X, (2 * r / 3) * hsVar (CFC.sqrt ρ) X
      ≤ (hsInner X (parentGramFamOp
          (fun a b => ckgSourceWeight β (ν a) (ν b)) ρ A X)).re := by
  have hRsa : (fourthRoot ρ)ᴴ = fourthRoot ρ := fourthRoot_isHermitian ρ
  have hd : FormGapAtLeast (fun X => (ckgSourceDampedForm β ρ ν A X).re)
      (CFC.sqrt ρ) r := by
    intro X'
    show r * hsVar (CFC.sqrt ρ) X' ≤ (ckgSourceDampedForm β ρ ν A X').re
    rw [ckgSourceDampedForm_eq_parentGramFamOp hRsa β ν A X']
    exact hgap X'
  have h := ckgSourceFormGap_of_expSpacing (W := CFC.sqrt ρ) ν hsum ρ A hd
  intro X
  have hX : (2 * r / 3) * hsVar (CFC.sqrt ρ) X
      ≤ (ckgSourcePlainForm β ρ ν A X).re := h X
  rw [ckgSourcePlainForm_eq_parentGramFamOp hRsa β ν A X] at hX
  exact hX

/-- The Hilbert-Schmidt inner product is the sum of conjugated products of corresponding
entries. -/
theorem hsInner_eq_sum_entries (U V : Operator D) :
    hsInner U V = ∑ k, ∑ l, star (U k l) * V k l := by
  rw [hsInner]
  have h1 : ∀ i : Fin D, (Uᴴ * V) i i
      = ∑ l : Fin D, star (U l i) * V l i := by
    intro i
    simp [Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [show Matrix.trace (Uᴴ * V) = ∑ i : Fin D, (Uᴴ * V) i i from rfl]
  rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_comm]

/-- The conjugate of a complex number times that number equals the complex embedding of its
squared norm. -/
theorem star_mul_self_eq (z : ℂ) : star z * z = ((Complex.normSq z : ℝ) : ℂ) := by
  simp [Complex.normSq_eq_conj_mul_self]

/-- The real part of the conjugate self-product is the squared complex norm. -/
theorem re_star_mul_self (z : ℂ) : (star z * z).re = Complex.normSq z := by
  rw [star_mul_self_eq]
  exact Complex.ofReal_re _

section QubitLadder

abbrev qubitRaise : Operator 2 := matUnit 0 1 1

abbrev qubitLower : Operator 2 := matUnit 1 0 1

/-- The qubit raising matrix has its only nonzero entry, equal to one, in row zero and column
one. -/
theorem qubitRaise_apply (k l : Fin 2) :
    qubitRaise k l = if k = 0 ∧ l = 1 then 1 else 0 := rfl

/-- The qubit lowering matrix has its only nonzero entry, equal to one, in row one and column
zero. -/
theorem qubitLower_apply (k l : Fin 2) :
    qubitLower k l = if k = 1 ∧ l = 0 then 1 else 0 := rfl

/-- Left multiplication by `qubitRaise` places the second row of `X` in the first row and sets
the second row to zero. -/
theorem qubitRaise_mul_entry (X : Operator 2) :
    (qubitRaise * X) 0 0 = X 1 0 ∧ (qubitRaise * X) 0 1 = X 1 1 ∧
    (qubitRaise * X) 1 0 = 0 ∧ (qubitRaise * X) 1 1 = 0 := by
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single 1]
    · rw [qubitRaise_apply]; simp
    · intro b _ hb; rw [qubitRaise_apply]; simp [hb]
    · simp
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single 1]
    · rw [qubitRaise_apply]; simp
    · intro b _ hb; rw [qubitRaise_apply]; simp [hb]
    · simp
  constructor
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [qubitRaise_apply]; simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [qubitRaise_apply]; simp

/-- Right multiplication by `qubitRaise` places the first column of `X` in the second column and
sets the first column to zero. -/
theorem qubitRaise_rmul_entry (X : Operator 2) :
    (X * qubitRaise) 0 0 = 0 ∧ (X * qubitRaise) 0 1 = X 0 0 ∧
    (X * qubitRaise) 1 0 = 0 ∧ (X * qubitRaise) 1 1 = X 1 0 := by
  constructor
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [qubitRaise_apply]; simp
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [qubitRaise_apply]; simp
    · intro b _ hb; rw [qubitRaise_apply]; simp [hb]
    · simp
  constructor
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [qubitRaise_apply]; simp
  · rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [qubitRaise_apply]; simp
    · intro b _ hb; rw [qubitRaise_apply]; simp [hb]
    · simp

/-- Left multiplication by `qubitLower` places the first row of `X` in the second row and sets
the first row to zero. -/
theorem qubitLower_mul_entry (X : Operator 2) :
    (qubitLower * X) 0 0 = 0 ∧ (qubitLower * X) 0 1 = 0 ∧
    (qubitLower * X) 1 0 = X 0 0 ∧ (qubitLower * X) 1 1 = X 0 1 := by
  constructor
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [qubitLower_apply]; simp
  constructor
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [qubitLower_apply]; simp
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [qubitLower_apply]; simp
    · intro b _ hb; rw [qubitLower_apply]; simp [hb]
    · simp
  · rw [Matrix.mul_apply, Finset.sum_eq_single 0]
    · rw [qubitLower_apply]; simp
    · intro b _ hb; rw [qubitLower_apply]; simp [hb]
    · simp

/-- Right multiplication by `qubitLower` places the second column of `X` in the first column and
sets the second column to zero. -/
theorem qubitLower_rmul_entry (X : Operator 2) :
    (X * qubitLower) 0 0 = X 0 1 ∧ (X * qubitLower) 0 1 = 0 ∧
    (X * qubitLower) 1 0 = X 1 1 ∧ (X * qubitLower) 1 1 = 0 := by
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single 1]
    · rw [qubitLower_apply]; simp
    · intro b _ hb; rw [qubitLower_apply]; simp [hb]
    · simp
  constructor
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [qubitLower_apply]; simp
  constructor
  · rw [Matrix.mul_apply, Finset.sum_eq_single 1]
    · rw [qubitLower_apply]; simp
    · intro b _ hb; rw [qubitLower_apply]; simp [hb]
    · simp
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [qubitLower_apply]; simp

noncomputable def ckgLadderC1 (β g : ℝ) : ℂ := ((Real.exp (-(β * g / 4)) : ℝ) : ℂ)

noncomputable def ckgLadderC2 (β g : ℝ) : ℂ := ((Real.exp (β * g / 4) : ℝ) : ℂ)

noncomputable def ckgLadderU (β g : ℝ) (X : Operator 2) : ℂ :=
  ckgLadderC1 β g * X 1 1 - ckgLadderC2 β g * X 0 0

/-- Identifies the negative quarter-gap exponential with the complex ladder coefficient
`ckgLadderC1`. -/
theorem ckgLadderC1_eq (β g : ℝ) :
    ((Real.exp (-(β * g) / 4) : ℝ) : ℂ) = ckgLadderC1 β g := by
  simp only [ckgLadderC1]
  congr 1
  ring

/-- Identifies the positive quarter-gap exponential with the complex ladder coefficient
`ckgLadderC2`. -/
theorem ckgLadderC2_eq (β g : ℝ) :
    ((Real.exp (β * g / 4) : ℝ) : ℂ) = ckgLadderC2 β g := rfl

/-- The square of the negative quarter-gap exponential equals the negative half-gap exponential. -/
theorem exp_sq_half (β g : ℝ) :
    Real.exp (-(β * g / 4)) * Real.exp (-(β * g / 4)) = Real.exp (-(β * g / 2)) := by
  rw [← Real.exp_add]
  congr 1
  ring

/-- The square of the positive quarter-gap exponential equals the positive half-gap exponential. -/
theorem exp_sq_half' (β g : ℝ) :
    Real.exp (β * g / 4) * Real.exp (β * g / 4) = Real.exp (β * g / 2) := by
  rw [← Real.exp_add]
  congr 1
  ring

noncomputable def ckgQubitGap (β g : ℝ) : ℝ :=
  (ckgSourceWeight β g g * (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))) / 2)
    * min (Real.exp (β * g / 2) + Real.exp (-(β * g / 2)))
      (2 * (1 + Real.exp (β * g)) / Real.exp (β * g / 2))

/-- Computes every entry of the qubit raising parent factor for the two-level diagonal Gibbs
state. -/
theorem parentFactor_raise_entry (β g : ℝ) (X : Operator 2) :
    parentFactor (gibbsDiag ![g, 0] β) qubitRaise X 0 0 = ckgLadderC1 β g * X 1 0 ∧
    parentFactor (gibbsDiag ![g, 0] β) qubitRaise X 0 1 = ckgLadderU β g X ∧
    parentFactor (gibbsDiag ![g, 0] β) qubitRaise X 1 0 = 0 ∧
    parentFactor (gibbsDiag ![g, 0] β) qubitRaise X 1 1 = -(ckgLadderC2 β g * X 1 0) := by
  have h1 : sharp (gibbsDiag ![g, 0] β) qubitRaise = ckgLadderC1 β g • qubitRaise := by
    rw [sharp_matUnit ![g, 0] β 0 1 1]
    simp only [qubitRaise, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, ckgLadderC1]
    congr 1
    ring
  have h2 : flat (gibbsDiag ![g, 0] β) qubitRaise = ckgLadderC2 β g • qubitRaise := by
    rw [flat_matUnit ![g, 0] β 0 1 1]
    simp only [qubitRaise, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero, ckgLadderC2]
  have hr := qubitRaise_mul_entry X
  have hl := qubitRaise_rmul_entry X
  rw [parentFactor_apply_of_sharp_flat h1 h2]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  constructor
  · rw [hr.1, hl.1]; simp
  constructor
  · rw [hr.2.1, hl.2.1, ckgLadderU]
  constructor
  · rw [hr.2.2.1, hl.2.2.1]; simp
  · rw [hr.2.2.2, hl.2.2.2]; simp

/-- Computes every entry of the qubit lowering parent factor for the two-level diagonal Gibbs
state. -/
theorem parentFactor_lower_entry (β g : ℝ) (X : Operator 2) :
    parentFactor (gibbsDiag ![g, 0] β) qubitLower X 0 0 = -(ckgLadderC1 β g * X 0 1) ∧
    parentFactor (gibbsDiag ![g, 0] β) qubitLower X 0 1 = 0 ∧
    parentFactor (gibbsDiag ![g, 0] β) qubitLower X 1 0 = -(ckgLadderU β g X) ∧
    parentFactor (gibbsDiag ![g, 0] β) qubitLower X 1 1 = ckgLadderC2 β g * X 0 1 := by
  have h1 : sharp (gibbsDiag ![g, 0] β) qubitLower = ckgLadderC2 β g • qubitLower := by
    rw [sharp_matUnit ![g, 0] β 1 0 1]
    simp only [qubitLower, Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub, ckgLadderC2]
    congr 1
    ring
  have h2 : flat (gibbsDiag ![g, 0] β) qubitLower = ckgLadderC1 β g • qubitLower := by
    rw [flat_matUnit ![g, 0] β 1 0 1]
    simp only [qubitLower, Matrix.cons_val_zero, Matrix.cons_val_one, zero_sub, ckgLadderC1]
    congr 1
    ring
  have hr := qubitLower_mul_entry X
  have hl := qubitLower_rmul_entry X
  rw [parentFactor_apply_of_sharp_flat h1 h2]
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  constructor
  · rw [hr.1, hl.1]; simp
  constructor
  · rw [hr.2.1, hl.2.1]; simp
  constructor
  · rw [hr.2.2.1, hl.2.2.1, ckgLadderU]; ring
  · rw [hr.2.2.2, hl.2.2.2]; simp

/-- The raising parent-factor squared norm is the weighted squared lower-left entry plus the
squared ladder residual. -/
theorem hsInner_raise_raise_re (β g : ℝ) (X : Operator 2) :
    (hsInner (parentFactor (gibbsDiag ![g, 0] β) qubitRaise X)
        (parentFactor (gibbsDiag ![g, 0] β) qubitRaise X)).re
      = (Real.exp (β * g / 2) + Real.exp (-(β * g / 2))) * Complex.normSq (X 1 0)
        + Complex.normSq (ckgLadderU β g X) := by
  rw [hsInner_eq_sum_entries]
  have h := parentFactor_raise_entry β g X
  simp only [Fin.sum_univ_two, h.1, h.2.1, h.2.2.1, h.2.2.2, Complex.add_re]
  rw [re_star_mul_self, re_star_mul_self, re_star_mul_self, re_star_mul_self]
  rw [Complex.normSq_mul, Complex.normSq_neg, Complex.normSq_mul,
    ckgLadderC1, ckgLadderC2, Complex.normSq_ofReal, Complex.normSq_ofReal,
    Complex.normSq_zero]
  rw [exp_sq_half, exp_sq_half']
  ring

/-- The lowering parent-factor squared norm is the weighted squared upper-right entry plus the
squared ladder residual. -/
theorem hsInner_lower_lower_re (β g : ℝ) (X : Operator 2) :
    (hsInner (parentFactor (gibbsDiag ![g, 0] β) qubitLower X)
        (parentFactor (gibbsDiag ![g, 0] β) qubitLower X)).re
      = (Real.exp (β * g / 2) + Real.exp (-(β * g / 2))) * Complex.normSq (X 0 1)
        + Complex.normSq (ckgLadderU β g X) := by
  rw [hsInner_eq_sum_entries]
  have h := parentFactor_lower_entry β g X
  simp only [Fin.sum_univ_two, h.1, h.2.1, h.2.2.1, h.2.2.2, Complex.add_re]
  rw [re_star_mul_self, re_star_mul_self, re_star_mul_self, re_star_mul_self]
  rw [Complex.normSq_neg, Complex.normSq_mul, Complex.normSq_mul,
    ckgLadderC1, ckgLadderC2, Complex.normSq_ofReal, Complex.normSq_ofReal,
    Complex.normSq_neg, Complex.normSq_zero]
  rw [exp_sq_half, exp_sq_half']
  ring

/-- Conjugation commutes with multiplication by a real scalar embedded in the complex numbers. -/
theorem star_ofReal_mul (r : ℝ) (x : ℂ) :
    star (((r : ℝ) : ℂ) * x) = ((r : ℝ) : ℂ) * star x := by
  simp

/-- The real part of a real scalar times a complex number is the scalar times its real part. -/
theorem re_ofReal_mul' (r : ℝ) (z : ℂ) : (((r : ℝ) : ℂ) * z).re = r * z.re := by
  simp [Complex.mul_re]

/-- Negating the right factor negates the real part of a complex product. -/
theorem re_mul_neg (a b : ℂ) : (a * -b).re = -(a * b).re := by
  simp

/-- Negating the left factor negates the real part of a complex product. -/
theorem re_neg_mul (a b : ℂ) : (-a * b).re = -(a * b).re := by
  simp

/-- Real scalar factors can be pulled out of the real part of a conjugated complex product. -/
theorem re_star_ofReal_mul_ofReal_mul (r s : ℝ) (x y : ℂ) :
    (star (((r : ℝ) : ℂ) * x) * (((s : ℝ) : ℂ) * y)).re
      = r * s * (star x * y).re := by
  rw [star_ofReal_mul]
  have hz : ((r : ℝ) : ℂ) * star x * (((s : ℝ) : ℂ) * y)
      = ((r * s : ℝ) : ℂ) * (star x * y) := by
    rw [Complex.ofReal_mul]
    ring
  rw [hz, re_ofReal_mul']

/-- The real conjugate product of equally scaled complex numbers with the second negated is
minus the scalar square times their real conjugate product. -/
theorem re_star_ofReal_mul_neg (r : ℝ) (x y : ℂ) :
    (star (((r : ℝ) : ℂ) * x) * (-(((r : ℝ) : ℂ) * y))).re
      = -(r * r) * (star x * y).re := by
  rw [re_mul_neg, re_star_ofReal_mul_ofReal_mul]
  ring

/-- The real conjugate product of equally scaled complex numbers with the first negated is minus
the scalar square times their real conjugate product. -/
theorem re_star_neg_mul_ofReal (r : ℝ) (x y : ℂ) :
    (star (-(((r : ℝ) : ℂ) * x)) * (((r : ℝ) : ℂ) * y)).re
      = -(r * r) * (star x * y).re := by
  rw [star_neg, re_neg_mul, re_star_ofReal_mul_ofReal_mul]
  ring

/-- The real raising-lowering parent-factor inner product is the negative exponential weight
times the real conjugate product of the off-diagonal entries. -/
theorem hsInner_raise_lower_re (β g : ℝ) (X : Operator 2) :
    (hsInner (parentFactor (gibbsDiag ![g, 0] β) qubitRaise X)
        (parentFactor (gibbsDiag ![g, 0] β) qubitLower X)).re
      = -(Real.exp (β * g / 2) + Real.exp (-(β * g / 2)))
          * (star (X 1 0) * X 0 1).re := by
  rw [hsInner_eq_sum_entries]
  have h := parentFactor_raise_entry β g X
  have h' := parentFactor_lower_entry β g X
  simp only [Fin.sum_univ_two, h.1, h.2.1, h.2.2.1, h.2.2.2,
    h'.1, h'.2.1, h'.2.2.1, h'.2.2.2, Complex.add_re, star_zero,
    MulZeroClass.zero_mul, MulZeroClass.mul_zero, Complex.zero_re]
  rw [show ckgLadderC1 β g = ((Real.exp (-(β * g / 4)) : ℝ) : ℂ) from rfl,
    show ckgLadderC2 β g = ((Real.exp (β * g / 4) : ℝ) : ℂ) from rfl]
  rw [re_star_ofReal_mul_neg, re_star_neg_mul_ofReal]
  rw [exp_sq_half, exp_sq_half']
  ring

/-- Evaluates the diagonal source weight at gap `g` using four times the squared gap in the
exponent. -/
theorem ckgSourceWeight_self_twoLevel (β g : ℝ) :
    ckgSourceWeight β g g = ckgC * Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) := by
  rw [ckgSourceWeight,
    show -(β ^ 2 / 16) * ((g - g) ^ 2 + 2 * g ^ 2 + 2 * g ^ 2)
        = -(β ^ 2 / 16) * (4 * g ^ 2) from by ring]

/-- Evaluates the source weight at opposite gaps using eight times the squared gap in the
exponent. -/
theorem ckgSourceWeight_cross_twoLevel (β g : ℝ) :
    ckgSourceWeight β g (-g) = ckgC * Real.exp (-(β ^ 2 / 16) * (8 * g ^ 2)) := by
  rw [ckgSourceWeight,
    show -(β ^ 2 / 16) * ((g - (-g)) ^ 2 + 2 * g ^ 2 + 2 * (-g) ^ 2)
        = -(β ^ 2 / 16) * (8 * g ^ 2) from by ring]

/-- The source weight at opposite gaps equals the diagonal source weight times the stated
Gaussian suppression factor. -/
theorem ckgSourceWeight_cross_ratio (β g : ℝ) :
    ckgSourceWeight β g (-g) = ckgSourceWeight β g g
      * Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) := by
  rw [ckgSourceWeight_self_twoLevel, ckgSourceWeight_cross_twoLevel, mul_assoc,
    ← Real.exp_add]
  congr 1
  ring

/-- The diagonal source weight at the negative gap has the same explicit Gaussian expression as
at the positive gap. -/
theorem ckgSourceWeight_self_neg_twoLevel (β g : ℝ) :
    ckgSourceWeight β (-g) (-g) = ckgC * Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) := by
  rw [ckgSourceWeight,
    show -(β ^ 2 / 16) * ((-g - (-g)) ^ 2 + 2 * (-g) ^ 2 + 2 * (-g) ^ 2)
        = -(β ^ 2 / 16) * (4 * g ^ 2) from by ring]

/-- The real part of a conjugate product is symmetric in its two complex arguments. -/
theorem re_star_comm (x y : ℂ) : (star x * y).re = (star y * x).re := by
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Expresses the real qubit ladder source plain form using the off-diagonal squared norms,
their cross term, and the squared ladder residual. -/
theorem ckgSourcePlainForm_qubitLadder_re (β g : ℝ) (X : Operator 2) :
    (ckgSourcePlainForm β (gibbsDiag ![g, 0] β) ![g, -g] ![qubitRaise, qubitLower] X).re
      = ckgSourceWeight β g g / 2
          * ((Real.exp (β * g / 2) + Real.exp (-(β * g / 2)))
              * (Complex.normSq (X 0 1) + Complex.normSq (X 1 0)
                - 2 * Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) * (star (X 1 0) * X 0 1).re)
            + 2 * Complex.normSq (ckgLadderU β g X)) := by
  have h10 : (hsInner (parentFactor (gibbsDiag ![g, 0] β) qubitLower X)
      (parentFactor (gibbsDiag ![g, 0] β) qubitRaise X)).re
      = (hsInner (parentFactor (gibbsDiag ![g, 0] β) qubitRaise X)
          (parentFactor (gibbsDiag ![g, 0] β) qubitLower X)).re := by
    rw [hsInner_conj_swap]
    simp
  rw [ckgSourcePlainForm, wplainForm_re]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [h10, hsInner_raise_raise_re, hsInner_raise_lower_re, hsInner_lower_lower_re]
  rw [ckgSourceWeight_cross_ratio, ckgSourceWeight_symm β (-g) g,
    ckgSourceWeight_cross_ratio, ckgSourceWeight_self_neg_twoLevel,
    ← ckgSourceWeight_self_twoLevel]
  ring

noncomputable def ckgLadderP (β g : ℝ) : ℝ :=
  Real.exp (-(β * g)) / (Real.exp (-(β * g)) + 1)

noncomputable def ckgLadderQ (β g : ℝ) : ℝ := 1 / (Real.exp (-(β * g)) + 1)

/-- The two ladder Gibbs probabilities sum to one. -/
theorem ckgLadderPQ_add (β g : ℝ) : ckgLadderP β g + ckgLadderQ β g = 1 := by
  unfold ckgLadderP ckgLadderQ
  field_simp

/-- The ladder probability `ckgLadderQ` is `ckgLadderP` multiplied by the gap exponential. -/
theorem ckgLadderQ_eq (β g : ℝ) :
    ckgLadderQ β g = ckgLadderP β g * Real.exp (β * g) := by
  have h1 : Real.exp (-(β * g)) * Real.exp (β * g) = 1 := by
    rw [← Real.exp_add, show -(β * g) + β * g = 0 from by ring]
    exact Real.exp_zero
  unfold ckgLadderP ckgLadderQ
  rw [← h1]
  field_simp

/-- The ladder Gibbs probability `ckgLadderP` is nonnegative. -/
theorem ckgLadderP_nonneg (β g : ℝ) : 0 ≤ ckgLadderP β g := by
  unfold ckgLadderP
  positivity

/-- The square root of `ckgLadderQ` equals the square root of `ckgLadderP` times the half-gap
exponential. -/
theorem ckgLadderSqrtQ_eq (β g : ℝ) :
    Real.sqrt (ckgLadderQ β g) = Real.sqrt (ckgLadderP β g) * Real.exp (β * g / 2) := by
  rw [ckgLadderQ_eq, Real.sqrt_mul (ckgLadderP_nonneg β g),
    show Real.exp (β * g) = (Real.exp (β * g / 2)) ^ 2 from by
      rw [pow_two, ← Real.exp_add]; congr 1; ring,
    Real.sqrt_sq (Real.exp_nonneg _)]

/-- The complex embedding of a real number is fixed by conjugation. -/
theorem star_ofReal (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

/-- The real conjugate product is symmetric in its complex arguments. -/
theorem re_conj_comm (x y : ℂ) :
    ((starRingEnd ℂ) x * y).re = ((starRingEnd ℂ) y * x).re := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Pulls two real scalar factors out of the real part of a product with a conjugated second
factor. -/
theorem re_ofReal_mul_conj (r s : ℝ) (x y : ℂ) :
    (((r : ℝ) : ℂ) * x * (starRingEnd ℂ) (((s : ℝ) : ℂ) * y)).re
      = r * s * ((starRingEnd ℂ) y * x).re := by
  have hconj : (starRingEnd ℂ) (((s : ℝ) : ℂ) * y)
      = ((s : ℝ) : ℂ) * (starRingEnd ℂ) y := by
    rw [map_mul, Complex.conj_ofReal]
  have hz : ((r : ℝ) : ℂ) * x * (((s : ℝ) : ℂ) * (starRingEnd ℂ) y)
      = ((r * s : ℝ) : ℂ) * ((starRingEnd ℂ) y * x) := by
    rw [Complex.ofReal_mul]
    ring
  rw [hconj, hz, re_ofReal_mul']

/-- The Hilbert-Schmidt variance relative to the two-level Gibbs square root is the off-diagonal
squared-norm sum plus the stated weighted squared ladder residual. -/
theorem hsVar_sqrt_gibbsDiag_two (β g : ℝ) (X : Operator 2) :
    hsVar (CFC.sqrt (gibbsDiag ![g, 0] β)) X
      = Complex.normSq (X 0 1) + Complex.normSq (X 1 0)
        + (Real.exp (β * g / 2) / (1 + Real.exp (β * g)))
          * Complex.normSq (ckgLadderU β g X) := by
  classical
  have hf : ∀ i : Fin 2, 0 ≤ Real.exp (-(β * (![g, 0] : Fin 2 → ℝ) i))
      / ∑ k', Real.exp (-(β * (![g, 0] : Fin 2 → ℝ) k')) := by
    intro i
    have hZ : 0 < ∑ k' : Fin 2, Real.exp (-(β * (![g, 0] : Fin 2 → ℝ) k')) :=
      Finset.sum_pos (fun k _ => Real.exp_pos _) ⟨0, Finset.mem_univ 0⟩
    exact div_nonneg (Real.exp_pos _).le hZ.le
  have hW : CFC.sqrt (gibbsDiag ![g, 0] β)
      = Matrix.diagonal fun i : Fin 2 => ((Real.sqrt (Real.exp (-(β * (![g, 0] : Fin 2 → ℝ) i))
          / ∑ k', Real.exp (-(β * (![g, 0] : Fin 2 → ℝ) k'))) : ℝ) : ℂ) := by
    have h := CFC_sqrt_diagonal
      (fun k : Fin 2 => Real.exp (-(β * (![g, 0] : Fin 2 → ℝ) k))
        / ∑ k', Real.exp (-(β * (![g, 0] : Fin 2 → ℝ) k'))) hf
    simpa [gibbsDiag] using h
  have hsum : (∑ k' : Fin 2, Real.exp (-(β * (![g, 0] : Fin 2 → ℝ) k')))
      = Real.exp (-(β * g)) + 1 := by
    simp [Fin.sum_univ_two]
  have hW00 : (CFC.sqrt (gibbsDiag ![g, 0] β)) 0 0
      = ((Real.sqrt (ckgLadderP β g) : ℝ) : ℂ) := by
    rw [hW]
    simp [hsum, ckgLadderP]
  have hW11 : (CFC.sqrt (gibbsDiag ![g, 0] β)) 1 1
      = ((Real.sqrt (ckgLadderQ β g) : ℝ) : ℂ) := by
    rw [hW]
    simp [hsum, ckgLadderQ]
  have hW01 : (CFC.sqrt (gibbsDiag ![g, 0] β)) 0 1 = 0 := by
    rw [hW]; simp
  have hW10 : (CFC.sqrt (gibbsDiag ![g, 0] β)) 1 0 = 0 := by
    rw [hW]; simp

  have hWX : hsInner (CFC.sqrt (gibbsDiag ![g, 0] β)) X
      = ((Real.sqrt (ckgLadderP β g) : ℝ) : ℂ) * X 0 0
        + ((Real.sqrt (ckgLadderQ β g) : ℝ) : ℂ) * X 1 1 := by
    rw [hsInner_eq_sum_entries]
    simp only [Fin.sum_univ_two, hW00, hW01, hW10, hW11, star_zero, star_ofReal,
      MulZeroClass.zero_mul, add_zero, zero_add]
  have hWWre : (hsInner (CFC.sqrt (gibbsDiag ![g, 0] β))
      (CFC.sqrt (gibbsDiag ![g, 0] β))).re = 1 := by
    rw [hsInner_eq_sum_entries]
    simp only [Fin.sum_univ_two, hW00, hW01, hW10, hW11, star_zero, star_ofReal,
      MulZeroClass.zero_mul, add_zero, zero_add]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, Complex.add_re, Complex.ofReal_re,
      Complex.ofReal_re, Real.mul_self_sqrt (ckgLadderP_nonneg β g),
      Real.mul_self_sqrt (show 0 ≤ ckgLadderQ β g from by
        unfold ckgLadderQ; positivity),
      ← ckgLadderPQ_add β g]
  have hXXre : (hsInner X X).re = Complex.normSq (X 0 0) + Complex.normSq (X 0 1)
      + Complex.normSq (X 1 0) + Complex.normSq (X 1 1) := by
    rw [hsInner_eq_sum_entries]
    simp only [Fin.sum_univ_two, Complex.add_re, re_star_mul_self]
    ring

  have hQsub : ckgLadderQ β g = 1 - ckgLadderP β g := by
    rw [← ckgLadderPQ_add β g]
    ring
  have hsq : Real.sqrt (ckgLadderP β g) * Real.sqrt (ckgLadderQ β g)
      = ckgLadderP β g * Real.exp (β * g / 2) := by
    rw [ckgLadderSqrtQ_eq, ← mul_assoc, Real.mul_self_sqrt (ckgLadderP_nonneg β g)]
  have he12 : Real.exp (-(β * g / 4)) * Real.exp (β * g / 4) = 1 := by
    rw [← Real.exp_add, show -(β * g / 4) + β * g / 4 = 0 from by ring]
    exact Real.exp_zero
  rw [hsVar, hXXre, hWX, hWWre, div_one]
  rw [Complex.normSq_add, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal, re_ofReal_mul_conj]
  rw [show ckgLadderU β g X = ((Real.exp (-(β * g / 4)) : ℝ) : ℂ) * X 1 1
        - ((Real.exp (β * g / 4) : ℝ) : ℂ) * X 0 0 from rfl]
  rw [Complex.normSq_sub, Complex.normSq_mul, Complex.normSq_mul,
    Complex.normSq_ofReal, Complex.normSq_ofReal, re_ofReal_mul_conj]
  rw [Real.mul_self_sqrt (ckgLadderP_nonneg β g),
    Real.mul_self_sqrt (show 0 ≤ ckgLadderQ β g from by
      unfold ckgLadderQ; positivity), hsq, hQsub,
    he12, exp_sq_half, exp_sq_half', re_conj_comm]
  have he0 : Real.exp (-(β * g)) * Real.exp (β * g) = 1 := by
    rw [← Real.exp_add, show -(β * g) + β * g = 0 from by ring]
    exact Real.exp_zero
  have hD : (1 + Real.exp (β * g))⁻¹ = ckgLadderP β g := by
    unfold ckgLadderP
    field_simp
    nlinarith [he0]
  have hD2 : Real.exp (β * g / 2) / (1 + Real.exp (β * g))
      = ckgLadderP β g * Real.exp (β * g / 2) := by
    rw [div_eq_mul_inv, hD, mul_comm]
  rw [hD2]
  have hE2sq : ckgLadderP β g * (Real.exp (β * g / 2) * Real.exp (β * g / 2))
      = 1 - ckgLadderP β g := by
    rw [show Real.exp (β * g / 2) * Real.exp (β * g / 2) = Real.exp (β * g) from by
        rw [← Real.exp_add]; congr 1; ring,
      ← ckgLadderQ_eq β g, hQsub]
  have he2inv : Real.exp (β * g / 2) * Real.exp (-(β * g / 2)) = 1 := by
    rw [← Real.exp_add, show β * g / 2 + -(β * g / 2) = 0 from by ring]
    exact Real.exp_zero
  linear_combination (-Complex.normSq (X 0 0)) * hE2sq
    - ckgLadderP β g * Complex.normSq (X 1 1) * he2inv

/-- The explicit qubit gap `ckgQubitGap` is strictly positive for positive inverse temperature
and positive gap. -/
theorem ckgQubitGap_pos {β g : ℝ} (hβ : 0 < β) (hg : 0 < g) :
    0 < ckgQubitGap β g := by
  have hσlt : Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hnz : (β * g : ℝ) ≠ 0 := by nlinarith [hβ, hg]
    have hp : (0 : ℝ) < β ^ 2 * g ^ 2 := by
      nlinarith [sq_pos_of_ne_zero hnz]
    nlinarith [hp]
  have h1σ : 0 < 1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) := by linarith
  have hK : 0 < Real.exp (β * g / 2) + Real.exp (-(β * g / 2)) := by positivity
  have hM2 : 0 < 2 * (1 + Real.exp (β * g)) / Real.exp (β * g / 2) := by positivity
  unfold ckgQubitGap
  apply mul_pos
  · exact div_pos (mul_pos (ckgSourceWeight_pos β g g) h1σ) (by norm_num)
  · exact lt_min hK hM2

/-- The qubit ladder source plain form bounds the Gibbs-relative Hilbert-Schmidt variance
multiplied by `ckgQubitGap`. -/
theorem ckgSourceFormGap_qubitLadder {β g : ℝ} (hβ : 0 < β) (hg : 0 < g)
    (X : Operator 2) :
    ckgQubitGap β g * hsVar (CFC.sqrt (gibbsDiag ![g, 0] β)) X
      ≤ (ckgSourcePlainForm β (gibbsDiag ![g, 0] β) ![g, -g]
          ![qubitRaise, qubitLower] X).re := by
  rw [ckgSourcePlainForm_qubitLadder_re, hsVar_sqrt_gibbsDiag_two]
  have hσlt : Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) < 1 := by
    apply Real.exp_lt_one_iff.mpr
    have hnz : (β * g : ℝ) ≠ 0 := by nlinarith [hβ, hg]
    have hp : (0 : ℝ) < β ^ 2 * g ^ 2 := by
      nlinarith [sq_pos_of_ne_zero hnz]
    nlinarith [hp]
  have hσle : Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) ≤ 1 := le_of_lt hσlt
  have hσnn : 0 ≤ Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) := by positivity
  have hWpos : 0 < ckgSourceWeight β g g := ckgSourceWeight_pos β g g
  have hKpos : 0 < Real.exp (β * g / 2) + Real.exp (-(β * g / 2)) := by positivity

  have hsplit : Complex.normSq (X 0 1) + Complex.normSq (X 1 0)
      - 2 * Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) * (star (X 1 0) * X 0 1).re
      = (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)))
          * (Complex.normSq (X 0 1) + Complex.normSq (X 1 0))
        + Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))
          * Complex.normSq (X 0 1 - X 1 0) := by
    have hc : (X 0 1 * (starRingEnd ℂ) (X 1 0)).re
        = (star (X 1 0) * X 0 1).re := by
      rw [Complex.star_def]
      exact congrArg Complex.re (mul_comm _ _)
    rw [Complex.normSq_sub, hc]
    ring
  rw [hsplit]

  have hSnn : 0 ≤ Complex.normSq (X 0 1) + Complex.normSq (X 1 0) :=
    add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _)
  have hUnn : 0 ≤ Complex.normSq (ckgLadderU β g X) := Complex.normSq_nonneg _
  have hDnn : 0 ≤ Complex.normSq (X 0 1 - X 1 0) := Complex.normSq_nonneg _

  have hm1 : ckgQubitGap β g
      ≤ ckgSourceWeight β g g * (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))) / 2
        * (Real.exp (β * g / 2) + Real.exp (-(β * g / 2))) := by
    unfold ckgQubitGap
    exact mul_le_mul_of_nonneg_left (min_le_left _ _)
      (div_nonneg (mul_nonneg (ckgSourceWeight_pos β g g).le (by positivity))
        (by norm_num))
  have h1σnn : 0 ≤ 1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) := by
    linarith
  have hm2 : ckgQubitGap β g
      * (Real.exp (β * g / 2) / (1 + Real.exp (β * g)))
      ≤ ckgSourceWeight β g g * (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))) := by
    have hr : ckgQubitGap β g
        ≤ ckgSourceWeight β g g * (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))) / 2
          * (2 * (1 + Real.exp (β * g)) / Real.exp (β * g / 2)) := by
      unfold ckgQubitGap
      exact mul_le_mul_of_nonneg_left (min_le_right _ _)
        (div_nonneg (mul_nonneg (ckgSourceWeight_pos β g g).le (by positivity))
          (by norm_num))
    have hpos : 0 < Real.exp (β * g / 2) / (1 + Real.exp (β * g)) := by positivity
    calc ckgQubitGap β g * (Real.exp (β * g / 2) / (1 + Real.exp (β * g)))
        ≤ (ckgSourceWeight β g g * (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))) / 2
            * (2 * (1 + Real.exp (β * g)) / Real.exp (β * g / 2)))
            * (Real.exp (β * g / 2) / (1 + Real.exp (β * g))) :=
          mul_le_mul_of_nonneg_right hr hpos.le
      _ = ckgSourceWeight β g g * (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))) := by
          field_simp

  have e1 := mul_le_mul_of_nonneg_right hm1 hSnn
  have e2' : ckgQubitGap β g
      * (Real.exp (β * g / 2) / (1 + Real.exp (β * g))
        * Complex.normSq (ckgLadderU β g X))
      ≤ ckgSourceWeight β g g
        * Complex.normSq (ckgLadderU β g X) := by
    have hle : ckgQubitGap β g * (Real.exp (β * g / 2) / (1 + Real.exp (β * g)))
        ≤ ckgSourceWeight β g g := by
      refine le_trans hm2 ?_
      nlinarith [hWpos.le, hσnn]
    have h0 := mul_le_mul_of_nonneg_right hle hUnn
    rw [mul_assoc] at h0
    exact h0
  have hsDnn : 0 ≤ ckgSourceWeight β g g
      * (Real.exp (β * g / 2) + Real.exp (-(β * g / 2)))
      * Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) / 2
      * Complex.normSq (X 0 1 - X 1 0) := by
    have h1 := (ckgSourceWeight_pos β g g).le
    have h2 : 0 ≤ Real.exp (β * g / 2) + Real.exp (-(β * g / 2)) := by positivity
    have h3 : 0 ≤ Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) := by positivity
    exact mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg h1 h2) h3)
      (by norm_num)) hDnn
  calc ckgQubitGap β g
        * (Complex.normSq (X 0 1) + Complex.normSq (X 1 0)
          + Real.exp (β * g / 2) / (1 + Real.exp (β * g))
            * Complex.normSq (ckgLadderU β g X))
      = ckgQubitGap β g * (Complex.normSq (X 0 1) + Complex.normSq (X 1 0))
          + ckgQubitGap β g
            * (Real.exp (β * g / 2) / (1 + Real.exp (β * g))
              * Complex.normSq (ckgLadderU β g X)) := by ring
    _ ≤ ckgSourceWeight β g g * (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))) / 2
          * (Real.exp (β * g / 2) + Real.exp (-(β * g / 2)))
          * (Complex.normSq (X 0 1) + Complex.normSq (X 1 0))
          + ckgQubitGap β g
            * (Real.exp (β * g / 2) / (1 + Real.exp (β * g))
              * Complex.normSq (ckgLadderU β g X)) := add_le_add_left e1 _
    _ ≤ ckgSourceWeight β g g * (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))) / 2
          * (Real.exp (β * g / 2) + Real.exp (-(β * g / 2)))
          * (Complex.normSq (X 0 1) + Complex.normSq (X 1 0))
          + ckgSourceWeight β g g
            * Complex.normSq (ckgLadderU β g X) := by linarith [e2']
    _ ≤ ckgSourceWeight β g g * (1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))) / 2
          * (Real.exp (β * g / 2) + Real.exp (-(β * g / 2)))
          * (Complex.normSq (X 0 1) + Complex.normSq (X 1 0))
          + ckgSourceWeight β g g
            * (Real.exp (β * g / 2) + Real.exp (-(β * g / 2)))
            * Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)) / 2
            * Complex.normSq (X 0 1 - X 1 0)
          + ckgSourceWeight β g g
            * Complex.normSq (ckgLadderU β g X) := by linarith [hsDnn]
    _ = ckgSourceWeight β g g / 2
          * ((Real.exp (β * g / 2) + Real.exp (-(β * g / 2)))
              * ((1 - Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2)))
                  * (Complex.normSq (X 0 1) + Complex.normSq (X 1 0))
                + Real.exp (-(β ^ 2 / 16) * (4 * g ^ 2))
                  * Complex.normSq (X 0 1 - X 1 0))
            + 2 * Complex.normSq (ckgLadderU β g X)) := by
        ring

/-- The source-weighted qubit ladder parent Gram form has gap at least `ckgQubitGap` relative to
the Gibbs state square root. -/
theorem ckgSourceFormGap_op_qubitLadder {β g : ℝ} (hβ : 0 < β) (hg : 0 < g) :
    FormGapAtLeast
      (fun X => (hsInner X (parentGramFamOp
        (fun a b => ckgSourceWeight β (![g, -g] a) (![g, -g] b))
        (gibbsDiag ![g, 0] β) ![qubitRaise, qubitLower] X)).re)
      (CFC.sqrt (gibbsDiag ![g, 0] β)) (ckgQubitGap β g) := by
  intro X
  show ckgQubitGap β g * hsVar (CFC.sqrt (gibbsDiag ![g, 0] β)) X
      ≤ (hsInner X (parentGramFamOp
          (fun a b => ckgSourceWeight β (![g, -g] a) (![g, -g] b))
          (gibbsDiag ![g, 0] β) ![qubitRaise, qubitLower] X)).re
  have hRsa : (fourthRoot (gibbsDiag ![g, 0] β))ᴴ = fourthRoot (gibbsDiag ![g, 0] β) :=
    fourthRoot_isHermitian _
  rw [← ckgSourcePlainForm_eq_parentGramFamOp hRsa β ![g, -g]
    ![qubitRaise, qubitLower] X]
  exact ckgSourceFormGap_qubitLadder hβ hg X

end QubitLadder

end Qatlib.Concepts.GibbsSource.CkgBounds
