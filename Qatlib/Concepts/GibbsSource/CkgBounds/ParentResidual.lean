/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.FormAlgebra.ParentWeightedForm
public import Qatlib.Concepts.GibbsSource.FormAlgebra.ParentGap
public import Qatlib.Concepts.GibbsSource.CkgBounds.ParentPairedForm

@[expose] public section


/-! Residual quadratic forms and finite Hilbert--Schmidt comparison bounds.
The estimates state their actual coefficient and support premises explicitly. -/
open Qatlib.Concepts.QuantumGibbs.FormAlgebra Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Foundations.DirichletForm.KmsDirichlet Qatlib.Foundations.InstrumentCore.Measurement Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.PureStateMath.Reflection

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GibbsSource.FormAlgebra Qatlib.Concepts.QuantumGibbs.FormAlgebra

namespace Qatlib.Concepts.GibbsSource.CkgBounds

open Matrix

variable {D : ℕ} {ι : Type*} [Fintype ι]

noncomputable def residualForm (w : ι → ι → ℝ) (β : ℝ) (ρ : Operator D)
    (ν : ι → ℝ) (A : ι → Operator D) (O : Operator D) : ℂ :=
  ∑ a, ∑ b, (↑(w a b * (1 / 2 - phaseKernel β (ν a - ν b))) : ℂ)
    * hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)

/-- The weighted damped form equals the weighted plain form minus the residual form. -/
theorem wdampedForm_eq_wplainForm_sub_residual (w : ι → ι → ℝ) (β : ℝ)
    (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D) (O : Operator D) :
    wdampedForm w β ρ ν A O = wplainForm w ρ A O - residualForm w β ρ ν A O := by
  simp only [wdampedForm, wplainForm, residualForm, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  push_cast
  ring

omit [Fintype ι] in
/-- A nonnegative weight gives a nonnegative residual coefficient. -/
theorem residualCoeff_nonneg (w : ι → ι → ℝ) (β : ℝ) (ν : ι → ℝ)
    (a b : ι) (hw : 0 ≤ w a b) :
    0 ≤ w a b * (1 / 2 - phaseKernel β (ν a - ν b)) := by
  have h := phaseKernel_le_half β (ν a - ν b)
  exact mul_nonneg hw (by linarith)

omit [Fintype ι] in
/-- The residual coefficient vanishes for equal frequencies. -/
theorem residualCoeff_of_eq_freq (w : ι → ι → ℝ) (β : ℝ) (ν : ι → ℝ) {a b : ι}
    (hν : ν a = ν b) : w a b * (1 / 2 - phaseKernel β (ν a - ν b)) = 0 := by
  rw [hν, sub_self, phaseKernel_self β]
  ring

/-- The three-halves domination bound is equivalent to the residual being at least minus one
half of the plain form. -/
theorem dominationAt_iff_residual (w : ι → ι → ℝ) (β : ℝ)
    (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D) (O : Operator D) :
    (wdampedForm w β ρ ν A O).re ≤ 3 / 2 * (wplainForm w ρ A O).re
      ↔ -(1 / 2) * (wplainForm w ρ A O).re ≤ (residualForm w β ρ ν A O).re := by
  rw [wdampedForm_eq_wplainForm_sub_residual]
  simp only [Complex.sub_re]
  constructor <;> intro h <;> linarith

/-- Expands the residual form for frequencies zero and opposite gaps into its six off-diagonal
parent-factor inner-product terms. -/
theorem residualForm_three {β δ : ℝ} {ρ P M N O : Operator D} (w : Fin 3 → Fin 3 → ℝ) :
    residualForm w β ρ ![0, δ, -δ] ![P, M, N] O
      = (↑(w 0 1 * (1 / 2 - phaseKernel β (0 - δ))) : ℂ)
          * hsInner (parentFactor ρ P O) (parentFactor ρ M O)
      + (↑(w 1 0 * (1 / 2 - phaseKernel β (δ - 0))) : ℂ)
          * hsInner (parentFactor ρ M O) (parentFactor ρ P O)
      + (↑(w 0 2 * (1 / 2 - phaseKernel β (0 - (-δ)))) : ℂ)
          * hsInner (parentFactor ρ P O) (parentFactor ρ N O)
      + (↑(w 2 0 * (1 / 2 - phaseKernel β (-δ - 0))) : ℂ)
          * hsInner (parentFactor ρ N O) (parentFactor ρ P O)
      + (↑(w 1 2 * (1 / 2 - phaseKernel β (δ - (-δ)))) : ℂ)
          * hsInner (parentFactor ρ M O) (parentFactor ρ N O)
      + (↑(w 2 1 * (1 / 2 - phaseKernel β (-δ - δ))) : ℂ)
          * hsInner (parentFactor ρ N O) (parentFactor ρ M O) := by
  classical
  simp only [residualForm, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hz : ∀ x : ℝ, x - x = 0 := fun x => sub_self x
  simp only [hz, phaseKernel_self β, mul_zero]
  norm_num
  ring

/-- The Hilbert-Schmidt inner product equals the sum of conjugated products of corresponding
matrix entries. -/
theorem hsInner_eq (U V : Operator D) :
    hsInner U V = ∑ i, ∑ j, (star (U i j) * V i j : ℂ) := by
  classical
  simp only [hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply]
  exact Finset.sum_comm

/-- The real part of a conjugate product is unchanged when conjugation is moved to the other
factor. -/
theorem re_star_mul_comm (u v : ℂ) : (star u * v).re = (u * star v).re := by
  simp [Complex.mul_re]

/-- The real product with the second factor conjugated equals the real product with the first
factor conjugated. -/
theorem re_starRingEnd_mul_comm (u v : ℂ) :
    (u * (starRingEnd ℂ) v).re = (star u * v).re := by
  simp [Complex.mul_re]

/-- The real conjugate product is bounded below by minus one half the sum of the squared norms. -/
theorem re_star_mul_ge_neg_half (u v : ℂ) :
    -((Complex.normSq u + Complex.normSq v) / 2) ≤ (star u * v).re := by
  have h0 : (0 : ℝ) ≤ Complex.normSq (u + v) := Complex.normSq_nonneg _
  rw [Complex.normSq_add, re_starRingEnd_mul_comm u v] at h0
  have h1 : Complex.normSq u = (star u * u).re := by
    have h := Complex.normSq_eq_conj_mul_self (z := u)
    calc Complex.normSq u = ((↑(Complex.normSq u) : ℂ)).re := (Complex.ofReal_re _).symm
      _ = (star u * u).re := by rw [h]; simp [Complex.mul_re]
  have h2 : Complex.normSq v = (star v * v).re := by
    have h := Complex.normSq_eq_conj_mul_self (z := v)
    calc Complex.normSq v = ((↑(Complex.normSq v) : ℂ)).re := (Complex.ofReal_re _).symm
      _ = (star v * v).re := by rw [h]; simp [Complex.mul_re]
  rw [h1, h2] at h0
  linarith

/-- The real Hilbert-Schmidt inner product is bounded below by minus one half the sum of the two
squared Hilbert-Schmidt norms. -/
theorem hsInner_re_ge_neg_half (U V : Operator D) :
    -((hsInner U U).re + (hsInner V V).re) / 2 ≤ (hsInner U V).re := by
  rw [hsInner_self_re_sum U, hsInner_self_re_sum V]
  have hmix : (hsInner U V).re = ∑ i, ∑ j, (star (U i j) * V i j).re := by
    rw [hsInner_eq]; simp [Complex.re_sum]
  rw [hmix]
  have hge : (∑ i, ∑ j, -((Complex.normSq (U i j) + Complex.normSq (V i j)) / 2))
      ≤ ∑ i, ∑ j, (star (U i j) * V i j).re :=
    Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
      re_star_mul_ge_neg_half (U i j) (V i j)
  have hconv : (∑ i, ∑ j, -((Complex.normSq (U i j) + Complex.normSq (V i j)) / 2))
      = -((∑ i, ∑ j, Complex.normSq (U i j) + ∑ i, ∑ j, Complex.normSq (V i j)) / 2) := by
    have e1 : (∑ i, ∑ j, -((Complex.normSq (U i j) + Complex.normSq (V i j)) / 2))
        = ∑ i, ∑ j, ((-(Complex.normSq (U i j)) - Complex.normSq (V i j)) / 2) :=
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    have e23 : (∑ i, ∑ j, ((-(Complex.normSq (U i j)) - Complex.normSq (V i j)) / 2))
        = -((∑ i, ∑ j, Complex.normSq (U i j) + ∑ i, ∑ j, Complex.normSq (V i j)) / 2) := by
      simp only [div_eq_mul_inv]
      simp only [← Finset.sum_mul, Finset.sum_sub_distrib, Finset.sum_neg_distrib]
      ring
    rw [e1, e23]
  linarith

variable {ι : Type*} [Fintype ι]

noncomputable def kappaRow (w : ι → ι → ℝ) (β : ℝ) (ν : ι → ℝ) (a : ι) : ℝ :=
  ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b))
      + w b a * (1 / 2 - phaseKernel β (ν b - ν a))) / 2

/-- Pointwise nonnegative weights give nonnegative kappa row sums. -/
theorem kappaRow_nonneg (w : ι → ι → ℝ) (β : ℝ) (ν : ι → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (a : ι) : 0 ≤ kappaRow w β ν a := by
  refine Finset.sum_nonneg fun b _ => ?_
  have h1 := phaseKernel_le_half β (ν a - ν b)
  have h2 := phaseKernel_le_half β (ν b - ν a)
  have hna : 0 ≤ w a b * (1 / 2 - phaseKernel β (ν a - ν b)) :=
    mul_nonneg (hw a b) (by linarith)
  have hnb : 0 ≤ w b a * (1 / 2 - phaseKernel β (ν b - ν a)) :=
    mul_nonneg (hw b a) (by linarith)
  exact div_nonneg (add_nonneg hna hnb) zero_le_two

/-- The kappa row is half the sum of the outgoing and incoming weighted phase-defect sums. -/
theorem kappaRow_eq (w : ι → ι → ℝ) (β : ℝ) (ν : ι → ℝ) (a : ι) :
    kappaRow w β ν a
      = (1 / 2) * ((∑ b, w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
            + (∑ b, w b a * (1 / 2 - phaseKernel β (ν b - ν a)))) := by
  rw [kappaRow, ← Finset.sum_add_distrib]
  have hdiv : (∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b))
        + w b a * (1 / 2 - phaseKernel β (ν b - ν a))) / 2)
      = (1 / 2) * ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b))
        + w b a * (1 / 2 - phaseKernel β (ν b - ν a))) := by
    simp only [div_eq_mul_inv]
    simp only [← Finset.sum_mul]
    norm_num
    ring
  rw [hdiv]

/-- For nonnegative weights, the real residual form is bounded below by the negative
kappa-weighted sum of parent-factor squared norms. -/
theorem residualForm_re_ge_neg_rowsum {w : ι → ι → ℝ} (hw : ∀ a b, 0 ≤ w a b) (β : ℝ)
    (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D) (O : Operator D) :
    -(∑ a, kappaRow w β ν a * (hsInner (parentFactor ρ (A a) O)
        (parentFactor ρ (A a) O)).re)
      ≤ (residualForm w β ρ ν A O).re := by
  classical
  have hknn : ∀ a b, 0 ≤ w a b * (1 / 2 - phaseKernel β (ν a - ν b)) := fun a b =>
    mul_nonneg (hw a b) (by have := phaseKernel_le_half β (ν a - ν b); linarith)
  have hsum : (residualForm w β ρ ν A O).re
      = ∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re := by
    simp only [residualForm, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
  rw [hsum]
  have hy : ∀ a b : ι, -((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
        + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) / 2
      ≤ (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re :=
    fun a b => hsInner_re_ge_neg_half _ _
  have hstep : (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re)
      ≥ ∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
          * ( -((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
              + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) / 2) :=
    Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
      mul_le_mul_of_nonneg_left (hy a b) (hknn a b)

  have e0 : (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
          * ( -((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
              + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) / 2))
      = -(∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
            * ((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
              + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) / 2) := by
    have e0' : (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
          * ( -((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
              + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) / 2))
        = (∑ a, ∑ b, -((w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
            * ((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
              + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) / 2)) :=
      Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    rw [e0']
    simp only [Finset.sum_neg_distrib]
  have eA : (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
          * ((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
            + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re))
      = (∑ a, ((∑ b, w a b * (1 / 2 - phaseKernel β (ν a - ν b))
              + ∑ b, w b a * (1 / 2 - phaseKernel β (ν b - ν a)))
            * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re)) := by
    have s1 : (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
            * ((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
              + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re))
        = (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
              * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re)
          + (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
              * (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) := by
      simp only [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
    have s2 : (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
            * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re)
        = (∑ a, (∑ b, w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
              * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re) := by
      simp only [Finset.sum_mul]
    have s3 : (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
            * (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re)
        = (∑ a, (∑ b, w b a * (1 / 2 - phaseKernel β (ν b - ν a)))
              * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re) := by
      rw [Finset.sum_comm]
      simp only [Finset.sum_mul]
    rw [s1, s2, s3, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have eD : (∑ a, ((∑ b, w a b * (1 / 2 - phaseKernel β (ν a - ν b))
              + ∑ b, w b a * (1 / 2 - phaseKernel β (ν b - ν a)))
            * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re) / 2)
      = (∑ a, kappaRow w β ν a
            * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [kappaRow_eq w β ν a]
    ring
  calc (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
          * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A b) O)).re)
      ≥ ∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
          * ( -((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
              + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) / 2) :=
        hstep
    _ = -(∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
            * ((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
              + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) / 2) := e0
    _ = -(∑ a, kappaRow w β ν a
            * (hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re) := by
        have hall : (∑ a, ∑ b, (w a b * (1 / 2 - phaseKernel β (ν a - ν b)))
              * ((hsInner (parentFactor ρ (A a) O) (parentFactor ρ (A a) O)).re
                + (hsInner (parentFactor ρ (A b) O) (parentFactor ρ (A b) O)).re) / 2)
            = ((∑ a, ((∑ b, w a b * (1 / 2 - phaseKernel β (ν a - ν b))
                    + ∑ b, w b a * (1 / 2 - phaseKernel β (ν b - ν a)))
                  * (hsInner (parentFactor ρ (A a) O)
                      (parentFactor ρ (A a) O)).re))) / 2 := by
          rw [← eA]
          simp only [div_eq_mul_inv]
          simp only [← Finset.sum_mul]
        rw [hall]
        have hfin : -(((∑ a, ((∑ b, w a b * (1 / 2 - phaseKernel β (ν a - ν b))
                    + ∑ b, w b a * (1 / 2 - phaseKernel β (ν b - ν a)))
                  * (hsInner (parentFactor ρ (A a) O)
                      (parentFactor ρ (A a) O)).re))) / 2)
            = -(∑ a, kappaRow w β ν a
                * (hsInner (parentFactor ρ (A a) O)
                    (parentFactor ρ (A a) O)).re) := by
          have hpush : (((∑ a, ((∑ b, w a b * (1 / 2 - phaseKernel β (ν a - ν b))
                      + ∑ b, w b a * (1 / 2 - phaseKernel β (ν b - ν a)))
                    * (hsInner (parentFactor ρ (A a) O)
                        (parentFactor ρ (A a) O)).re))) / 2)
              = (∑ a, (((∑ b, w a b * (1 / 2 - phaseKernel β (ν a - ν b))
                      + ∑ b, w b a * (1 / 2 - phaseKernel β (ν b - ν a)))
                    * (hsInner (parentFactor ρ (A a) O)
                        (parentFactor ρ (A a) O)).re) / 2)) := by
            simp only [div_eq_mul_inv]
            simp only [← Finset.sum_mul]
          rw [hpush, eD]
        rw [hfin]

/-- Control of twice the kappa-weighted parent-factor squared norms by the plain form implies
the three-halves damped-form bound. -/
theorem domination_of_diag_control {w : ι → ι → ℝ} (hw : ∀ a b, 0 ≤ w a b) (β : ℝ)
    (ρ : Operator D) (ν : ι → ℝ) (A : ι → Operator D)
    (h : ∀ O : Operator D, 2 * (∑ a, kappaRow w β ν a * (hsInner (parentFactor ρ (A a) O)
        (parentFactor ρ (A a) O)).re) ≤ (wplainForm w ρ A O).re)
    (O : Operator D) :
    (wdampedForm w β ρ ν A O).re ≤ 3 / 2 * (wplainForm w ρ A O).re := by
  have hres := residualForm_re_ge_neg_rowsum hw β ρ ν A O
  have hdiag := h O
  have key : -(1 / 2) * (wplainForm w ρ A O).re ≤ (residualForm w β ρ ν A O).re := by
    linarith
  exact (dominationAt_iff_residual w β ρ ν A O).mpr key

/-- The Hilbert-Schmidt inner product equals the conjugate of the inner product with its
arguments exchanged. -/
theorem hsInner_conj_swap (U V : Operator D) :
    hsInner U V = star (hsInner V U) := by
  rw [hsInner, hsInner]
  have h1 : (Vᴴ * U)ᴴ = Uᴴ * V := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  rw [show Uᴴ * V = (Vᴴ * U)ᴴ from h1.symm, Matrix.trace_conjTranspose]

/-- The Hilbert-Schmidt inner product commutes with finite sums in its second argument. -/
theorem hsInner_sum_right (U : Operator D) (v : ι → Operator D) :
    hsInner U (∑ a, v a) = ∑ a, hsInner U (v a) := by
  simp only [hsInner, Matrix.mul_sum, Matrix.trace_sum]

/-- The Hilbert-Schmidt inner product commutes with finite sums in its first argument. -/
theorem hsInner_sum_left (v : ι → Operator D) (U : Operator D) :
    hsInner (∑ a, v a) U = ∑ a, hsInner (v a) U := by
  simp only [hsInner, conjTranspose_sum', Matrix.sum_mul, Matrix.trace_sum]

/-- Two embedded real scalar factors pull out of the real part of the conjugate-weighted complex
product. -/
theorem re_ofReal_mul_star_ofReal_mul (r s : ℝ) (z : ℂ) :
    (↑s * (star ↑r * z)).re = r * s * z.re := by
  rw [show star ((r : ℝ) : ℂ) = (starRingEnd ℂ) ((r : ℝ) : ℂ) from rfl, Complex.conj_ofReal]
  have h1 := Complex.mul_re ((s : ℝ) : ℂ) (((r : ℝ) : ℂ) * z)
  have h2 := Complex.mul_re ((r : ℝ) : ℂ) z
  rw [h1, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, h2,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- Expands the real Hilbert-Schmidt inner product of two real-weighted operator sums as the
corresponding double Gram sum. -/
theorem hsInner_re_bilinear_sum (c d : ι → ℝ) (B C : ι → Operator D) :
    (hsInner (∑ a, ((c a : ℝ) : ℂ) • B a) (∑ b, ((d b : ℝ) : ℂ) • C b)).re
      = ∑ a, ∑ b, c a * d b * (hsInner (B a) (C b)).re := by
  rw [hsInner_sum_left, Finset.sum_congr rfl fun a _ => hsInner_sum_right _ _]
  simp only [hsInner_smul_left, hsInner_smul_right]
  rw [Complex.re_sum, Finset.sum_congr rfl fun a _ => Complex.re_sum _ _]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
    re_ofReal_mul_star_ofReal_mul (c a) (d b) _

noncomputable def gramMat (B : ι → Operator D) : Matrix ι ι ℝ :=
  Matrix.of fun a b => (hsInner (B a) (B b)).re

omit [Fintype ι] in
/-- The operator Gram matrix `gramMat` is Hermitian. -/
theorem gramMat_isHermitian (B : ι → Operator D) : (gramMat B).IsHermitian := by
  show (gramMat B)ᴴ = gramMat B
  ext a b
  have h := hsInner_conj_swap (B a) (B b)
  rw [show star (hsInner (B b) (B a)) = (starRingEnd ℂ) (hsInner (B b) (B a)) from rfl] at h
  simp only [gramMat, Matrix.conjTranspose_apply, Matrix.of_apply]
  rw [star_trivial, h]
  exact (Complex.conj_re _).symm

/-- The operator Gram matrix `gramMat` is positive semidefinite. -/
theorem gramMat_posSemidef (B : ι → Operator D) : Matrix.PosSemidef (gramMat B) := by
  refine ⟨gramMat_isHermitian B, fun x => ?_⟩
  have h1 : x.sum (fun i xi => x.sum (fun j xj => star xi * gramMat B i j * xj))
      = ∑ i, ∑ j, x i * x j * (hsInner (B i) (B j)).re := by
    rw [Finsupp.sum_fintype x _ (fun i => by
      rw [Finsupp.sum_fintype x _ (fun j => by simp)]
      simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finsupp.sum_fintype x _ (fun j => by simp)]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [gramMat, Matrix.of_apply, star_trivial]
    ring
  rw [h1]
  rw [← hsInner_re_bilinear_sum (fun i => x i) (fun j => x j) B B]
  exact hsInner_self_nonneg _

end Qatlib.Concepts.GibbsSource.CkgBounds
