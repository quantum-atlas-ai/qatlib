/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Pair Coefficients

Squaring the actual finite complex sum retains every ordered cross term.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk

/-- Squaring the actual finite complex sum retains every ordered cross term. -/
theorem normSq_sum_cross {A : Type*} [Fintype A] (f : A → ℂ) :
    Complex.normSq (∑ x, f x) = ∑ x, ∑ y, (f x * star (f y)).re := by
  simp only [Complex.normSq_apply, Complex.re_sum, Complex.im_sum, Complex.mul_re,
    Complex.star_def, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add]
  simp_rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]

/-- The actual symmetrized coefficient square, expanded without a positivity or likelihood certificate. -/
theorem symmetrized_coefficient_point (a b c d : ℂ) :
    Complex.normSq (a*d+c*b) = Complex.normSq a*Complex.normSq d +
      Complex.normSq c*Complex.normSq b + 2*(a*star b*star (c*star d)).re := by
  simp only [Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.star_def, Complex.conj_re, Complex.conj_im]
  ring

/-- The sum of symmetrized physical amplitudes equals the actual norm product plus the actual overlap square. -/
theorem symmetrized_coefficient_sum {A : Type*} [Fintype A] (a b : A → ℂ) :
    (∑ x, ∑ y, Complex.normSq (a x*b y+a y*b x)) / 2 =
      (∑ x, Complex.normSq (a x))*(∑ x, Complex.normSq (b x)) +
        Complex.normSq (∑ x, a x*star (b x)) := by
  simp_rw [symmetrized_coefficient_point, Finset.sum_add_distrib]
  have hfirst : (∑ x, ∑ y, Complex.normSq (a x)*Complex.normSq (b y)) =
      (∑ x, Complex.normSq (a x))*(∑ y, Complex.normSq (b y)) := by
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hsecond : (∑ x, ∑ y, Complex.normSq (a y)*Complex.normSq (b x)) =
      (∑ x, Complex.normSq (a x))*(∑ y, Complex.normSq (b y)) := by
    simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hcross : (∑ x, ∑ y, 2*(a x*star (b x)*star (a y*star (b y))).re) =
      2*Complex.normSq (∑ x, a x*star (b x)) := by
    rw [normSq_sum_cross]
    simp_rw [Finset.mul_sum]
  rw [hfirst, hsecond, hcross]
  ring

/-- Diagonal coefficient mass is bounded by the literal full nonnegative double sum. -/
theorem diagonal_le_full_sum {A : Type*} [Fintype A] [DecidableEq A]
    (f : A → A → ℝ) (hf : ∀ x y, 0 ≤ f x y) :
    (∑ x, f x x) ≤ ∑ x, ∑ y, f x y := by
  exact Finset.sum_le_sum fun x _ =>
    Finset.single_le_sum (fun y _ => hf x y) (Finset.mem_univ x)

/-- The diagonal collision mass cannot exceed half the symmetrized coefficient mass; repeated addresses are retained. -/
theorem diagonal_collision_le_symmetrized {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A → ℂ) :
    2*(∑ x, Complex.normSq (a x*b x)) ≤
      (∑ x, ∑ y, Complex.normSq (a x*b y+a y*b x)) / 2 := by
  have h := diagonal_le_full_sum (fun x y => Complex.normSq (a x*b y+a y*b x))
    (fun _ _ => Complex.normSq_nonneg _)
  have hd : (∑ x, Complex.normSq (a x*b x+a x*b x)) =
      4*(∑ x, Complex.normSq (a x*b x)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
    ring
  rw [hd] at h
  linarith

/-- The actual finite complex overlap obeys Cauchy--Schwarz in the existing Euclidean space. -/
theorem overlap_normSq_le_energy_product {A : Type*} [Fintype A] (a b : A → ℂ) :
    Complex.normSq (∑ x, a x*star (b x)) ≤
      (∑ x, Complex.normSq (a x))*(∑ x, Complex.normSq (b x)) := by
  let av : EuclideanSpace ℂ A := WithLp.toLp 2 a
  let bv : EuclideanSpace ℂ A := WithLp.toLp 2 b
  have ha : ‖av‖^2 = ∑ x, Complex.normSq (a x) := by
    simpa only [av, PiLp.toLp_apply, Complex.normSq_eq_norm_sq] using
      EuclideanSpace.norm_sq_eq av
  have hb : ‖bv‖^2 = ∑ x, Complex.normSq (b x) := by
    simpa only [bv, PiLp.toLp_apply, Complex.normSq_eq_norm_sq] using
      EuclideanSpace.norm_sq_eq bv
  have hi : inner ℂ bv av = ∑ x, a x*star (b x) := by
    simp [EuclideanSpace.inner_eq_star_dotProduct, av, bv, dotProduct]
  have h := pow_le_pow_left₀ (norm_nonneg (inner ℂ bv av)) (norm_inner_le_norm bv av) 2
  rw [hi, mul_pow, hb, ha, ← Complex.normSq_eq_norm_sq] at h
  simpa only [mul_comm] using h

/-- The literal paired coefficient mass, before identifying it with the actual shared-phase Born average. -/
def pairedCoefficientMass {A : Type*} [Fintype A] (a b : A → ℂ) : ℝ :=
  (∑ x, Complex.normSq (a x))*(∑ x, Complex.normSq (b x)) +
    Complex.normSq (∑ x, a x*star (b x)) - ∑ x, Complex.normSq (a x*b x)

/-- The lower product bound follows from the real nonnegative symmetrized amplitudes, including every repeated-address diagonal. -/
theorem pairedCoefficientMass_lower {A : Type*} [Fintype A] [DecidableEq A]
    (a b : A → ℂ) :
    (∑ x, Complex.normSq (a x))*(∑ x, Complex.normSq (b x)) / 2 ≤
      pairedCoefficientMass a b := by
  have hd := diagonal_collision_le_symmetrized a b
  rw [symmetrized_coefficient_sum] at hd
  unfold pairedCoefficientMass
  linarith [Complex.normSq_nonneg (∑ x, a x*star (b x))]

/-- The upper product bound uses the existing complex Cauchy--Schwarz theorem and nonnegative collision mass. -/
theorem pairedCoefficientMass_upper {A : Type*} [Fintype A] (a b : A → ℂ) :
    pairedCoefficientMass a b ≤
      2*(∑ x, Complex.normSq (a x))*(∑ x, Complex.normSq (b x)) := by
  have hi := overlap_normSq_le_energy_product a b
  have hd : 0 ≤ ∑ x, Complex.normSq (a x*b x) :=
    Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _
  unfold pairedCoefficientMass
  linarith

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
