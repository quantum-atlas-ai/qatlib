/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HittingTimes08.MainResults.Rotate
import Qatlib.Papers.HittingTimes08.MainResults.Tulsi
import Qatlib.Papers.HittingTimes08.MainResults.TulsiSpectrum

/-!
# Norm and overlap bounds for the Tulsi construction

This module proves scalar norm estimates and stability of real inner-product overlaps under
vector perturbations. With the specified spectral comparisons, it derives the constant overlap
bound used in the Tulsi analysis of [MagniezEtAl2008].

## Main statements

* `lemma_4_8_norm_le`: bounds the modified spectral norm expression by `3 * cos θ` times the
  original expression.
* `theorem_4_9_constant_overlap`: proves the spectral overlap lower bound `(1 - ε) / 90`.
* `corollary_4_10_constant_overlap`: transfers the constant overlap through a controlled
  rotation error.

## References

* [Magniez et al., 2008][MagniezEtAl2008]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HittingTimes08.MainResults

open scoped BigOperators InnerProductSpace

/-- For `0 < x ≤ a < c ≤ π / 2`, the squared ratio `sin x / (cos x - cos c)` is at most the
corresponding squared ratio at `a`. -/
theorem sin_div_cos_sub_cos_sq_le {x a c : ℝ}
    (hx : 0 < x) (hxa : x ≤ a) (hac : a < c) (hc : c ≤ Real.pi / 2) :
    (Real.sin x / (Real.cos x - Real.cos c)) ^ 2 ≤
      (Real.sin a / (Real.cos a - Real.cos c)) ^ 2 := by
  have hpi := Real.pi_pos
  have ha0 : 0 ≤ a := le_trans hx.le hxa
  have hcpos : 0 < c := lt_trans (lt_of_lt_of_le hx hxa) hac
  have hcx : Real.cos c < Real.cos x :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hx.le hc (by linarith)
  have hca : Real.cos c < Real.cos a :=
    Real.cos_lt_cos_of_nonneg_of_le_pi_div_two ha0 hc hac
  have hsinx_nonneg : 0 ≤ Real.sin x :=
    Real.sin_nonneg_of_nonneg_of_le_pi hx.le (by nlinarith [hc, hpi])
  have hsina_nonneg : 0 ≤ Real.sin a :=
    Real.sin_nonneg_of_nonneg_of_le_pi ha0 (by nlinarith [hc, hpi])
  have hdenx : 0 < Real.cos x - Real.cos c := by linarith
  have hdena : 0 < Real.cos a - Real.cos c := by linarith
  have hgx : 0 ≤ Real.sin x / (Real.cos x - Real.cos c) := div_nonneg hsinx_nonneg hdenx.le

  have hsinax : Real.sin (a - x) =
      Real.sin a * Real.cos x - Real.cos a * Real.sin x := Real.sin_sub a x
  have hsindiff : Real.sin a - Real.sin x =
      2 * Real.sin ((a - x) / 2) * Real.cos ((a + x) / 2) := Real.sin_sub_sin a x
  have hsinax2 : Real.sin (a - x) =
      2 * Real.sin ((a - x) / 2) * Real.cos ((a - x) / 2) := by
    have := Real.sin_sub_sin (a - x) 0
    simpa using this
  have h1 : Real.sin a * Real.cos x - Real.sin x * Real.cos a = Real.sin (a - x) := by
    rw [Real.sin_sub]; ring
  have h2 : Real.sin x - Real.sin a =
      -(2 * Real.sin ((a - x) / 2) * Real.cos ((a + x) / 2)) := by
    rw [← hsindiff]; ring
  have hD_eq : Real.sin a * (Real.cos x - Real.cos c) -
        Real.sin x * (Real.cos a - Real.cos c) =
      2 * Real.sin ((a - x) / 2) *
        (Real.cos ((a - x) / 2) - Real.cos c * Real.cos ((a + x) / 2)) := by
    have hexp : Real.sin a * (Real.cos x - Real.cos c) -
        Real.sin x * (Real.cos a - Real.cos c) =
        (Real.sin a * Real.cos x - Real.sin x * Real.cos a) +
          Real.cos c * (Real.sin x - Real.sin a) := by ring
    rw [hexp, h1, h2, hsinax2]
    ring
  have hdelta_nonneg : 0 ≤ (a - x) / 2 := by linarith
  have hbracket : 0 ≤ Real.cos ((a - x) / 2) - Real.cos c * Real.cos ((a + x) / 2) := by
    have hcosd : Real.cos c ≤ Real.cos ((a - x) / 2) :=
      Real.cos_le_cos_of_nonneg_of_le_pi hdelta_nonneg (by linarith [hc, hpi])
        (by linarith)
    have hcosc_nonneg : 0 ≤ Real.cos c :=
      Real.cos_nonneg_of_mem_Icc ⟨by linarith [hpi], hc⟩
    have hcosax : Real.cos ((a + x) / 2) ≤ 1 := Real.cos_le_one _
    nlinarith [mul_le_mul_of_nonneg_left hcosax hcosc_nonneg, hcosd]
  have hsin_delta : 0 ≤ Real.sin ((a - x) / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi hdelta_nonneg (by nlinarith [hc, hpi])
  have hprod : 0 ≤ 2 * Real.sin ((a - x) / 2) *
      (Real.cos ((a - x) / 2) - Real.cos c * Real.cos ((a + x) / 2)) :=
    mul_nonneg (mul_nonneg (by norm_num) hsin_delta) hbracket
  have hD : 0 ≤ Real.sin a * (Real.cos x - Real.cos c) -
      Real.sin x * (Real.cos a - Real.cos c) := by
    rw [hD_eq]; exact hprod
  have hratio : Real.sin x / (Real.cos x - Real.cos c) ≤
      Real.sin a / (Real.cos a - Real.cos c) := by
    rw [div_le_div_iff₀ hdenx hdena]
    linarith
  exact pow_le_pow_left₀ hgx hratio 2

/-- If `A ≤ 2 * B`, multiplying by `4 * cos θ ^ 2` gives `4 * cos θ ^ 2 * A ≤ 8 * cos θ ^ 2 *
B`. -/
theorem lemma_4_8_norm_bound (A B : ℝ) (θ : ℝ) (h : A ≤ 2 * B) :
    4 * (Real.cos θ) ^ 2 * A ≤ 8 * (Real.cos θ) ^ 2 * B := by
  have hc2 : 0 ≤ (Real.cos θ) ^ 2 := sq_nonneg _
  nlinarith [hc2, h]

/-- For a target of norm at most one, replacing `urot` by a vector within distance `δ` decreases
its overlap with the target by at most `δ`. This is the perturbation estimate used for
Theorem 4.9 of [MagniezEtAl2008]. -/
theorem theorem_4_9_overlap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (target urot u : E) (c δ : ℝ) (ht : ‖target‖ ≤ 1)
    (hrot : c ≤ ⟪target, urot⟫_ℝ) (hδ : ‖urot - u‖ ≤ δ) :
    c - δ ≤ ⟪target, u⟫_ℝ := by
  have hcs : |⟪target, urot - u⟫_ℝ| ≤ ‖target‖ * ‖urot - u‖ :=
    abs_real_inner_le_norm target (urot - u)
  have hdiff : ⟪target, urot⟫_ℝ - ⟪target, u⟫_ℝ = ⟪target, urot - u⟫_ℝ := by
    rw [inner_sub_right]
  have hle : ⟪target, urot⟫_ℝ - ⟪target, u⟫_ℝ ≤ δ := by
    rw [hdiff]
    calc ⟪target, urot - u⟫_ℝ
        ≤ ‖target‖ * ‖urot - u‖ := le_trans (le_abs_self _) hcs
      _ ≤ 1 * δ := by
          exact mul_le_mul ht hδ (norm_nonneg _) (by norm_num)
      _ = δ := by ring
  linarith

/-- If the ideal overlap is at least `c` and the perturbation is at most `sqrt (8 * ε) < c`,
then the actual overlap is positive and at least `c - sqrt (8 * ε)`, as in Corollary 4.10 of
[MagniezEtAl2008]. -/
theorem corollary_4_10_overlap {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (target urot u : E) (c ε : ℝ) (ht : ‖target‖ ≤ 1)
    (hrot : c ≤ ⟪target, urot⟫_ℝ) (hδ : ‖urot - u‖ ≤ Real.sqrt (8 * ε))
    (hc : Real.sqrt (8 * ε) < c) :
    c - Real.sqrt (8 * ε) ≤ ⟪target, u⟫_ℝ ∧ 0 < ⟪target, u⟫_ℝ := by
  have h := theorem_4_9_overlap target urot u c (Real.sqrt (8 * ε)) ht hrot hδ
  constructor
  · exact h
  · linarith

/-- Under the stated phase, cotangent, tangent, and spectral-sum comparisons, the modified
square-root norm expression is at most `3 * cos θ` times the original square-root
expression. This is the norm comparison associated with [Magniez et al., Lemma
4.8][MagniezEtAl2008]. -/
theorem lemma_4_8_norm_le {J : Type*} [Fintype J] (a0 : ℝ) (a : J → ℝ)
    (θ x α : ℝ) (θj : J → ℝ) (hcos : 0 ≤ Real.cos θ)
    (hx : 0 < x) (hxπ : x < Real.pi) (hα : 0 < α) (hα4 : α ≤ Real.pi / 4)
    (hcot : cot (x / 2) ≤ (101 / 100) * cot (α / 2))
    (hcomp : ∀ j, (Real.sin x / (Real.cos x - Real.cos (θj j))) ^ 2 ≤
        (Real.sin α / (Real.cos α - Real.cos (θj j))) ^ 2)
    (htanθ : Real.tan θ ^ 2 = a0 ^ 2 * (cot (α / 2)) ^ 2 / 100)
    (htanx : Real.tan (x / 2) ^ 2 ≤ 1) :
    Real.sqrt (4 * (Real.cos θ) ^ 2 *
        (a0 ^ 2 * (cot (x / 2)) ^ 2 +
          2 * (∑ j, (a j) ^ 2 *
            (Real.sin x / (Real.cos x - Real.cos (θj j))) ^ 2) +
          (Real.tan θ) ^ 2 * (Real.tan (x / 2)) ^ 2))
      ≤ 3 * Real.cos θ *
        Real.sqrt (4 * (a0 ^ 2 * (cot (α / 2)) ^ 2 +
          2 * (∑ j, (a j) ^ 2 *
            (Real.sin α / (Real.cos α - Real.cos (θj j))) ^ 2))) := by
  have hpi := Real.pi_pos
  have hcotx_nonneg : 0 ≤ cot (x / 2) := by
    rw [cot]
    apply div_nonneg
    · exact le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hpi], by nlinarith [hpi, hxπ]⟩)
    · exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [hpi, hxπ]))
  have hcota_nonneg : 0 ≤ cot (α / 2) := by
    rw [cot]
    apply div_nonneg
    · exact le_of_lt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hpi], by nlinarith [hpi, hα4]⟩)
    · exact le_of_lt (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by nlinarith [hpi, hα4]))
  have hcot_sq : (cot (x / 2)) ^ 2 ≤ (101 / 100) ^ 2 * (cot (α / 2)) ^ 2 := by
    nlinarith [hcot, hcotx_nonneg, hcota_nonneg]
  have hcomp_sum : (∑ j, (a j) ^ 2 *
        (Real.sin x / (Real.cos x - Real.cos (θj j))) ^ 2) ≤
      ∑ j, (a j) ^ 2 *
        (Real.sin α / (Real.cos α - Real.cos (θj j))) ^ 2 := by
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_left (hcomp j) (sq_nonneg _)
  have htanterm : (Real.tan θ) ^ 2 * (Real.tan (x / 2)) ^ 2 ≤
      a0 ^ 2 * (cot (α / 2)) ^ 2 := by
    rw [htanθ]
    have hq : 0 ≤ (cot (α / 2)) ^ 2 := sq_nonneg _
    have ha0 : 0 ≤ a0 ^ 2 := sq_nonneg _
    nlinarith [htanx, hq, ha0]
  have hAle : a0 ^ 2 * (cot (x / 2)) ^ 2 +
        2 * (∑ j, (a j) ^ 2 *
          (Real.sin x / (Real.cos x - Real.cos (θj j))) ^ 2) +
        (Real.tan θ) ^ 2 * (Real.tan (x / 2)) ^ 2
      ≤ 4 * (a0 ^ 2 * (cot (α / 2)) ^ 2 +
        2 * (∑ j, (a j) ^ 2 *
          (Real.sin α / (Real.cos α - Real.cos (θj j))) ^ 2)) := by
    have h1 : a0 ^ 2 * (cot (x / 2)) ^ 2 ≤
        a0 ^ 2 * ((101 / 100) ^ 2 * (cot (α / 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left hcot_sq (sq_nonneg _)
    have h2 : 2 * (∑ j, (a j) ^ 2 *
          (Real.sin x / (Real.cos x - Real.cos (θj j))) ^ 2)
        ≤ 2 * (∑ j, (a j) ^ 2 *
          (Real.sin α / (Real.cos α - Real.cos (θj j))) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hcomp_sum (by norm_num)
    have ha0cot : 0 ≤ a0 ^ 2 * (cot (α / 2)) ^ 2 := by positivity
    have hS : 0 ≤ ∑ j, (a j) ^ 2 *
        (Real.sin α / (Real.cos α - Real.cos (θj j))) ^ 2 := by positivity
    nlinarith [h1, h2, htanterm, ha0cot, hS]
  have hA_nonneg : 0 ≤ a0 ^ 2 * (cot (x / 2)) ^ 2 +
        2 * (∑ j, (a j) ^ 2 *
          (Real.sin x / (Real.cos x - Real.cos (θj j))) ^ 2) +
        (Real.tan θ) ^ 2 * (Real.tan (x / 2)) ^ 2 := by positivity
  have hB_nonneg : 0 ≤ a0 ^ 2 * (cot (α / 2)) ^ 2 +
        2 * (∑ j, (a j) ^ 2 *
          (Real.sin α / (Real.cos α - Real.cos (θj j))) ^ 2) := by positivity
  set A := a0 ^ 2 * (cot (x / 2)) ^ 2 +
        2 * (∑ j, (a j) ^ 2 *
          (Real.sin x / (Real.cos x - Real.cos (θj j))) ^ 2) +
        (Real.tan θ) ^ 2 * (Real.tan (x / 2)) ^ 2 with hAdef
  set B := a0 ^ 2 * (cot (α / 2)) ^ 2 +
        2 * (∑ j, (a j) ^ 2 *
          (Real.sin α / (Real.cos α - Real.cos (θj j))) ^ 2) with hBdef
  have hAle' : A ≤ 4 * B := by rw [hAdef, hBdef]; exact hAle
  have hcos2 : 0 ≤ (Real.cos θ) ^ 2 := sq_nonneg _
  have hstep : 4 * (Real.cos θ) ^ 2 * A ≤ 4 * (Real.cos θ) ^ 2 * (4 * B) := by
    nlinarith [hAle', hcos2]
  have hsqrt_le : Real.sqrt (4 * (Real.cos θ) ^ 2 * A) ≤
      Real.sqrt (4 * (Real.cos θ) ^ 2 * (4 * B)) := Real.sqrt_le_sqrt hstep
  have hsqrt_eq : Real.sqrt (4 * (Real.cos θ) ^ 2 * (4 * B)) =
      4 * Real.cos θ * Real.sqrt B := by
    have h16 : 4 * (Real.cos θ) ^ 2 * (4 * B) = 16 * ((Real.cos θ) ^ 2 * B) := by ring
    rw [h16, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 16),
      show Real.sqrt 16 = 4 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
        norm_num,
      Real.sqrt_mul (sq_nonneg (Real.cos θ)), Real.sqrt_sq_eq_abs,
      abs_of_nonneg hcos]
    ring
  rw [hAdef, hBdef]
  calc Real.sqrt (4 * (Real.cos θ) ^ 2 * A)
      ≤ Real.sqrt (4 * (Real.cos θ) ^ 2 * (4 * B)) := hsqrt_le
    _ = 4 * Real.cos θ * Real.sqrt B := hsqrt_eq
    _ ≤ 3 * Real.cos θ * Real.sqrt (4 * B) := by
        have hs : Real.sqrt (4 * B) = 2 * Real.sqrt B := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4),
            show Real.sqrt 4 = 2 by
              rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq_eq_abs]
              norm_num]
        rw [hs]
        have hb : 0 ≤ Real.sqrt B := Real.sqrt_nonneg B
        nlinarith [hcos, hb]

/-- Every summand in a finite sum of nonnegative real numbers is at most the whole sum. -/
theorem single_le_sum_of_nonneg {P : Type*} [Fintype P] (f : P → ℝ) (p0 : P)
    (h : ∀ p, 0 ≤ f p) : f p0 ≤ ∑ p, f p := by
  have hmem := Finset.single_le_sum (s := Finset.univ) (f := f) (fun p _ => h p)
    (Finset.mem_univ p0)
  simpa using hmem

/-- Under the stated positive weights, angle choice, projection bound, and spectral comparisons,
`2 * a0 * cos θ * ∑ p, cot (alphaT p / 2) / Wt p` is at least `(1 - ε) / 90`. This is the
constant-overlap estimate associated with [Magniez et al., Theorem 4.9][MagniezEtAl2008]. -/
theorem theorem_4_9_constant_overlap {P : Type*} [Fintype P]
    (W Wt alphaT : P → ℝ) (p0 : P) (a0 α θ ε : ℝ)
    (ha0 : 0 < a0) (hα0 : 0 < α) (hα4 : α ≤ Real.pi / 4)
    (hW : 0 < W p0) (hWt : 0 < Wt p0)
    (hcos : 0 < Real.cos θ)
    (htan : Real.tan θ = a0 * cot (α / 2) / 10)
    (htle : a0 * cot (α / 2) ≤ 10)
    (hproj : (1 - ε) / 2 ≤ a0 ^ 2 * (cot (α / 2)) ^ 2 / W p0)
    (hWtle : Wt p0 ≤ 9 * (Real.cos θ) ^ 2 * W p0)
    (hcot : cot (α / 2) ≤ cot (alphaT p0 / 2))
    (hpos : ∀ p, 0 ≤ cot (alphaT p / 2) / Wt p) :
    (1 - ε) / 90 ≤ 2 * a0 * Real.cos θ * ∑ p, cot (alphaT p / 2) / Wt p := by
  have hpi := Real.pi_pos
  have hc2pos : 0 < cot (α / 2) :=
    cot_pos_of_pos_of_lt_half_pi (by linarith : 0 < α / 2) (by nlinarith [hα4, hpi])
  have htpos : 0 < a0 * cot (α / 2) := mul_pos ha0 hc2pos
  have hcT : 0 ≤ cot (alphaT p0 / 2) := by
    have h := hpos p0
    have h2 : 0 ≤ cot (alphaT p0 / 2) / Wt p0 * Wt p0 := mul_nonneg h hWt.le
    rwa [div_mul_cancel₀ _ (ne_of_gt hWt)] at h2
  have hproj' : (1 - ε) / 2 ≤ (a0 * cot (α / 2)) ^ 2 / W p0 := by
    have heq : (a0 * cot (α / 2)) ^ 2 / W p0 = a0 ^ 2 * (cot (α / 2)) ^ 2 / W p0 := by
      ring
    rw [heq]
    exact hproj
  have htW : (1 - ε) / 20 ≤ a0 * cot (α / 2) / W p0 := by
    rw [le_div_iff₀ hW]
    have h2 : (1 - ε) / 2 * W p0 ≤ (a0 * cot (α / 2)) ^ 2 :=
      (le_div_iff₀ hW).mp hproj'
    have h3 : 2 * (a0 * cot (α / 2)) ^ 2 ≤ 20 * (a0 * cot (α / 2)) := by
      nlinarith [htle, htpos]
    nlinarith [h2, h3, htpos]
  have hden : 0 < 9 * (Real.cos θ) ^ 2 * W p0 :=
    mul_pos (mul_pos (by norm_num) (pow_pos hcos 2)) hW
  have hfac0 : 0 ≤ 2 * a0 * Real.cos θ := by positivity
  have hnum_nonneg : 0 ≤ 2 * a0 * Real.cos θ * cot (alphaT p0 / 2) :=
    mul_nonneg hfac0 hcT
  have hterm : 2 * a0 * Real.cos θ * cot (α / 2) / (9 * (Real.cos θ) ^ 2 * W p0) ≤
      2 * a0 * Real.cos θ * cot (alphaT p0 / 2) / Wt p0 := by
    have hnum : 2 * a0 * Real.cos θ * cot (α / 2) ≤
        2 * a0 * Real.cos θ * cot (alphaT p0 / 2) :=
      mul_le_mul_of_nonneg_left hcot hfac0
    calc 2 * a0 * Real.cos θ * cot (α / 2) / (9 * (Real.cos θ) ^ 2 * W p0)
        ≤ 2 * a0 * Real.cos θ * cot (alphaT p0 / 2) / (9 * (Real.cos θ) ^ 2 * W p0) :=
          div_le_div_of_nonneg_right hnum hden.le
      _ ≤ 2 * a0 * Real.cos θ * cot (alphaT p0 / 2) / Wt p0 :=
          div_le_div_of_nonneg_left hnum_nonneg hWt hWtle
  have heq : 2 * a0 * Real.cos θ * cot (α / 2) / (9 * (Real.cos θ) ^ 2 * W p0)
      = (2 / 9) * (a0 * cot (α / 2) / W p0) * (1 / Real.cos θ) := by
    field_simp [ne_of_gt hcos, ne_of_gt hW]
  have hcos_inv : 1 ≤ 1 / Real.cos θ := by
    rw [le_div_iff₀ hcos]
    simpa using Real.cos_le_one θ
  have hbase : 0 ≤ (2 / 9) * (a0 * cot (α / 2) / W p0) := by positivity
  have hstep1 : (1 - ε) / 90 ≤ (2 / 9) * ((1 - ε) / 20) := by
    have : (2 / 9) * ((1 - ε) / 20) = (1 - ε) / 90 := by ring
    linarith
  have hstep2 : (2 / 9) * ((1 - ε) / 20) ≤ (2 / 9) * (a0 * cot (α / 2) / W p0) := by
    have hnn : (0 : ℝ) ≤ 2 / 9 := by norm_num
    exact mul_le_mul_of_nonneg_left htW hnn
  have hstep3 : (2 / 9) * (a0 * cot (α / 2) / W p0) ≤
      (2 / 9) * (a0 * cot (α / 2) / W p0) * (1 / Real.cos θ) := by
    nlinarith [hcos_inv, hbase]
  have hmain : (1 - ε) / 90 ≤
      (2 / 9) * (a0 * cot (α / 2) / W p0) * (1 / Real.cos θ) := by
    linarith [hstep1, hstep2, hstep3]
  have hrot : (1 - ε) / 90 ≤ 2 * a0 * Real.cos θ * cot (alphaT p0 / 2) / Wt p0 := by
    rw [heq] at hterm
    linarith [hmain, hterm]
  have hsingle : cot (alphaT p0 / 2) / Wt p0 ≤ ∑ p, cot (alphaT p / 2) / Wt p :=
    single_le_sum_of_nonneg (fun p => cot (alphaT p / 2) / Wt p) p0 hpos
  have hsum_ge : 2 * a0 * Real.cos θ * (cot (alphaT p0 / 2) / Wt p0) ≤
      2 * a0 * Real.cos θ * ∑ p, cot (alphaT p / 2) / Wt p :=
    mul_le_mul_of_nonneg_left hsingle hfac0
  have hrot' : (1 - ε) / 90 ≤
      2 * a0 * Real.cos θ * (cot (alphaT p0 / 2) / Wt p0) := by
    have hmul : 2 * a0 * Real.cos θ * cot (alphaT p0 / 2) / Wt p0 =
        2 * a0 * Real.cos θ * (cot (alphaT p0 / 2) / Wt p0) :=
      mul_div_assoc _ _ _
    rw [hmul] at hrot
    exact hrot
  linarith [hrot', hsum_ge]

/-- If the ideal overlap is at least `(1 - ε) / 90` and the rotation error is bounded by `sqrt
(8 * εrot) < (1 - ε) / 90`, the actual overlap is positive and at least their difference, as
in Corollary 4.10 of [MagniezEtAl2008]. -/
theorem corollary_4_10_constant_overlap {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (target urot u : E) (ε εrot : ℝ)
    (ht : ‖target‖ ≤ 1)
    (hrot : (1 - ε) / 90 ≤ ⟪target, urot⟫_ℝ)
    (hδ : ‖urot - u‖ ≤ Real.sqrt (8 * εrot))
    (hc : Real.sqrt (8 * εrot) < (1 - ε) / 90) :
    (1 - ε) / 90 - Real.sqrt (8 * εrot) ≤ ⟪target, u⟫_ℝ ∧ 0 < ⟪target, u⟫_ℝ :=
  corollary_4_10_overlap target urot u ((1 - ε) / 90) εrot ht hrot hδ hc

end Qatlib.Papers.HittingTimes08.MainResults
