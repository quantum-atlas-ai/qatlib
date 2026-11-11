/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Weighted Error

Harmonic Error constructions for Decision Risk.
Defines `pairWeight`, `decisionError`, `KrausMeasurement`.
Proves `pairWeight_nonneg`, `weighted_cauchy`, `weighted_remainder`.
-/


set_option autoImplicit false

noncomputable section

namespace Qatlib.Foundations.DecisionRisk.HarmonicError

/-- Harmonic pair weight; the zero/zero case is zero in `ℝ`. -/
def pairWeight (a b : ℝ) : ℝ := a * b / (a + b)

/-- The stated finite risk construction satisfies `pairWeight_nonneg` with all displayed hypotheses retained. -/
lemma pairWeight_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    0 ≤ pairWeight a b := div_nonneg (mul_nonneg ha hb) (add_nonneg ha hb)

/-- The stated finite risk construction satisfies `weighted_cauchy` with all displayed hypotheses retained. -/
lemma weighted_cauchy {a b x y : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    pairWeight a b * (x + y)^2 ≤ a*y^2+b*x^2 := by
  by_cases h : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0, hb0, pairWeight]
  · have hp : 0<a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    unfold pairWeight
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hp).2
    nlinarith [sq_nonneg (a*y-b*x)]

/-- Uniform correction bound, valid even when either posterior weight vanishes. -/
lemma weighted_remainder {a b e f : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (he : 0 ≤ e) (hf : 0 ≤ f) :
    4 * pairWeight a b * Real.sqrt e * Real.sqrt f ≤ a*e+b*f := by
  by_cases h : a+b=0
  · have ha0 : a=0 := by linarith
    have hb0 : b=0 := by linarith
    simp [ha0, hb0, pairWeight]
  · have hp : 0<a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm h)
    have heq := Real.sq_sqrt he
    have hfq := Real.sq_sqrt hf
    have h1 : 2 * Real.sqrt e * Real.sqrt f ≤ e+f := by
      nlinarith [sq_nonneg (Real.sqrt e-Real.sqrt f)]
    have h2 : 2*a*b*Real.sqrt e*Real.sqrt f ≤ a^2*e+b^2*f := by
      have hh := sq_nonneg (a*Real.sqrt e-b*Real.sqrt f)
      have hae : a^2 * (Real.sqrt e)^2 = a^2*e := by rw [heq]
      have hbf : b^2 * (Real.sqrt f)^2 = b^2*f := by rw [hfq]
      nlinarith only [hh, hae, hbf]
    have h3 : 2*a*b*Real.sqrt e*Real.sqrt f ≤ a*b*(e+f) := by
      nlinarith [mul_nonneg (mul_nonneg ha hb) (sub_nonneg.mpr h1)]
    unfold pairWeight
    apply (mul_le_mul_iff_of_pos_right hp).mp
    field_simp
    nlinarith

/-- The pairwise overlap estimate with a correction from the third decision. -/
lemma pair_error_bound {a b e f x y t : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (he : 0 ≤ e) (hf : 0 ≤ f)
    (_hx : 0 ≤ x) (_hy : 0 ≤ y) (ht : 0 ≤ t)
    (hov : t ≤ x+y+Real.sqrt e*Real.sqrt f) :
    pairWeight a b*t^2 ≤ a*y^2+b*x^2+t/2*(a*e+b*f) := by
  let r := Real.sqrt e*Real.sqrt f
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hs : t^2 ≤ (x+y)^2+2*t*r := by
    by_cases h : t ≤ r
    · nlinarith [sq_nonneg (x+y), mul_nonneg ht (sub_nonneg.mpr h)]
    · have htr : 0 ≤ t-r := by linarith
      have hxy : 0 ≤ x+y := by linarith
      have hsq : (t-r)^2 ≤ (x+y)^2 :=
        (sq_le_sq₀ htr hxy).2 (by dsimp [r] at *; linarith)
      nlinarith [sq_nonneg r]
  have hw := weighted_cauchy (x := x) (y := y) ha hb
  have hc := weighted_remainder ha hb he hf
  have hs' := mul_le_mul_of_nonneg_left hs (pairWeight_nonneg ha hb)
  have hc' := mul_le_mul_of_nonneg_left hc ht
  dsimp [r] at *
  nlinarith only [hw, hs', hc']

/-- Physical measurement-image overlap estimate. The three summands are the
three final decision sectors, so no restriction to projective measurements is used. -/
lemma decision_overlap {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u₀ u₁ u₂ v₀ v₁ v₂ : H) (hu : ‖u₀‖ ≤ 1) (hv : ‖v₁‖ ≤ 1) :
    ‖inner ℂ u₀ v₀ + inner ℂ u₁ v₁ + inner ℂ u₂ v₂‖ ≤
      ‖v₀‖ + ‖u₁‖ + ‖u₂‖*‖v₂‖ := by
  calc
    _ ≤ ‖inner ℂ u₀ v₀ + inner ℂ u₁ v₁‖ + ‖inner ℂ u₂ v₂‖ := norm_add_le _ _
    _ ≤ (‖inner ℂ u₀ v₀‖ + ‖inner ℂ u₁ v₁‖) + ‖inner ℂ u₂ v₂‖ :=
      add_le_add (norm_add_le _ _) le_rfl
    _ ≤ (‖u₀‖*‖v₀‖+‖u₁‖*‖v₁‖)+‖u₂‖*‖v₂‖ :=
      add_le_add (add_le_add (norm_inner_le_norm _ _) (norm_inner_le_norm _ _))
        (norm_inner_le_norm _ _)
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hu (norm_nonneg v₀),
      mul_le_mul_of_nonneg_left hv (norm_nonneg u₁)]

/-- Pair error bound for actual complex measurement vectors. This consumes the
preserved overlap, not a postulated lower bound on the error probability. -/
lemma decision_pair_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (u₀ u₁ u₂ v₀ v₁ v₂ : H) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : ‖u₀‖ ≤ 1) (hv : ‖v₁‖ ≤ 1) :
    pairWeight a b * ‖inner ℂ u₀ v₀ + inner ℂ u₁ v₁ + inner ℂ u₂ v₂‖^2 ≤
      a*‖u₁‖^2+b*‖v₀‖^2 +
        ‖inner ℂ u₀ v₀ + inner ℂ u₁ v₁ + inner ℂ u₂ v₂‖/2 *
          (a*‖u₂‖^2+b*‖v₂‖^2) := by
  apply pair_error_bound ha hb (sq_nonneg _) (sq_nonneg _)
    (norm_nonneg _) (norm_nonneg _) (norm_nonneg _)
  simpa only [Real.sqrt_sq (norm_nonneg _)] using decision_overlap u₀ u₁ u₂ v₀ v₁ v₂ hu hv

/-- Total weighted misclassification mass of three decision sectors. -/
def decisionError {H : Type*} [NormedAddCommGroup H]
    (v : Fin 3 → Fin 3 → H) (q : Fin 3 → ℝ) : ℝ :=
  q 0*(‖v 1 0‖^2+‖v 2 0‖^2) + q 1*(‖v 0 1‖^2+‖v 2 1‖^2) +
    q 2*(‖v 0 2‖^2+‖v 1 2‖^2)

/-- Three-sector physical overlap bound. Each column is the image of one state
under a measurement dilation. The hypotheses fix its preserved Gram data and
correct-decision norms; they do not postulate any error lower bound. -/
theorem three_decision_error {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (v : Fin 3 → Fin 3 → H) (q : Fin 3 → ℝ) {t : ℝ}
    (hq : ∀ i, 0 ≤ q i) (ht : 0 ≤ t)
    (hc : ∀ i, ‖v i i‖ ≤ 1)
    (h01 : ‖inner ℂ (v 0 0) (v 0 1) + inner ℂ (v 1 0) (v 1 1) +
      inner ℂ (v 2 0) (v 2 1)‖ = t)
    (h02 : ‖inner ℂ (v 0 0) (v 0 2) + inner ℂ (v 2 0) (v 2 2) +
      inner ℂ (v 1 0) (v 1 2)‖ = t)
    (h12 : ‖inner ℂ (v 1 1) (v 1 2) + inner ℂ (v 2 1) (v 2 2) +
      inner ℂ (v 0 1) (v 0 2)‖ = t) :
    t^2 * (pairWeight (q 0) (q 1) + pairWeight (q 0) (q 2) +
      pairWeight (q 1) (q 2)) ≤ (1+t)*decisionError v q := by
  have p01 := decision_pair_error (v 0 0) (v 1 0) (v 2 0)
    (v 0 1) (v 1 1) (v 2 1) (hq 0) (hq 1) (hc 0) (hc 1)
  have p02 := decision_pair_error (v 0 0) (v 2 0) (v 1 0)
    (v 0 2) (v 2 2) (v 1 2) (hq 0) (hq 2) (hc 0) (hc 2)
  have p12 := decision_pair_error (v 1 1) (v 2 1) (v 0 1)
    (v 1 2) (v 2 2) (v 0 2) (hq 1) (hq 2) (hc 1) (hc 2)
  rw [h01] at p01
  rw [h02] at p02
  rw [h12] at p12
  have he : 0 ≤ decisionError v q := by
    have h0 := hq 0
    have h1 := hq 1
    have h2 := hq 2
    unfold decisionError
    positivity
  have hte := mul_nonneg ht he
  unfold decisionError at *
  nlinarith only [p01, p02, p12, hte]

/-- Three-decision Kraus instrument. Completeness is specified on all input
vectors; it preserves both total Born mass and the input Gram inner product. -/
structure KrausMeasurement (H K : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K] where
  op : Fin 3 → H →ₗ[ℂ] K
  mass_complete : ∀ x, ∑ k, ‖op k x‖^2 = ‖x‖^2
  gram_complete : ∀ x y, ∑ k, inner ℂ (op k x) (op k y) = inner ℂ x y

/-- Physical instrument consumer of the three-decision error bound. -/
theorem kraus_error_bound {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    (M : KrausMeasurement H K) (ψ : Fin 3 → H) (q : Fin 3 → ℝ) {t : ℝ}
    (hq : ∀ i, 0 ≤ q i) (ht : 0 ≤ t) (hn : ∀ i, ‖ψ i‖ = 1)
    (ho : ∀ i j, i ≠ j → ‖inner ℂ (ψ i) (ψ j)‖ = t) :
    t^2*(pairWeight (q 0) (q 1)+pairWeight (q 0) (q 2)+pairWeight (q 1) (q 2)) ≤
      (1+t)*decisionError (fun k i => M.op k (ψ i)) q := by
  apply three_decision_error _ q hq ht
  · intro i
    have hm := M.mass_complete (ψ i)
    rw [hn i] at hm
    have hs : ‖M.op i (ψ i)‖^2 ≤ ∑ k, ‖M.op k (ψ i)‖^2 :=
      Finset.single_le_sum (f := fun k : Fin 3 => ‖M.op k (ψ i)‖^2)
        (fun k _ => sq_nonneg ‖M.op k (ψ i)‖) (Finset.mem_univ i)
    nlinarith [norm_nonneg (M.op i (ψ i))]
  · simpa only [Fin.sum_univ_three] using
      (congrArg norm (M.gram_complete (ψ 0) (ψ 1))).trans (ho 0 1 (by decide))
  · have hg := (congrArg norm (M.gram_complete (ψ 0) (ψ 2))).trans (ho 0 2 (by decide))
    simpa only [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using hg
  · have hg := (congrArg norm (M.gram_complete (ψ 1) (ψ 2))).trans (ho 1 2 (by decide))
    simpa only [Fin.sum_univ_three, add_comm, add_left_comm, add_assoc] using hg

end Qatlib.Foundations.DecisionRisk.HarmonicError
