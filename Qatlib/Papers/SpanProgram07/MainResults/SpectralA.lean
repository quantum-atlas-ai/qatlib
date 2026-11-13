/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgram07.MainResults.WitnessSize
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Scalar estimates for span-program spectral analysis

This module bounds changes in positive and negative witness sizes when their weights are scaled
or perturbed by squares. It also supplies scalar inverse identities, nonvanishing denominators,
and constrained minimization formulas for the spectral analysis in [ReichardtSpalek2008].

## Main statements

* `WsizeTrueAt.le_add_sq`: If old weights are at least positive `σ` and perturbations have
  magnitude at most `τ`, adding their squares increases the exact positive witness size to at
  most `c + (τ²/σ)*c`.
* `WsizeFalseAt.le_add_sq`: If old weights are at least positive `σ` and perturbations have
  magnitude at most `τ`, adding their squares increases the exact negative witness size to at
  most `c + (τ²/σ)*c`.

## References

* [Reichardt and Spalek, 2008][ReichardtSpalek2008]
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpanProgram07.MainResults

open Finset SpanProgram
open scoped BigOperators

variable {n : ℕ} {J C I : Type}

namespace SpanProgram

/-- If each new weight is at most `k` times the old weight, the new weighted squared norm is at
most `k` times the old one. See [ReichardtSpalek2008]. -/
theorem wt_le_mul [Fintype J] {z z' : J → ℝ} {k : ℝ} (_hk : 0 ≤ k)
    (hz : ∀ j, z' j ≤ k * z j) (w : J → ℂ) : wt z' w ≤ k * wt z w := by
  rw [wt, wt, Finset.mul_sum]
  refine sum_le_sum fun j _ => ?_
  have h := mul_le_mul_of_nonneg_right (hz j) (sq_nonneg (‖w j‖))
  simpa [mul_assoc] using h

/-- Under the pointwise weight bound `z' ≤ k*z`, exact positive witness sizes satisfy `c' ≤
k*c`. See [ReichardtSpalek2008]. -/
theorem WsizeTrueAt.le_mul [Fintype J] {P : SpanProgram n J C I} {z z' : J → ℝ}
    {S : Finset J} {c c' k : ℝ} (_hk : 0 ≤ k) (hz : ∀ j, z' j ≤ k * z j)
    (h : P.WsizeTrueAt z S c) (h' : P.WsizeTrueAt z' S c') : c' ≤ k * c := by
  obtain ⟨w, hsupp, hsum, hval⟩ := h.2
  calc c' ≤ wt z' w := h'.1 w hsupp hsum
    _ ≤ k * wt z w := wt_le_mul _hk hz w
    _ = k * c := by rw [hval]

/-- Under the pointwise weight bound `z' ≤ k*z`, exact negative witness sizes satisfy `c' ≤
k*c`. See [ReichardtSpalek2008]. -/
theorem WsizeFalseAt.le_mul [Fintype J] [Fintype C] {P : SpanProgram n J C I} {z z' : J → ℝ}
    {S : Finset J} {c c' k : ℝ} (_hk : 0 ≤ k) (hz : ∀ j, z' j ≤ k * z j)
    (h : P.WsizeFalseAt z S c) (h' : P.WsizeFalseAt z' S c') : c' ≤ k * c := by
  obtain ⟨b, hb, horth, hval⟩ := h.2
  have hlow : c' ≤ ∑ j, z' j * ‖P.pair b j‖ ^ 2 := h'.1 b hb horth
  have hsum : ∑ j, z' j * ‖P.pair b j‖ ^ 2 ≤ k * ∑ j, z j * ‖P.pair b j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine sum_le_sum fun j _ => ?_
    have hj := mul_le_mul_of_nonneg_right (hz j) (sq_nonneg (‖P.pair b j‖))
    simpa [mul_assoc] using hj
  calc c' ≤ ∑ j, z' j * ‖P.pair b j‖ ^ 2 := hlow
    _ ≤ k * ∑ j, z j * ‖P.pair b j‖ ^ 2 := hsum
    _ = k * c := by rw [hval]

/-- Adding the squared perturbations `t j²` to the weights adds the corresponding weighted
coordinate-norm sum to `wt`. See [ReichardtSpalek2008]. -/
theorem wt_add_sq [Fintype J] (z t : J → ℝ) (w : J → ℂ) :
    wt (fun j => z j + t j ^ 2) w = wt z w + ∑ j, t j ^ 2 * ‖w j‖ ^ 2 := by
  rw [wt, wt, ← Finset.sum_add_distrib]
  exact sum_congr rfl fun j _ => by ring

/-- If old weights are at least positive `σ` and perturbations have magnitude at most `τ`,
adding their squares increases the exact positive witness size to at most `c + (τ²/σ)*c`.
See [ReichardtSpalek2008]. -/
theorem WsizeTrueAt.le_add_sq [Fintype J] {P : SpanProgram n J C I} {z z' t : J → ℝ}
    {S : Finset J} {c c' σ τ : ℝ} (hσ : 0 < σ) (hzσ : ∀ j, σ ≤ z j)
    (_hτ : 0 ≤ τ) (ht : ∀ j, |t j| ≤ τ) (hzt : ∀ j, z' j = z j + t j ^ 2)
    (h : P.WsizeTrueAt z S c) (h' : P.WsizeTrueAt z' S c') :
    c' ≤ c + (τ ^ 2 / σ) * c := by
  obtain ⟨w, hsupp, hsum, hval⟩ := h.2
  have hlow : c' ≤ wt z' w := h'.1 w hsupp hsum
  have hz'eq : z' = fun j => z j + t j ^ 2 := funext hzt
  have hextra : ∑ j, t j ^ 2 * ‖w j‖ ^ 2 ≤ (τ ^ 2 / σ) * wt z w := by
    rw [wt, Finset.mul_sum]
    refine sum_le_sum fun j _ => ?_
    have ht2 : t j ^ 2 ≤ τ ^ 2 := by
      have hab := abs_le.mp (ht j)
      nlinarith [hab.1, hab.2]
    have hk : 0 ≤ τ ^ 2 / σ := div_nonneg (sq_nonneg τ) (le_of_lt hσ)
    have hmul : (τ ^ 2 / σ) * σ = τ ^ 2 := by field_simp
    have hcoef : t j ^ 2 ≤ (τ ^ 2 / σ) * z j := by
      nlinarith [mul_le_mul_of_nonneg_left (hzσ j) hk]
    have := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (‖w j‖))
    simpa [mul_assoc] using this
  calc c' ≤ wt z' w := hlow
    _ = wt (fun j => z j + t j ^ 2) w := by rw [hz'eq]
    _ = wt z w + ∑ j, t j ^ 2 * ‖w j‖ ^ 2 := wt_add_sq z t w
    _ ≤ wt z w + (τ ^ 2 / σ) * wt z w := by linarith
    _ = c + (τ ^ 2 / σ) * c := by rw [hval]

/-- If old weights are at least positive `σ` and perturbations have magnitude at most `τ`,
adding their squares increases the exact negative witness size to at most `c + (τ²/σ)*c`.
See [ReichardtSpalek2008]. -/
theorem WsizeFalseAt.le_add_sq [Fintype J] [Fintype C] {P : SpanProgram n J C I} {z z' t : J → ℝ}
    {S : Finset J} {c c' σ τ : ℝ} (hσ : 0 < σ) (hzσ : ∀ j, σ ≤ z j)
    (_hτ : 0 ≤ τ) (ht : ∀ j, |t j| ≤ τ) (hzt : ∀ j, z' j = z j + t j ^ 2)
    (h : P.WsizeFalseAt z S c) (h' : P.WsizeFalseAt z' S c') :
    c' ≤ c + (τ ^ 2 / σ) * c := by
  obtain ⟨b, hb, horth, hval⟩ := h.2
  have hlow : c' ≤ ∑ j, z' j * ‖P.pair b j‖ ^ 2 := h'.1 b hb horth
  have hextra : ∑ j, t j ^ 2 * ‖P.pair b j‖ ^ 2
      ≤ (τ ^ 2 / σ) * ∑ j, z j * ‖P.pair b j‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine sum_le_sum fun j _ => ?_
    have ht2 : t j ^ 2 ≤ τ ^ 2 := by
      have hab := abs_le.mp (ht j)
      nlinarith [hab.1, hab.2]
    have hk : 0 ≤ τ ^ 2 / σ := div_nonneg (sq_nonneg τ) (le_of_lt hσ)
    have hmul : (τ ^ 2 / σ) * σ = τ ^ 2 := by field_simp
    have hcoef : t j ^ 2 ≤ (τ ^ 2 / σ) * z j := by
      nlinarith [mul_le_mul_of_nonneg_left (hzσ j) hk]
    have hj := mul_le_mul_of_nonneg_right hcoef (sq_nonneg (‖P.pair b j‖))
    simpa [mul_assoc] using hj
  have hsplit : ∑ j, z' j * ‖P.pair b j‖ ^ 2
      = ∑ j, z j * ‖P.pair b j‖ ^ 2 + ∑ j, t j ^ 2 * ‖P.pair b j‖ ^ 2 := by
    rw [← Finset.sum_add_distrib]
    exact sum_congr rfl fun j _ => by rw [hzt j]; ring
  rw [hsplit] at hlow
  calc c' ≤ ∑ j, z j * ‖P.pair b j‖ ^ 2 + ∑ j, t j ^ 2 * ‖P.pair b j‖ ^ 2 := hlow
    _ ≤ ∑ j, z j * ‖P.pair b j‖ ^ 2
        + (τ ^ 2 / σ) * ∑ j, z j * ‖P.pair b j‖ ^ 2 := by linarith
    _ = c + (τ ^ 2 / σ) * c := by rw [hval]

end SpanProgram

/-- For nonzero `r` and `1 + r*b`, express `(r⁻¹ + b)⁻¹` by the scalar Woodbury identity. See
[ReichardtSpalek2008]. -/
theorem woodbury_scalar {r b : ℝ} (hr : r ≠ 0) (h : 1 + r * b ≠ 0) :
    (r⁻¹ + b)⁻¹ = r - r * b * (1 + r * b)⁻¹ * r := by
  have hne : r⁻¹ + b ≠ 0 := by
    have hrewrite : r⁻¹ + b = (1 + r * b) / r := by
      field_simp
    rw [hrewrite]
    exact div_ne_zero h hr
  field_simp [hne]
  ring

/-- For positive `lam` and nonnegative `r`, the scalar `1 + (1/lam)*c*r*c` is positive. See
[ReichardtSpalek2008]. -/
theorem one_add_sq_mul_pos {lam c r : ℝ} (hlam : 0 < lam) (hr : 0 ≤ r) :
    0 < 1 + (1 / lam) * c * r * c := by
  have hlam' : 0 < 1 / lam := by positivity
  have hcc : 0 ≤ c * c := mul_self_nonneg c
  have hterm : 0 ≤ (1 / lam) * c * r * c := by
    have := mul_nonneg (mul_nonneg (le_of_lt hlam') hcc) hr
    nlinarith [this]
  linarith

/-- For positive `lam` and `s` with `c² < lam²*s`, the specified scalar inverse-update
denominator is nonzero. See [ReichardtSpalek2008]. -/
theorem one_add_neg_inv_ne_zero {lam s c : ℝ} (hlam : 0 < lam) (hs : 0 < s)
    (hc : c ^ 2 < lam ^ 2 * s) :
    1 + (1 / lam) * c * (-(1 / (lam * s))) * c ≠ 0 := by
  have hlamne : lam ≠ 0 := ne_of_gt hlam
  have hprod : lam * s ≠ 0 := ne_of_gt (mul_pos hlam hs)
  intro hzero
  have hsq : c ^ 2 = lam ^ 2 * s := by
    field_simp at hzero
    linarith
  linarith

/-- For positive `lam` and `s`, the expression `a² / (-(1/(lam*s))) - lam` is nonzero. See
[ReichardtSpalek2008]. -/
theorem tilde_inv_ne_zero {lam s a : ℝ} (hlam : 0 < lam) (hs : 0 < s) :
    a ^ 2 / (-(1 / (lam * s))) - lam ≠ 0 := by
  have hprod : lam * s ≠ 0 := ne_of_gt (mul_pos hlam hs)
  have hval : a ^ 2 / (-(1 / (lam * s))) - lam = -(lam * (a ^ 2 * s + 1)) := by
    field_simp
    ring
  rw [hval]
  have hpos : 0 < lam * (a ^ 2 * s + 1) := by
    have : 0 ≤ a ^ 2 * s := mul_nonneg (sq_nonneg a) (le_of_lt hs)
    nlinarith
  exact ne_of_lt (neg_neg_of_pos hpos)

/-- For nonzero `a`, the feasible value `w = t/a` minimizes `w²` subject to `a*w = t`. See
[ReichardtSpalek2008]. -/
theorem scalar_primal_min (a t : ℝ) (ha : a ≠ 0) :
    (∀ w : ℝ, a * w = t → (t / a) ^ 2 ≤ w ^ 2) ∧ a * (t / a) = t := by
  constructor
  · intro w hw
    have hw' : w = t / a := by
      field_simp
      linarith
    rw [hw']
  · field_simp

/-- For nonzero `t`, the feasible value `w = 1/t` attains the lower bound `(a/t)²` for `(a*w)²`
subject to `t*w = 1`. See [ReichardtSpalek2008]. -/
theorem scalar_dual_min (a t : ℝ) (ht : t ≠ 0) :
    (∀ w : ℝ, t * w = 1 → (a / t) ^ 2 ≤ (a * w) ^ 2) ∧ t * (1 / t) = 1 := by
  constructor
  · intro w hw
    have hw' : w = 1 / t := by
      field_simp
      linarith
    rw [hw']
    have : a * (1 / t) = a / t := by ring
    rw [this]
  · field_simp

end Qatlib.Papers.SpanProgram07.MainResults
