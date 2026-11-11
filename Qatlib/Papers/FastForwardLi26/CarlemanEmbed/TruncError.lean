/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Qatlib.Papers.FastForwardLi26.CarlemanEmbed.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.3: truncation error of the Carleman embedding

Paper: FastForwardLi26 (Yixiang Li, Dong An), *Fast-forwarding quantum
algorithms for weakly nonlinear dissipative differential equations and
beyond*, arXiv:2608.25822v1 (fixed source version).

Source: Lemma 3.3, p. 6 (extracted-text lines 165–169); proof in Appendix A,
p. 23.

The source proves, via Duhamel's principle applied to the error equation
Eq. (7) and Lemmas 3.1–3.2,
`‖η(t)‖ ≤ (2NR/(1-R)) (2R/(1+R))^N`.

The file proves

* `lemma33_gamma_mu_lower`, the Eq. (8) consequence
  `2‖F₂‖/(1+R) ≤ -γ μ(F₁)` used in the final arithmetic (Appendix A, Eq. (14));
* `lemma33_rate`, the final scalar chain of the source proof;
* `lemma33_carleman_error`, the Duhamel integral bound of Lemma 3.3, proved
  by evaluating the exponential interval integral and applying `lemma33_rate`.
-/

open MeasureTheory
open scoped Interval

namespace Qatlib.Papers.FastForwardLi26.CarlemanEmbed.TruncError

open Qatlib.Papers.FastForwardLi26.CarlemanEmbed.SourceModel

/-- **Eq. (8) consequence** `2‖F₂‖/(1+R) ≤ -γ μ(F₁)`: rewriting Eq. (8)
as `((1+R)/2) b = a/γ + cγ` (Eq. (14)) gives `γ b = 2(a + cγ²)/(1+R)`, so
`γ b ≥ 2a/(1+R)` because `cγ² ≥ 0`.  Here `a = ‖F₂‖`, `b = -μ(F₁)`,
`c = ‖F₀‖`. -/
theorem lemma33_gamma_mu_lower (p : CarlemanParams) (hp : p.Valid) :
    2 * p.a / (1 + p.R) ≤ -p.γ * p.muF1 := by
  have hres := p.rescale_mul_gamma hp
  have hone : 0 < 1 + p.R := by
    have := p.R_pos hp
    linarith
  have hγ := hp.gamma_pos
  have hc := hp.c_nonneg
  have hcγ : 0 ≤ p.c * p.γ ^ 2 := mul_nonneg hc (sq_nonneg p.γ)
  unfold CarlemanParams.muF1
  rw [div_le_iff₀ hone]
  nlinarith [hres, hcγ, hγ]

/-- **Lemma 3.3, final arithmetic step** (Appendix A, p. 23): the Duhamel
contraction bound
`2N‖F₂‖ / (-(1-R)γ μ(F₁)) · (2R/(1+R))^(N+1)`
is at most `(2NR/(1-R)) (2R/(1+R))^N`.  This is the last displayed inequality
in the proof of Lemma 3.3, using `-γ μ(F₁) ≥ 2‖F₂‖/(1+R)`. -/
theorem lemma33_rate (p : CarlemanParams) (hp : p.Valid) (N : ℕ) (hN : 1 ≤ N) :
    2 * (N : ℝ) * p.a / ((1 - p.R) * (-p.γ * p.muF1)) *
        (2 * p.R / (1 + p.R)) ^ (N + 1) ≤
      2 * (N : ℝ) * p.R / (1 - p.R) * (2 * p.R / (1 + p.R)) ^ N :=
  p.truncError_rate hp N hN (lemma33_gamma_mu_lower p hp)

/-- **Lemma 3.3** (arXiv:2608.25822v1, Lemma 3.3, p. 6; proof Appendix A,
p. 23).

Duhamel's principle for the error equation Eq. (7) gives
`η(t) = ∫₀ᵗ T exp(∫_s^t A(τ)dτ) ζ(s) ds` with
`‖ζ(s)‖ ≤ N ‖F₂‖/γ · ‖u_γ(s)‖^{N+1}`.  Lemmas 3.1–3.2 give the exponential
decay factor `e^{(1-R)μ(F₁)(t-s)/2}` and the bound
`‖u_γ(s)‖ ≤ 2R/(1+R)`, hence the stated estimate.

The hypothesis `hduhamel` is the Duhamel representation together with the
contraction estimate (the paper's displayed integral inequality); the
conclusion is the pointwise bound of Lemma 3.3.

Proof: evaluate `∫₀ᵗ e^{c(t-s)} ds = (e^{ct}-1)/c` with
`intervalIntegral.integral_comp_sub_left` and the fundamental theorem of
calculus, bound it by `1/|c|` using `e^{ct} ≤ 1`, and close the scalar
comparison with `lemma33_rate`; `hduhamel` supplies the Duhamel input. -/
theorem lemma33_carleman_error
    (p : CarlemanParams) (hp : p.Valid) (N : ℕ) (hN : 1 ≤ N) (η : ℝ → ℝ)
    (hduhamel : ∀ t, 0 ≤ t →
      |η t| ≤ ∫ s in (0 : ℝ)..t,
        Real.exp (((1 - p.R) * p.muF1 / 2) * (t - s)) *
          ((N : ℝ) * (p.a / p.γ) * (2 * p.R / (1 + p.R)) ^ (N + 1))) :
    ∀ t, 0 ≤ t →
      |η t| ≤ 2 * (N : ℝ) * p.R / (1 - p.R) * (2 * p.R / (1 + p.R)) ^ N := by
  intro t ht
  set c : ℝ := (1 - p.R) * p.muF1 / 2 with hc
  have hcneg : c < 0 := by
    have hR : 0 < 1 - p.R := p.one_sub_R_pos hp
    have hmu : p.muF1 < 0 := by
      unfold CarlemanParams.muF1
      linarith [hp.b_pos]
    rw [hc]
    nlinarith
  set K : ℝ := (N : ℝ) * (p.a / p.γ) * (2 * p.R / (1 + p.R)) ^ (N + 1) with hK
  have hKnonneg : 0 ≤ K := by
    rw [hK]
    have ha : 0 ≤ p.a := hp.a_nonneg
    have hg : 0 < p.γ := hp.gamma_pos
    have hRpos := p.R_pos hp
    have hbase : 0 ≤ 2 * p.R / (1 + p.R) := by positivity
    positivity
  have hInt : (∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)))
      = (Real.exp (c * t) - 1) / c := by
    rw [intervalIntegral.integral_comp_sub_left (f := fun u : ℝ => Real.exp (c * u))
      (a := 0) (b := t) (d := t)]
    simp only [sub_self, sub_zero]
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun u : ℝ => Real.exp (c * u) / c)
      (f' := fun u : ℝ => Real.exp (c * u))]
    · simp only [div_sub_div_same]
      simp
    · intro x _
      have hd : HasDerivAt (fun u : ℝ => Real.exp (c * u)) (Real.exp (c * x) * c) x := by
        convert! (Real.hasDerivAt_exp (c * x)).comp x ((hasDerivAt_id x).const_mul c) using 1 <;> simp
      convert! hd.div_const c using 1
      rw [mul_div_cancel_right₀ _ (ne_of_lt hcneg)]
    · exact (by fun_prop : Continuous fun u : ℝ => Real.exp (c * u)).intervalIntegrable _ _
  have hstep : |η t| ≤ K * ((Real.exp (c * t) - 1) / c) := by
    calc |η t| ≤ ∫ s in (0 : ℝ)..t,
          Real.exp (((1 - p.R) * p.muF1 / 2) * (t - s)) *
            ((N : ℝ) * (p.a / p.γ) * (2 * p.R / (1 + p.R)) ^ (N + 1)) :=
          hduhamel t ht
      _ = ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) * K := by
          simp only [hc, hK]
      _ = K * ∫ s in (0 : ℝ)..t, Real.exp (c * (t - s)) := by
          rw [intervalIntegral.integral_mul_const, mul_comm]
      _ = K * ((Real.exp (c * t) - 1) / c) := by rw [hInt]
  have hexp : Real.exp (c * t) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hbound : (Real.exp (c * t) - 1) / c ≤ 1 / (-c) := by
    have hcpos : 0 < -c := by linarith
    rw [show (Real.exp (c * t) - 1) / c = (1 - Real.exp (c * t)) / (-c) by
      field_simp
      ring]
    apply div_le_div_of_nonneg_right _ (le_of_lt hcpos)
    linarith [Real.exp_pos (c * t)]
  have hKbound : K * ((Real.exp (c * t) - 1) / c) ≤ K * (1 / (-c)) := by
    exact mul_le_mul_of_nonneg_left hbound hKnonneg
  have heq : K * (1 / (-c)) =
      2 * (N : ℝ) * p.a / ((1 - p.R) * (-p.γ * p.muF1)) *
        (2 * p.R / (1 + p.R)) ^ (N + 1) := by
    rw [hK, hc]
    field_simp
  calc |η t| ≤ K * ((Real.exp (c * t) - 1) / c) := hstep
    _ ≤ K * (1 / (-c)) := hKbound
    _ = 2 * (N : ℝ) * p.a / ((1 - p.R) * (-p.γ * p.muF1)) *
          (2 * p.R / (1 + p.R)) ^ (N + 1) := heq
    _ ≤ 2 * (N : ℝ) * p.R / (1 - p.R) * (2 * p.R / (1 + p.R)) ^ N :=
        lemma33_rate p hp N hN

end Qatlib.Papers.FastForwardLi26.CarlemanEmbed.TruncError
