/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DenseOutSim26.FreeTruncation.Core.DenseOutput

/-!
# Dense output with a Lindbladian gap (arXiv:2609.40094v1, p.22-23)

Theorem 10 bounds the truncation error of the dense output for a local
Lindbladian `L = Σ_X L_X` with interaction strength `λ`, range `d*`, unique
stationary state `π`, spectral gap `Δ > 0`, and Jordan basis with
`‖S‖ = ‖S⁻¹‖`:

`|J_H(O) − J_{H_R}(O)| ≤ C λ_∂ ‖S‖² e^{−(R−d*)} F(μ,T)`,  `μ = Δ − v_LR`,
                                                             (80)

where `F(μ,T) = ∫₀^T (T−s) e^{−μ s} ds` (Eq. (79), `lindbladF` in
`Core/DenseOutput.lean`).  This file evaluates `F` in closed form and proves the
three asymptotic regimes of the paper:

* no gap (`Δ = 0`, `μ = −v_LR < 0`): `F = (1/v_LR²)(e^{v_LR T} − 1 − v_LR T)`,
  bounded by `(1/v_LR²) e^{v_LR T}`; a radius `R = d* + v_LR T + log(C/(ε v_LR²))`
  suffices;
* weak gap (`0 < Δ < v_LR`, `μ < 0`): `F ≤ (1/μ²) e^{−μT}`, and the radius
  `R = d* + (v_LR − Δ)T + log(C/(ε (v_LR − Δ)²))` suffices;
* strong gap (`Δ > v_LR`, `μ > 0`): `F ≤ T/μ`, and the radius
  `R = d* + log(C T/(ε μ))` suffices.

The paper's Lieb-Robinson-based estimate (80) is an external input; the content
proved here is the evaluation of `F` and the radius algebra that follows from it.
-/

namespace Qatlib.Papers.DenseOutSim26.FreeTruncation.Lindblad

open MeasureTheory intervalIntegral
open Qatlib.Papers.DenseOutSim26.FreeTruncation.Core

set_option autoImplicit false

/-- `F(μ,T)` is nonnegative for `T ≥ 0`: the integrand `(T−s)e^{−μs}` is
nonnegative on `[0,T]`. -/
theorem lindbladF_nonneg {μ T : ℝ} (hT : 0 ≤ T) : 0 ≤ lindbladF μ T := by
  unfold lindbladF
  exact integral_nonneg hT (fun s hs => mul_nonneg (by linarith [hs.2]) (Real.exp_pos _).le)

/-- The derivative `d/ds e^{−μs} = −μ e^{−μs}`. -/
private theorem hasDerivAt_exp_neg_mul (μ s : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-μ * x)) (Real.exp (-μ * s) * (-μ)) s := by
  have h1 : HasDerivAt (fun x : ℝ => -μ * x) (-μ) s := by
    simpa using (hasDerivAt_id s).const_mul (-μ)
  simpa using h1.exp

/-- `∫₀^T e^{−μs} ds = (1 − e^{−μT})/μ` for `μ ≠ 0`. -/
theorem integral_exp_neg_mul {μ T : ℝ} (hμ : μ ≠ 0) :
    ∫ s in (0 : ℝ)..T, Real.exp (-μ * s) = (1 - Real.exp (-μ * T)) / μ := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun x : ℝ => -(1 / μ) * Real.exp (-μ * x)) (Real.exp (-μ * s)) s := by
    intro s _
    have h3 := (hasDerivAt_exp_neg_mul μ s).const_mul (-(1 / μ))
    rw [show -(1 / μ) * (Real.exp (-μ * s) * -μ) = Real.exp (-μ * s) by
      field_simp] at h3
    exact h3
  have hint : IntervalIntegrable (fun s : ℝ => Real.exp (-μ * s)) volume (0 : ℝ) T := by
    have hcont : Continuous (fun s : ℝ => Real.exp (-μ * s)) := by fun_prop
    exact hcont.intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, Real.exp_zero]
  field_simp
  ring

/-- `∫₀^T s e^{−μs} ds = −T e^{−μT}/μ − e^{−μT}/μ² + 1/μ²` for `μ ≠ 0`. -/
theorem integral_mul_exp_neg_mul {μ T : ℝ} (hμ : μ ≠ 0) :
    ∫ s in (0 : ℝ)..T, s * Real.exp (-μ * s) =
      -(T * Real.exp (-μ * T)) / μ - Real.exp (-μ * T) / μ ^ 2 + 1 / μ ^ 2 := by
  have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) T,
      HasDerivAt (fun x : ℝ => -(x / μ) * Real.exp (-μ * x) + -(1 / μ ^ 2) * Real.exp (-μ * x))
        (s * Real.exp (-μ * s)) s := by
    intro s _
    have hx : HasDerivAt (fun x : ℝ => -(x / μ)) (-(1 / μ)) s := by
      convert ((hasDerivAt_id s).div_const μ).neg using 1 <;> simp <;> rfl
    have h2 := hasDerivAt_exp_neg_mul μ s
    have h4 := hx.mul h2
    have h5 := h2.const_mul (-(1 / μ ^ 2))
    have h6 := h4.add h5
    rw [show -(1 / μ) * Real.exp (-μ * s) + -(s / μ) * (Real.exp (-μ * s) * -μ)
          + -(1 / μ ^ 2) * (Real.exp (-μ * s) * -μ) = s * Real.exp (-μ * s) by
        field_simp
        ring] at h6
    exact h6
  have hint : IntervalIntegrable (fun s : ℝ => s * Real.exp (-μ * s)) volume (0 : ℝ) T := by
    have hcont : Continuous (fun s : ℝ => s * Real.exp (-μ * s)) := by fun_prop
    exact hcont.intervalIntegrable _ _
  rw [integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [mul_zero, neg_zero, Real.exp_zero, zero_div]
  field_simp
  ring

/-- **Theorem 10, Eq. (79), closed form**: `F(μ,T) = T/μ − (1 − e^{−μT})/μ²`
for `μ ≠ 0`. -/
theorem lindbladF_eq {μ T : ℝ} (hμ : μ ≠ 0) :
    lindbladF μ T = T / μ - (1 - Real.exp (-μ * T)) / μ ^ 2 := by
  unfold lindbladF
  have hfun : (fun s : ℝ => (T - s) * Real.exp (-μ * s))
      = fun s : ℝ => T * Real.exp (-μ * s) - s * Real.exp (-μ * s) := by
    funext s; ring
  rw [hfun]
  have h1 : IntervalIntegrable (fun s : ℝ => T * Real.exp (-μ * s)) volume (0 : ℝ) T := by
    have hcont : Continuous (fun s : ℝ => T * Real.exp (-μ * s)) := by fun_prop
    exact hcont.intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s : ℝ => s * Real.exp (-μ * s)) volume (0 : ℝ) T := by
    have hcont : Continuous (fun s : ℝ => s * Real.exp (-μ * s)) := by fun_prop
    exact hcont.intervalIntegrable _ _
  rw [intervalIntegral.integral_sub h1 h2]
  rw [intervalIntegral.integral_const_mul, integral_exp_neg_mul hμ,
    integral_mul_exp_neg_mul hμ]
  field_simp
  ring

/-- The no-gap shape `F(μ,T)` with `μ = −v_LR`: `(1/v_LR²)(e^{v_LR T} − 1 − v_LR T)`. -/
noncomputable def lindbladFNoGap (vLR T : ℝ) : ℝ :=
  (1 / vLR ^ 2) * (Real.exp (vLR * T) - 1 - vLR * T)

/-- **Theorem 10, regime 1 (no gap)**: with `μ = −v_LR`, `F` is the exponential
expression `lindbladFNoGap`. -/
theorem theorem10_no_gap_F {vLR T : ℝ} (hv : vLR ≠ 0) :
    lindbladF (-vLR) T = lindbladFNoGap vLR T := by
  rw [lindbladF_eq (neg_ne_zero.mpr hv)]
  unfold lindbladFNoGap
  field_simp
  ring

/-- **Theorem 10, regime 1 (no gap), growth**: `F(−v,T) ≤ (1/v²) e^{vT}` for
`v > 0`, `T ≥ 0`, since `1 + vT ≥ 0`. -/
theorem lindbladF_noGap_le_exp {v T : ℝ} (hv : 0 < v) (hT : 0 ≤ T) :
    lindbladF (-v) T ≤ (1 / v ^ 2) * Real.exp (v * T) := by
  rw [theorem10_no_gap_F (ne_of_gt hv)]
  unfold lindbladFNoGap
  have h1 : 0 ≤ 1 + v * T := by nlinarith [mul_nonneg hv.le hT]
  have hcoef : 0 ≤ 1 / v ^ 2 := by positivity
  have hkey : Real.exp (v * T) - 1 - v * T ≤ Real.exp (v * T) := by linarith
  exact mul_le_mul_of_nonneg_left hkey hcoef

/-- **Theorem 10, regime 3 (strong gap), linear growth**: for `μ > 0`,
`F(μ,T) ≤ T/μ` for all `T`. -/
theorem lindbladF_le_div {μ T : ℝ} (hμ : 0 < μ) (hT : 0 ≤ T) :
    lindbladF μ T ≤ T / μ := by
  rw [lindbladF_eq (ne_of_gt hμ)]
  have hexp : Real.exp (-μ * T) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    nlinarith
  have hnum : 0 ≤ 1 - Real.exp (-μ * T) := by linarith
  have hμ2 : (0 : ℝ) < μ ^ 2 := by positivity
  have hq : 0 ≤ (1 - Real.exp (-μ * T)) / μ ^ 2 := div_nonneg hnum hμ2.le
  linarith

/-- **Theorem 10, regimes 1-2 (negative `μ`)**: for `μ < 0` and `T ≥ 0`,
`F(μ,T) ≤ (1/μ²) e^{−μT}`, the exponential growth `e^{|μ|T}` of Eq. (81). -/
theorem lindbladF_le_exp_of_neg {μ T : ℝ} (hμ : μ < 0) (hT : 0 ≤ T) :
    lindbladF μ T ≤ (1 / μ ^ 2) * Real.exp (-μ * T) := by
  rw [lindbladF_eq (ne_of_lt hμ)]
  have hμ2 : (0 : ℝ) < μ ^ 2 := sq_pos_of_ne_zero (ne_of_lt hμ)
  have hTμ : T * μ ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hT hμ.le
  have hEmul : T * μ ≤ 1 := by nlinarith
  have hL : T / μ - (1 - Real.exp (-μ * T)) / μ ^ 2
      = (T * μ - (1 - Real.exp (-μ * T))) / μ ^ 2 := by
    field_simp
  rw [hL, show (1 : ℝ) / μ ^ 2 * Real.exp (-μ * T) = Real.exp (-μ * T) / μ ^ 2 by ring]
  rw [div_le_div_iff_of_pos_right hμ2]
  nlinarith [hEmul]

/-- **Theorem 10, Eq. (80), radius monotonicity**: the right-hand side of (80)
is nonincreasing in the radius `R` (the factor `e^{−(R−d*)}` decreases). -/
theorem theorem10_error_bound
    {C lam S μ T dStar : ℝ} (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hS : 0 ≤ S)
    (hF : 0 ≤ lindbladF μ T) {R R' : ℝ} (hRR : R ≤ R') :
    C * lam * S ^ 2 * Real.exp (-(R' - dStar)) * lindbladF μ T ≤
      C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF μ T := by
  have hcoef : 0 ≤ C * lam * S ^ 2 * lindbladF μ T :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hlam) (pow_nonneg hS 2)) hF
  have hmono : Real.exp (-(R' - dStar)) ≤ Real.exp (-(R - dStar)) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hstep := mul_le_mul_of_nonneg_right hmono hcoef
  calc C * lam * S ^ 2 * Real.exp (-(R' - dStar)) * lindbladF μ T
      = Real.exp (-(R' - dStar)) * (C * lam * S ^ 2 * lindbladF μ T) := by ring
    _ ≤ Real.exp (-(R - dStar)) * (C * lam * S ^ 2 * lindbladF μ T) := hstep
    _ = C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF μ T := by ring

/-- **Theorem 10, regime 1 (no gap), radius**: the radius
`R = d* + v_LR T + log(C λ ‖S‖²/(ε v_LR²))` makes the error bound at most `ε`. -/
theorem theorem10_no_gap_radius
    {JH JHR C lam S v T ε dStar R : ℝ}
    (hε : 0 < ε) (hv : 0 < v) (hT : 0 ≤ T)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hS : 0 ≤ S)
    (hR : R = dStar + v * T + Real.log (C * lam * S ^ 2 / (ε * v ^ 2)))
    (herr : |JH - JHR| ≤
      C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF (-v) T) :
    |JH - JHR| ≤ ε := by
  have hcoef0 : 0 ≤ C * lam * S ^ 2 := mul_nonneg (mul_nonneg hC hlam) (pow_nonneg hS 2)
  rcases lt_or_eq_of_le hcoef0 with hpos | hzero
  · have hF : lindbladF (-v) T ≤ (1 / v ^ 2) * Real.exp (v * T) :=
      lindbladF_noGap_le_exp hv hT
    have hB : 0 < C * lam * S ^ 2 / (ε * v ^ 2) :=
      div_pos hpos (mul_pos hε (pow_pos hv 2))
    have hexp : Real.exp (-(R - dStar)) =
        Real.exp (-(v * T)) * (C * lam * S ^ 2 / (ε * v ^ 2))⁻¹ := by
      rw [hR]
      have h1 : dStar + v * T + Real.log (C * lam * S ^ 2 / (ε * v ^ 2)) - dStar
          = v * T + Real.log (C * lam * S ^ 2 / (ε * v ^ 2)) := by ring
      rw [h1, show -(v * T + Real.log (C * lam * S ^ 2 / (ε * v ^ 2)))
          = -(v * T) + -(Real.log (C * lam * S ^ 2 / (ε * v ^ 2))) by ring]
      rw [Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hB]
    have hcoefexp : 0 ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) :=
      mul_nonneg hcoef0 (Real.exp_pos _).le
    have hBne : C * lam * S ^ 2 ≠ 0 := ne_of_gt hpos
    calc |JH - JHR|
        ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF (-v) T := herr
      _ ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) *
            ((1 / v ^ 2) * Real.exp (v * T)) :=
          mul_le_mul_of_nonneg_left hF hcoefexp
      _ = ε := by
          rw [hexp, Real.exp_neg]
          have hCne : C ≠ 0 := fun h => hBne (by rw [h]; ring)
          have hlamne : lam ≠ 0 := fun h => hBne (by rw [h]; ring)
          have hSne : S ≠ 0 := fun h => hBne (by rw [h]; ring)
          have hεne : ε ≠ 0 := ne_of_gt hε
          have hvne : v ≠ 0 := ne_of_gt hv
          field_simp
  · have hzero' : C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF (-v) T = 0 := by
      rw [← hzero]; ring
    rw [hzero'] at herr
    linarith

/-- **Theorem 10, regime 2, Eq. (81)**: for a weak gap `0 < Δ < v_LR` the error
obeys `|J_H − J_{H_R}| = O(e^{−(R−d*)} e^{(v_LR−Δ)T})`. -/
theorem theorem10_weak_gap
    {JH JHR C lam S Δ vLR T dStar R : ℝ}
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hS : 0 ≤ S) (hΔv : Δ < vLR)
    (hT : 0 ≤ T)
    (herr : |JH - JHR| ≤
      C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF (Δ - vLR) T) :
    |JH - JHR| ≤
      C * lam * S ^ 2 * Real.exp (-(R - dStar)) *
        (1 / (vLR - Δ) ^ 2) * Real.exp ((vLR - Δ) * T) := by
  have hcoefexp : 0 ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hC hlam) (pow_nonneg hS 2)) (Real.exp_pos _).le
  calc |JH - JHR|
      ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF (Δ - vLR) T := herr
    _ ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) *
          ((1 / (vLR - Δ) ^ 2) * Real.exp ((vLR - Δ) * T)) := by
        refine mul_le_mul_of_nonneg_left ?_ hcoefexp
        have h := lindbladF_le_exp_of_neg (show Δ - vLR < 0 by linarith) hT
        simpa [show (Δ - vLR) ^ 2 = (vLR - Δ) ^ 2 by ring,
          show -(Δ - vLR) * T = (vLR - Δ) * T by ring] using h
    _ = C * lam * S ^ 2 * Real.exp (-(R - dStar)) *
          (1 / (vLR - Δ) ^ 2) * Real.exp ((vLR - Δ) * T) := by ring

/-- **Theorem 10, regime 2, radius**: `R = d* + (v_LR − Δ)T + log(C λ ‖S‖²/(ε (v_LR−Δ)²))`
suffices. -/
theorem theorem10_weak_gap_radius
    {JH JHR C lam S Δ vLR T ε dStar R : ℝ}
    (hε : 0 < ε) (hΔv : Δ < vLR) (hT : 0 ≤ T)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hS : 0 ≤ S)
    (hR : R = dStar + (vLR - Δ) * T +
        Real.log (C * lam * S ^ 2 / (ε * (vLR - Δ) ^ 2)))
    (herr : |JH - JHR| ≤
      C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF (Δ - vLR) T) :
    |JH - JHR| ≤ ε := by
  have hcoef0 : 0 ≤ C * lam * S ^ 2 := mul_nonneg (mul_nonneg hC hlam) (pow_nonneg hS 2)
  have hvpos : 0 < vLR - Δ := by linarith
  rcases lt_or_eq_of_le hcoef0 with hpos | hzero
  · have hB : 0 < C * lam * S ^ 2 / (ε * (vLR - Δ) ^ 2) :=
      div_pos hpos (mul_pos hε (pow_pos hvpos 2))
    have hw := theorem10_weak_gap hC hlam hS hΔv hT herr
    have hexp : Real.exp (-(R - dStar)) =
        Real.exp (-((vLR - Δ) * T)) *
          (C * lam * S ^ 2 / (ε * (vLR - Δ) ^ 2))⁻¹ := by
      rw [hR]
      have h1 : dStar + (vLR - Δ) * T +
          Real.log (C * lam * S ^ 2 / (ε * (vLR - Δ) ^ 2)) - dStar
          = (vLR - Δ) * T + Real.log (C * lam * S ^ 2 / (ε * (vLR - Δ) ^ 2)) := by
        ring
      rw [h1, show -((vLR - Δ) * T +
          Real.log (C * lam * S ^ 2 / (ε * (vLR - Δ) ^ 2)))
          = -((vLR - Δ) * T) +
            -(Real.log (C * lam * S ^ 2 / (ε * (vLR - Δ) ^ 2))) by ring]
      rw [Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_log hB]
    have hBne : C * lam * S ^ 2 ≠ 0 := ne_of_gt hpos
    calc |JH - JHR|
        ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) *
            (1 / (vLR - Δ) ^ 2) * Real.exp ((vLR - Δ) * T) := hw
      _ = ε := by
          rw [hexp, Real.exp_neg]
          have hCne : C ≠ 0 := fun h => hBne (by rw [h]; ring)
          have hlamne : lam ≠ 0 := fun h => hBne (by rw [h]; ring)
          have hSne : S ≠ 0 := fun h => hBne (by rw [h]; ring)
          have hεne : ε ≠ 0 := ne_of_gt hε
          have hvne : vLR - Δ ≠ 0 := ne_of_gt hvpos
          field_simp
  · have hzero' : C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF (Δ - vLR) T = 0 := by
      rw [← hzero]; ring
    rw [hzero'] at herr
    linarith

/-- **Theorem 10, regime 3, Eq. (82)**: for a strong gap `μ = Δ − v_LR > 0` the
radius `d* + log(C λ ‖S‖² T/(ε μ))` makes the error at most `ε`. -/
theorem theorem10_strong_gap_radius
    {JH JHR C lam S μ T ε dStar R : ℝ}
    (hε : 0 < ε) (hμ : 0 < μ) (hT : 0 < T)
    (hC : 0 ≤ C) (hlam : 0 ≤ lam) (hS : 0 ≤ S)
    (hR : R = dStar + Real.log (C * lam * S ^ 2 * T / (ε * μ)))
    (herr : |JH - JHR| ≤
      C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF μ T) :
    |JH - JHR| ≤ ε := by
  have hcoef0 : 0 ≤ C * lam * S ^ 2 := mul_nonneg (mul_nonneg hC hlam) (pow_nonneg hS 2)
  rcases lt_or_eq_of_le hcoef0 with hpos | hzero
  · have hF : lindbladF μ T ≤ T / μ := lindbladF_le_div hμ hT.le
    have hB : 0 < C * lam * S ^ 2 * T / (ε * μ) :=
      div_pos (mul_pos hpos hT) (mul_pos hε hμ)
    have hexp : Real.exp (-(R - dStar)) = ε * μ / (C * lam * S ^ 2 * T) := by
      rw [hR]
      have h1 : dStar + Real.log (C * lam * S ^ 2 * T / (ε * μ)) - dStar
          = Real.log (C * lam * S ^ 2 * T / (ε * μ)) := by ring
      rw [h1, Real.exp_neg, Real.exp_log hB]
      field_simp
    have hcoefexp : 0 ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) :=
      mul_nonneg hcoef0 (Real.exp_pos _).le
    have hBne : C * lam * S ^ 2 * T ≠ 0 := ne_of_gt (mul_pos hpos hT)
    have hμne : μ ≠ 0 := ne_of_gt hμ
    calc |JH - JHR|
        ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF μ T := herr
      _ ≤ C * lam * S ^ 2 * Real.exp (-(R - dStar)) * (T / μ) :=
          mul_le_mul_of_nonneg_left hF hcoefexp
      _ = ε := by
          rw [hexp]
          have hCne : C ≠ 0 := fun h => hBne (by rw [h]; ring)
          have hlamne : lam ≠ 0 := fun h => hBne (by rw [h]; ring)
          have hSne : S ≠ 0 := fun h => hBne (by rw [h]; ring)
          have hμne' : μ ≠ 0 := ne_of_gt hμ
          field_simp
  · have hzero' : C * lam * S ^ 2 * Real.exp (-(R - dStar)) * lindbladF μ T = 0 := by
      rw [← hzero]; ring
    rw [hzero'] at herr
    linarith

end Qatlib.Papers.DenseOutSim26.FreeTruncation.Lindblad
