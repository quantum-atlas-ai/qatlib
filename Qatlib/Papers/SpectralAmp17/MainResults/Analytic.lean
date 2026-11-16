/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SpectralAmp17.MainResults.SourceModel.PolynomialToolkit
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Push

@[expose] public section


set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.SpectralAmp17.MainResults.Analytic

open Qatlib.Papers.SpectralAmp17.MainResults.SourceModel
open Qatlib.Concepts.QsvtCore.ApproxToolkit

/-- The source smoothing parameter gives sign error at most epsilon on the positive side of its gap. -/
theorem positive_sign_error (κ ε x : ℝ) (hκ : 0 < κ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))) (hx : κ / 2 ≤ x) :
    |fSgn κ ε x - 1| ≤ ε := by
  let L : ℝ := Real.log (2 / (Real.pi * ε ^ 2))
  have hden : 0 < Real.exp 1 * Real.pi := mul_pos (Real.exp_pos _) Real.pi_pos
  have hεsq : ε ^ 2 ≤ 2 / (Real.exp 1 * Real.pi) := by
    have hsq := (sq_le_sq₀ hε0.le (Real.sqrt_nonneg _)).2 hε
    rwa [Real.sq_sqrt (by positivity)] at hsq
  have hprod : ε ^ 2 * (Real.exp 1 * Real.pi) ≤ 2 :=
    (le_div_iff₀ hden).mp hεsq
  have hzpos : 0 < 2 / (Real.pi * ε ^ 2) := by positivity
  have hzge : Real.exp 1 ≤ 2 / (Real.pi * ε ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < Real.pi * ε ^ 2)).2
    nlinarith [hprod]
  have hL1 : 1 ≤ L := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hzge
    simpa only [Real.log_exp] using hlog
  have hL0 : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  have hk : 0 < kSgn κ ε := by
    change 0 < Real.sqrt 2 / κ * Real.sqrt L
    exact mul_pos (div_pos (Real.sqrt_pos.2 (by norm_num)) hκ)
      (Real.sqrt_pos.2 hLpos)
  have hx0 : 0 < x := by linarith
  let u : ℝ := kSgn κ ε * x
  have hu0 : 0 < u := mul_pos hk hx0
  have hk2 : (kSgn κ ε) ^ 2 * κ ^ 2 = 2 * L := by
    change (Real.sqrt 2 / κ * Real.sqrt L) ^ 2 * κ ^ 2 = 2 * L
    rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num), Real.sq_sqrt hL0]
    field_simp [hκ.ne']
  have hx2 : (κ / 2) ^ 2 ≤ x ^ 2 :=
    (sq_le_sq₀ (by positivity) hx0.le).2 hx
  have hscaled := mul_le_mul_of_nonneg_left hx2 (sq_nonneg (kSgn κ ε))
  have hu2 : L / 2 ≤ u ^ 2 := by
    dsimp [u]
    nlinarith [hscaled, hk2]
  have hhalf : (1 / 2 : ℝ) ≤ u ^ 2 := by linarith
  have hexp2 : Real.exp (-u ^ 2) ^ 2 ≤ Real.pi * ε ^ 2 / 2 := by
    calc Real.exp (-u ^ 2) ^ 2 = Real.exp (-2 * u ^ 2) := by
          rw [sq, ← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-L) := Real.exp_le_exp.mpr (by linarith)
      _ = (2 / (Real.pi * ε ^ 2))⁻¹ := by
          change Real.exp (-Real.log (2 / (Real.pi * ε ^ 2))) = _
          rw [Real.exp_neg, Real.exp_log hzpos]
      _ = Real.pi * ε ^ 2 / 2 := by rw [inv_div]
  have hrootpi : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
  have htarget0 : 0 ≤ ε * (u * Real.sqrt Real.pi) := by positivity
  have htarget2 : (ε * (u * Real.sqrt Real.pi)) ^ 2 = ε ^ 2 * u ^ 2 * Real.pi := by
    rw [mul_pow, mul_pow, Real.sq_sqrt Real.pi_pos.le]
    ring
  have hlow := mul_le_mul_of_nonneg_left hhalf
    (mul_nonneg (sq_nonneg ε) Real.pi_pos.le)
  have hnormsq : Real.exp (-u ^ 2) ^ 2 ≤ (ε * (u * Real.sqrt Real.pi)) ^ 2 := by
    rw [htarget2]
    nlinarith [hexp2, hlow]
  have hmain : Real.exp (-u ^ 2) ≤ ε * (u * Real.sqrt Real.pi) :=
    (sq_le_sq₀ (Real.exp_pos _).le htarget0).1 hnormsq
  have htail : 1 - erf u ≤ ε := by
    calc 1 - erf u ≤ Real.exp (-u ^ 2) / (u * Real.sqrt Real.pi) :=
          one_sub_erf_le u hu0
      _ ≤ ε := (div_le_iff₀ (mul_pos hu0 hrootpi)).2 hmain
  have herf : erf u ≤ 1 := erf_le_one u
  change |erf u - 1| ≤ ε
  rw [abs_of_nonpos (by linarith : erf u - 1 ≤ 0)]
  linarith

/-- The actual source erf smoothing satisfies both the global unit bound and the full two-sided sign estimate. -/
theorem lemma10_signFunction (κ ε : ℝ) (hκ : 0 < κ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))) :
    (∀ x : ℝ, |fSgn κ ε x| ≤ 1) ∧
      (∀ x : ℝ, κ / 2 ≤ |x| → |fSgn κ ε x - signFun x| ≤ ε) := by
  refine ⟨fun x => abs_erf_le_one (kSgn κ ε * x), ?_⟩
  intro x hx
  rcases le_total 0 x with hx0 | hx0
  · have hx' : κ / 2 ≤ x := by simpa only [abs_of_nonneg hx0] using hx
    have hxpos : 0 < x := by linarith
    have hsign : signFun x = 1 := by simp [signFun, hxpos]
    rw [hsign]
    exact positive_sign_error κ ε x hκ hε0 hε hx'
  · have hx' : κ / 2 ≤ -x := by simpa only [abs_of_nonpos hx0] using hx
    have hxneg : x < 0 := by linarith
    have hsign : signFun x = -1 := by
      simp [signFun, hxneg, not_lt.mpr hx0]
    have hodd : fSgn κ ε (-x) = -fSgn κ ε x := by
      unfold fSgn
      rw [mul_neg, erf_neg]
    have herr := positive_sign_error κ ε (-x) hκ hε0 hε hx'
    rw [hodd] at herr
    have heq : -fSgn κ ε x - 1 = -(fSgn κ ε x + 1) := by ring
    rw [heq, abs_neg] at herr
    rw [hsign]
    simpa only [sub_neg_eq_add] using herr

/-- The source smoothed rectangle has absolute value at most one on the whole real line. -/
theorem fRect_abs_le_one (w κ ε x : ℝ) : |fRect w κ ε x| ≤ 1 := by
  have h1 := abs_erf_le_one (kSgn κ ε * (x + (w + κ) / 2))
  have h2 := abs_erf_le_one (kSgn κ ε * ((w + κ) / 2 - x))
  have hsum := abs_add_le (erf (kSgn κ ε * (x + (w + κ) / 2)))
    (erf (kSgn κ ε * ((w + κ) / 2 - x)))
  change |(1 / 2 : ℝ) * (erf (kSgn κ ε * (x + (w + κ) / 2)) +
    erf (kSgn κ ε * ((w + κ) / 2 - x)))| ≤ 1
  rw [abs_mul]
  norm_num
  linarith

/-- On its central interval the source smoothed linear response is bounded by one. -/
theorem fLin_central_unit (Γ ε x : ℝ) (hΓ : 0 < Γ) (hx : |x| ≤ 2 * Γ) :
    |fLin Γ ε x| ≤ 1 := by
  have hden : 0 < 2 * Γ := by positivity
  have hratio : |x| / (2 * Γ) ≤ 1 := (div_le_one hden).2 hx
  have hr := fRect_abs_le_one (2 * Γ) (2 * Γ) ε x
  unfold fLin
  rw [abs_mul, abs_div, abs_of_pos hden]
  calc |x| / (2 * Γ) * |fRect (2 * Γ) (2 * Γ) ε x|
      ≤ 1 * 1 := mul_le_mul hratio hr (abs_nonneg _) (by norm_num)
    _ = 1 := by norm_num

/-- The integral definition of erf is monotone because its Gaussian integrand is nonnegative. -/
theorem erf_monotone : Monotone erf := by
  intro a b hab
  have hc : Continuous (fun t : ℝ => Real.exp (-t ^ 2)) := by fun_prop
  have h0a : IntervalIntegrable (fun t : ℝ => Real.exp (-t ^ 2))
      MeasureTheory.volume 0 a := hc.intervalIntegrable 0 a
  have habi : IntervalIntegrable (fun t : ℝ => Real.exp (-t ^ 2))
      MeasureTheory.volume a b := hc.intervalIntegrable a b
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0a habi
  have hnonneg : 0 ≤ ∫ t : ℝ in a..b, Real.exp (-t ^ 2) :=
    intervalIntegral.integral_nonneg hab (by intro t ht; exact (Real.exp_pos _).le)
  unfold erf
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  linarith

/-- The source smoothing scale times its gap width is at least one under its stated tolerance range. -/
theorem kSgn_scaled_lower (κ ε : ℝ) (hκ : 0 < κ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))) :
    1 ≤ κ * kSgn κ ε := by
  let L : ℝ := Real.log (2 / (Real.pi * ε ^ 2))
  have hεsq : ε ^ 2 ≤ 2 / (Real.exp 1 * Real.pi) := by
    have hsq := (sq_le_sq₀ hε0.le (Real.sqrt_nonneg _)).2 hε
    rwa [Real.sq_sqrt (by positivity)] at hsq
  have hprod : ε ^ 2 * (Real.exp 1 * Real.pi) ≤ 2 :=
    (le_div_iff₀ (by positivity : 0 < Real.exp 1 * Real.pi)).mp hεsq
  have hzge : Real.exp 1 ≤ 2 / (Real.pi * ε ^ 2) := by
    apply (le_div_iff₀ (by positivity : 0 < Real.pi * ε ^ 2)).2
    nlinarith [hprod]
  have hL1 : 1 ≤ L := by
    have hlog := Real.log_le_log (Real.exp_pos 1) hzge
    simpa only [Real.log_exp] using hlog
  have hL0 : 0 ≤ L := by linarith
  have hrootL : 1 ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num) hL0).2
    simpa using hL1
  have hroot2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    apply (Real.le_sqrt (by norm_num) (by norm_num : (0 : ℝ) ≤ 2)).2
    norm_num
  have heq : κ * kSgn κ ε = Real.sqrt 2 * Real.sqrt L := by
    unfold kSgn
    change κ * (Real.sqrt 2 / κ * Real.sqrt L) = Real.sqrt 2 * Real.sqrt L
    field_simp [hκ.ne']
  rw [heq]
  have hm := mul_le_mul hroot2 hrootL (by norm_num : (0 : ℝ) ≤ 1)
    (Real.sqrt_nonneg 2)
  simpa using hm

/-- Reflecting the source smoothed rectangle leaves its value unchanged. -/
theorem fRect_neg (w κ ε x : ℝ) : fRect w κ ε (-x) = fRect w κ ε x := by
  unfold fRect
  dsimp only
  have h1 : -x + (w + κ) / 2 = (w + κ) / 2 - x := by ring
  have h2 : (w + κ) / 2 - (-x) = x + (w + κ) / 2 := by ring
  rw [h1, h2]
  ring

/-- The source smoothed linear response is odd. -/
theorem fLin_neg (Γ ε x : ℝ) : fLin Γ ε (-x) = -fLin Γ ε x := by
  unfold fLin
  rw [fRect_neg, neg_div, neg_mul]

/-- The source smoothed linear response is globally bounded on the nonnegative half-line. -/
theorem fLin_positive_unit (Γ ε x : ℝ) (hΓ : 0 < Γ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))) (hx0 : 0 ≤ x) :
    |fLin Γ ε x| ≤ 1 := by
  by_cases hxsmall : x ≤ 2 * Γ
  · exact fLin_central_unit Γ ε x hΓ (by simpa only [abs_of_nonneg hx0] using hxsmall)
  have hx2 : 2 * Γ ≤ x := le_of_lt (lt_of_not_ge hxsmall)
  let K : ℝ := kSgn (2 * Γ) ε
  let A : ℝ := K * (x + 2 * Γ)
  let B : ℝ := K * (x - 2 * Γ)
  let c : ℝ := x / (4 * Γ)
  have hK0 : 0 ≤ K := by
    dsimp [K, kSgn]
    positivity
  have hKscale : 1 ≤ 2 * Γ * K :=
    kSgn_scaled_lower (2 * Γ) ε (by positivity) hε0 hε
  have hKpos : 0 < K := by
    by_contra! hk
    have hn := mul_nonpos_of_nonneg_of_nonpos (by positivity : 0 ≤ 2 * Γ) hk
    linarith
  have hBA : B ≤ A := by
    dsimp [A, B]
    nlinarith [mul_nonneg hK0 hΓ.le]
  have hdiff0 : 0 ≤ erf A - erf B := sub_nonneg.mpr (erf_monotone hBA)
  have hc0 : 0 ≤ c := div_nonneg hx0 (by positivity)
  have hrepr : fLin Γ ε x = c * (erf A - erf B) := by
    change x / (2 * Γ) * ((1 / 2 : ℝ) *
      (erf (K * (x + (2 * Γ + 2 * Γ) / 2)) +
        erf (K * ((2 * Γ + 2 * Γ) / 2 - x)))) =
          x / (4 * Γ) * (erf (K * (x + 2 * Γ)) - erf (K * (x - 2 * Γ)))
    rw [show (2 * Γ + 2 * Γ) / 2 = 2 * Γ by ring,
      show K * (2 * Γ - x) = -(K * (x - 2 * Γ)) by ring, erf_neg]
    ring
  have hf0 : 0 ≤ fLin Γ ε x := by rw [hrepr]; exact mul_nonneg hc0 hdiff0
  rw [abs_of_nonneg hf0, hrepr]
  by_cases hx4small : x ≤ 4 * Γ
  · have hB0 : 0 ≤ B := mul_nonneg hK0 (by linarith)
    have hB := erf_ge_zero B hB0
    have hA := erf_le_one A
    have hdiff1 : erf A - erf B ≤ 1 := by linarith
    have hc1 : c ≤ 1 := (div_le_one (by positivity : 0 < 4 * Γ)).2 hx4small
    calc c * (erf A - erf B) ≤ c * 1 := mul_le_mul_of_nonneg_left hdiff1 hc0
      _ = c := by ring
      _ ≤ 1 := hc1
  · have hx4 : 4 * Γ ≤ x := le_of_lt (lt_of_not_ge hx4small)
    have hBpos : 0 < B := mul_pos hKpos (by linarith)
    have hrootpi0 : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    have hrootpi1 : 1 ≤ Real.sqrt Real.pi := by
      apply (Real.le_sqrt (by norm_num) Real.pi_pos.le).2
      nlinarith [Real.pi_gt_three]
    have hscale_x := mul_le_mul_of_nonneg_right hKscale hx0
    have hrest : 0 ≤ 2 * Γ * K * (x - 4 * Γ) :=
      mul_nonneg (by positivity) (sub_nonneg.mpr hx4)
    have hcB : c ≤ B := by
      apply (div_le_iff₀ (by positivity : 0 < 4 * Γ)).2
      dsimp [B]
      nlinarith [hscale_x, hrest]
    have hcden : c ≤ B * Real.sqrt Real.pi := by
      calc c ≤ B := hcB
        _ = B * 1 := by ring
        _ ≤ B * Real.sqrt Real.pi := mul_le_mul_of_nonneg_left hrootpi1 hBpos.le
    have hdenpos : 0 < B * Real.sqrt Real.pi := mul_pos hBpos hrootpi0
    have hexp : Real.exp (-B ^ 2) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg B))
    have hdiffTail : erf A - erf B ≤ 1 / (B * Real.sqrt Real.pi) := by
      calc erf A - erf B ≤ 1 - erf B := sub_le_sub_right (erf_le_one A) _
        _ ≤ Real.exp (-B ^ 2) / (B * Real.sqrt Real.pi) := one_sub_erf_le B hBpos
        _ ≤ 1 / (B * Real.sqrt Real.pi) := div_le_div_of_nonneg_right hexp hdenpos.le
    calc c * (erf A - erf B) ≤ c * (1 / (B * Real.sqrt Real.pi)) :=
          mul_le_mul_of_nonneg_left hdiffTail hc0
      _ = c / (B * Real.sqrt Real.pi) := by ring
      _ ≤ 1 := (div_le_one hdenpos).2 hcden

/-- The source smoothed linear response has absolute value at most one on the entire real line. -/
theorem fLin_abs_le_one (Γ ε x : ℝ) (hΓ : 0 < Γ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))) : |fLin Γ ε x| ≤ 1 := by
  rcases le_total 0 x with hx | hx
  · exact fLin_positive_unit Γ ε x hΓ hε0 hε hx
  · have h := fLin_positive_unit Γ ε (-x) hΓ hε0 hε (by linarith)
    simpa only [fLin_neg, abs_neg] using h

/-- On the source linear-response interval, its smoothed rectangle is epsilon-close to one. -/
theorem fRect_linear_error (Γ ε x : ℝ) (hΓ : 0 < Γ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))) (hx : |x| ≤ Γ) :
    |fRect (2 * Γ) (2 * Γ) ε x - 1| ≤ ε := by
  have hxs := abs_le.mp hx
  have ha := positive_sign_error (2 * Γ) ε (x + 2 * Γ) (by positivity) hε0 hε
    (by linarith)
  have hb := positive_sign_error (2 * Γ) ε (2 * Γ - x) (by positivity) hε0 hε
    (by linarith)
  change |erf (kSgn (2 * Γ) ε * (x + 2 * Γ)) - 1| ≤ ε at ha
  change |erf (kSgn (2 * Γ) ε * (2 * Γ - x)) - 1| ≤ ε at hb
  have hsum := abs_add_le
    (erf (kSgn (2 * Γ) ε * (x + 2 * Γ)) - 1)
    (erf (kSgn (2 * Γ) ε * (2 * Γ - x)) - 1)
  have heq : fRect (2 * Γ) (2 * Γ) ε x - 1 = (1 / 2 : ℝ) *
      ((erf (kSgn (2 * Γ) ε * (x + 2 * Γ)) - 1) +
        (erf (kSgn (2 * Γ) ε * (2 * Γ - x)) - 1)) := by
    unfold fRect
    dsimp only
    rw [show (2 * Γ + 2 * Γ) / 2 = 2 * Γ by ring]
    ring
  rw [heq, abs_mul]
  norm_num
  linarith

/-- The actual source smoothed linear function satisfies its global range and relative-error guarantees. -/
theorem lemma12_linearFunction (Γ ε : ℝ) (hΓ : 0 < Γ) (hε0 : 0 < ε)
    (hε : ε ≤ Real.sqrt (2 / (Real.exp 1 * Real.pi))) :
    (∀ x : ℝ, |fLin Γ ε x| ≤ 1) ∧
      (∀ x : ℝ, |x| ≤ Γ → |fLin Γ ε x - x / (2 * Γ)| ≤ |x| * ε / (2 * Γ)) := by
  refine ⟨fun x => fLin_abs_le_one Γ ε x hΓ hε0 hε, ?_⟩
  intro x hx
  have hr := fRect_linear_error Γ ε x hΓ hε0 hε hx
  have hden : 0 < 2 * Γ := by positivity
  have heq : fLin Γ ε x - x / (2 * Γ) =
      x / (2 * Γ) * (fRect (2 * Γ) (2 * Γ) ε x - 1) := by
    unfold fLin
    ring
  rw [heq, abs_mul, abs_div, abs_of_pos hden]
  calc |x| / (2 * Γ) * |fRect (2 * Γ) (2 * Γ) ε x - 1|
      ≤ |x| / (2 * Γ) * ε := mul_le_mul_of_nonneg_left hr (by positivity)
    _ = |x| * ε / (2 * Γ) := by ring

end Qatlib.Papers.SpectralAmp17.MainResults.Analytic
