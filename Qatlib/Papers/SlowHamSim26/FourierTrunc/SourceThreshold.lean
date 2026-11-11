/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SlowHamSim26.FourierTrunc.Definitions
import Mathlib.Analysis.Complex.ExponentialBounds

set_option backward.isDefEq.respectTransparency false

/-!
# SlowHamSim26 / FourierTrunc — Lemma 4.1 (Eqs. (4.1)–(4.2), p. 18)

Fixed source: arXiv:2608.17653v1.  The threshold lemma for
`f(m) = log m / m^{1/ρ}`: with `C₀(ρ) = f(2) = log 2 / 2^{1/ρ}` and

`m_up = (ρ/C (log(ρ/C) + log log(ρ/C) + 1))^ρ`,

if `C ≤ C₀(ρ)` then `f(m) < C` for every `m ≥ ⌈m_up⌉`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SlowHamSim26.FourierTrunc

/-- Fixed arXiv:2608.17653v1, Lemma 4.1, Eqs. (4.1)–(4.2), p. 18.
If `C ≤ C₀(ρ) = log 2 / 2^{1/ρ}` then `log m / m^{1/ρ} < C` for all
`m ≥ ⌈(ρ/C (log(ρ/C) + log log(ρ/C) + 1))^ρ⌉`. -/
theorem lemma_four_one_log_threshold
    (ρ C : ℝ) (hρ : 1 < ρ) (hC : 0 < C)
    (hC0 : C ≤ Real.log 2 / (2 : ℝ) ^ (1 / ρ)) :
    ∀ m : ℕ,
      Nat.ceil ((ρ / C * (Real.log (ρ / C) + Real.log (Real.log (ρ / C)) + 1)) ^ ρ) ≤ m →
      Real.log (m : ℝ) / (m : ℝ) ^ (1 / ρ) < C := by
  have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
  have hρne : ρ ≠ 0 := ne_of_gt hρpos
  have hCne : C ≠ 0 := hC.ne'
  -- Numeric input facts: `log 2 < 1`, `2 < e`, and `e * log 2 < 2`.
  have hl2 := Real.log_two_lt_d9
  have hlog2lt1 : Real.log 2 < 1 := by linarith
  have h2e : (2 : ℝ) < Real.exp 1 := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    exact Real.exp_lt_exp.mpr hlog2lt1
  have helog2 : Real.exp 1 * Real.log 2 < 2 := by
    have h1 : Real.exp 1 * Real.log 2 ≤ 2.7182818286 * 0.6931471808 :=
      mul_le_mul Real.exp_one_lt_d9.le Real.log_two_lt_d9.le (by positivity) (by positivity)
    have h2 : (2.7182818286 : ℝ) * 0.6931471808 < 2 := by norm_num
    exact lt_of_le_of_lt h1 h2
  -- `log ρ ≥ 1 - 1/ρ`, hence `2 ≤ ρ * 2^{1/ρ}`, i.e. `2 / 2^{1/ρ} ≤ ρ`.
  have h2powpos : 0 < (2 : ℝ) ^ (1 / ρ) := Real.rpow_pos_of_pos two_pos _
  have hlogge : 1 - 1 / ρ ≤ Real.log ρ := by
    have h1 : Real.log (1 / ρ) ≤ 1 / ρ - 1 := Real.log_le_sub_one_of_pos (div_pos one_pos hρpos)
    rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) hρne, Real.log_one] at h1
    linarith
  have hkey : (2 : ℝ) ≤ ρ * (2 : ℝ) ^ (1 / ρ) := by
    have hinvρ : 1 / ρ < 1 := (div_lt_one hρpos).mpr hρ
    have hpos : 0 < 1 - 1 / ρ := by linarith
    have h1 : Real.log 2 * (1 - 1 / ρ) < 1 * (1 - 1 / ρ) :=
      mul_lt_mul_of_pos_right hlog2lt1 hpos
    have h1' : Real.log 2 - (1 / ρ) * Real.log 2 < 1 - 1 / ρ := by nlinarith [h1]
    have h2 : Real.log 2 ≤ Real.log ρ + (1 / ρ) * Real.log 2 := by linarith
    have h3 : Real.log ρ + (1 / ρ) * Real.log 2 = Real.log (ρ * (2 : ℝ) ^ (1 / ρ)) := by
      rw [Real.log_mul (ne_of_gt hρpos) (ne_of_gt h2powpos), Real.log_rpow two_pos]
    have h4 : Real.exp (Real.log ρ + (1 / ρ) * Real.log 2) = ρ * (2 : ℝ) ^ (1 / ρ) := by
      rw [h3, Real.exp_log (mul_pos hρpos h2powpos)]
    calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log two_pos).symm
      _ ≤ Real.exp (Real.log ρ + (1 / ρ) * Real.log 2) := Real.exp_le_exp.mpr h2
      _ = ρ * (2 : ℝ) ^ (1 / ρ) := h4
  -- Therefore `e < ρ/C`: multiply `C ≤ C₀` by `e`, use `e log 2 < 2` and `2 ≤ ρ 2^{1/ρ}`.
  have ht : Real.exp 1 < ρ / C := by
    apply (lt_div_iff₀ hC).mpr
    have hEC : Real.exp 1 * C ≤ Real.exp 1 * (Real.log 2 / (2 : ℝ) ^ (1 / ρ)) :=
      mul_le_mul_of_nonneg_left hC0 (by positivity)
    have hEq1 : Real.exp 1 * (Real.log 2 / (2 : ℝ) ^ (1 / ρ))
        = Real.exp 1 * Real.log 2 / (2 : ℝ) ^ (1 / ρ) := by ring
    rw [hEq1] at hEC
    have hEq2 : Real.exp 1 * Real.log 2 / (2 : ℝ) ^ (1 / ρ) < 2 / (2 : ℝ) ^ (1 / ρ) :=
      (div_lt_div_iff₀ h2powpos h2powpos).mpr (mul_lt_mul_of_pos_right helog2 h2powpos)
    have hEq3 : 2 / (2 : ℝ) ^ (1 / ρ) ≤ ρ :=
      (div_le_iff₀ h2powpos).mpr hkey
    linarith
  -- The threshold body: `t = ρ/C`, `v = log t`, `u = v + log v + 1`.
  set t : ℝ := ρ / C with htdef
  have hv1 : 1 < Real.log t := by
    have h := Real.log_lt_log (Real.exp_pos 1) ht
    rwa [Real.log_exp] at h
  set v : ℝ := Real.log t with hvdef
  have hvpos : 0 < v := lt_trans zero_lt_one hv1
  have hlogv1 : Real.log v + 1 ≤ v := by
    have h := Real.log_le_sub_one_of_pos hvpos
    linarith
  set u : ℝ := v + Real.log v + 1 with hudef
  have hupos : 0 < u := by
    have h : 0 < Real.log v := Real.log_pos hv1
    linarith
  have hu2 : 2 ≤ u := by
    have h : 0 ≤ Real.log v := Real.log_nonneg hv1.le
    linarith
  have hlogu : Real.log u < Real.log v + 1 := by
    have hA : u ≤ 2 * v := by linarith
    have hB : (2 : ℝ) * v < Real.exp 1 * v := mul_lt_mul_of_pos_right h2e hvpos
    have h1 : u < Real.exp 1 * v := by linarith
    have h2 : Real.exp 1 * v = Real.exp (1 + Real.log v) := by
      rw [Real.exp_add, Real.exp_log hvpos]
    rw [h2] at h1
    have h3 := Real.log_lt_log hupos h1
    rw [Real.log_exp] at h3
    linarith
  have htpos : 0 < t := by rw [htdef]; exact div_pos hρpos hC
  have htC : ρ / t = C := by
    rw [htdef]
    field_simp [hCne, hρne]
  have htu2 : Real.exp 1 * 2 ≤ t * u := by
    have h1 : Real.exp 1 * 2 ≤ t * 2 := mul_le_mul_of_nonneg_right ht.le (by norm_num : (0 : ℝ) ≤ 2)
    have h2 : t * 2 ≤ t * u := mul_le_mul_of_nonneg_left hu2 htpos.le
    linarith
  have hetu : Real.exp 1 ≤ t * u :=
    le_trans (le_mul_of_one_le_right (Real.exp_pos 1).le (by norm_num : (1 : ℝ) ≤ 2)) htu2
  have heρ : Real.exp ρ ≤ (t * u) ^ ρ := by
    rw [Real.rpow_def_of_pos (mul_pos htpos hupos)]
    apply Real.exp_le_exp.mpr
    have hlog1 : (1 : ℝ) ≤ Real.log (t * u) := by
      have h0 := Real.log_le_log (Real.exp_pos 1) hetu
      rwa [Real.log_exp] at h0
    linarith [mul_le_mul_of_nonneg_right hlog1 hρpos.le]
  -- `f (m_up) < C`.
  have hmuppow : ((t * u) ^ ρ) ^ (1 / ρ) = t * u := by
    have hpos : 0 < t * u := mul_pos htpos hupos
    have hinv : ρ * (1 / ρ) = 1 := by field_simp
    rw [← Real.rpow_mul hpos.le ρ (1 / ρ), hinv, Real.rpow_one]
  have hlogmup : Real.log ((t * u) ^ ρ) = ρ * (v + Real.log u) := by
    rw [Real.log_rpow (mul_pos htpos hupos), Real.log_mul htpos.ne' hupos.ne', ← hvdef]
  have hfmup : Real.log ((t * u) ^ ρ) / ((t * u) ^ ρ) ^ (1 / ρ) < C := by
    have hkey2 : v + Real.log u < u := by linarith
    have hEq : ρ * (v + Real.log u) / (t * u) = C * ((v + Real.log u) / u) := by
      rw [htdef]
      field_simp [hCne, hρne, hupos.ne']
    rw [hlogmup, hmuppow, hEq]
    have h1 : (v + Real.log u) / u < 1 := by
      rw [div_lt_iff₀ hupos]
      linarith
    calc C * ((v + Real.log u) / u) < C * 1 := mul_lt_mul_of_pos_left h1 hC
      _ = C := by ring
  -- `f` is antitone on `[e^ρ, ∞)`.
  have hsub : ∀ x ∈ Set.Ici (Real.exp ρ), (0 : ℝ) < x := fun x hx =>
    lt_of_lt_of_le (Real.exp_pos ρ) hx
  have hanti : AntitoneOn (fun x : ℝ => Real.log x / x ^ (1 / ρ)) (Set.Ici (Real.exp ρ)) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (Real.exp ρ))
    · have hlogc : ContinuousOn Real.log (Set.Ici (Real.exp ρ)) :=
        Real.continuousOn_log.mono (fun x hx => (hsub x hx).ne')
      have hpowc : ContinuousOn (fun x : ℝ => x ^ (1 / ρ)) (Set.Ici (Real.exp ρ)) :=
        continuousOn_id.rpow_const (fun x hx => Or.inl (hsub x hx).ne')
      exact hlogc.div hpowc (fun x hx => (Real.rpow_pos_of_pos (hsub x hx) _).ne')
    · intro x hx
      rw [interior_Ici] at hx
      have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos ρ) hx.le
      have h1 : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hxpos.ne'
      have h2 : HasDerivAt (fun y : ℝ => y ^ (1 / ρ)) ((1 / ρ) * x ^ (1 / ρ - 1)) x :=
        Real.hasDerivAt_rpow_const (Or.inl hxpos.ne')
      exact (h1.div h2 (Real.rpow_pos_of_pos hxpos _).ne').hasDerivWithinAt
    · intro x hx
      rw [interior_Ici] at hx
      have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos ρ) hx.le
      have hlogx : ρ ≤ Real.log x := by
        have h := Real.log_le_log (Real.exp_pos ρ) hx.le
        rwa [Real.log_exp] at h
      have hA : 0 < x ^ (1 / ρ) := Real.rpow_pos_of_pos hxpos _
      have hB : 0 < x ^ (1 / ρ - 1) := Real.rpow_pos_of_pos hxpos _
      have hAB' : x⁻¹ * x ^ (1 / ρ) = x ^ (1 / ρ - 1) := by
        rw [inv_mul_eq_div, Real.rpow_sub hxpos (1 / ρ) 1, Real.rpow_one]
      have hge : 1 ≤ Real.log x / ρ := by
        rw [le_div_iff₀ hρpos]
        linarith
      have hnum : x ^ (1 / ρ - 1) - Real.log x * ((1 / ρ) * x ^ (1 / ρ - 1))
          = -(x ^ (1 / ρ - 1)) * (Real.log x / ρ - 1) := by ring
      rw [hAB', hnum]
      have hnn : 0 ≤ x ^ (1 / ρ - 1) * (Real.log x / ρ - 1) :=
        mul_nonneg hB.le (by linarith)
      have hnumle : (-(x ^ (1 / ρ - 1))) * (Real.log x / ρ - 1) ≤ 0 := by
        have hrw : (-(x ^ (1 / ρ - 1))) * (Real.log x / ρ - 1)
            = -(x ^ (1 / ρ - 1) * (Real.log x / ρ - 1)) := by ring
        rw [hrw, neg_nonpos]
        exact hnn
      exact div_nonpos_of_nonpos_of_nonneg hnumle (pow_nonneg hA.le 2)
  intro m hm
  have hstep : (t * u) ^ ρ ≤ (m : ℝ) :=
    le_trans (Nat.le_ceil _) (by exact_mod_cast hm)
  exact lt_of_le_of_lt (hanti heρ (le_trans heρ hstep) hstep) hfmup

/-- Fixed arXiv:2608.17653v1, Lemma 4.1, Eqs. (4.1)–(4.2), p. 18 (claim c006,
same result as `lemma_four_one_log_threshold`). -/
theorem claim_c006_lemma_four_one
    (ρ C : ℝ) (hρ : 1 < ρ) (hC : 0 < C)
    (hC0 : C ≤ Real.log 2 / (2 : ℝ) ^ (1 / ρ)) :
    ∀ m : ℕ,
      Nat.ceil ((ρ / C * (Real.log (ρ / C) + Real.log (Real.log (ρ / C)) + 1)) ^ ρ) ≤ m →
      Real.log (m : ℝ) / (m : ℝ) ^ (1 / ρ) < C :=
  lemma_four_one_log_threshold ρ C hρ hC hC0

end Qatlib.Papers.SlowHamSim26.FourierTrunc
end
