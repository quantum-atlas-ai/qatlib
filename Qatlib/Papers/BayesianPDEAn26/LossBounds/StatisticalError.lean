/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BayesianPDEAn26.LossBounds.LossDefinitions
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 4.3 — statistical error for normalized-loss estimation

Fixed source: arXiv:2608.27028v1, Lemma 4.3 and its proof, pp.14–15.

## Source content

The infinite-shot normalized loss and its finite-shot estimator are (p.14, Eq. (3.6))

`L̃_norm = 2 − (4 p_H − 2)/√p_succ`,   `L̂_norm = 2 − (4 p̂_H − 2)/√p̂_succ`,

where `p̂_H`, `p̂_succ` are the empirical frequencies from `N_H` independent
Hadamard-test Bernoulli measurements and `N_q` projected-success measurements.
For `0 < ε_stat ≤ 1` the proof uses the simultaneous concentration event

`|p̂_H − p_H| ≤ ε_stat √p_succ / 16`,  `|p̂_succ − p_succ| ≤ ε_stat p_succ / 8`,

on which `p̂_succ ≥ (1 − ε_stat/8) p_succ ≥ (7/8) p_succ > 0` and
`|L̂_norm − L̃_norm| < ε_stat`. Hoeffding and multiplicative Chernoff bound the
failure probability by
`2 exp(−N_H p_succ ε_stat²/128) + 2 exp(−N_q p_succ ε_stat²/192)`;
`N_H ≥ 128 log(4/ρ)/(p_succ ε_stat²)` and `N_q ≥ 192 log(4/ρ)/(p_succ ε_stat²)`
make this `≤ ρ` by the union bound, giving
`P(|L̂_norm − L̃_norm| ≤ ε_stat) ≥ 1 − ρ`.

## Lean model

The sample space is the finite product `(Fin N_H → Bool) × (Fin N_q → Bool)` with
the product of Bernoulli laws; `empiricalFreq` is the empirical frequency. The
deterministic concentration-to-estimator step is proved in full
(`estimator_deviation_bound`, credited to c003 as `partial_support`). The
Hoeffding/multiplicative-Chernoff tail with union bound
(`concentration_event_mass`) and the combined Lemma 4.3 statement
(`normalizedLoss_statistical_error`) are not formalized: the second tail is
multiplicative in `p_succ`, beyond additive sub-Gaussian Hoeffding, and the
Bernoulli product tail instantiation is not yet wired up.  Both statements are
preserved in this branch's history; the sampling vocabulary
(`bernoulliMeasure`, `empiricalFreq`, `sampleMeasure`, `estLoss`) is retained.

The hypothesis `hCS : |2 p_H − 1| ≤ √p_succ` is not an extra mathematical
assumption: it is the source's Cauchy–Schwarz relation
`|2p_H − 1| = |Re⟨ψ_obs|ψ_T⟩| ≤ ‖P_u|ψ_T⟩‖ = √p_succ` (p.14, immediately after
the Lemma). We carry it explicitly because the Hilbert-space states are not
modelled here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Qatlib.Papers.BayesianPDEAn26.LossBounds

/-- Bernoulli law on `Bool` with mass `p` on `true` and `1 − p` on `false`. -/
def bernoulliMeasure (p : ℝ) : Measure Bool :=
  ENNReal.ofReal (1 - p) • Measure.dirac false + ENNReal.ofReal p • Measure.dirac true

/-- The Bernoulli law is a probability measure for `0 ≤ p ≤ 1`. -/
lemma isProbabilityMeasure_bernoulliMeasure (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    IsProbabilityMeasure (bernoulliMeasure p) where
  measure_univ := by
    have hfalse : (Measure.dirac false : Measure Bool) Set.univ = 1 := by simp
    have htrue : (Measure.dirac true : Measure Bool) Set.univ = 1 := by simp
    simp only [bernoulliMeasure, Measure.add_apply, Measure.smul_apply, smul_eq_mul,
      hfalse, htrue, mul_one]
    have hsum : (1 - p) + p = 1 := by ring
    rw [← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ 1 - p) h0, hsum]
    simp

/-- Empirical frequency of `true` among `n` Bernoulli samples. -/
def empiricalFreq {n : ℕ} (ω : Fin n → Bool) : ℝ :=
  ((Finset.univ.filter (fun i => ω i = true)).card : ℝ) / n

/-- The product sample measure of `N_H` Hadamard-test and `N_q` projected-success
measurements. -/
def sampleMeasure (pH pSucc : ℝ) (NH Nq : ℕ) :
    Measure ((Fin NH → Bool) × (Fin Nq → Bool)) :=
  (Measure.pi (fun _ : Fin NH => bernoulliMeasure pH)).prod
    (Measure.pi (fun _ : Fin Nq => bernoulliMeasure pSucc))

/-- Finite-shot normalized-loss estimator, p.14:
`L̂_norm = 2 − (4 p̂_H − 2)/√p̂_succ`. -/
def estLoss (pH pSucc : ℝ) : ℝ := 2 - (4 * pH - 2) / Real.sqrt pSucc

/-- **Deterministic core of Lemma 4.3** (arXiv:2608.27028v1, p.15). On the
simultaneous concentration event the finite-shot estimator is within `ε` of the
infinite-shot loss. This is the algebraic half of the source proof, fully
formalized. -/
theorem estimator_deviation_bound
    (pH pSucc pHat pHatSucc ε : ℝ)
    (hSuccPos : 0 < pSucc) (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (hCS : |2 * pH - 1| ≤ Real.sqrt pSucc)
    (hH : |pHat - pH| ≤ ε * Real.sqrt pSucc / 16)
    (hS : |pHatSucc - pSucc| ≤ ε * pSucc / 8) :
    |estLoss pHat pHatSucc - estLoss pH pSucc| ≤ ε := by
  set a : ℝ := Real.sqrt pSucc with ha_def
  set b : ℝ := Real.sqrt pHatSucc with hb_def
  have ha_pos : 0 < a := Real.sqrt_pos.mpr hSuccPos
  have ha_sq : a ^ 2 = pSucc := Real.sq_sqrt hSuccPos.le
  -- `p̂_succ ≥ (7/8) p_succ > 0`, hence `b > 0` and `b² ≥ (7/8) p_succ`.
  have hSuccHat_pos : 0 < pHatSucc := by
    have h1 : pSucc - pHatSucc ≤ ε * pSucc / 8 := by
      have := neg_le_abs (pHatSucc - pSucc); linarith
    nlinarith
  have hb_pos : 0 < b := Real.sqrt_pos.mpr hSuccHat_pos
  have hb_sq : b ^ 2 = pHatSucc := Real.sq_sqrt hSuccHat_pos.le
  have hb_sq_ge : (7 / 8) * pSucc ≤ b ^ 2 := by
    have h1 : pSucc - pHatSucc ≤ ε * pSucc / 8 := by
      have := neg_le_abs (pHatSucc - pSucc); linarith
    rw [hb_sq]
    nlinarith
  -- First term: `4|p̂_H − p_H|/a ≤ ε/4`.
  have hterm1 : 4 * |pHat - pH| / a ≤ ε / 4 := by
    rw [div_le_iff₀ ha_pos]
    have h := hH
    rw [abs_sub_comm (pHat) (pH)] at h
    nlinarith
  -- Second term: `|4p̂_H − 2| ≤ (9/4) a`.
  have hfour : |4 * pHat - 2| ≤ (9 / 4) * a := by
    have hsplit : 4 * pHat - 2 = 4 * (pHat - pH) + (4 * pH - 2) := by ring
    rw [hsplit]
    have hCS' : |4 * pH - 2| ≤ 2 * a := by
      have : |4 * pH - 2| = 2 * |2 * pH - 1| := by
        rw [show (4 : ℝ) * pH - 2 = 2 * (2 * pH - 1) by ring, abs_mul]
        norm_num
      rw [this]; linarith
    calc |4 * (pHat - pH) + (4 * pH - 2)|
        ≤ |4 * (pHat - pH)| + |4 * pH - 2| := abs_add_le _ _
      _ = 4 * |pHat - pH| + |4 * pH - 2| := by
            rw [abs_mul]; norm_num
      _ ≤ 4 * (ε * a / 16) + 2 * a := by
            have h := hH; rw [abs_sub_comm (pHat) (pH)] at h; linarith
      _ ≤ (9 / 4) * a := by nlinarith
  -- Exact reciprocal difference: `|1/a − 1/b| = |p̂_succ − p_succ|/(a b (a+b))`.
  have hrec : |1 / a - 1 / b| = |pHatSucc - pSucc| / (a * b * (a + b)) := by
    have hab_pos : 0 < a + b := by linarith
    have hba : |b - a| = |pHatSucc - pSucc| / (a + b) := by
      have hfac : (b - a) * (a + b) = pHatSucc - pSucc := by
        rw [← hb_sq, ← ha_sq]; ring
      have h2 : |b - a| * (a + b) = |pHatSucc - pSucc| := by
        rw [← abs_of_pos hab_pos, ← abs_mul, hfac]
      rw [eq_div_iff hab_pos.ne']
      exact h2
    rw [show (1 : ℝ) / a - 1 / b = a⁻¹ - b⁻¹ by simp [one_div]]
    rw [inv_sub_inv ha_pos.ne' hb_pos.ne']
    rw [abs_div, abs_mul, abs_of_pos ha_pos, abs_of_pos hb_pos]
    rw [hba, div_div, mul_comm (a + b) (a * b)]
  -- Bound the second term by `9ε/28`.
  have hterm2 : |4 * pHat - 2| * |1 / a - 1 / b| ≤ 9 * ε / 28 := by
    rw [hrec]
    have hden_ge : (7 / 8 : ℝ) * pSucc ≤ b * (a + b) := by
      have : b * b ≤ b * (a + b) := by
        exact mul_le_mul_of_nonneg_left (by linarith) hb_pos.le
      nlinarith [hb_sq_ge]
    have hden_pos : 0 < b * (a + b) := by positivity
    have hquot : |pHatSucc - pSucc| / (b * (a + b)) ≤ ε / 7 := by
      rw [div_le_iff₀ hden_pos]
      have h2 : (ε / 7) * ((7 / 8) * pSucc) = ε * pSucc / 8 := by ring
      have h3 : (ε / 7) * ((7 / 8) * pSucc) ≤ (ε / 7) * (b * (a + b)) :=
        mul_le_mul_of_nonneg_left hden_ge (by positivity)
      linarith [hS, h2, h3]
    have hX : 0 ≤ |pHatSucc - pSucc| / (a * b * (a + b)) := by positivity
    calc |4 * pHat - 2| * (|pHatSucc - pSucc| / (a * b * (a + b)))
        ≤ ((9 / 4) * a) * (|pHatSucc - pSucc| / (a * b * (a + b))) :=
          mul_le_mul_of_nonneg_right hfour hX
      _ = (9 / 4) * (|pHatSucc - pSucc| / (b * (a + b))) := by
          field_simp
      _ ≤ (9 / 4) * (ε / 7) :=
          mul_le_mul_of_nonneg_left hquot (by norm_num)
      _ = 9 * ε / 28 := by ring
  -- Assemble: `D = 4(p_H − p̂_H)/a + (4p̂_H − 2)(1/a − 1/b)`.
  have hdecomp : estLoss pHat pHatSucc - estLoss pH pSucc =
      4 * (pH - pHat) / a + (4 * pHat - 2) * (1 / a - 1 / b) := by
    rw [estLoss, estLoss]
    rw [ha_def, hb_def]
    field_simp <;> ring
  have htermA : |4 * (pH - pHat) / a| = 4 * |pHat - pH| / a := by
    rw [abs_div, abs_mul, abs_of_pos ha_pos, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4),
      abs_sub_comm (pH) (pHat)]
  have htermB : |(4 * pHat - 2) * (1 / a - 1 / b)| =
      |4 * pHat - 2| * |1 / a - 1 / b| := by
    rw [abs_mul]
  rw [hdecomp]
  calc |4 * (pH - pHat) / a + (4 * pHat - 2) * (1 / a - 1 / b)|
      ≤ |4 * (pH - pHat) / a| + |(4 * pHat - 2) * (1 / a - 1 / b)| := abs_add_le _ _
    _ = 4 * |pHat - pH| / a +
          |4 * pHat - 2| * |1 / a - 1 / b| := by rw [htermA, htermB]
    _ ≤ ε / 4 + 9 * ε / 28 := by
          linarith [hterm1, hterm2]
    _ ≤ ε := by nlinarith

end Qatlib.Papers.BayesianPDEAn26.LossBounds
