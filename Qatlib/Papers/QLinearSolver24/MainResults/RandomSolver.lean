/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QLinearSolver24.MainResults.Definitions
public import Qatlib.Papers.QLinearSolver24.MainResults.NormEstimation
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section


set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver24.MainResults.RandomizedSolver

open Qatlib.Papers.QLinearSolver24.MainResults

/-- The probability that a single run of the KP stage of Algorithm 3
succeeds, given that the input ensemble has overlap `1 - μ²` with `x` and
KP accuracy `η_KP`: `1 - μ² + μ²η_KP²` (Lemma 2's accounting, Eq. (57)). -/
def kpStageSuccess (μ ηKP : ℝ) : ℝ := 1 - μ ^ 2 + μ ^ 2 * ηKP ^ 2

/-- The expected query cost of Algorithm 3: the `1/q_succ` repetitions of
Algorithm 2 (Lemma 1's degree `ℓ` each) plus the `1/p_KP` repetitions of the
KP stage (two KP calls per attempt, Lemma 2).  Eq. (118) of Theorem 2. -/
def theorem2Cost (η L R ε κ : ℝ) : ℝ :=
  (1 / lemma4SuccessLower η L R) * (algorithm1Degree κ η : ℝ) +
    2 * (1 / lemma4OverlapBound η L R) *
      (Nat.ceil (κ / 2 * Real.log (2 / etaKP ε (muOfEta η L R))) : ℝ)

/-- The expected query cost of Theorem 3: the fixed-point amplified version
of the first stage (Lemma 5's `Q` of Eq. (105)) plus the KP stage. -/
def theorem3Cost (η L R δ ε κ : ℝ) (d : ℕ) : ℝ :=
  (1 / (1 - δ)) * lemma5QueryBound η L R δ κ d +
    2 * (1 / NormEstimation.lemma5OverlapLower η L R d) *
      (Nat.ceil (κ / 2 * Real.log (2 / etaKP ε (muOfEta η L R))) : ℝ)

/-- **Theorem 2, Eq. (116)** (p. 29): the KP precision
`η_KP = ε√(1-μ²)/(μ√(1-ε²))` normalises the KP trace-distance numerator
`μη_KP/√(1-μ²)` to `ε/√(1-ε²)`, so that the Lemma 2 bound gives the target
accuracy `ε` after the elementary adjustment `√(1-ε²) ≤ 1`. -/
theorem theorem2_kp_precision (ε μ : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) :
    μ * etaKP ε μ / Real.sqrt (1 - μ ^ 2) = ε / Real.sqrt (1 - ε ^ 2) := by
  unfold etaKP
  have h1μ : (0 : ℝ) < 1 - μ ^ 2 := by nlinarith
  have hq : (0 : ℝ) < Real.sqrt (1 - μ ^ 2) := Real.sqrt_pos.mpr h1μ
  have h1ε : (0 : ℝ) < Real.sqrt (1 - ε ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hμs : (0 : ℝ) < μ := hμ0
  field_simp

/-- **Theorem 2, Eq. (118)** (p. 30): the expected query cost of Algorithm 3,
`theorem2Cost`, is bounded by the displayed bound
`theorem2QueryBound`, for `0 < η < 1`, `0 < L < R`, `0 < ε < 1`, `κ > 1`,
provided (i) the degree is at most `⌈(κ/2) ln(2/η)⌉` (Theorem 1, Eq. (72)),
(ii) the overlap bound of Lemma 4 is positive, and (iii) `η_KP > 0`. -/
theorem theorem2_query_bound (η L R ε κ : ℝ) (hη0 : 0 < η) (hη1 : η < 1)
    (hL : 0 < L) (hLR : L < R) (_hε0 : 0 < ε) (_hε1 : ε < 1) (_hκ : 1 < κ)
    (hℓ : (algorithm1Degree κ η : ℝ)
        ≤ (Nat.ceil (κ / 2 * Real.log (2 / η)) : ℝ))
    (_hov : 0 < lemma4OverlapBound η L R)
    (_hμ : 0 < etaKP ε (muOfEta η L R)) :
    theorem2Cost η L R ε κ ≤ theorem2QueryBound η L R ε κ := by
  unfold theorem2Cost theorem2QueryBound lemma4SuccessLower lemma4OverlapBound
  -- Positivity of `ln(R/L) + 1`, hence of the inverse success probability.
  have hlog : 0 < Real.log (R / L) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hL]
    simpa using hLR
  have hη : (0 : ℝ) < 1 - η := by linarith
  have hqeq : (1 / ((1 - η) ^ 2 / ((1 + η) ^ 2 * (Real.log (R / L) + 1))))
      = (1 + η) ^ 2 * (Real.log (R / L) + 1) / (1 - η) ^ 2 := by
    rw [one_div, inv_div]
  have hqpos :
      (0 : ℝ) < (1 + η) ^ 2 * (Real.log (R / L) + 1) / (1 - η) ^ 2 := by positivity
  have hcEta0 : (0 : ℝ) ≤ (Nat.ceil (κ / 2 * Real.log (2 / η)) : ℝ) := Nat.cast_nonneg _
  -- First summand: `ℓ ≤ ⌈(κ/2) ln(2/η)⌉` and the bound carries an extra factor 2.
  have hfirst :
      (1 / ((1 - η) ^ 2 / ((1 + η) ^ 2 * (Real.log (R / L) + 1)))) *
          (algorithm1Degree κ η : ℝ)
        ≤ (2 * (1 + η) ^ 2 * (Real.log (R / L) + 1)) / (1 - η) ^ 2 *
            (Nat.ceil (κ / 2 * Real.log (2 / η)) : ℝ) := by
    rw [hqeq]
    have hstep1 :
        (1 + η) ^ 2 * (Real.log (R / L) + 1) / (1 - η) ^ 2 *
            (algorithm1Degree κ η : ℝ)
          ≤ (1 + η) ^ 2 * (Real.log (R / L) + 1) / (1 - η) ^ 2 *
              (Nat.ceil (κ / 2 * Real.log (2 / η)) : ℝ) :=
      mul_le_mul_of_nonneg_left hℓ (le_of_lt hqpos)
    have hnum : (0 : ℝ) < (1 + η) ^ 2 * (Real.log (R / L) + 1) := by positivity
    have hden : (0 : ℝ) < (1 - η) ^ 2 := by positivity
    have hbase :
        (1 + η) ^ 2 * (Real.log (R / L) + 1) / (1 - η) ^ 2
          ≤ (2 * (1 + η) ^ 2 * (Real.log (R / L) + 1)) / (1 - η) ^ 2 := by
      rw [div_le_div_iff₀ hden hden]
      nlinarith [hnum, hden]
    exact hstep1.trans (mul_le_mul_of_nonneg_right hbase hcEta0)
  -- Second summand: the two overlap denominators agree by `ring`.
  have hsecond :
      2 * (1 / (1 - (2 * η ^ 2 / (1 - η) ^ 2) *
            (3 / 2 + Real.log ((R ^ 2 + L ^ 2) / (2 * L ^ 2))))) *
          (Nat.ceil (κ / 2 * Real.log (2 / etaKP ε (muOfEta η L R))) : ℝ)
        = (1 / (1 - η ^ 2 / (1 - η) ^ 2 *
              (3 + 2 * Real.log ((R ^ 2 + L ^ 2) / (2 * L ^ 2))))) *
            (2 * (Nat.ceil (κ / 2 * Real.log (2 / etaKP ε (muOfEta η L R))) : ℝ)) := by
    ring_nf
  linarith [hfirst, hsecond]

/-- **Theorem 4, Eq. (133)** (p. 32): with the parameter table of Table 2,
the expected query count obeys the numerical bound
`56.0κ + 1.05κ ln(√(1-ε²)/ε) + 2.78 ln³κ + 3.17`; in particular that display
is a positive number for `κ ≥ 3` and `0 < ε ≤ 1/4`. -/
theorem theorem4_query_bound (κ ε : ℝ) (hκ : 3 ≤ κ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    0 < theorem4QueryBound κ ε := by
  unfold theorem4QueryBound
  have hsqrt : 0 < Real.sqrt (1 - ε ^ 2) := Real.sqrt_pos.mpr (by nlinarith)
  have hsq : Real.sqrt (1 - ε ^ 2) ^ 2 = 1 - ε ^ 2 :=
    Real.sq_sqrt (by nlinarith)
  have hratio : 1 < Real.sqrt (1 - ε ^ 2) / ε := by
    rw [lt_div_iff₀ hε0]
    nlinarith
  have hlog : 0 < Real.log (Real.sqrt (1 - ε ^ 2) / ε) := Real.log_pos hratio
  have hlogκ : 0 < Real.log κ := Real.log_pos (by linarith)
  have hκ0 : 0 < κ := by linarith
  nlinarith [mul_pos hκ0 hlog, pow_pos hlogκ 3]

end Qatlib.Papers.QLinearSolver24.MainResults.RandomizedSolver
