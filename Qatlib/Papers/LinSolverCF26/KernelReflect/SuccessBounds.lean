/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# `SuccessBounds` — post-selection success probability of the KR step

Source: P. C. S. Costa, A. M. Dalzell, D. An, D. W. Berry,
*Constant Factor Analysis of Optimal Quantum Linear Solvers in Practice*,
arXiv:2604.22185v2 (fixed version), Section II B, Eqs. (12)–(15), and
Appendix A, Eqs. (A27)–(A28).

After the approximate kernel reflection, the post-selected register is
proportional to `cos θ sin θ (2 − δ₁′) |x⟩ + δ₂′ sin θ |z⟩` (Eq. (13)), so the
probability that all ancillas are measured in `|0⟩` is Eq. (14):

`p_succ = ¼ sin²(2θ) (2 − δ₁′)² + (δ₂′)² sin²θ`.

The reflection errors obey (Eq. (A27), (A28), with `η = η_KR`)
`√((δ₁′)² + (δ₂′)²) ≤ 4η/(1+η)` and `|δ₂′| ≤ 2η/(1+η)`. From these we derive
the two-sided bound Eq. (15):
`sin²(2θ) ((1−η)/(1+η))² ≤ p_succ ≤ sin²(2θ) + 4η/(1+η)²`.
All results below are exact real inequalities.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LinSolverCF26.KernelReflect.SuccessBounds

/-- Eq. (14): total success probability of the KR step, as a function of the
rotation angle `θ` and the two reflection errors `δ₁′`, `δ₂′`. -/
def pSucc (θ δ1 δ2 : ℝ) : ℝ :=
  (1 / 4) * Real.sin (2 * θ) ^ 2 * (2 - δ1) ^ 2 + δ2 ^ 2 * Real.sin θ ^ 2

/-- Eq. (13) ⇒ Eq. (14): the success probability is the squared norm of the
unnormalised post-selected amplitudes `sin θ cos θ (2 − δ₁′)` and
`δ₂′ sin θ`, using `sin(2θ) = 2 sin θ cos θ`. -/
theorem pSucc_eq_amplitudes (θ δ1 δ2 : ℝ) :
    pSucc θ δ1 δ2 =
      (Real.sin θ * Real.cos θ * (2 - δ1)) ^ 2 + (δ2 * Real.sin θ) ^ 2 := by
  unfold pSucc
  rw [Real.sin_two_mul]
  ring

/-- For `δ₁′ ≥ 0`, the first root obeys `δ₁′ ≤ √((δ₁′)² + (δ₂′)²)`. -/
lemma le_sqrt_sq_add {δ1 δ2 : ℝ} (hd1 : 0 ≤ δ1) :
    δ1 ≤ Real.sqrt (δ1 ^ 2 + δ2 ^ 2) := by
  have h1 : δ1 ^ 2 ≤ δ1 ^ 2 + δ2 ^ 2 := by nlinarith [sq_nonneg δ2]
  have h2 : Real.sqrt (δ1 ^ 2) ≤ Real.sqrt (δ1 ^ 2 + δ2 ^ 2) :=
    Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq hd1] at h2

/-- Scalar core of the lower bound in Eq. (15): under Eq. (A28), the coefficient
`¼ (2 − δ₁′)²` dominates `((1−η)/(1+η))²`. -/
lemma lower_coeff {δ1 δ2 η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hd1 : 0 ≤ δ1)
    (hsqrt : Real.sqrt (δ1 ^ 2 + δ2 ^ 2) ≤ 4 * η / (1 + η)) :
    ((1 - η) / (1 + η)) ^ 2 ≤ (1 / 4) * (2 - δ1) ^ 2 := by
  have hdpos : 0 < 1 + η := by linarith
  have h4 : δ1 ≤ 4 * η / (1 + η) := le_trans (le_sqrt_sq_add hd1) hsqrt
  have hmult : δ1 * (1 + η) ≤ 4 * η := (le_div_iff₀ hdpos).mp h4
  have hmain : 2 * (1 - η) ≤ (2 - δ1) * (1 + η) := by nlinarith [hmult]
  have hnonneg : 0 ≤ 2 * (1 - η) := by nlinarith [hη1]
  have hpow : (2 * (1 - η)) ^ 2 ≤ ((2 - δ1) * (1 + η)) ^ 2 :=
    pow_le_pow_left₀ hnonneg hmain 2
  rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + η) ^ 2)]
  nlinarith [hpow]

/-- Scalar core of the upper bound in Eq. (15): under Eq. (A28), the coefficient
`¼ (2 − δ₁′)²` is at most `1`. -/
lemma upper_coeff_one {δ1 η : ℝ} (hη0 : 0 ≤ η) (hd1 : 0 ≤ δ1)
    (h4 : δ1 ≤ 4 * η / (1 + η)) :
    (1 / 4) * (2 - δ1) ^ 2 ≤ 1 := by
  have hdpos : 0 < 1 + η := by linarith
  have hδ1le4 : δ1 ≤ 4 := by
    have hle : 4 * η / (1 + η) ≤ 4 := by
      rw [div_le_iff₀ hdpos]
      nlinarith [hη0]
    linarith [le_trans h4 hle]
  nlinarith [hd1, hδ1le4]

/-- Scalar core of the upper bound in Eq. (15): under Eq. (A28), the second
coefficient satisfies `(δ₂′)² ≤ 4η/(1+η)²`. -/
lemma upper_coeff_two {δ2 η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hd2 : |δ2| ≤ 2 * η / (1 + η)) :
    δ2 ^ 2 ≤ 4 * η / (1 + η) ^ 2 := by
  have hdpos : 0 < 1 + η := by linarith
  have hc0 : 0 ≤ 2 * η / (1 + η) := by positivity
  have h2 : δ2 ^ 2 ≤ (2 * η / (1 + η)) ^ 2 := by
    have h := pow_le_pow_left₀ (abs_nonneg δ2) hd2 2
    rwa [sq_abs] at h
  have h3 : (2 * η / (1 + η)) ^ 2 ≤ 4 * η / (1 + η) ^ 2 := by
    rw [div_pow, div_le_iff₀ (by positivity : (0 : ℝ) < (1 + η) ^ 2)]
    have hcancel : 4 * η / (1 + η) ^ 2 * (1 + η) ^ 2 = 4 * η := by
      field_simp
    rw [hcancel]
    nlinarith [mul_nonneg hη0 (show (0 : ℝ) ≤ 1 - η by linarith)]
  linarith [h2, h3]

/-- Eq. (15), lower bound: with `η = η_KR` and the reflection-error relations of
Eq. (A28), the KR success probability is at least
`sin²(2θ) ((1−η)/(1+η))²`. -/
theorem pSucc_lower {θ δ1 δ2 η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hd1 : 0 ≤ δ1)
    (hsqrt : Real.sqrt (δ1 ^ 2 + δ2 ^ 2) ≤ 4 * η / (1 + η)) :
    Real.sin (2 * θ) ^ 2 * ((1 - η) / (1 + η)) ^ 2 ≤ pSucc θ δ1 δ2 := by
  have hkey := lower_coeff hη0 hη1 hd1 hsqrt
  have hs : 0 ≤ Real.sin (2 * θ) ^ 2 := sq_nonneg _
  have h1 : Real.sin (2 * θ) ^ 2 * ((1 - η) / (1 + η)) ^ 2 ≤
      Real.sin (2 * θ) ^ 2 * ((1 / 4) * (2 - δ1) ^ 2) :=
    mul_le_mul_of_nonneg_left hkey hs
  have h2 : 0 ≤ δ2 ^ 2 * Real.sin θ ^ 2 :=
    mul_nonneg (sq_nonneg δ2) (sq_nonneg _)
  unfold pSucc
  nlinarith [h1, h2]

/-- Eq. (15), upper bound: with `η = η_KR` and the reflection-error relations of
Eq. (A28), the KR success probability is at most
`sin²(2θ) + 4η/(1+η)²`. -/
theorem pSucc_upper {θ δ1 δ2 η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hd1 : 0 ≤ δ1)
    (hsqrt : Real.sqrt (δ1 ^ 2 + δ2 ^ 2) ≤ 4 * η / (1 + η))
    (hd2 : |δ2| ≤ 2 * η / (1 + η)) :
    pSucc θ δ1 δ2 ≤ Real.sin (2 * θ) ^ 2 + 4 * η / (1 + η) ^ 2 := by
  have h4 : δ1 ≤ 4 * η / (1 + η) := le_trans (le_sqrt_sq_add hd1) hsqrt
  have hb1 := upper_coeff_one hη0 hd1 h4
  have hb2 := upper_coeff_two hη0 hη1 hd2
  have hsin2 : 0 ≤ Real.sin (2 * θ) ^ 2 := sq_nonneg _
  have hsin : Real.sin θ ^ 2 ≤ 1 := Real.sin_sq_le_one θ
  have hsin0 : 0 ≤ Real.sin θ ^ 2 := sq_nonneg _
  have hb2nonneg : 0 ≤ 4 * η / (1 + η) ^ 2 := by positivity
  have hterm1 : (1 / 4) * Real.sin (2 * θ) ^ 2 * (2 - δ1) ^ 2 ≤
      Real.sin (2 * θ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hb1 hsin2
    nlinarith [h]
  have hterm2 : δ2 ^ 2 * Real.sin θ ^ 2 ≤ 4 * η / (1 + η) ^ 2 := by
    have h := mul_le_mul hb2 hsin hsin0 hb2nonneg
    simpa using h
  unfold pSucc
  linarith [hterm1, hterm2]

/-- Eq. (15) combined: the two-sided success-probability bound. -/
theorem pSucc_two_sided {θ δ1 δ2 η : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1)
    (hd1 : 0 ≤ δ1)
    (hsqrt : Real.sqrt (δ1 ^ 2 + δ2 ^ 2) ≤ 4 * η / (1 + η))
    (hd2 : |δ2| ≤ 2 * η / (1 + η)) :
    Real.sin (2 * θ) ^ 2 * ((1 - η) / (1 + η)) ^ 2 ≤ pSucc θ δ1 δ2 ∧
      pSucc θ δ1 δ2 ≤ Real.sin (2 * θ) ^ 2 + 4 * η / (1 + η) ^ 2 :=
  ⟨pSucc_lower hη0 hη1 hd1 hsqrt, pSucc_upper hη0 hη1 hd1 hsqrt hd2⟩

end Qatlib.Papers.LinSolverCF26.KernelReflect.SuccessBounds
