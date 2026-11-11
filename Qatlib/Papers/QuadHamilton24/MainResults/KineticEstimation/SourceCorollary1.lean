/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuadHamilton24.MainResults.QuadHamiltonModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 1 (multiplicative kinetic-energy estimate for `b = 0`)

Source: arXiv:2404.07303, §4, Corollary 1 and (4.54)–(4.59), page 26.

The source shows that when the source term vanishes, the kinetic-energy estimate can be
made multiplicative: `|K − K̂| ≤ ε K`.  The proof combines the quadratic decomposition
(4.55), the componentwise relative velocity error (4.56) of Lemma 13, and the elementary
identity
`|q̇ᵢ² − q̇̂ᵢ²| = |q̇ᵢ − q̇̂ᵢ| |q̇ᵢ + q̇̂ᵢ| ≤ ε₁ (2 + ε₁) q̇ᵢ²` (4.57),
then chooses `γ = ε₁ = ε/16` to absorb all coefficients (4.58)–(4.59).

Fully proved here: the component factor (4.57) and the coefficient arithmetic
(4.58) ⇒ (4.59).  The quantum algorithm that produces `K̂` and the decomposition
(4.55) are the algorithmic premise, recorded as the hypothesis.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QuadHamilton24.MainResults

/-- **Corollary 1, (4.56) ⇒ (4.57).**  If the `i`-th velocity component has relative
error `|q̇ᵢ − q̇̂ᵢ| ≤ ε₁ q̇ᵢ` (`q̇ᵢ ≥ 0`), then
`|q̇ᵢ² − q̇̂ᵢ²| ≤ ε₁ (2 + ε₁) q̇ᵢ²`. -/
theorem quad_error_factor (q qhat ε₁ : ℝ) (hq : 0 ≤ q) (hε₁ : 0 ≤ ε₁)
    (h : |q - qhat| ≤ ε₁ * q) :
    |q ^ 2 - qhat ^ 2| ≤ ε₁ * (2 + ε₁) * q ^ 2 := by
  have h' : |qhat - q| ≤ ε₁ * q := by simpa [abs_sub_comm] using h
  have h2 : |q + qhat| ≤ (2 + ε₁) * q := by
    calc |q + qhat| = |2 * q + (qhat - q)| := by ring_nf
      _ ≤ |2 * q| + |qhat - q| := abs_add_le _ _
      _ = 2 * q + |qhat - q| := by
        rw [abs_mul, abs_of_nonneg hq]
        norm_num
      _ ≤ 2 * q + ε₁ * q := by linarith
      _ = (2 + ε₁) * q := by ring
  calc |q ^ 2 - qhat ^ 2| = |q - qhat| * |q + qhat| := by
        rw [show q ^ 2 - qhat ^ 2 = (q - qhat) * (q + qhat) by ring, abs_mul]
    _ ≤ (ε₁ * q) * ((2 + ε₁) * q) :=
        mul_le_mul h h2 (abs_nonneg _) (by positivity)
    _ = ε₁ * (2 + ε₁) * q ^ 2 := by ring

/-- **Corollary 1, (4.58) ⇒ (4.59).**  With the source's choice `γ = ε₁ = ε/16`, the
coefficient of `K` on the right of (4.58) is at most `ε` for `0 < ε ≤ 1`, so
`|K − K̂| ≤ ε K`. -/
theorem corollary1_coefficient_absorption (K Khat ε ε₁ γ : ℝ)
    (hK : 0 ≤ K) (hε : 0 < ε) (hsmall : ε ≤ 1)
    (h : |K - Khat| ≤ (ε₁ * (2 + ε₁) * (1 + γ * (2 + γ)) + γ * (2 + γ)) * K)
    (hγ : γ = ε₁) (hε₁ : ε₁ = ε / 16) :
    |K - Khat| ≤ ε * K := by
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hK)
  subst hγ
  subst hε₁
  have ht0 : (0 : ℝ) ≤ ε / 16 := by positivity
  have ht : ε / 16 ≤ 1 / 16 := by nlinarith
  have h2 : 2 + ε / 16 ≤ 3 := by nlinarith
  have hprod0 : (0 : ℝ) ≤ ε / 16 * (2 + ε / 16) :=
    mul_nonneg ht0 (by linarith)
  have hc : ε / 16 * (2 + ε / 16) ≤ 1 := by
    have h := mul_le_mul ht h2 (by linarith : (0 : ℝ) ≤ 2 + ε / 16)
      (by norm_num : (0 : ℝ) ≤ 1 / 16)
    nlinarith
  have hc2 : 1 + ε / 16 * (2 + ε / 16) ≤ 2 := by linarith
  have hA : (2 + ε / 16) * (1 + ε / 16 * (2 + ε / 16)) ≤ 6 := by
    have h := mul_le_mul h2 hc2 (by linarith : (0 : ℝ) ≤ 1 + ε / 16 * (2 + ε / 16))
      (by norm_num : (0 : ℝ) ≤ 3)
    nlinarith
  have hsum :
      (2 + ε / 16) * (1 + ε / 16 * (2 + ε / 16)) + (2 + ε / 16) ≤ 9 := by linarith
  calc ε / 16 * (2 + ε / 16) * (1 + ε / 16 * (2 + ε / 16)) + ε / 16 * (2 + ε / 16)
      = ε / 16 * ((2 + ε / 16) * (1 + ε / 16 * (2 + ε / 16)) + (2 + ε / 16)) := by ring
    _ ≤ ε / 16 * 9 := mul_le_mul_of_nonneg_left hsum ht0
    _ ≤ ε := by nlinarith

/-- **Corollary 1 (§4, (4.54)).**  The algorithmic conclusion: there is an estimate
`K̂` of the kinetic energy with multiplicative error at most `ε`, whenever the source
term vanishes.  Formalised here as the existence of the multiplicative error constant
`ε' ≤ ε` (with `ε' = ε`), given the Section-4 error output (4.55)–(4.58).  The
construction of `K̂` is the algorithmic premise; the analytic coefficient chain is
`corollary1_coefficient_absorption`. -/
theorem corollary1_multiplicative_estimate (K Khat ε ε₁ γ : ℝ)
    (hK : 0 ≤ K) (hε : 0 < ε) (hsmall : ε ≤ 1)
    (h : |K - Khat| ≤ (ε₁ * (2 + ε₁) * (1 + γ * (2 + γ)) + γ * (2 + γ)) * K)
    (hγ : γ = ε₁) (hε₁ : ε₁ = ε / 16) :
    ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ ε ∧ |K - Khat| ≤ ε' * K :=
  ⟨ε, hε, le_refl ε,
    corollary1_coefficient_absorption K Khat ε ε₁ γ hK hε hsmall h hγ hε₁⟩

end Qatlib.Papers.QuadHamilton24.MainResults
