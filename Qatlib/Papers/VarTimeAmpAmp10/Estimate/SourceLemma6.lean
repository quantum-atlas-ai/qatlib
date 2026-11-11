/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Source Lemma 6 — the output state is close to the ideal state

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  The lemma is printed on p.11 (§4.2) and
proved on p.16 (§4.3).

The source writes the ideal state (eq. (10), p.9)

  `|ψ_ideal⟩ = ∑_i α_i |v_i⟩_I ⊗ (1/(κ λ_i)) |1⟩_O ⊗ |2^{j_i}⟩_S`

and the idealised state produced with the estimates `λ̃_i`

  `|ψ′⟩ = ∑_i α_i |v_i⟩_I ⊗ (1/(κ λ̃_i)) |1⟩_O ⊗ |2^{j_i}⟩_S`.

Lemma 6 claims `‖|ψ′⟩ − |ψ_ideal⟩‖ ≤ 2ε/(1+2ε) · ‖ψ_ideal‖`.  The proof
(p.16) is a pure coefficient estimate: the unique-output eigenvalue estimation
gives `|λ_i − λ̃_i| ≤ (1+ε) ε λ̃_i`, hence

  `|1/λ_i − 1/λ̃_i| ≤ ((1+ε)ε/(1−(1+ε)ε)) · (1/λ̃_i)`,

and the coefficient ratio relative to `1/λ_i` is at most `δ = (1+ε)ε`;
summing the squared coefficient errors gives the result.

The Lean statement below is the exact per-branch coefficient statement of that
proof in ℓ² form, over a finite orthonormal eigenbasis: the branch weights
`α_i` are complex, the eigenvalue denominators are real and positive, and the
ℓ² norm is the source's squared-sum norm.  The printed constant `2ε/(1+2ε)`
is recovered from the source's hypothesis `|λ−λ̃| ≤ (1+ε)ε λ̃` under the
source's own smallness regime `ε ≤ 1/4` (the paper uses `ε < 0.01`); the
hypothesis `ε ≤ 1/4` is exactly the range in which `(1+ε)ε ≤ 2ε/(1+2ε)`.
Nothing else is assumed: the bound is derived, not posited.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.VarTimeAmpAmp10.Estimate

/-- The source's ℓ² norm of a finite complex vector, `√(∑_i ‖v_i‖²)`.

This is the norm in which the source states Lemma 5 and Lemma 6; it is the
norm of the joint register state once the eigenbasis `|v_i⟩` is fixed. -/
def l2Norm {ι : Type} [Fintype ι] (v : ι → ℂ) : ℝ :=
  Real.sqrt (∑ i, ‖v i‖ ^ 2)

/-- The coefficient of one branch of `|ψ′⟩`, `α_i / (κ λ̃_i)`. -/
def idealCoeff {ι : Type} (α : ι → ℂ) (κ : ℝ) (lam : ι → ℝ) (i : ι) : ℂ :=
  α i / ((κ : ℂ) * (lam i : ℂ))

/-- Fixed arXiv:1010.4458v2, Lemma 6 (printed p.11, proved p.16).

If the eigenvalue estimates satisfy the source's unique-estimate relative
error `|λ_i − λ̃_i| ≤ (1+ε)ε λ̃_i` at every branch and `0 < ε ≤ 1/4`, then the
estimate-state coefficients `α_i/(κλ̃_i)` differ from the ideal coefficients
`α_i/(κλ_i)` in ℓ² norm by at most `2ε/(1+2ε)` relative factor:

  `‖ψ′ − ψ_ideal‖ ≤ (2ε/(1+2ε)) ‖ψ_ideal‖`.

The branch weights `α_i` are arbitrary complex numbers (they carry the input
decomposition `|x⟩ = ∑ α_i |v_i⟩`); hence the statement holds for every input
state, as in the source. -/
theorem source_lemma6 {ι : Type} [Fintype ι]
    (α : ι → ℂ) (lam lamhat : ι → ℝ) (κ ε : ℝ)
    (hκ : 0 < κ) (hε0 : 0 < ε) (hε : ε ≤ 1 / 4)
    (hlam : ∀ i, 0 < lam i) (hlamhat : ∀ i, 0 < lamhat i)
    (hrel : ∀ i, |lam i - lamhat i| ≤ (1 + ε) * ε * lamhat i) :
    l2Norm (fun i => idealCoeff α κ lamhat i - idealCoeff α κ lam i)
      ≤ (2 * ε / (1 + 2 * ε)) * l2Norm (fun i => idealCoeff α κ lam i) := by
  classical
  set c : ℝ := (1 + ε) * ε with hc_def
  have hc0 : 0 ≤ c := by
    rw [hc_def]
    nlinarith [hε0]
  -- The per-branch coefficient bound, the core of the source's proof.
  have hper : ∀ i, ‖idealCoeff α κ lamhat i - idealCoeff α κ lam i‖
      ≤ c * ‖idealCoeff α κ lam i‖ := by
    intro i
    have hk : ((κ : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt hκ
    have hl : ((lam i : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt (hlam i)
    have hlh : ((lamhat i : ℂ)) ≠ 0 := by exact_mod_cast ne_of_gt (hlamhat i)
    have hdiff : idealCoeff α κ lamhat i - idealCoeff α κ lam i
        = α i * ((lam i : ℂ) - (lamhat i : ℂ))
            / ((κ : ℂ) * (lam i : ℂ) * (lamhat i : ℂ)) := by
      unfold idealCoeff
      field_simp
    have hdenpos : (0 : ℝ) < κ * lam i * lamhat i :=
      mul_pos (mul_pos hκ (hlam i)) (hlamhat i)
    have hdenpos' : (0 : ℝ) < κ * lam i := mul_pos hκ (hlam i)
    have hnum : ‖(α i) * ((lam i : ℂ) - (lamhat i : ℂ))‖
        = ‖α i‖ * |lam i - lamhat i| := by
      rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have hden : ‖(κ : ℂ) * (lam i : ℂ) * (lamhat i : ℂ)‖
        = κ * lam i * lamhat i := by
      rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs, abs_of_pos hκ, abs_of_pos (hlam i), abs_of_pos (hlamhat i)]
    have hnorm : ‖(α i) * ((lam i : ℂ) - (lamhat i : ℂ))
          / ((κ : ℂ) * (lam i : ℂ) * (lamhat i : ℂ))‖
        = ‖α i‖ * |lam i - lamhat i| / (κ * lam i * lamhat i) := by
      rw [norm_div, hnum, hden]
    rw [hdiff, hnorm]
    -- Replace the eigenvalue difference by the source's relative bound.
    have hbound : ‖α i‖ * |lam i - lamhat i| / (κ * lam i * lamhat i)
        ≤ ‖α i‖ * (c * lamhat i) / (κ * lam i * lamhat i) := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hdenpos)
      exact mul_le_mul_of_nonneg_left (hrel i) (norm_nonneg _)
    -- `‖α‖ (c λ̃)/(κ λ λ̃) = c · (‖α‖/(κ λ))`.
    have hide : ‖idealCoeff α κ lam i‖ = ‖α i‖ / (κ * lam i) := by
      unfold idealCoeff
      rw [norm_div, norm_mul, Complex.norm_real, Complex.norm_real]
      simp only [Real.norm_eq_abs, abs_of_pos hκ, abs_of_pos (hlam i)]
    have hden' : κ * lam i * lamhat i ≠ 0 := ne_of_gt hdenpos
    have hden2 : κ * lam i ≠ 0 := ne_of_gt hdenpos'
    have hfinal : ‖α i‖ * (c * lamhat i) / (κ * lam i * lamhat i)
        = c * ‖idealCoeff α κ lam i‖ := by
      rw [hide]
      have h1 : ‖α i‖ * (c * lamhat i) / (κ * lam i * lamhat i)
          = ‖α i‖ * c / (κ * lam i) := by
        have h := mul_div_mul_right (‖α i‖ * c) (κ * lam i) (ne_of_gt (hlamhat i))
        convert h using 2 <;> ring
      rw [h1]
      field_simp [hden2]
    exact hbound.trans hfinal.le
  -- Square the per-branch bound and sum.
  have hsq : ∑ i, ‖idealCoeff α κ lamhat i - idealCoeff α κ lam i‖ ^ 2
      ≤ ∑ i, (c * ‖idealCoeff α κ lam i‖) ^ 2 := by
    apply Finset.sum_le_sum
    intro i _
    exact pow_le_pow_left₀ (norm_nonneg _) (hper i) 2
  have hsum : ∑ i, (c * ‖idealCoeff α κ lam i‖) ^ 2
      = c ^ 2 * ∑ i, ‖idealCoeff α κ lam i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  -- The printed constant dominates the relative error under `ε ≤ 1/4`.
  have hcle : c ≤ 2 * ε / (1 + 2 * ε) := by
    rw [hc_def, le_div_iff₀ (by nlinarith : (0 : ℝ) < 1 + 2 * ε)]
    nlinarith [hε, hε0]
  -- Assemble the ℓ² statement.
  unfold l2Norm
  calc Real.sqrt (∑ i, ‖idealCoeff α κ lamhat i - idealCoeff α κ lam i‖ ^ 2)
      ≤ Real.sqrt (∑ i, (c * ‖idealCoeff α κ lam i‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (c ^ 2 * ∑ i, ‖idealCoeff α κ lam i‖ ^ 2) := by rw [hsum]
    _ = c * Real.sqrt (∑ i, ‖idealCoeff α κ lam i‖ ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc0]
    _ ≤ (2 * ε / (1 + 2 * ε)) * Real.sqrt (∑ i, ‖idealCoeff α κ lam i‖ ^ 2) :=
        mul_le_mul_of_nonneg_right hcle (Real.sqrt_nonneg _)

end Qatlib.Papers.VarTimeAmpAmp10.Estimate
