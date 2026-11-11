/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GevreyGrad19.MainResults.Model.GevreyGradDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# GevreyGrad19 — Theorem 2.2 (properties of Gevrey functions)

Fixed arXiv:1909.13528v1, Theorem 2.2, page 18 and its proof on pages 18–19.

The three monotonicity / restriction properties of the Gevrey classes are
fully proved here from Definition 2.1 (`Gevrey`).  The only analytic inputs are
`ContDiffOn.mono` (restriction of smoothness to a subset), monotonicity of
`x ↦ x^k` on non-negative reals and monotonicity of `x ↦ (k!)^x` for `k! ≥ 1`.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.GevreyGrad19.MainResults

/-- The factorial is at least one, so `(k!)^σ` is monotone in `σ`. -/
theorem one_le_factorial_cast (k : ℕ) : (1 : ℝ) ≤ (k.factorial : ℝ) := by
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero k)

/-- Theorem 2.2 (1), p. 18: if `0 < c₁ ≤ c₂` then
`G_{d,c₁,σ,Ω} ⊆ G_{d,c₂,σ,Ω}`. -/
theorem gevrey_mono_coeff {d : ℕ} {σ c₁ c₂ : ℝ} {Ω : Set (Fin d → ℝ)}
    (hc : 0 < c₁) (hle : c₁ ≤ c₂) {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ Gevrey d c₁ σ Ω) : f ∈ Gevrey d c₂ σ Ω := by
  refine ⟨hf.1, ?_⟩
  intro x hx k α
  refine le_trans (hf.2 x hx k α) ?_
  have hpow : c₁ ^ k ≤ c₂ ^ k := pow_le_pow_left₀ hc.le hle k
  have hfac : 0 ≤ (k.factorial : ℝ) ^ σ := Real.rpow_nonneg (Nat.cast_nonneg _) σ
  have hprod : c₁ ^ k * (k.factorial : ℝ) ^ σ ≤ c₂ ^ k * (k.factorial : ℝ) ^ σ :=
    mul_le_mul_of_nonneg_right hpow hfac
  calc (1 / 2) * c₁ ^ k * (k.factorial : ℝ) ^ σ
      = (1 / 2) * (c₁ ^ k * (k.factorial : ℝ) ^ σ) := by ring
    _ ≤ (1 / 2) * (c₂ ^ k * (k.factorial : ℝ) ^ σ) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (1 / 2) * c₂ ^ k * (k.factorial : ℝ) ^ σ := by ring

/-- Theorem 2.2 (2), p. 18: if `σ₁ ≤ σ₂` then `G_{d,c,σ₁,Ω} ⊆ G_{d,c,σ₂,Ω}`. -/
theorem gevrey_mono_order {d : ℕ} {c σ₁ σ₂ : ℝ} {Ω : Set (Fin d → ℝ)}
    (hc : 0 < c) (hle : σ₁ ≤ σ₂) {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ Gevrey d c σ₁ Ω) : f ∈ Gevrey d c σ₂ Ω := by
  refine ⟨hf.1, ?_⟩
  intro x hx k α
  refine le_trans (hf.2 x hx k α) ?_
  have hfac : (k.factorial : ℝ) ^ σ₁ ≤ (k.factorial : ℝ) ^ σ₂ :=
    Real.rpow_le_rpow_of_exponent_le (one_le_factorial_cast k) hle
  have hck : 0 ≤ c ^ k := pow_nonneg hc.le k
  have hprod : c ^ k * (k.factorial : ℝ) ^ σ₁ ≤ c ^ k * (k.factorial : ℝ) ^ σ₂ :=
    mul_le_mul_of_nonneg_left hfac hck
  calc (1 / 2) * c ^ k * (k.factorial : ℝ) ^ σ₁
      = (1 / 2) * (c ^ k * (k.factorial : ℝ) ^ σ₁) := by ring
    _ ≤ (1 / 2) * (c ^ k * (k.factorial : ℝ) ^ σ₂) :=
        mul_le_mul_of_nonneg_left hprod (by norm_num)
    _ = (1 / 2) * c ^ k * (k.factorial : ℝ) ^ σ₂ := by ring

/-- Theorem 2.2 (3), p. 18: for open `Ω₁ ⊆ Ω₂`,
`f ∈ G_{d,c,σ,Ω₂} ⇒ f|_{Ω₁} ∈ G_{d,c,σ,Ω₁}`.  Because the paper's
`f|_{Ω₁}` is the same ambient function restricted to a subset of its domain of
definition, this is exactly `f ∈ G_{d,c,σ,Ω₁}`. -/
theorem gevrey_restrict {d : ℕ} {c σ : ℝ} {Ω₁ Ω₂ : Set (Fin d → ℝ)}
    (_hΩ₁ : IsOpen Ω₁) (_hΩ₂ : IsOpen Ω₂) (hsub : Ω₁ ⊆ Ω₂) {f : (Fin d → ℝ) → ℝ}
    (hf : f ∈ Gevrey d c σ Ω₂) : f ∈ Gevrey d c σ Ω₁ := by
  refine ⟨hf.1.mono hsub, ?_⟩
  intro x hx k α
  exact hf.2 x (hsub hx) k α

/-- Bundled subset form of Theorem 2.2 (1). -/
theorem gevrey_class_subset_coeff {d : ℕ} {σ c₁ c₂ : ℝ} {Ω : Set (Fin d → ℝ)}
    (hc : 0 < c₁) (hle : c₁ ≤ c₂) :
    Gevrey d c₁ σ Ω ⊆ Gevrey d c₂ σ Ω :=
  fun _ hf => gevrey_mono_coeff hc hle hf

/-- Bundled subset form of Theorem 2.2 (2). -/
theorem gevrey_class_subset_order {d : ℕ} {c σ₁ σ₂ : ℝ} {Ω : Set (Fin d → ℝ)}
    (hc : 0 < c) (hle : σ₁ ≤ σ₂) : Gevrey d c σ₁ Ω ⊆ Gevrey d c σ₂ Ω :=
  fun _ hf => gevrey_mono_order hc hle hf

end Qatlib.Papers.GevreyGrad19.MainResults
