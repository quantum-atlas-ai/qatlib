/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
# Smooth-gradient Taylor and descent bounds

`BetaSmooth` expresses the gradient Lipschitz inequality, and `SmoothGrad` adds existence of the
specified gradient at every point. Differentiation along affine lines yields two-sided quadratic
Taylor bounds and the lower and upper per-step descent estimates for a positive step size at
most `1 / β`.

This development follows [YaoEtAl2026].

## Main statements

* `quadratic_upper_bound` and `quadratic_lower_bound`: Taylor bounds with remainder magnitude at
  most `β / 2 * ‖d‖ ^ 2`.
* `lemma1_descent_lower`: descent is at least `η / 2` times the squared gradient norm.
* `lemma2_descent_upper`: descent is at most `3 * η / 2` times the squared gradient norm.

## References

* [Yao et al., 2026][YaoEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped Gradient InnerProductSpace RealInnerProductSpace

namespace Qatlib.Papers.DissipVarFw26.FrameworkCost.Descent

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The condition `‖∇ f x - ∇ f y‖ ≤ β * ‖x - y‖` for every pair of points. -/
def BetaSmooth (f : E → ℝ) (β : ℝ) : Prop :=
  ∀ x y, ‖∇ f x - ∇ f y‖ ≤ β * ‖x - y‖

/-- The condition that `f` has gradient `∇ f x` at every point and satisfies `BetaSmooth f β`. -/
def SmoothGrad (f : E → ℝ) (β : ℝ) : Prop :=
  (∀ x, HasGradientAt f (∇ f x) x) ∧ BetaSmooth f β

omit [CompleteSpace E] in

/-- The affine line `τ ↦ x + τ • d` has derivative `d` at every real parameter. -/
lemma hasDerivAt_line (x d : E) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => x + τ • d) d t := by
  have h1 : HasDerivAt (fun τ : ℝ => τ • d) d t := by
    simpa only [one_smul, id] using (hasDerivAt_id t).smul_const d
  exact h1.const_add x

/-- If `f` has the specified gradient at `x + t • d`, its restriction to the affine line has
derivative `⟪∇ f (x + t • d), d⟫_ℝ` at `t`. -/
lemma hasDerivAt_comp_line (f : E → ℝ) (x d : E) (t : ℝ)
    (hgrad : HasGradientAt f (∇ f (x + t • d)) (x + t • d)) :
    HasDerivAt (fun τ : ℝ => f (x + τ • d)) ⟪∇ f (x + t • d), d⟫_ℝ t := by
  have hc : HasDerivAt (fun τ : ℝ => x + τ • d) d t := hasDerivAt_line x d t
  have hcomp :
      HasDerivAt (f ∘ (fun τ : ℝ => x + τ • d))
        ((InnerProductSpace.toDual ℝ E (∇ f (x + t • d))) d) t :=
    HasFDerivAt.comp_hasDerivAt (x := t) hgrad.hasFDerivAt hc
  simpa only [Function.comp_apply, InnerProductSpace.toDual_apply_apply] using! hcomp

omit [CompleteSpace E] in

/-- The derivative of `τ ↦ ⟪g, τ • d⟫_ℝ` is `⟪g, d⟫_ℝ`. -/
lemma hasDerivAt_inner_smul (g d : E) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => ⟪g, τ • d⟫_ℝ) ⟪g, d⟫_ℝ t := by
  have hcl : HasDerivAt (fun τ : ℝ => τ * ⟪g, d⟫_ℝ) ⟪g, d⟫_ℝ t := by
    simpa only [one_mul, id] using (hasDerivAt_id t).mul_const ⟪g, d⟫_ℝ
  convert! hcl using 1
  funext τ
  rw [inner_smul_right]

omit [InnerProductSpace ℝ E] [CompleteSpace E] in

/-- The derivative of `τ ↦ β / 2 * τ ^ 2 * ‖d‖ ^ 2` at `t` is `β * t * ‖d‖ ^ 2`. -/
lemma hasDerivAt_quad (β : ℝ) (d : E) (t : ℝ) :
    HasDerivAt (fun τ : ℝ => β / 2 * τ ^ 2 * ‖d‖ ^ 2) (β * t * ‖d‖ ^ 2) t := by
  have hp : HasDerivAt (fun τ : ℝ => τ ^ 2) (2 * t) t := by
    simpa using hasDerivAt_pow 2 t
  have hm := hp.const_mul (β / 2 * ‖d‖ ^ 2)
  convert! hm using 1
  · funext τ; ring
  · ring

/-- For nonnegative `β` and `SmoothGrad f β`, the value at `x + d` is at most `f x + ⟪∇ f x,
d⟫_ℝ + β / 2 * ‖d‖ ^ 2`. -/
theorem quadratic_upper_bound (f : E → ℝ) (β : ℝ) (_hβ : 0 ≤ β)
    (hsmooth : SmoothGrad f β) (x d : E) :
    f (x + d) ≤ f x + ⟪∇ f x, d⟫_ℝ + β / 2 * ‖d‖ ^ 2 := by
  obtain ⟨hgrad, hlip⟩ := hsmooth
  let h : ℝ → ℝ := fun t =>
    f (x + t • d) - ⟪∇ f x, t • d⟫_ℝ - β / 2 * t ^ 2 * ‖d‖ ^ 2
  have hderiv : ∀ t, HasDerivAt h (⟪∇ f (x + t • d) - ∇ f x, d⟫_ℝ - β * t * ‖d‖ ^ 2) t := by
    intro t
    have e1 := hasDerivAt_comp_line f x d t (hgrad _)
    have e2 := hasDerivAt_inner_smul (∇ f x) d t
    have e3 := hasDerivAt_quad β d t
    have hsub : HasDerivAt h
        (⟪∇ f (x + t • d), d⟫_ℝ - ⟪∇ f x, d⟫_ℝ - β * t * ‖d‖ ^ 2) t :=
      (e1.sub e2).sub e3
    rw [← inner_sub_left] at hsub
    exact hsub
  have hcont : Continuous h :=
    continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hmono : AntitoneOn h (Set.Icc 0 1) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc 0 1) hcont.continuousOn
    · intro t _; exact (hderiv t).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc, Set.mem_Ioo] at ht
      have ht0 : 0 < t := ht.1
      have hinner : ⟪∇ f (x + t • d) - ∇ f x, d⟫_ℝ ≤ β * t * ‖d‖ ^ 2 := by
        have hle : ⟪∇ f (x + t • d) - ∇ f x, d⟫_ℝ ≤ ‖∇ f (x + t • d) - ∇ f x‖ * ‖d‖ :=
          real_inner_le_norm _ _
        have hlip' : ‖∇ f (x + t • d) - ∇ f x‖ ≤ β * ‖t • d‖ := by
          have := hlip (x + t • d) x
          rwa [add_sub_cancel_left] at this
        have hnorm : ‖t • d‖ = t * ‖d‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        calc ⟪∇ f (x + t • d) - ∇ f x, d⟫_ℝ
            ≤ ‖∇ f (x + t • d) - ∇ f x‖ * ‖d‖ := hle
          _ ≤ (β * ‖t • d‖) * ‖d‖ :=
              mul_le_mul_of_nonneg_right hlip' (norm_nonneg d)
          _ = β * t * ‖d‖ ^ 2 := by rw [hnorm]; ring
      linarith
  have h10 : h 1 ≤ h 0 :=
    hmono (by simp : (0 : ℝ) ∈ Set.Icc 0 1) (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
      (by norm_num)
  simp only [h, one_smul, zero_smul, add_zero, one_pow,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), inner_zero_right, mul_zero, zero_mul,
    mul_one] at h10
  linarith

/-- For nonnegative `β` and `SmoothGrad f β`, the value at `x + d` is at least `f x + ⟪∇ f x,
d⟫_ℝ - β / 2 * ‖d‖ ^ 2`. -/
theorem quadratic_lower_bound (f : E → ℝ) (β : ℝ) (_hβ : 0 ≤ β)
    (hsmooth : SmoothGrad f β) (x d : E) :
    f (x + d) ≥ f x + ⟪∇ f x, d⟫_ℝ - β / 2 * ‖d‖ ^ 2 := by
  obtain ⟨hgrad, hlip⟩ := hsmooth
  let k : ℝ → ℝ := fun t =>
    f (x + t • d) - ⟪∇ f x, t • d⟫_ℝ + β / 2 * t ^ 2 * ‖d‖ ^ 2
  have hderiv : ∀ t, HasDerivAt k (⟪∇ f (x + t • d) - ∇ f x, d⟫_ℝ + β * t * ‖d‖ ^ 2) t := by
    intro t
    have e1 := hasDerivAt_comp_line f x d t (hgrad _)
    have e2 := hasDerivAt_inner_smul (∇ f x) d t
    have e3 := hasDerivAt_quad β d t
    have hsub : HasDerivAt k
        (⟪∇ f (x + t • d), d⟫_ℝ - ⟪∇ f x, d⟫_ℝ + β * t * ‖d‖ ^ 2) t :=
      (e1.sub e2).add e3
    rw [← inner_sub_left] at hsub
    exact hsub
  have hcont : Continuous k :=
    continuous_iff_continuousAt.mpr fun t => (hderiv t).continuousAt
  have hmono : MonotoneOn k (Set.Icc 0 1) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 1) hcont.continuousOn
    · intro t _; exact (hderiv t).hasDerivWithinAt
    · intro t ht
      rw [interior_Icc, Set.mem_Ioo] at ht
      have ht0 : 0 < t := ht.1
      have hinner : ⟪∇ f (x + t • d) - ∇ f x, d⟫_ℝ ≥ -(β * t * ‖d‖ ^ 2) := by
        have habs : |⟪∇ f (x + t • d) - ∇ f x, d⟫_ℝ| ≤
            ‖∇ f (x + t • d) - ∇ f x‖ * ‖d‖ := abs_real_inner_le_norm _ _
        have hlip' : ‖∇ f (x + t • d) - ∇ f x‖ ≤ β * ‖t • d‖ := by
          have := hlip (x + t • d) x
          rwa [add_sub_cancel_left] at this
        have hnorm : ‖t • d‖ = t * ‖d‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht0]
        have hstep : ‖∇ f (x + t • d) - ∇ f x‖ * ‖d‖ ≤ β * t * ‖d‖ ^ 2 := by
          calc ‖∇ f (x + t • d) - ∇ f x‖ * ‖d‖
              ≤ (β * ‖t • d‖) * ‖d‖ :=
                mul_le_mul_of_nonneg_right hlip' (norm_nonneg d)
            _ = β * t * ‖d‖ ^ 2 := by rw [hnorm]; ring
        rw [abs_le] at habs
        linarith [habs.1]
      linarith
  have h10 : k 0 ≤ k 1 :=
    hmono (by simp : (0 : ℝ) ∈ Set.Icc 0 1) (by simp : (1 : ℝ) ∈ Set.Icc 0 1)
      (by norm_num)
  simp only [k, one_smul, zero_smul, add_zero, one_pow,
    zero_pow (by norm_num : (2 : ℕ) ≠ 0), inner_zero_right, mul_zero, zero_mul,
    mul_one] at h10
  linarith

/-- For positive `β`, `SmoothGrad f β`, and `0 < η ≤ 1 / β`, one gradient step decreases `f` by
at least `(η / 2) * ‖∇ f x‖ ^ 2`. See [YaoEtAl2026]. -/
theorem lemma1_descent_lower (f : E → ℝ) (β η : ℝ) (hβ : 0 < β)
    (hsmooth : SmoothGrad f β) (hη0 : 0 < η) (hη : η ≤ 1 / β) (x : E) :
    f x - f (x - η • ∇ f x) ≥ (η / 2) * ‖∇ f x‖ ^ 2 := by
  have hβle : 0 ≤ β := le_of_lt hβ
  have hquad := quadratic_upper_bound f β hβle hsmooth x ((-η) • ∇ f x)
  have hinner : ⟪∇ f x, (-η) • ∇ f x⟫_ℝ = -η * ‖∇ f x‖ ^ 2 := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  have hnorm2 : ‖(-η) • ∇ f x‖ ^ 2 = η ^ 2 * ‖∇ f x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hη0, mul_pow]
  have hβη : β * η ≤ 1 := by
    rw [le_div_iff₀ hβ] at hη
    linarith
  have hηle : 0 ≤ η := le_of_lt hη0
  have hX0 : (0 : ℝ) ≤ ‖∇ f x‖ ^ 2 := sq_nonneg _
  have hprod : β * η ^ 2 * ‖∇ f x‖ ^ 2 ≤ η * ‖∇ f x‖ ^ 2 := by
    have h1 : β * η * (η * ‖∇ f x‖ ^ 2) ≤ 1 * (η * ‖∇ f x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hβη (mul_nonneg hηle hX0)
    nlinarith [h1]
  have hq : f (x + (-η) • ∇ f x) ≤
      f x + ⟪∇ f x, (-η) • ∇ f x⟫_ℝ + β / 2 * ‖(-η) • ∇ f x‖ ^ 2 := hquad
  rw [hinner, hnorm2] at hq
  have hx : (x : E) - η • ∇ f x = x + (-η) • ∇ f x := by
    rw [neg_smul, sub_eq_add_neg]
  rw [hx]
  nlinarith [hq, hprod]

/-- For positive `β`, `SmoothGrad f β`, and `0 < η ≤ 1 / β`, one gradient step decreases `f` by
at most `(3 * η / 2) * ‖∇ f x‖ ^ 2`. See [YaoEtAl2026]. -/
theorem lemma2_descent_upper (f : E → ℝ) (β η : ℝ) (hβ : 0 < β)
    (hsmooth : SmoothGrad f β) (hη0 : 0 < η) (hη : η ≤ 1 / β) (x : E) :
    f x - f (x - η • ∇ f x) ≤ (3 * η / 2) * ‖∇ f x‖ ^ 2 := by
  have hβle : 0 ≤ β := le_of_lt hβ
  have hquad := quadratic_lower_bound f β hβle hsmooth x ((-η) • ∇ f x)
  have hinner : ⟪∇ f x, (-η) • ∇ f x⟫_ℝ = -η * ‖∇ f x‖ ^ 2 := by
    rw [inner_smul_right, real_inner_self_eq_norm_sq]
  have hnorm2 : ‖(-η) • ∇ f x‖ ^ 2 = η ^ 2 * ‖∇ f x‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_of_pos hη0, mul_pow]
  have hβη : β * η ≤ 1 := by
    rw [le_div_iff₀ hβ] at hη
    linarith
  have hηle : 0 ≤ η := le_of_lt hη0
  have hX0 : (0 : ℝ) ≤ ‖∇ f x‖ ^ 2 := sq_nonneg _
  have hprod : β * η ^ 2 * ‖∇ f x‖ ^ 2 ≤ η * ‖∇ f x‖ ^ 2 := by
    have h1 : β * η * (η * ‖∇ f x‖ ^ 2) ≤ 1 * (η * ‖∇ f x‖ ^ 2) :=
      mul_le_mul_of_nonneg_right hβη (mul_nonneg hηle hX0)
    nlinarith [h1]
  have hq : f (x + (-η) • ∇ f x) ≥
      f x + ⟪∇ f x, (-η) • ∇ f x⟫_ℝ - β / 2 * ‖(-η) • ∇ f x‖ ^ 2 := hquad
  rw [hinner, hnorm2] at hq
  have hx : (x : E) - η • ∇ f x = x + (-η) • ∇ f x := by
    rw [neg_smul, sub_eq_add_neg]
  rw [hx]
  nlinarith [hq, hprod]

end Qatlib.Papers.DissipVarFw26.FrameworkCost.Descent
