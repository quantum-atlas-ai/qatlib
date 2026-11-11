/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# CIRPricing.RiccatiSolution

Source: Herman, Sun, Liu, Pistoia, Che, Otter, Chakrabarti, Harrow,
*Quantum Speedups for Derivative Pricing Beyond Black-Scholes*,
fixed version arXiv:2602.03725v1, Appendix D, Proposition D.1
(v1 text, line 5102 of the extracted source: "Consider the Riccati ODE
`d/dx y(x) = a y^2(x) + b y(x) + c` with initial condition `y(0) = 0`.
The solution is `y = (1/(2a)) (β tan ((1/2) β (x - C)) - b)` where
`β = sqrt(4ac - b^2)` and `C = -(2/β) arctan (b/β)`").

The paper's proof separates variables, integrates the rational expression
`1/(ay^2 + by + c)` into an arctangent, inverts the arctangent with a tangent,
and fixes the integration constant `C` from `y(0) = 0`. This module formalises
the two verifiable halves of that proof over `ℝ`: the closed form takes the
prescribed initial value, and wherever the tangent is defined it satisfies the
Riccati equation exactly. Uniqueness of the initial value problem is *not*
claimed here; the paper only uses the displayed closed form.

Boundary: real coefficients and the real closed form only, matching the
appendix; no complex `β`, no global solution claim across the poles
`cos ((1/2) β (x - C)) = 0`, and no dependency on any CIR or Heston model
assumption.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DerivPricing26.CIRPricing.RiccatiSolution

open Filter Real
open scoped Topology

/-- Proposition D.1 (v1 Appendix D): the integration constant
`C = -(2 / β) * arctan (b / β)` selected by the initial condition `y(0) = 0`. -/
def riccatiShift (b β : ℝ) : ℝ := -(2 / β) * Real.arctan (b / β)

/-- Proposition D.1 (v1 Appendix D): the closed form
`y(x) = (β * tan ((1/2) β (x - C)) - b) / (2a)` of the Riccati solution, with
`C` given by `riccatiShift`. -/
def riccatiSolution (a b β : ℝ) (x : ℝ) : ℝ :=
  (β * Real.tan (β * (x - riccatiShift b β) / 2) - b) / (2 * a)

/-- Proposition D.1: the closed form satisfies the initial condition `y(0) = 0`
for nonzero `a` and `β`. -/
theorem riccatiSolution_zero {a b β : ℝ} (ha : a ≠ 0) (hβ : β ≠ 0) :
    riccatiSolution a b β 0 = 0 := by
  have harg : β * (0 - riccatiShift b β) / 2 = Real.arctan (b / β) := by
    unfold riccatiShift
    field_simp
    ring
  unfold riccatiSolution
  rw [harg, Real.tan_arctan]
  field_simp
  ring

/-- Proposition D.1, algebraic core: for `β^2 = 4ac - b^2` and `t = tan ((1/2) β (x - C))`,
`a ((β t - b)/(2a))^2 + b ((β t - b)/(2a)) + c = β^2 (1 + t^2)/(4a)`. This is the
quadratic identity that turns the derivative of the closed form into the
Riccati right-hand side. -/
theorem riccati_algebra {a b c β t : ℝ} (ha : a ≠ 0) (hβ : β ^ 2 = 4 * a * c - b ^ 2) :
    a * ((β * t - b) / (2 * a)) ^ 2 + b * ((β * t - b) / (2 * a)) + c
      = β ^ 2 * (1 + t ^ 2) / (4 * a) := by
  field_simp
  nlinarith [hβ]

/-- Proposition D.1: the closed form satisfies the Riccati ODE at every point
where the tangent of the shifted argument is defined. -/
theorem riccatiSolution_hasDerivAt {a b c β : ℝ} (ha : a ≠ 0)
    (hβ : β ^ 2 = 4 * a * c - b ^ 2) {x : ℝ}
    (hcos : Real.cos (β * (x - riccatiShift b β) / 2) ≠ 0) :
    HasDerivAt (riccatiSolution a b β)
      (a * riccatiSolution a b β x ^ 2 + b * riccatiSolution a b β x + c) x := by
  have hinner : HasDerivAt (fun y : ℝ => β * (y - riccatiShift b β) / 2) (β / 2) x := by
    have h1 : HasDerivAt (fun y : ℝ => y - riccatiShift b β) 1 x :=
      (hasDerivAt_id x).sub_const (riccatiShift b β)
    have h2 := (h1.const_mul β).div_const 2
    simpa using h2
  have htan : HasDerivAt (fun y : ℝ => Real.tan (β * (y - riccatiShift b β) / 2))
      ((1 / Real.cos (β * (x - riccatiShift b β) / 2) ^ 2) * (β / 2)) x := by
    simpa only [Function.comp_def, one_div] using
      (Real.hasDerivAt_tan (x := β * (x - riccatiShift b β) / 2) hcos).comp x hinner
  have hfull : HasDerivAt
      (fun y : ℝ => (β * Real.tan (β * (y - riccatiShift b β) / 2) - b) / (2 * a))
      ((β * ((1 / Real.cos (β * (x - riccatiShift b β) / 2) ^ 2) * (β / 2))) / (2 * a)) x :=
    ((htan.const_mul β).sub_const b).div_const (2 * a)
  have htrig : 1 / Real.cos (β * (x - riccatiShift b β) / 2) ^ 2
      = 1 + Real.tan (β * (x - riccatiShift b β) / 2) ^ 2 := by
    rw [Real.tan_eq_sin_div_cos]
    field_simp
    nlinarith [Real.sin_sq_add_cos_sq (β * (x - riccatiShift b β) / 2)]
  have hsol : riccatiSolution a b β x
      = (β * Real.tan (β * (x - riccatiShift b β) / 2) - b) / (2 * a) := by
    rfl
  have hderiv : (β * ((1 / Real.cos (β * (x - riccatiShift b β) / 2) ^ 2) * (β / 2)))
        / (2 * a)
      = a * riccatiSolution a b β x ^ 2 + b * riccatiSolution a b β x + c := by
    have hval : (β * ((1 / Real.cos (β * (x - riccatiShift b β) / 2) ^ 2) * (β / 2)))
          / (2 * a)
        = β ^ 2 * (1 + Real.tan (β * (x - riccatiShift b β) / 2) ^ 2) / (4 * a) := by
      rw [htrig]
      field_simp
      ring
    rw [hval, hsol, riccati_algebra ha hβ]
  rw [hderiv] at hfull
  exact hfull

/-- Proposition D.1 in derivative form: wherever the tangent is defined,
`d/dx y(x) = a y(x)^2 + b y(x) + c` for the closed form `y = riccatiSolution`. -/
theorem riccatiSolution_deriv_eq {a b c β : ℝ} (ha : a ≠ 0)
    (hβ : β ^ 2 = 4 * a * c - b ^ 2) {x : ℝ}
    (hcos : Real.cos (β * (x - riccatiShift b β) / 2) ≠ 0) :
    deriv (riccatiSolution a b β) x
      = a * riccatiSolution a b β x ^ 2 + b * riccatiSolution a b β x + c :=
  (riccatiSolution_hasDerivAt ha hβ hcos).deriv

/-- Proposition D.1 bundled: the closed form both vanishes at `0` and solves the
Riccati ODE wherever it is differentiable. -/
theorem riccatiSolution_solves_ivp {a b c β : ℝ} (ha : a ≠ 0) (hβ0 : β ≠ 0)
    (hβ : β ^ 2 = 4 * a * c - b ^ 2) :
    riccatiSolution a b β 0 = 0 ∧
      ∀ x : ℝ, Real.cos (β * (x - riccatiShift b β) / 2) ≠ 0 →
        deriv (riccatiSolution a b β) x
          = a * riccatiSolution a b β x ^ 2 + b * riccatiSolution a b β x + c :=
  ⟨riccatiSolution_zero ha hβ0, fun _ hcos => riccatiSolution_deriv_eq ha hβ hcos⟩


/-- Proposition D.1, uniqueness half: any function `g` that vanishes at `0` and
satisfies the Riccati equation `y' = a y² + b y + c` on a neighbourhood of `0`
agrees with the closed form `riccatiSolution` near `0`. This is the
Picard–Lindelöf local uniqueness for the quadratic right-hand side, whose
Lipschitz constant on `[-1, 1]` is `2|a| + |b|`. -/
theorem riccatiSolution_unique_near_zero {a b c β : ℝ} (ha : a ≠ 0) (hβ0 : β ≠ 0)
    (hβ : β ^ 2 = 4 * a * c - b ^ 2) {g : ℝ → ℝ} (hg0 : g 0 = 0)
    (hg : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt g (a * g t ^ 2 + b * g t + c) t) :
    g =ᶠ[𝓝 (0 : ℝ)] riccatiSolution a b β := by
  have harg : β * (0 - riccatiShift b β) / 2 = Real.arctan (b / β) := by
    unfold riccatiShift
    field_simp
    ring
  have hcos0 : Real.cos (β * (0 - riccatiShift b β) / 2) ≠ 0 := by
    rw [harg]
    exact (Real.cos_arctan_pos (b / β)).ne'
  have hcont : Continuous fun t : ℝ => Real.cos (β * (t - riccatiShift b β) / 2) := by fun_prop
  have hcosEv : ∀ᶠ t in 𝓝 (0 : ℝ), Real.cos (β * (t - riccatiShift b β) / 2) ≠ 0 :=
    hcont.continuousAt.eventually_ne hcos0
  have hf0 : riccatiSolution a b β 0 = 0 := riccatiSolution_zero ha hβ0
  have hfcont : ContinuousAt (riccatiSolution a b β) 0 :=
    (riccatiSolution_hasDerivAt ha hβ hcos0).continuousAt
  have hfmem : ∀ᶠ t in 𝓝 (0 : ℝ), riccatiSolution a b β t ∈ Set.Icc (-1 : ℝ) 1 := by
    have h : ∀ᶠ t in 𝓝 (0 : ℝ),
        riccatiSolution a b β t ∈ Metric.ball (riccatiSolution a b β 0) 1 :=
      hfcont.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [h] with t ht
    rw [Metric.mem_ball, Real.dist_eq, hf0, sub_zero, abs_lt] at ht
    rw [Set.mem_Icc]
    constructor <;> linarith [ht.1, ht.2]
  have hgcont : ContinuousAt g 0 := (hg.self_of_nhds).continuousAt
  have hgmem : ∀ᶠ t in 𝓝 (0 : ℝ), g t ∈ Set.Icc (-1 : ℝ) 1 := by
    have h : ∀ᶠ t in 𝓝 (0 : ℝ), g t ∈ Metric.ball (g 0) 1 :=
      hgcont.eventually (Metric.ball_mem_nhds _ one_pos)
    filter_upwards [h] with t ht
    rw [Metric.mem_ball, Real.dist_eq, hg0, sub_zero, abs_lt] at ht
    rw [Set.mem_Icc]
    constructor <;> linarith [ht.1, ht.2]
  have hKnn : (0 : ℝ) ≤ 2 * |a| + |b| := by positivity
  have hlip : LipschitzOnWith (⟨2 * |a| + |b|, hKnn⟩ : NNReal)
      (fun y : ℝ => a * y ^ 2 + b * y + c) (Set.Icc (-1 : ℝ) 1) := by
    rw [lipschitzOnWith_iff_dist_le_mul]
    intro x hx y hy
    rw [Real.dist_eq, Real.dist_eq]
    show |a * x ^ 2 + b * x + c - (a * y ^ 2 + b * y + c)| ≤ (2 * |a| + |b|) * |x - y|
    have hx1 : |x| ≤ 1 := by rw [abs_le]; exact ⟨hx.1, hx.2⟩
    have hy1 : |y| ≤ 1 := by rw [abs_le]; exact ⟨hy.1, hy.2⟩
    have hfac : a * x ^ 2 + b * x + c - (a * y ^ 2 + b * y + c) = (x - y) * (a * (x + y) + b) := by
      ring
    have hlin : |a * (x + y) + b| ≤ 2 * |a| + |b| := by
      have h1 : |x + y| ≤ 2 := by
        calc |x + y| ≤ |x| + |y| := abs_add_le _ _
          _ ≤ 2 := by linarith
      calc |a * (x + y) + b| ≤ |a * (x + y)| + |b| := abs_add_le _ _
        _ = |a| * |x + y| + |b| := by rw [abs_mul]
        _ ≤ |a| * 2 + |b| := by
            have := mul_le_mul_of_nonneg_left h1 (abs_nonneg a)
            linarith
        _ = 2 * |a| + |b| := by ring
    rw [hfac, abs_mul]
    calc |x - y| * |a * (x + y) + b| ≤ |x - y| * (2 * |a| + |b|) :=
          mul_le_mul_of_nonneg_left hlin (abs_nonneg _)
      _ = (2 * |a| + |b|) * |x - y| := by ring
  have hff : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt (riccatiSolution a b β)
        (a * riccatiSolution a b β t ^ 2 + b * riccatiSolution a b β t + c) t ∧
      riccatiSolution a b β t ∈ Set.Icc (-1 : ℝ) 1 := by
    filter_upwards [hcosEv, hfmem] with t htcos htmem
    exact ⟨riccatiSolution_hasDerivAt ha hβ htcos, htmem⟩
  have hgg : ∀ᶠ t in 𝓝 (0 : ℝ),
      HasDerivAt g (a * g t ^ 2 + b * g t + c) t ∧ g t ∈ Set.Icc (-1 : ℝ) 1 :=
    hg.and hgmem
  have heq : riccatiSolution a b β 0 = g 0 := by rw [hf0, hg0]
  have hres := ODE_solution_unique_of_eventually
    (v := fun (_ : ℝ) (y : ℝ) => a * y ^ 2 + b * y + c)
    (s := fun _ => Set.Icc (-1 : ℝ) 1)
    (K := ⟨2 * |a| + |b|, hKnn⟩)
    (Filter.Eventually.of_forall fun _ => hlip) hff hgg heq
  exact hres.symm

end Qatlib.Papers.DerivPricing26.CIRPricing.RiccatiSolution
