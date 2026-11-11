/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic
import Qatlib.Papers.LatticeSieve21.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# LatticeSieve21 / MainResults / Geometry — the reduction criterion (Proposition 7)

Fixed paper version: arXiv:2105.05608v1 (12 May 2021), André Chailloux and
Johanna Loyer, *Lattice sieving via quantum random walks*.

Section 4.1 (p.7) considers two vectors `x₀, x₁` lying in the same `α`-filter
bucket of centre `s`, written as

  `x₀ = cos(α)·s + sin(α)·y₀`,  `x₁ = cos(α)·s + sin(α)·y₁`  (Equations (1),(2))

with unit residuals `y₀, y₁ ⊥ s`.  Proposition 7 states

  `θ(y₀,y₁) ≤ 2·arcsin(1/(2 sin α))  ⟺  θ(x₀,x₁) ≤ π/3`,

and Corollary 1 turns this into the reduction criterion: the probability that
a random pair in a bucket is reducing equals `V_{d-1}(θ_α^*)`.

The proof follows the paper's computation exactly: subtracting the two
equations and squaring gives `‖x₀-x₁‖² = sin²α·‖y₀-y₁‖²`; the claim is then a
chain of equivalences between cosine inequalities, using the monotonicity of
`cos` on `[0,π]` and `cos(2 arcsin u) = 1 - 2u²`.
-/

set_option autoImplicit false
noncomputable section

open Real
open scoped RealInnerProductSpace

namespace Qatlib.Papers.LatticeSieve21.MainResults.Geometry

open InnerProductGeometry
open Qatlib.Papers.LatticeSieve21.MainResults.Definitions

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ## Elementary scalar and trigonometric ingredients -/

/-- Arithmetic core of Proposition 7 (p.7): for `s > 0`,
`1/2 ≤ (1 - s²) + s²·t ↔ 1 - 1/(2 s²) ≤ t`. -/
theorem half_le_iff (s t : ℝ) (hs : 0 < s) :
    (1 / 2 : ℝ) ≤ 1 - s ^ 2 + s ^ 2 * t ↔ 1 - 1 / (2 * s ^ 2) ≤ t := by
  have hs2 : (0 : ℝ) < 2 * s ^ 2 := by positivity
  have hkey : 1 - 1 / (2 * s ^ 2) = (2 * s ^ 2 - 1) / (2 * s ^ 2) := by
    field_simp
  rw [hkey, div_le_iff₀ hs2]
  constructor <;> intro h <;> nlinarith [h, sq_nonneg s]

/-- `cos(2·arcsin u) = 1 - 2u²` for `|u| ≤ 1` (used for the paper's
`arccos(1 - 1/(2 sin²α)) = 2 arcsin(1/(2 sin α))`, p.7). -/
theorem cos_two_arcsin (u : ℝ) (hu : u ^ 2 ≤ 1) :
    Real.cos (2 * Real.arcsin u) = 1 - 2 * u ^ 2 := by
  rw [Real.cos_two_mul, Real.cos_arcsin]
  have hsq : (Real.sqrt (1 - u ^ 2)) ^ 2 = 1 - u ^ 2 := Real.sq_sqrt (by linarith)
  rw [hsq]
  ring

/-! ## The cosine of the angle between the two bucket vectors -/

/-- **Algebraic core of Proposition 7** (p.7): if `s` and the residuals
`y₀, y₁` are unit vectors with `y₀, y₁ ⊥ s`, then
`cos θ(x₀,x₁) = cos²α + sin²α · cos θ(y₀,y₁)` for
`xᵢ = cos α · s + sin α · yᵢ`.  This is the paper's computation
`‖x₀-x₁‖² = sin²α‖y₀-y₁‖²` written on inner products. -/
theorem cos_angle_offset {s y₀ y₁ : E} {α : ℝ}
    (hs : ‖s‖ = 1) (hy₀ : ‖y₀‖ = 1) (hy₁ : ‖y₁‖ = 1)
    (hsy₀ : ⟪s, y₀⟫ = 0) (hsy₁ : ⟪s, y₁⟫ = 0) :
    Real.cos (angle (Real.cos α • s + Real.sin α • y₀)
        (Real.cos α • s + Real.sin α • y₁))
      = Real.cos α ^ 2 + Real.sin α ^ 2 * Real.cos (angle y₀ y₁) := by
  have hsy₀' : ⟪y₀, s⟫ = 0 := by rw [real_inner_comm, hsy₀]
  have hsy₁' : ⟪y₁, s⟫ = 0 := by rw [real_inner_comm, hsy₁]
  have hss : ⟪s, s⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hs]; norm_num
  have hy₀y₀ : ⟪y₀, y₀⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hy₀]; norm_num
  have hy₁y₁ : ⟪y₁, y₁⟫ = (1 : ℝ) := by rw [real_inner_self_eq_norm_sq, hy₁]; norm_num
  have hcy : Real.cos (angle y₀ y₁) = ⟪y₀, y₁⟫ := by
    rw [cos_angle, hy₀, hy₁]
    norm_num
  have hinner : ⟪Real.cos α • s + Real.sin α • y₀,
      Real.cos α • s + Real.sin α • y₁⟫
      = Real.cos α ^ 2 + Real.sin α ^ 2 * ⟪y₀, y₁⟫ := by
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hsy₀', hsy₁, hss, mul_zero, mul_one, add_zero, zero_add]
    ring
  have hnorm₀ : ‖Real.cos α • s + Real.sin α • y₀‖ = 1 := by
    have hsq : ‖Real.cos α • s + Real.sin α • y₀‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hsy₀', hsy₀, hss, hy₀y₀, mul_zero, mul_one, add_zero, zero_add]
      have hcs := Real.cos_sq_add_sin_sq α
      nlinarith
    nlinarith [norm_nonneg (Real.cos α • s + Real.sin α • y₀)]
  have hnorm₁ : ‖Real.cos α • s + Real.sin α • y₁‖ = 1 := by
    have hsq : ‖Real.cos α • s + Real.sin α • y₁‖ ^ 2 = 1 := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
        hsy₁', hsy₁, hss, hy₁y₁, mul_zero, mul_one, add_zero, zero_add]
      have hcs := Real.cos_sq_add_sin_sq α
      nlinarith
    nlinarith [norm_nonneg (Real.cos α • s + Real.sin α • y₁)]
  rw [cos_angle, hnorm₀, hnorm₁, hinner, hcy]
  norm_num

/-! ## Proposition 7 -/

/-- **Proposition 7 (claim c006), p.7.**  For unit `s` and residuals
`y₀, y₁ ⊥ s`, the bucket vectors `xᵢ = cos α·s + sin α·yᵢ` satisfy
`θ(y₀,y₁) ≤ 2 arcsin(1/(2 sin α)) ⟺ θ(x₀,x₁) ≤ π/3`, for
`α ∈ [π/3, π/2]`. -/
theorem prop7_angle_iff {s y₀ y₁ x₀ x₁ : E} {α : ℝ}
    (hs : ‖s‖ = 1) (hy₀ : ‖y₀‖ = 1) (hy₁ : ‖y₁‖ = 1)
    (hsy₀ : ⟪s, y₀⟫ = 0) (hsy₁ : ⟪s, y₁⟫ = 0)
    (hx₀ : x₀ = Real.cos α • s + Real.sin α • y₀)
    (hx₁ : x₁ = Real.cos α • s + Real.sin α • y₁)
    (hα : α ∈ Set.Icc (π / 3) (π / 2)) :
    angle y₀ y₁ ≤ 2 * Real.arcsin (1 / (2 * Real.sin α)) ↔ angle x₀ x₁ ≤ π / 3 := by
  have hα0 : 0 < α := by linarith [Real.pi_pos, hα.1]
  have hαπ : α < Real.pi := by linarith [Real.pi_pos, hα.2]
  have hsa : 0 < Real.sin α := Real.sin_pos_of_pos_of_lt_pi hα0 hαπ
  have hsin3 : Real.sin (Real.pi / 3) ≤ Real.sin α := by
    refine Real.sin_le_sin_of_le_of_le_pi_div_two ?_ hα.2 hα.1
    linarith [Real.pi_pos]
  have h3 : (1 : ℝ) ≤ Real.sqrt 3 := by
    have h := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
    nlinarith [Real.sqrt_nonneg 3]
  have hhalf : (1 / 2 : ℝ) ≤ Real.sin α := by
    rw [Real.sin_pi_div_three] at hsin3
    nlinarith
  have hu1 : (1 : ℝ) ≤ 2 * Real.sin α := by linarith
  have hcosx : Real.cos (angle x₀ x₁) =
      Real.cos α ^ 2 + Real.sin α ^ 2 * Real.cos (angle y₀ y₁) := by
    rw [hx₀, hx₁]
    exact cos_angle_offset hs hy₀ hy₁ hsy₀ hsy₁
  -- Step 1: `θ(x₀,x₁) ≤ π/3` is the same as `1/2 ≤ cos θ(x₀,x₁)`.
  have hA : angle x₀ x₁ ≤ π / 3 ↔ (1 / 2 : ℝ) ≤ Real.cos (angle x₀ x₁) := by
    have hx : angle x₀ x₁ ∈ Set.Icc (0 : ℝ) Real.pi :=
      ⟨angle_nonneg _ _, angle_le_pi _ _⟩
    have hp : (Real.pi / 3) ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor <;> nlinarith [Real.pi_pos]
    have h := Real.strictAntiOn_cos.le_iff_ge hp hx
    rw [Real.cos_pi_div_three] at h
    exact h.symm
  -- Step 2: the residual condition is the same as `1 - 1/(2 sin²α) ≤ cos θ(y₀,y₁)`.
  have hB : angle y₀ y₁ ≤ 2 * Real.arcsin (1 / (2 * Real.sin α)) ↔
      1 - 1 / (2 * Real.sin α ^ 2) ≤ Real.cos (angle y₀ y₁) := by
    have hu0 : 0 < 1 / (2 * Real.sin α) := by positivity
    have hu1' : 1 / (2 * Real.sin α) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 2 * Real.sin α)]
      exact hu1
    have hu_sq : (1 / (2 * Real.sin α)) ^ 2 ≤ 1 := by nlinarith
    have hcos : Real.cos (2 * Real.arcsin (1 / (2 * Real.sin α))) =
        1 - 1 / (2 * Real.sin α ^ 2) := by
      rw [cos_two_arcsin (1 / (2 * Real.sin α)) hu_sq]
      field_simp
    have harc0 : 0 ≤ Real.arcsin (1 / (2 * Real.sin α)) :=
      Real.arcsin_nonneg.mpr hu0.le
    have harcpi : Real.arcsin (1 / (2 * Real.sin α)) ≤ Real.pi / 2 :=
      Real.arcsin_le_pi_div_two _
    have hφ0 : 0 ≤ 2 * Real.arcsin (1 / (2 * Real.sin α)) := by linarith
    have hφπ : 2 * Real.arcsin (1 / (2 * Real.sin α)) ≤ Real.pi := by
      linarith [Real.pi_pos]
    have h := Real.strictAntiOn_cos.le_iff_ge (s := Set.Icc (0 : ℝ) Real.pi)
      ⟨hφ0, hφπ⟩ ⟨angle_nonneg y₀ y₁, angle_le_pi y₀ y₁⟩
    rw [hcos] at h
    exact h.symm
  rw [hA, hcosx, hB]
  have hc : Real.cos α ^ 2 = 1 - Real.sin α ^ 2 := by
    have := Real.cos_sq_add_sin_sq α
    linarith
  rw [hc]
  exact (half_le_iff (Real.sin α) (Real.cos (angle y₀ y₁)) hsa).symm

/-! ## Corollary 1 -/

/-- **Corollary 1 (claim c007), criterion form, p.7.**  Under the same
hypotheses, a pair of bucket vectors is reducing exactly when the residual
angle is at most `θ_α^*`. -/
theorem corollary1_reduction_iff {s y₀ y₁ x₀ x₁ : E} {α : ℝ}
    (hs : ‖s‖ = 1) (hy₀ : ‖y₀‖ = 1) (hy₁ : ‖y₁‖ = 1)
    (hsy₀ : ⟪s, y₀⟫ = 0) (hsy₁ : ⟪s, y₁⟫ = 0)
    (hx₀ : x₀ = Real.cos α • s + Real.sin α • y₀)
    (hx₁ : x₁ = Real.cos α • s + Real.sin α • y₁)
    (hα : α ∈ Set.Icc (π / 3) (π / 2)) :
    Reduces x₀ x₁ ↔ angle y₀ y₁ ≤ thetaStar α := by
  unfold Reduces thetaStar
  exact (prop7_angle_iff hs hy₀ hy₁ hsy₀ hsy₁ hx₀ hx₁ hα).symm

/-- **Corollary 1 (claim c007), probability form, p.7.**  The residuals are
uniform on the `(d-1)`-dimensional sphere of vectors orthogonal to `s`, so the
reduction event is the cap event of angle `θ_α^*`; the paper denotes its
probability `V_{d-1}(θ_α^*)` (`V` is defined as the cap probability, p.5,
line 402).  The cap probability `V_{d-1}(θ_α^*)` itself is the model input
recorded by the hypothesis `hcap`. -/
theorem corollary1_reduction_probability
    {Ω : Type*} [MeasurableSpace Ω] (μ : MeasureTheory.Measure Ω)
    [MeasureTheory.IsProbabilityMeasure μ]
    (s : E) {y₀ y₁ : Ω → E} {α d : ℝ}
    (hs : ‖s‖ = 1)
    (hy₀ : ∀ ω, ‖y₀ ω‖ = 1) (hy₁ : ∀ ω, ‖y₁ ω‖ = 1)
    (hsy₀ : ∀ ω, ⟪s, y₀ ω⟫ = 0) (hsy₁ : ∀ ω, ⟪s, y₁ ω⟫ = 0)
    (hα : α ∈ Set.Icc (π / 3) (π / 2))
    (hcap : μ.real {ω | angle (y₀ ω) (y₁ ω) ≤ thetaStar α} = V (d - 1) (thetaStar α)) :
    μ.real {ω | Reduces (Real.cos α • s + Real.sin α • y₀ ω)
        (Real.cos α • s + Real.sin α • y₁ ω)} = V (d - 1) (thetaStar α) := by
  have hset : {ω | Reduces (Real.cos α • s + Real.sin α • y₀ ω)
        (Real.cos α • s + Real.sin α • y₁ ω)}
      = {ω | angle (y₀ ω) (y₁ ω) ≤ thetaStar α} := by
    ext ω
    exact corollary1_reduction_iff hs (hy₀ ω) (hy₁ ω) (hsy₀ ω) (hsy₁ ω) rfl rfl hα
  rw [hset]
  exact hcap

end Qatlib.Papers.LatticeSieve21.MainResults.Geometry
