/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 2: amplitude amplification started from the bad state

Fixed version: arXiv:2205.14023, *Finding many Collisions via Reusable Quantum
Walks*, Proposition 2, page 7 (Section 2.2, "Starting from `|ψ_B⟩`, known α").

Statement (paper):

> Consider the following algorithm, with `α ≤ π/4`:
> 1. Start from `|ψ_B⟩`.
> 2. Apply `Rot_{2α} = Ref_{|ψ_U⟩} Ref_{|ψ_B⟩}` `N'` times on `|ψ_B⟩` with
>    `N' = ⌊ (π/2) / (2α) ⌋`.
> 3. Apply the checking oracle and measure the last qubit.
> This procedure measures 1 w.p. at least `1 − 4α²` and the resulting state is
> `|ψ_G⟩`.

On the two-dimensional span `{|ψ_B⟩, |ψ_G⟩}` the rotation `Rot_{2α}` is the
standard rotation by `2α`:
`Rot_{2α} (cos θ |ψ_B⟩ + sin θ |ψ_G⟩)
   = cos(θ+2α) |ψ_B⟩ + sin(θ+2α) |ψ_G⟩`,
so `N'` iterations send `|ψ_B⟩` to `cos γ' |ψ_B⟩ + sin γ' |ψ_G⟩` with
`γ' = 2 N' α` (`proposition_two_rotation`).  The checking oracle appends the
flag `1` to the `|ψ_G⟩` component, so measuring the flag gives `1` with
probability `sin² γ'` (`proposition_two_measurement_probability`), which the
paper lower-bounds by `1 − 4α²` (`proposition_two_success_probability`).

The paper's numerical chain is
`sin² γ' = cos²(π/2 − γ') ≥ cos²(2α) ≥ 1 − 4α²`,
using `π/2 − γ' ∈ [0, 2α)`.  All three pieces are proved below; no gaps.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QWalkCollide22.MainResults

/-- The rotation by `θ` acting on the coefficients `(cos θ, sin θ)` of the
two-dimensional span `{|ψ_B⟩, |ψ_G⟩}`. -/
def rot2 (θ : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos θ * v.1 - Real.sin θ * v.2, Real.sin θ * v.1 + Real.cos θ * v.2)

/-- **Iterated rotation (paper p.7, proof of Proposition 2).**  Applying
`Rot_{2α}` `N` times to `|ψ_B⟩` (coefficients `(1, 0)`) yields
`cos(N·2α) |ψ_B⟩ + sin(N·2α) |ψ_G⟩`. -/
theorem rot2_iterate (θ : ℝ) (N : ℕ) :
    (rot2 θ)^[N] (1, 0) = (Real.cos ((N : ℝ) * θ), Real.sin ((N : ℝ) * θ)) := by
  induction N with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih]
      simp only [rot2]
      rw [show ((n + 1 : ℕ) : ℝ) * θ = (n : ℝ) * θ + θ by push_cast; ring,
        Real.cos_add, Real.sin_add]
      apply Prod.ext <;> ring

/-- **The measurement probability of Proposition 2 (paper p.7).**  With
`γ' = 2αN'`, the amplitude on `|ψ_G⟩` is `sin γ'`, hence the checking oracle
followed by measuring the flag returns `1` with probability `sin² γ'`.  Here
`N' = ⌊(π/2)/(2α)⌋`, and the probability bound `≥ 1 − 4α²` is proved below. -/
theorem proposition_two_measurement_probability (α : ℝ) (_hα0 : 0 < α) :
    let N : ℕ := Nat.floor (Real.pi / 2 / (2 * α))
    let γ : ℝ := 2 * α * (N : ℝ)
    (rot2 (2 * α))^[N] (1, 0) = (Real.cos γ, Real.sin γ) := by
  intro N γ
  have : (N : ℝ) * (2 * α) = γ := by
    rw [show (N : ℝ) * (2 * α) = 2 * α * (N : ℝ) by ring]
  rw [rot2_iterate, this]

/-- **Proposition 2 (arXiv:2205.14023, p.7).**  For `0 < α ≤ π/4`, starting
from `|ψ_B⟩`, the procedure of Proposition 2 — `N' = ⌊(π/2)/(2α)⌋` applications
of `Rot_{2α}` followed by the checking oracle and a measurement of the last
qubit — measures `1` with probability at least `1 − 4α²`.

The proof follows the paper's chain
`sin² γ' = cos²(π/2 − γ') ≥ cos²(2α) ≥ 1 − 4α²` with `γ' = 2αN'` and
`π/2 − γ' ∈ [0, 2α)`. -/
theorem proposition_two_success_probability (α : ℝ) (hα0 : 0 < α)
    (hα : α ≤ Real.pi / 4) :
    1 - 4 * α ^ 2 ≤
      Real.sin (2 * α * (Nat.floor (Real.pi / 2 / (2 * α)))) ^ 2 := by
  set N : ℕ := Nat.floor (Real.pi / 2 / (2 * α)) with hN
  set γ : ℝ := 2 * α * (N : ℝ) with hγ
  have h2α : 0 < 2 * α := by positivity
  -- `N ≤ (π/2)/(2α) < N+1`
  have hfloor : (N : ℝ) ≤ Real.pi / 2 / (2 * α) := Nat.floor_le (by positivity)
  have hfloor' : Real.pi / 2 / (2 * α) < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hcancel : 2 * α * (Real.pi / 2 / (2 * α)) = Real.pi / 2 := by
    field_simp
  -- `γ = 2αN ≤ π/2 < γ + 2α`
  have hγle : γ ≤ Real.pi / 2 := by
    have h := mul_le_mul_of_nonneg_left hfloor h2α.le
    rw [hγ]
    linarith [h, hcancel]
  have hγlt : Real.pi / 2 < γ + 2 * α := by
    have h := mul_lt_mul_of_pos_left hfloor' h2α
    nlinarith [h, hcancel]
  have hδ0 : 0 ≤ Real.pi / 2 - γ := by linarith
  have hδ2α : Real.pi / 2 - γ ≤ 2 * α := by linarith
  have h2αpi : 2 * α ≤ Real.pi / 2 := by linarith
  have h2αpi' : 2 * α ≤ Real.pi := by linarith [Real.pi_pos]
  -- `sin γ = cos (π/2 − γ)`
  have hsin : Real.sin γ = Real.cos (Real.pi / 2 - γ) := by
    rw [Real.cos_pi_div_two_sub]
  -- monotonicity of `cos` on `[0, π/2]`
  have hcosδ_nonneg : 0 ≤ Real.cos (Real.pi / 2 - γ) :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  have hmono : Real.cos (2 * α) ≤ Real.cos (Real.pi / 2 - γ) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hδ0 h2αpi' hδ2α
  have hcos2α_nonneg : 0 ≤ Real.cos (2 * α) :=
    Real.cos_nonneg_of_mem_Icc ⟨by linarith [Real.pi_pos], h2αpi⟩
  have hsq : Real.cos (2 * α) ^ 2 ≤ Real.cos (Real.pi / 2 - γ) ^ 2 :=
    pow_le_pow_left₀ hcos2α_nonneg hmono 2
  rw [hsin]
  -- now: `1 − 4α² ≤ cos(π/2 − γ)²`
  by_cases hcase : 1 - 4 * α ^ 2 ≤ 0
  · nlinarith [sq_nonneg (Real.cos (Real.pi / 2 - γ))]
  · push Not at hcase
    have hα2lt : α ^ 2 < 1 / 4 := by nlinarith
    have hpos : 0 ≤ 1 - 2 * α ^ 2 := by nlinarith
    have hcos_lower : 1 - 2 * α ^ 2 ≤ Real.cos (2 * α) := by
      have h := Real.one_sub_sq_div_two_le_cos (x := 2 * α)
      nlinarith [h]
    have hstep : (1 - 2 * α ^ 2) ^ 2 ≤ Real.cos (2 * α) ^ 2 :=
      pow_le_pow_left₀ hpos hcos_lower 2
    have hexpand : (1 - 2 * α ^ 2) ^ 2 = 1 - 4 * α ^ 2 + 4 * α ^ 4 := by ring
    nlinarith [hstep, hsq, sq_nonneg (α ^ 2)]

end Qatlib.Papers.QWalkCollide22.MainResults
