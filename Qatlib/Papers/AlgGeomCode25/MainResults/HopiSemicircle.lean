/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# The semicircle-law satisfaction fraction of Theorem 1

Source: `arXiv:2510.06603v1`, Andi Gu and Stephen P. Jordan, "Algebraic Geometry
Codes and Decoded Quantum Interferometry", Section 4 (page 11), Theorem 1, Eq. (8).

Theorem 1 states that Decoded Quantum Interferometry on a HOPI instance achieves the
expected satisfaction fraction

`(√((ℓ/n)(1 - r/q^2)) + √((r/q^2)(1 - ℓ/n)))^2` when `r/q^2 ≤ 1 - ℓ/n`, and `1`
otherwise,

where `r/q^2` is the fraction of the alphabet `𝔽_{q^2}` taken by a constraint set and
`ℓ/n` is the fraction of constraints addressed by the dual decoder radius. The paper
says the formula "follows directly from the general semicircle law" of
`arXiv:2408.08292v5`, Eq. (6), whose only inputs are the length `n`, the constraint-set
size `r` and the decoding radius `ℓ`.

This module formalizes the closed form as a function of the two fractions, together
with the mathematical consequences the paper draws from it: the curve is a squared
cosine, hence bounded by `1` and saturating exactly at `ℓ/n + r/q^2 = 1`; it reduces to
the random-guessing baseline `r/q^2` at zero decoding radius; it is the semicircle
`1/2 + √(ε(1-ε))` in the balanced case `r/q^2 = 1/2`; and it is nondecreasing in the
decoding radius throughout the semicircle regime. The DQI expectation itself is not
reproved here.

`1 - curve = (√((1-ε)(1-α)) - √(εα))^2` is the key identity: it makes the complement
of the curve an explicit square, which is what all of the bounds below use.
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.AlgGeomCode25.MainResults

/-- The semicircle-law satisfaction fraction of `arXiv:2408.08292v5` Eq. (6) /
`arXiv:2510.06603v1` Eq. (8), as a function of the decoding fraction `ε = ℓ/n` and the
constraint-set fraction `α = r/q^2`. -/
def semicircleFraction (ε α : ℝ) : ℝ :=
  (Real.sqrt (ε * (1 - α)) + Real.sqrt (α * (1 - ε))) ^ 2

/-- The piecewise expected satisfaction fraction of Theorem 1: the semicircle value in
the regime `r/q^2 ≤ 1 - ℓ/n`, and full satisfaction `1` otherwise. -/
def hopiSatisfactionFraction (ε α : ℝ) : ℝ :=
  if α ≤ 1 - ε then semicircleFraction ε α else 1

/-- **Complement form of the curve.** On `[0,1]^2` the complement of the semicircle
fraction is a square, `1 - curve = (√((1-ε)(1-α)) - √(εα))^2`. This is the identity
that yields the range, the saturation point and the monotonicity of the curve. -/
theorem semicircleFraction_complement {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    1 - semicircleFraction ε α =
      (Real.sqrt ((1 - ε) * (1 - α)) - Real.sqrt (ε * α)) ^ 2 := by
  unfold semicircleFraction
  have h1 : 0 ≤ ε * (1 - α) := mul_nonneg hε0 (by linarith)
  have h2 : 0 ≤ α * (1 - ε) := mul_nonneg hα0 (by linarith)
  have h3 : 0 ≤ (1 - ε) * (1 - α) := mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ ε * α := mul_nonneg hε0 hα0
  have hAB : Real.sqrt (ε * (1 - α)) * Real.sqrt (α * (1 - ε))
      = Real.sqrt (ε * α) * Real.sqrt ((1 - ε) * (1 - α)) := by
    rw [← Real.sqrt_mul h1, ← Real.sqrt_mul h4]
    congr 1
    ring
  have e1 := Real.sq_sqrt h1
  have e2 := Real.sq_sqrt h2
  have e3 := Real.sq_sqrt h3
  have e4 := Real.sq_sqrt h4
  nlinarith [hAB, e1, e2, e3, e4]

/-- The semicircle fraction never exceeds `1`, i.e. DQI cannot satisfy more than all
constraints. -/
theorem semicircleFraction_le_one {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : semicircleFraction ε α ≤ 1 := by
  have h := semicircleFraction_complement hε0 hε1 hα0 hα1
  nlinarith [sq_nonneg (Real.sqrt ((1 - ε) * (1 - α)) - Real.sqrt (ε * α))]

/-- The semicircle fraction saturates exactly on the line `ℓ/n + r/q^2 = 1`; this is
the equality case of the squared-cosine form. -/
theorem semicircleFraction_eq_one_iff {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : semicircleFraction ε α = 1 ↔ ε + α = 1 := by
  have h3 : 0 ≤ (1 - ε) * (1 - α) := mul_nonneg (by linarith) (by linarith)
  have h4 : 0 ≤ ε * α := mul_nonneg hε0 hα0
  have hcomp := semicircleFraction_complement hε0 hε1 hα0 hα1
  constructor
  · intro hs
    have hz : (Real.sqrt ((1 - ε) * (1 - α)) - Real.sqrt (ε * α)) ^ 2 = 0 := by linarith
    have hsq := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    have heq : Real.sqrt ((1 - ε) * (1 - α)) = Real.sqrt (ε * α) := sub_eq_zero.mp hsq
    have := Real.sqrt_inj h3 h4 |>.mp heq
    nlinarith
  · intro h
    have heq : (1 - ε) * (1 - α) = ε * α := by nlinarith
    have hzero : Real.sqrt ((1 - ε) * (1 - α)) - Real.sqrt (ε * α) = 0 := by
      rw [heq, sub_self]
    rw [hzero] at hcomp
    linarith

/-- At zero decoding radius the semicircle fraction is exactly `r/q^2`, the fraction of
constraints satisfied by a uniformly random assignment (the paper's remark that `r/p`
is the random-guessing value). -/
theorem semicircleFraction_zero_left {α : ℝ} (hα : 0 ≤ α) :
    semicircleFraction 0 α = α := by
  unfold semicircleFraction
  rw [show (0:ℝ) * (1 - α) = 0 by ring, Real.sqrt_zero, zero_add]
  rw [show (1:ℝ) - 0 = 1 by ring, mul_one]
  exact Real.sq_sqrt hα

/-- In the balanced case `r/q^2 = 1/2` the curve is `1/2 + √(ε(1-ε))`, the semicircle
that gives the law its name (`arXiv:2408.08292v5`, discussion of Eq. (6)). -/
theorem semicircleFraction_balanced {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    semicircleFraction ε (1/2) = 1/2 + Real.sqrt (ε * (1 - ε)) := by
  unfold semicircleFraction
  have h1 : 0 ≤ ε / 2 := by linarith
  have h2 : 0 ≤ (1 - ε) / 2 := by linarith
  have hprod : Real.sqrt (ε * (1 - 1/2)) * Real.sqrt ((1/2 : ℝ) * (1 - ε))
      = Real.sqrt (ε * (1 - ε)) / 2 := by
    rw [show ε * (1 - 1/2) = ε / 2 by ring,
      show (1/2 : ℝ) * (1 - ε) = (1 - ε) / 2 by ring]
    rw [← Real.sqrt_mul h1]
    rw [show ε / 2 * ((1 - ε) / 2) = ε * (1 - ε) * (1/4) by ring]
    rw [Real.sqrt_mul (by nlinarith : (0:ℝ) ≤ ε * (1 - ε))]
    rw [show Real.sqrt ((1:ℝ)/4) = 1 / 2 by
      rw [show (1:ℝ)/4 = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)]]
    ring
  have e1 : Real.sqrt (ε * (1 - 1/2)) ^ 2 = ε / 2 := by
    rw [show ε * (1 - 1/2) = ε / 2 by ring]; exact Real.sq_sqrt h1
  have e2 : Real.sqrt ((1/2 : ℝ) * (1 - ε)) ^ 2 = (1 - ε) / 2 := by
    rw [show (1/2 : ℝ) * (1 - ε) = (1 - ε) / 2 by ring]; exact Real.sq_sqrt h2
  nlinarith [hprod, e1, e2]

/-- Throughout the semicircle regime `ε + α ≤ 1`, a larger decoding radius can only
improve the expected satisfaction fraction. This is the paper's statement that the
formula "makes precise the connection between the error-correcting capability of the
dual Hermitian code and the quality of approximate solutions". -/
theorem semicircleFraction_mono_left {ε₁ ε₂ α : ℝ} (hε₁ : 0 ≤ ε₁) (hε : ε₁ ≤ ε₂)
    (hε₂ : ε₂ + α ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    semicircleFraction ε₁ α ≤ semicircleFraction ε₂ α := by
  have h2 : ε₂ ≤ 1 := by linarith
  have h1 : ε₁ ≤ 1 := by linarith
  have hc1 : 1 - semicircleFraction ε₁ α =
      (Real.sqrt ((1 - ε₁) * (1 - α)) - Real.sqrt (ε₁ * α)) ^ 2 :=
    semicircleFraction_complement hε₁ h1 hα0 hα1
  have hc2 : 1 - semicircleFraction ε₂ α =
      (Real.sqrt ((1 - ε₂) * (1 - α)) - Real.sqrt (ε₂ * α)) ^ 2 :=
    semicircleFraction_complement (hε₁.trans hε) h2 hα0 hα1
  have hC : Real.sqrt ((1 - ε₂) * (1 - α)) ≤ Real.sqrt ((1 - ε₁) * (1 - α)) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hD : Real.sqrt (ε₁ * α) ≤ Real.sqrt (ε₂ * α) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have hC2D2 : 0 ≤ Real.sqrt ((1 - ε₂) * (1 - α)) - Real.sqrt (ε₂ * α) := by
    have : Real.sqrt (ε₂ * α) ≤ Real.sqrt ((1 - ε₂) * (1 - α)) := by
      apply Real.sqrt_le_sqrt
      nlinarith
    linarith
  have hle : Real.sqrt ((1 - ε₂) * (1 - α)) - Real.sqrt (ε₂ * α)
      ≤ Real.sqrt ((1 - ε₁) * (1 - α)) - Real.sqrt (ε₁ * α) := by linarith
  have hsq : (Real.sqrt ((1 - ε₂) * (1 - α)) - Real.sqrt (ε₂ * α)) ^ 2
      ≤ (Real.sqrt ((1 - ε₁) * (1 - α)) - Real.sqrt (ε₁ * α)) ^ 2 := by
    simpa [pow_two] using mul_self_le_mul_self hC2D2 hle
  linarith

/-- In the semicircle regime `α ≤ 1 - ε` the piecewise fraction is the curve itself. -/
theorem hopiSatisfactionFraction_eq_semicircleFraction {ε α : ℝ} (h : α ≤ 1 - ε) :
    hopiSatisfactionFraction ε α = semicircleFraction ε α := by
  unfold hopiSatisfactionFraction
  rw [if_pos h]

/-- Outside the semicircle regime the paper assigns full satisfaction `1`. -/
theorem hopiSatisfactionFraction_eq_one {ε α : ℝ} (h : ¬ α ≤ 1 - ε) :
    hopiSatisfactionFraction ε α = 1 := by
  unfold hopiSatisfactionFraction
  rw [if_neg h]

/-- The piecewise fraction is nonnegative for every pair of rates. -/
theorem hopiSatisfactionFraction_nonneg (ε α : ℝ) : 0 ≤ hopiSatisfactionFraction ε α := by
  unfold hopiSatisfactionFraction
  split
  · unfold semicircleFraction
    positivity
  · norm_num

/-- The piecewise fraction is at most `1` on `[0,1]^2`. -/
theorem hopiSatisfactionFraction_le_one {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : hopiSatisfactionFraction ε α ≤ 1 := by
  unfold hopiSatisfactionFraction
  split
  · exact semicircleFraction_le_one hε0 hε1 hα0 hα1
  · exact le_refl 1

/-- The piecewise fraction reaches `1` exactly when `ℓ/n + r/q^2 ≥ 1`: either the curve
saturates on the line `ℓ/n + r/q^2 = 1`, or the paper's second branch already reports
full satisfaction. -/
theorem hopiSatisfactionFraction_eq_one_iff {ε α : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    hopiSatisfactionFraction ε α = 1 ↔ 1 ≤ ε + α := by
  unfold hopiSatisfactionFraction
  split
  · rename_i hle
    have hle' : ε + α ≤ 1 := by linarith
    rw [semicircleFraction_eq_one_iff hε0 hε1 hα0 hα1]
    constructor <;> intro h' <;> linarith
  · rename_i hgt
    have hgt' : 1 ≤ ε + α := by linarith
    exact ⟨fun _ => hgt', fun _ => rfl⟩

/-- On the boundary `α = 1 - ε` both branches of Theorem 1 agree on `1`, so the
piecewise definition is continuous there. -/
theorem hopiSatisfactionFraction_boundary {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    hopiSatisfactionFraction ε (1 - ε) = 1 := by
  rw [hopiSatisfactionFraction_eq_semicircleFraction (le_refl _)]
  exact (semicircleFraction_eq_one_iff hε0 hε1 (by linarith) (by linarith)).mpr
    (by ring)

/-- DQI's expected satisfaction fraction is never below the random-guessing baseline
`r/q^2` on `[0,1]^2`. -/
theorem hopiSatisfactionFraction_lower_bound {ε α : ℝ} (hε0 : 0 ≤ ε)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) : α ≤ hopiSatisfactionFraction ε α := by
  unfold hopiSatisfactionFraction
  split
  · rename_i hle
    have hle' : ε + α ≤ 1 := by linarith
    calc α = semicircleFraction 0 α := (semicircleFraction_zero_left hα0).symm
      _ ≤ semicircleFraction ε α :=
        semicircleFraction_mono_left le_rfl hε0 hle' hα0 hα1
  · linarith

/-- The piecewise fraction is nondecreasing in the decoding fraction `ℓ/n`: a larger
decoding radius either stays inside the semicircle regime, where
`semicircleFraction_mono_left` applies, or lands in the second branch, which is the
constant `1`. -/
theorem hopiSatisfactionFraction_mono_left {ε₁ ε₂ α : ℝ} (hε₁ : 0 ≤ ε₁) (hε : ε₁ ≤ ε₂)
    (hε₂ : ε₂ ≤ 1) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    hopiSatisfactionFraction ε₁ α ≤ hopiSatisfactionFraction ε₂ α := by
  by_cases h₂ : α ≤ 1 - ε₂
  · have h₁ : α ≤ 1 - ε₁ := by linarith
    rw [hopiSatisfactionFraction_eq_semicircleFraction h₂,
      hopiSatisfactionFraction_eq_semicircleFraction h₁]
    exact semicircleFraction_mono_left hε₁ hε (by linarith) hα0 hα1
  · rw [hopiSatisfactionFraction_eq_one h₂]
    exact hopiSatisfactionFraction_le_one hε₁ (hε.trans hε₂) hα0 hα1

end Qatlib.Papers.AlgGeomCode25.MainResults
