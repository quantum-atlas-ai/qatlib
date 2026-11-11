/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# CIRPricing.ChiSquaredShift

Source: Herman, Sun, Liu, Pistoia, Che, Otter, Chakrabarti, Harrow,
*Quantum Speedups for Derivative Pricing Beyond Black-Scholes*,
fixed version arXiv:2602.03725v1, Appendix F, Lemma F.6
(v1 text, line 6919 of the extracted source):

> Let `Y` be `χ²_r` distributed. Then for `m < 1/2`,
> `∫_α^∞ exp(m y) p(y) dy = (1 − 2m)^{−r/2} P[Y ≥ (1 − 2m) α]`.

The printed proof substitutes `y = z/(1 − 2m)`: with the `χ²_r` density
`p(y) = y^{r/2−1} e^{−y/2} / (2^{r/2} Γ(r/2))` one gets
`exp(m y) p(y) dy = (1−2m)^{−r/2} p(z) dz` for `z = (1−2m) y`, hence the stated
identity between the two tail integrals.

This module formalises exactly that change of variables at the level of the
density: `χ²_r` is the Gamma distribution with shape `a = r/2` and rate `1/2`,
whose density is `ProbabilityTheory.gammaPDFReal a (1/2)`, so the statement is
the identity
`∫_{y > α} e^{my} p(y) dy = (1 − 2m)^{−a} ∫_{z > (1−2m)α} p(z) dz`.

Boundary: `α ≥ 0` and `a > 0` are assumed (the paper's tail parameter is
nonnegative and `r ≥ 2` gives `a ≥ 1`); the probability interpretation
`P[Y ≥ β] = ∫_{z > β} p` is the definition of the density integral and is
stated in that form, while measurability/probability-space packaging of `χ²_r`
itself is not duplicated here.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Topology

namespace Qatlib.Papers.DerivPricing26.CIRPricing.ChiSquaredShift

/-- Lemma F.6: for `α ≥ 0` and `m < 1/2`, the exponentially tilted `χ²` tail
integral is the untitled tail integral at the rescaled point `(1 − 2m) α`,
scaled by `(1 − 2m)^{−r/2}` (written with the Gamma shape parameter
`a = r/2`). -/
theorem lemmaF6_chiSquared_shift {a m α : ℝ} (ha : 0 < a) (hα : 0 ≤ α) (hm : m < 1 / 2) :
    ∫ y in Set.Ioi α, Real.exp (m * y) * ProbabilityTheory.gammaPDFReal a (1 / 2) y
      = (1 - 2 * m) ^ (-a) *
        ∫ z in Set.Ioi ((1 - 2 * m) * α), ProbabilityTheory.gammaPDFReal a (1 / 2) z := by
  have hb : (0 : ℝ) < 1 - 2 * m := by linarith
  have hlam : (0 : ℝ) < 1 / 2 - m := by linarith
  set b : ℝ := 1 - 2 * m with hbdef
  set lam : ℝ := 1 / 2 - m with hldef
  have hb2 : b = 2 * lam := by rw [hbdef, hldef]; ring
  set C : ℝ := (1 / 2) ^ a / Real.Gamma a with hCdef
  -- the density has its closed form on the positive axis
  have hdens : ∀ x : ℝ, 0 < x →
      ProbabilityTheory.gammaPDFReal a (1 / 2) x = C * (x ^ (a - 1) * Real.exp (-(x / 2))) := by
    intro x hx
    have harg : -((1 / 2 : ℝ) * x) = -(x / 2) := by ring
    simp only [ProbabilityTheory.gammaPDFReal, if_pos hx.le, harg, hCdef, mul_assoc]
  -- left side as `C` times the tilted monomial integral
  have hL : ∫ y in Set.Ioi α, Real.exp (m * y) * ProbabilityTheory.gammaPDFReal a (1 / 2) y
      = C * ∫ y in Set.Ioi α, y ^ (a - 1) * Real.exp (-(lam * y)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    have hy0 : 0 < y := lt_of_le_of_lt hα (Set.mem_Ioi.mp hy)
    rw [hdens y hy0]
    have hexp : Real.exp (m * y) * Real.exp (-(y / 2)) = Real.exp (-(lam * y)) := by
      rw [← Real.exp_add]
      congr 1
      rw [hldef]
      ring
    calc Real.exp (m * y) * (C * (y ^ (a - 1) * Real.exp (-(y / 2))))
        = C * (y ^ (a - 1) * (Real.exp (m * y) * Real.exp (-(y / 2)))) := by ring
      _ = C * (y ^ (a - 1) * Real.exp (-(lam * y))) := by rw [hexp]
  -- right side as `C` times the untitled monomial integral
  have hR : ∫ z in Set.Ioi (b * α), ProbabilityTheory.gammaPDFReal a (1 / 2) z
      = C * ∫ z in Set.Ioi (b * α), z ^ (a - 1) * Real.exp (-(z / 2)) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun z hz => ?_
    have hz0 : 0 < z := lt_of_le_of_lt (by positivity : (0 : ℝ) ≤ b * α) (Set.mem_Ioi.mp hz)
    rw [hdens z hz0]
  -- the change of variables `y = z / b` with `b = 1 - 2m`
  have hscale : ∫ x in Set.Ioi α, (b * x) ^ (a - 1) * Real.exp (-((b * x) / 2))
      = b⁻¹ * ∫ z in Set.Ioi (b * α), z ^ (a - 1) * Real.exp (-(z / 2)) := by
    have := MeasureTheory.integral_comp_mul_left_Ioi
      (fun z : ℝ => z ^ (a - 1) * Real.exp (-(z / 2))) α hb
    simpa [smul_eq_mul] using this
  have hpt : ∀ x ∈ Set.Ioi α, (b * x) ^ (a - 1) * Real.exp (-((b * x) / 2))
      = b ^ (a - 1) * (x ^ (a - 1) * Real.exp (-(lam * x))) := by
    intro x hx
    have hx0 : 0 < x := lt_of_le_of_lt hα (Set.mem_Ioi.mp hx)
    rw [Real.mul_rpow hb.le hx0.le]
    have hexp : Real.exp (-((b * x) / 2)) = Real.exp (-(lam * x)) := by
      congr 1
      rw [hb2]
      ring
    rw [hexp]
    ring
  have hI : b ^ (a - 1) * (∫ x in Set.Ioi α, x ^ (a - 1) * Real.exp (-(lam * x)))
      = b⁻¹ * ∫ z in Set.Ioi (b * α), z ^ (a - 1) * Real.exp (-(z / 2)) := by
    rw [← hscale, ← MeasureTheory.integral_const_mul]
    exact (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt).symm
  -- solve for the tilted integral
  have hIeq : (∫ x in Set.Ioi α, x ^ (a - 1) * Real.exp (-(lam * x)))
      = b ^ (-a) * ∫ z in Set.Ioi (b * α), z ^ (a - 1) * Real.exp (-(z / 2)) := by
    have hbpow : b ^ (a - 1) = b ^ a / b := by
      rw [Real.rpow_sub hb, Real.rpow_one]
    rw [hbpow] at hI
    have h2 : b ^ a * (∫ x in Set.Ioi α, x ^ (a - 1) * Real.exp (-(lam * x)))
        = ∫ z in Set.Ioi (b * α), z ^ (a - 1) * Real.exp (-(z / 2)) := by
      field_simp at hI ⊢
      linarith [hI]
    rw [Real.rpow_neg hb.le, ← h2]
    have hbne : b ^ a ≠ 0 := (Real.rpow_ne_zero hb.le ha.ne').mpr hb.ne'
    field_simp
  rw [hL, hR, hIeq]
  rw [hbdef] at *
  ring

end Qatlib.Papers.DerivPricing26.CIRPricing.ChiSquaredShift
