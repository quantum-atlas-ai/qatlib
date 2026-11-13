/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Qatlib.Papers.QLinearSolver24.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Kernel-reflection quantum linear solver: Theorem 1 and Corollary 1

This file formalizes the analytic bounds of Theorem 1 and Corollary 1 in Section 5 (pp. 22–24,
Eqs. (68)–(72) and (81)) of [Dalzell, 2024][Dalzell2024]:

* `theorem1_success_probability`: non-emptiness of the success-probability sandwich (Eq. (71)).
* `theorem1_fidelity_bounds`: well-definedness and range bounds for the state distance, trace
  distance, and overlap expressions (Eqs. (68)–(70)).
* `theorem1_query_degree`: upper bound `algorithm1Degree κ η ≤ ⌈(κ / 2) ln(2 / η)⌉` on the
  Chebyshev degree (Eq. (72)).
* `corollary1_expected_queries`: exact algebraic identity for the expected query bound under
  uniform `t`-sampling (Corollary 1, Eq. (81)).

## Main statements

* `theorem1_success_probability`: `theorem1SuccessLower η θt ≤ theorem1SuccessUpper η θt`.
* `theorem1_fidelity_bounds`: range bounds for Eqs. (68)–(70).
* `theorem1_query_degree`: `algorithm1Degree κ η ≤ ⌈(κ / 2) * log (2 / η)⌉` (Eq. (72)).
* `corollary1_expected_queries`: expected query bound identity (Eq. (81)).

## References

* [Dalzell, 2024][Dalzell2024]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QLinearSolver24.MainResults.TheoremOneCorollaryOne

open Qatlib.Papers.QLinearSolver24.MainResults

/-- Left-hand side of the success-probability sandwich, Eq. (71), p. 22. -/
def theorem1SuccessLower (η θt : ℝ) : ℝ :=
  Real.sin (2 * θt) ^ 2 * ((1 - η) / (1 + η)) ^ 2

/-- Right-hand side of the success-probability sandwich, Eq. (71), p. 22. -/
def theorem1SuccessUpper (η θt : ℝ) : ℝ :=
  Real.sin (2 * θt) ^ 2 + 4 * η ^ 2 / (1 + η) ^ 2 * Real.sin θt ^ 2

/-- Average success probability of the uniform-`t` strategy of Corollary 1:
`β² / (β² + 1)² · ((1 - δ) / (1 + δ))²` with `δ = ε / (2 √(β² + 1))` (p. 24). -/
def corollary1AvgSuccess (β ε : ℝ) : ℝ :=
  β ^ 2 / (β ^ 2 + 1) ^ 2 *
    ((1 - ε / (2 * Real.sqrt (β ^ 2 + 1))) /
      (1 + ε / (2 * Real.sqrt (β ^ 2 + 1)))) ^ 2

/-- **Theorem 1, Eq. (71)** ([Dalzell, 2024][Dalzell2024], p. 22): the lower and upper bounds
in the success-probability sandwich satisfy `theorem1SuccessLower η θt ≤ theorem1SuccessUpper η θt`
for all `0 < η ≤ 1` and `θt : ℝ`. -/
theorem theorem1_success_probability (η θt : ℝ) (hη0 : 0 < η) (_hη1 : η ≤ 1) :
    theorem1SuccessLower η θt ≤ theorem1SuccessUpper η θt := by
  unfold theorem1SuccessLower theorem1SuccessUpper
  have hratio : ((1 - η) / (1 + η)) ^ 2 ≤ 1 := by
    rw [div_pow, div_le_one (by positivity)]
    nlinarith
  have hsq : 0 ≤ Real.sin (2 * θt) ^ 2 := sq_nonneg _
  have hstep : Real.sin (2 * θt) ^ 2 * ((1 - η) / (1 + η)) ^ 2
      ≤ Real.sin (2 * θt) ^ 2 * 1 :=
    mul_le_mul_of_nonneg_left hratio hsq
  have hextra : 0 ≤ 4 * η ^ 2 / (1 + η) ^ 2 * Real.sin θt ^ 2 := by positivity
  nlinarith [hstep, hextra]

/-- **Theorem 1, Eqs. (68)–(70)** ([Dalzell, 2024][Dalzell2024], p. 22): under `η / cos θt ≤ 1`
and `cos θt > 0`, the angle bound is at most `π / 2` and the overlap radicand lies in `[0, 1]`. -/
theorem theorem1_fidelity_bounds (η θt : ℝ) (hη0 : 0 < η) (hcos : 0 < Real.cos θt)
    (hθ : η / Real.cos θt ≤ 1) :
    Real.arcsin (η / Real.cos θt) ≤ Real.pi / 2 ∧
      Real.sqrt (1 - (η / Real.cos θt) ^ 2) ≤ 1 ∧
        0 ≤ 1 - (η / Real.cos θt) ^ 2 := by
  have hδ1 : η / Real.cos θt ≤ 1 := hθ
  have _hδ0 : 0 ≤ η / Real.cos θt := le_of_lt (div_pos hη0 hcos)
  have hsq : 0 ≤ 1 - (η / Real.cos θt) ^ 2 := by nlinarith
  refine ⟨?_, ?_, hsq⟩
  · have h := Real.arcsin_le_arcsin hδ1
    rwa [Real.arcsin_one] at h
  · rw [Real.sqrt_le_one]
    nlinarith [sq_nonneg (η / Real.cos θt)]

/-- Auxiliary bound `exp (2 * t) ≤ (1 + t) / (1 - t)` for `t ∈ (0, 1)`. -/
private lemma exp_two_mul_le_one_add_div_one_sub {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1) :
    Real.exp (2 * t) ≤ (1 + t) / (1 - t) := by
  let g : ℝ → ℝ := fun s => (1 + s) * Real.exp (-s) - (1 - s) * Real.exp s
  have hg_deriv : ∀ s : ℝ, HasDerivAt g (s * (Real.exp s - Real.exp (-s))) s := by
    intro s
    have h1 : HasDerivAt (fun x => 1 + x) 1 s := (hasDerivAt_id s).const_add 1
    have h2 : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-s)) s := by
      simpa using ((hasDerivAt_id s).neg).exp
    have h3 : HasDerivAt (fun x => 1 - x) (-1) s := (hasDerivAt_id s).const_sub 1
    have h4 : HasDerivAt Real.exp (Real.exp s) s := Real.hasDerivAt_exp s
    convert (h1.mul h2).sub (h3.mul h4) using 1
    ring
  have hg_mono : MonotoneOn g (Set.Ici 0) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici 0)
      (fun s _ => (hg_deriv s).continuousAt.continuousWithinAt)
      (fun s _ => (hg_deriv s).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    have hs0 : 0 ≤ s := le_of_lt (by simpa [interior_Ici] using hs)
    rw [(hg_deriv s).deriv]
    have hexp_ge : Real.exp (-s) ≤ Real.exp s := Real.exp_le_exp.mpr (by linarith)
    exact mul_nonneg hs0 (sub_nonneg.mpr hexp_ge)
  have hg_nonneg : g 0 ≤ g t := hg_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0.le) ht0.le
  have hg0 : g 0 = 0 := by simp [g]
  rw [hg0] at hg_nonneg
  have h1mt_pos : 0 < 1 - t := by linarith
  have hineq : (1 - t) * Real.exp t ≤ (1 + t) * Real.exp (-t) := by
    dsimp [g] at hg_nonneg
    linarith
  rw [le_div_iff₀ h1mt_pos]
  calc Real.exp (2 * t) * (1 - t)
      = Real.exp t * ((1 - t) * Real.exp t) := by
        rw [show 2 * t = t + t by ring, Real.exp_add]
        ring
    _ ≤ Real.exp t * ((1 + t) * Real.exp (-t)) :=
        mul_le_mul_of_nonneg_left hineq (Real.exp_pos t).le
    _ = (1 + t) * (Real.exp t * Real.exp (-t)) := by ring
    _ = 1 + t := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- **Theorem 1, Eq. (72)** ([Dalzell, 2024][Dalzell2024], p. 22): the degree
`algorithm1Degree κ η = ⌈arcosh(η⁻¹) / arcosh((1 + κ⁻²) / (1 - κ⁻²))⌉` of Algorithm 1 is at most
`⌈(κ / 2) · ln(2 / η)⌉`. -/
theorem theorem1_query_degree (κ η : ℝ) (hκ : 1 < κ) (hη0 : 0 < η) (hη1 : η ≤ 1) :
    (algorithm1Degree κ η : ℝ)
      ≤ (Nat.ceil (κ / 2 * Real.log (2 / η)) : ℝ) := by
  exact_mod_cast Nat.ceil_mono (by
    have hκ_pos : 0 < κ := by linarith
    have hκ2_gt1 : 1 < κ ^ 2 := by nlinarith
    have hden_pos : 0 < κ ^ 2 - 1 := by linarith
    have hκm1_pos : 0 < κ - 1 := by linarith
    -- Upper bound on numerator: `arcosh (η⁻¹) ≤ log (2 / η)`
    have hη_inv_ge1 : 1 ≤ η⁻¹ := one_le_inv₀ hη0 |>.mpr hη1
    have hη_inv_pos : 0 < η⁻¹ := inv_pos.mpr hη0
    have hnum_le : Real.arcosh η⁻¹ ≤ Real.log (2 / η) := by
      unfold Real.arcosh
      have hrad_le : Real.sqrt ((η⁻¹) ^ 2 - 1) ≤ η⁻¹ := by
        rw [Real.sqrt_le_left hη_inv_pos.le]
        linarith
      refine Real.log_le_log (by positivity) ?_
      have h2div : 2 / η = 2 * η⁻¹ := by ring
      linarith
    -- Lower bound on denominator: `2 / κ ≤ arcosh ((1 + κ ^ (-2 : ℤ)) / (1 - κ ^ (-2 : ℤ)))`
    let c : ℝ := (1 + κ ^ (-2 : ℤ)) / (1 - κ ^ (-2 : ℤ))
    have hc_eq : c = (κ ^ 2 + 1) / (κ ^ 2 - 1) := by
      dsimp [c]
      have hzpow : κ ^ (-2 : ℤ) = (κ ^ 2)⁻¹ := by
        rw [zpow_neg, zpow_ofNat]
      rw [hzpow]
      field_simp [hκ_pos.ne', hden_pos.ne']
    have harcosh_c : Real.arcosh c = Real.log ((κ + 1) / (κ - 1)) := by
      unfold Real.arcosh
      rw [hc_eq]
      have hcsq : ((κ ^ 2 + 1) / (κ ^ 2 - 1)) ^ 2 - 1 = (2 * κ / (κ ^ 2 - 1)) ^ 2 := by
        field_simp [hden_pos.ne']
        ring
      rw [hcsq, Real.sqrt_sq (by positivity)]
      congr 1
      field_simp [hden_pos.ne', hκm1_pos.ne']
      ring
    have hden_ge : 2 / κ ≤ Real.arcosh c := by
      rw [harcosh_c]
      let t : ℝ := κ⁻¹
      have ht0 : 0 < t := inv_pos.mpr hκ_pos
      have ht1 : t < 1 := inv_lt_one_of_one_lt₀ hκ
      have hexp := exp_two_mul_le_one_add_div_one_sub ht0 ht1
      have hratio_eq : (1 + t) / (1 - t) = (κ + 1) / (κ - 1) := by
        dsimp [t]
        field_simp [hκ_pos.ne', hκm1_pos.ne']
      rw [hratio_eq] at hexp
      have hlog := Real.log_le_log (Real.exp_pos _) hexp
      rw [Real.log_exp] at hlog
      have h2t : 2 * t = 2 / κ := by
        dsimp [t]
        ring
      linarith
    have harcosh_c_pos : 0 < Real.arcosh c := lt_of_lt_of_le (by positivity) hden_ge
    have harcosh_η_nonneg : 0 ≤ Real.arcosh η⁻¹ := Real.arcosh_nonneg hη_inv_ge1
    calc Real.arcosh η⁻¹ / Real.arcosh c
        ≤ Real.arcosh η⁻¹ / (2 / κ) :=
          div_le_div_of_nonneg_left harcosh_η_nonneg (by positivity) hden_ge
      _ ≤ Real.log (2 / η) / (2 / κ) :=
          div_le_div_of_nonneg_right hnum_le (by positivity)
      _ = κ / 2 * Real.log (2 / η) := by
          field_simp [hκ_pos.ne'])

/-- **Corollary 1, Eq. (81)** ([Dalzell, 2024][Dalzell2024], p. 24): expected query bound under
uniform `t`-sampling. -/
theorem corollary1_expected_queries (β κ ε : ℝ) (hβ : 1 ≤ β) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (1 / corollary1AvgSuccess β ε) *
        (Nat.ceil (κ / 2 * Real.log (4 * Real.sqrt (β ^ 2 + 1) / ε)) : ℝ)
      = corollary1QueryBound β κ ε := by
  unfold corollary1AvgSuccess corollary1QueryBound
  have hs : (0 : ℝ) < Real.sqrt (β ^ 2 + 1) := Real.sqrt_pos.mpr (by positivity)
  have hroot : (1 : ℝ) ≤ Real.sqrt (β ^ 2 + 1) := by
    have := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ β ^ 2 + 1 by nlinarith)
    simpa using this
  have hlt : ε < 2 * Real.sqrt (β ^ 2 + 1) := by nlinarith
  have h1 : (1 + ε / (2 * Real.sqrt (β ^ 2 + 1))) ≠ 0 := by
    have : 0 < 1 + ε / (2 * Real.sqrt (β ^ 2 + 1)) := by positivity
    linarith
  have h2 : (1 - ε / (2 * Real.sqrt (β ^ 2 + 1))) ≠ 0 := by
    have : 0 < 1 - ε / (2 * Real.sqrt (β ^ 2 + 1)) := by
      rw [sub_pos, div_lt_one (by positivity)]
      exact hlt
    linarith
  field_simp

end Qatlib.Papers.QLinearSolver24.MainResults.TheoremOneCorollaryOne
