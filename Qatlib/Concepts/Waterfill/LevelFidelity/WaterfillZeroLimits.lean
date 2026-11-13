/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
import Mathlib.Topology.Algebra.Order.Field

/-!
# Water-fill limits at zero target coordinates

This module proves continuity in target coordinates at fixed levels, including fidelity
convergence when the limiting mass is nonzero. It also analyzes levels `lam / δ` under positive
target regularization, giving eventual saturation on positive-target coordinates and clipping on
zero-target coordinates in the water-fill setting of [OzolsRoettelerRoland2013].

## Main statements

* `fidelity_parameter_tendsto`: Pass to fidelity limits at nonzero mass.
* `boundary_fill`: Identify the eventual coordinatewise boundary fill.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.WaterLevel.WaterPrecision

set_option autoImplicit false
open Filter Set Qatlib.Concepts.WaterLevel.WaterPrecision
open scoped Topology BigOperators
namespace Qatlib.Concepts.Waterfill.LevelFidelity
variable {α : Type} {m : ℕ} {l : Filter α}

/-- Coordinatewise convergence of the target implies convergence of each filled coordinate at a
fixed source and level. -/
theorem fill_parameter_tendsto (π σ : Fin m → ℝ) (σn : α → Fin m → ℝ)
    (hσ : ∀ i, Tendsto (fun n => σn n i) l (𝓝 (σ i))) (γ : ℝ) (i : Fin m) :
    Tendsto (fun n => realFill π (σn n) γ i) l (𝓝 (realFill π σ γ i)) :=
  tendsto_const_nhds.min (tendsto_const_nhds.mul (hσ i))

/-- Coordinatewise convergence of the target implies convergence of the fill mass at a fixed
source and level. -/
theorem mass_parameter_tendsto (π σ : Fin m → ℝ) (σn : α → Fin m → ℝ)
    (hσ : ∀ i, Tendsto (fun n => σn n i) l (𝓝 (σ i))) (γ : ℝ) :
    Tendsto (fun n => realMass π (σn n) γ) l (𝓝 (realMass π σ γ)) := by
  have hcont : Continuous (fun s : Fin m → ℝ => realMass π s γ) := by
    unfold realMass realFill
    fun_prop
  exact hcont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hσ)

/-- Coordinatewise convergence of the target implies convergence of the target overlap at a
fixed source and level. -/
theorem dot_parameter_tendsto (π σ : Fin m → ℝ) (σn : α → Fin m → ℝ)
    (hσ : ∀ i, Tendsto (fun n => σn n i) l (𝓝 (σ i))) (γ : ℝ) :
    Tendsto (fun n => realDot π (σn n) γ) l (𝓝 (realDot π σ γ)) := by
  have hcont : Continuous (fun s : Fin m → ℝ => realDot π s γ) := by
    unfold realDot realFill
    fun_prop
  exact hcont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hσ)

/-- The real fidelity is the squared target overlap divided by the fill mass, including the
zero-mass case. -/
theorem fidelity_eq_div (π σ : Fin m → ℝ) (γ : ℝ) :
    realFidelity π σ γ = realDot π σ γ ^ 2 / realMass π σ γ := by
  by_cases hm : realMass π σ γ = 0 <;> simp [realFidelity, hm]

/-- At a fixed source and level with nonzero limiting mass, coordinatewise target convergence
implies fidelity convergence. -/
theorem fidelity_parameter_tendsto (π σ : Fin m → ℝ) (σn : α → Fin m → ℝ)
    (hσ : ∀ i, Tendsto (fun n => σn n i) l (𝓝 (σ i))) (γ : ℝ)
    (hm : realMass π σ γ ≠ 0) :
    Tendsto (fun n => realFidelity π (σn n) γ) l (𝓝 (realFidelity π σ γ)) := by
  simp_rw [fidelity_eq_div]
  exact ((dot_parameter_tendsto π σ σn hσ γ).pow 2).div
    (mass_parameter_tendsto π σ σn hσ γ) hm

/-- For positive `lam`, the level `lam / δ` tends to positive infinity as `δ` tends to zero from
above. -/
theorem level_atTop (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun δ : ℝ => lam / δ) (𝓝[>] (0 : ℝ)) atTop := by
  simpa only [div_eq_mul_inv] using!
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hlam

/-- For positive `lam` and `s`, `(lam / δ) * (s + δ)` tends to positive infinity as `δ` tends to
zero from above. -/
theorem scaled_positive_atTop (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    Tendsto (fun δ : ℝ => (lam/δ)*(s+δ)) (𝓝[>] (0 : ℝ)) atTop := by
  have hd : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsd : Tendsto (fun δ : ℝ => s+δ) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
    simpa only [add_zero] using! tendsto_const_nhds.add hd
  exact (level_atTop lam hlam).atTop_mul_pos hs hsd

/-- For positive `lam` and `s`, the minimum of `a` and `(lam / δ) * (s + δ)` eventually equals
`a` as `δ` tends to zero from above. -/
theorem min_eventually_saturated (a lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), min a ((lam/δ)*(s+δ)) = a := by
  exact ((scaled_positive_atTop lam s hlam hs).eventually (eventually_ge_atTop a)).mono
    (fun _ h => min_eq_left h)

/-- Near zero from above, the minimum of `a` and `(lam / δ) * (0 + δ)` equals `min a lam`. -/
theorem min_zero_sigma (a lam : ℝ) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), min a ((lam/δ)*(0+δ)) = min a lam := by
  filter_upwards [show ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ from self_mem_nhdsWithin] with δ hδ
  congr 1
  simp [div_eq_mul_inv, hδ.ne']

/-- For a nonnegative target and positive `lam`, the regularized fill at level `lam / δ`
eventually saturates positive-target coordinates and equals `min (π i) lam` on zero-target
coordinates. -/
theorem boundary_fill {m : ℕ} (π σ : Fin m → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (lam : ℝ) (hlam : 0 < lam) (i : Fin m) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      realFill π (fun j => σ j+δ) (lam/δ) i = if 0 < σ i then π i else min (π i) lam := by
  by_cases hs : 0 < σ i
  · simpa only [realFill, if_pos hs] using! min_eventually_saturated (π i) lam (σ i) hlam hs
  · have hz : σ i = 0 := le_antisymm (not_lt.mp hs) (hσ i)
    simpa [realFill, hz] using! min_zero_sigma (π i) lam

end Qatlib.Concepts.Waterfill.LevelFidelity
