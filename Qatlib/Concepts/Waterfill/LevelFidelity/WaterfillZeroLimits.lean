/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelFidelity.RealTableWaterLevel
import Mathlib.Topology.Algebra.Order.Field
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.WaterLevel.WaterPrecision

set_option autoImplicit false
open Filter Set Qatlib.Concepts.WaterLevel.WaterPrecision
open scoped Topology BigOperators
namespace Qatlib.Concepts.Waterfill.LevelFidelity
variable {α : Type} {m : ℕ} {l : Filter α}

theorem fill_parameter_tendsto (π σ : Fin m → ℝ) (σn : α → Fin m → ℝ)
    (hσ : ∀ i, Tendsto (fun n => σn n i) l (𝓝 (σ i))) (γ : ℝ) (i : Fin m) :
    Tendsto (fun n => realFill π (σn n) γ i) l (𝓝 (realFill π σ γ i)) :=
  tendsto_const_nhds.min (tendsto_const_nhds.mul (hσ i))

theorem mass_parameter_tendsto (π σ : Fin m → ℝ) (σn : α → Fin m → ℝ)
    (hσ : ∀ i, Tendsto (fun n => σn n i) l (𝓝 (σ i))) (γ : ℝ) :
    Tendsto (fun n => realMass π (σn n) γ) l (𝓝 (realMass π σ γ)) := by
  have hcont : Continuous (fun s : Fin m → ℝ => realMass π s γ) := by
    unfold realMass realFill
    fun_prop
  exact hcont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hσ)

theorem dot_parameter_tendsto (π σ : Fin m → ℝ) (σn : α → Fin m → ℝ)
    (hσ : ∀ i, Tendsto (fun n => σn n i) l (𝓝 (σ i))) (γ : ℝ) :
    Tendsto (fun n => realDot π (σn n) γ) l (𝓝 (realDot π σ γ)) := by
  have hcont : Continuous (fun s : Fin m → ℝ => realDot π s γ) := by
    unfold realDot realFill
    fun_prop
  exact hcont.continuousAt.tendsto.comp (tendsto_pi_nhds.mpr hσ)

theorem fidelity_eq_div (π σ : Fin m → ℝ) (γ : ℝ) :
    realFidelity π σ γ = realDot π σ γ ^ 2 / realMass π σ γ := by
  by_cases hm : realMass π σ γ = 0 <;> simp [realFidelity, hm]

theorem fidelity_parameter_tendsto (π σ : Fin m → ℝ) (σn : α → Fin m → ℝ)
    (hσ : ∀ i, Tendsto (fun n => σn n i) l (𝓝 (σ i))) (γ : ℝ)
    (hm : realMass π σ γ ≠ 0) :
    Tendsto (fun n => realFidelity π (σn n) γ) l (𝓝 (realFidelity π σ γ)) := by
  simp_rw [fidelity_eq_div]
  exact ((dot_parameter_tendsto π σ σn hσ γ).pow 2).div
    (mass_parameter_tendsto π σ σn hσ γ) hm

theorem level_atTop (lam : ℝ) (hlam : 0 < lam) :
    Tendsto (fun δ : ℝ => lam / δ) (𝓝[>] (0 : ℝ)) atTop := by
  simpa only [div_eq_mul_inv] using!
    (tendsto_inv_nhdsGT_zero (𝕜 := ℝ)).const_mul_atTop hlam

theorem scaled_positive_atTop (lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    Tendsto (fun δ : ℝ => (lam/δ)*(s+δ)) (𝓝[>] (0 : ℝ)) atTop := by
  have hd : Tendsto (fun δ : ℝ => δ) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsd : Tendsto (fun δ : ℝ => s+δ) (𝓝[>] (0 : ℝ)) (𝓝 s) := by
    simpa only [add_zero] using! tendsto_const_nhds.add hd
  exact (level_atTop lam hlam).atTop_mul_pos hs hsd

theorem min_eventually_saturated (a lam s : ℝ) (hlam : 0 < lam) (hs : 0 < s) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), min a ((lam/δ)*(s+δ)) = a := by
  exact ((scaled_positive_atTop lam s hlam hs).eventually (eventually_ge_atTop a)).mono
    (fun _ h => min_eq_left h)

theorem min_zero_sigma (a lam : ℝ) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), min a ((lam/δ)*(0+δ)) = min a lam := by
  filter_upwards [show ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ), 0 < δ from self_mem_nhdsWithin] with δ hδ
  congr 1
  simp [div_eq_mul_inv, hδ.ne']

theorem boundary_fill {m : ℕ} (π σ : Fin m → ℝ) (hσ : ∀ i, 0 ≤ σ i)
    (lam : ℝ) (hlam : 0 < lam) (i : Fin m) :
    ∀ᶠ δ : ℝ in 𝓝[>] (0 : ℝ),
      realFill π (fun j => σ j+δ) (lam/δ) i = if 0 < σ i then π i else min (π i) lam := by
  by_cases hs : 0 < σ i
  · simpa only [realFill, if_pos hs] using! min_eventually_saturated (π i) lam (σ i) hlam hs
  · have hz : σ i = 0 := le_antisymm (not_lt.mp hs) (hσ i)
    simpa [realFill, hz] using! min_zero_sigma (π i) lam

end Qatlib.Concepts.Waterfill.LevelFidelity
