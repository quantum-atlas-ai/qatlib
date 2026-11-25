/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.BiotSavart

import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Absolute integrability of Biot–Savart helicity

The near-diagonal singularity is dominated by the locally integrable
inverse-square kernel in three dimensions. Translation in the product
measure then separates the near-diagonal bound into this scalar
kernel and the norm of one vorticity field. Away from the diagonal,
the product of the two field norms is an integrable majorant.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Filter Metric MeasureTheory Set
open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)
open Qatlib.Papers.SuperfluidHel18.VanishCharge
open scoped Real Topology

local notation "VorticitySpace" => Fin 3 → ℝ

/-- The pairing kernel is bounded by an inverse square of the Cartesian
distance, including its assigned zero value on the diagonal. -/
theorem abs_bsPairKernel_le_inv_sq (ω φ : VorticitySpace → VorticitySpace) (x y : VorticitySpace) :
    |bsPairKernel ω φ x y| ≤
      3 / (2 * π) * (‖x - y‖ ^ 2)⁻¹ * ‖ω x‖ * ‖φ y‖ := by
  by_cases h : x = y
  · subst y
    simp [bsPairKernel, euclideanLength]
  · have hd : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
    have hK := abs_bsPairKernel_le_of_dist_le (ω := ω) (φ := φ) hd (norm_le_euclideanLength _)
    calc
      _ ≤ 3 / (2 * π * ‖x - y‖ ^ 2) * (‖ω x‖ * ‖φ y‖) := hK
      _ = _ := by
        field_simp [Real.pi_ne_zero, hd.ne']

/-- The inverse-square function is integrable on a ball in the Cartesian
three-dimensional space, with respect to its volume measure. -/
theorem integrableOn_vorticity_inv_sq (r : ℝ) :
    IntegrableOn (fun x : VorticitySpace => (‖x‖ ^ 2)⁻¹) (ball 0 r) := by
  have hdim : Module.finrank ℝ VorticitySpace = 3 := by simp [Module.finrank_fintype_fun_eq_card]
  refine integrableOn_ball_of_norm_le_rpow (C := 1) (α := 2) (by rw [hdim]; norm_num)
    (by rw [hdim]; norm_num) ?_ ((measurable_norm.pow_const 2).inv.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun x => by
    rw [Real.norm_of_nonneg (inv_nonneg.mpr (sq_nonneg _)),
      Real.rpow_neg (norm_nonneg _), Real.rpow_two, one_mul]

/-- A bounded factor gives both an integrable kernel and a quantitative
bound on the full pairing, including its near-diagonal part. -/
private theorem integrable_and_abs_crossPairing_le_of_bounded {ω φ : VorticitySpace → VorticitySpace}
    (hmω : Measurable ω) (hmφ : Measurable φ) (hω : Integrable ω) (hφ : Integrable φ)
    {M : ℝ} (hbound : ∀ x, ‖ω x‖ ≤ M) :
    Integrable (fun p : VorticitySpace × VorticitySpace => bsPairKernel ω φ p.1 p.2)
      (volume.prod volume) ∧
    |crossPairing ω φ| ≤ 3 / (2 * π) *
      (M * (∫ z in ball (0 : VorticitySpace) 1, (‖z‖ ^ 2)⁻¹) + (∫ x, ‖ω x‖)) *
      ∫ y, ‖φ y‖ := by
  let k := (ball (0 : VorticitySpace) 1).indicator (fun x : VorticitySpace => (‖x‖ ^ 2)⁻¹)
  have hk : Integrable k :=
    (integrableOn_vorticity_inv_sq 1).integrable_indicator measurableSet_ball
  have hn : Integrable (fun p : VorticitySpace × VorticitySpace => k (p.1 - p.2) * ‖φ p.2‖)
      (volume.prod volume) := by
    have hp := (measurePreserving_sub_prod (volume : Measure VorticitySpace) volume)
    simpa only [Function.comp_def, smul_eq_mul] using
      hp.integrable_comp_of_integrable (hk.smul_prod hφ.norm)
  have hf : Integrable (fun p : VorticitySpace × VorticitySpace => ‖ω p.1‖ * ‖φ p.2‖)
      (volume.prod volume) := by
    simpa only [smul_eq_mul] using hω.norm.smul_prod hφ.norm
  have hmajor := ((hn.const_mul M).add hf).const_mul (3 / (2 * π))
  have hdom : ∀ᵐ p : VorticitySpace × VorticitySpace ∂(volume.prod volume),
      |bsPairKernel ω φ p.1 p.2| ≤
        3 / (2 * π) * (M * (k (p.1 - p.2) * ‖φ p.2‖) + ‖ω p.1‖ * ‖φ p.2‖) := by
    filter_upwards with p
    rcases p with ⟨x, y⟩
    change |bsPairKernel ω φ x y| ≤ 3 / (2 * π) *
      (M * (k (x - y) * ‖φ y‖) + ‖ω x‖ * ‖φ y‖)
    by_cases hnxy : x - y ∈ ball (0 : VorticitySpace) 1
    · rw [show k (x - y) = (‖x - y‖ ^ 2)⁻¹ from indicator_of_mem hnxy _]
      calc
        _ ≤ 3 / (2 * π) * (‖x - y‖ ^ 2)⁻¹ * ‖ω x‖ * ‖φ y‖ :=
          abs_bsPairKernel_le_inv_sq ω φ x y
        _ = 3 / (2 * π) * (‖ω x‖ * ((‖x - y‖ ^ 2)⁻¹ * ‖φ y‖)) := by ring
        _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact le_add_of_le_of_nonneg
            (mul_le_mul_of_nonneg_right (hbound x) (by positivity)) (by positivity)
    · have hd : 1 ≤ ‖x - y‖ := le_of_not_gt (fun h => hnxy (by simpa [mem_ball, dist_zero_right] using h))
      have hK := abs_bsPairKernel_le_of_dist_le (ω := ω) (φ := φ) (by norm_num : 0 < (1 : ℝ))
        (hd.trans (norm_le_euclideanLength _))
      rw [show k (x - y) = 0 from indicator_of_notMem hnxy _, zero_mul, mul_zero, zero_add]
      simpa only [one_pow, mul_one] using hK

  have hK := Integrable.mono' hmajor (measurable_bsPairKernel hmω hmφ).aestronglyMeasurable hdom
  refine ⟨hK, ?_⟩
  let shear : (VorticitySpace × VorticitySpace) ≃ᵐ (VorticitySpace × VorticitySpace) :=
    { toFun := fun p => (p.1 - p.2, p.2)
      invFun := fun p => (p.1 + p.2, p.2)
      left_inv := fun p => Prod.ext (sub_add_cancel _ _) rfl
      right_inv := fun p => Prod.ext (add_sub_cancel_right _ _) rfl
      measurable_toFun := (measurable_fst.sub measurable_snd).prodMk measurable_snd
      measurable_invFun := (measurable_fst.add measurable_snd).prodMk measurable_snd }
  have hshear : MeasurePreserving shear (volume.prod volume) (volume.prod volume) :=
    measurePreserving_sub_prod volume volume
  have hnearIntegral : (∫ p : VorticitySpace × VorticitySpace, k (p.1 - p.2) * ‖φ p.2‖
      ∂(volume.prod volume)) =
      (∫ z in ball (0 : VorticitySpace) 1, (‖z‖ ^ 2)⁻¹) * ∫ y, ‖φ y‖ := by
    calc
      _ = ∫ p : VorticitySpace × VorticitySpace, k p.1 * ‖φ p.2‖ ∂(volume.prod volume) :=
        hshear.integral_comp' _
      _ = (∫ z, k z) * ∫ y, ‖φ y‖ :=
        integral_prod_mul (μ := volume) (ν := volume) k (fun y => ‖φ y‖)
      _ = _ := by rw [show (∫ z, k z) = _ from integral_indicator measurableSet_ball]
  have hfarIntegral := integral_prod_mul (μ := volume) (ν := volume)
    (fun x : VorticitySpace => ‖ω x‖) (fun y : VorticitySpace => ‖φ y‖)
  rw [crossPairing]
  calc
    _ ≤ ∫ p : VorticitySpace × VorticitySpace, |bsPairKernel ω φ p.1 p.2| ∂(volume.prod volume) :=
      abs_integral_le_integral_abs
    _ ≤ ∫ p : VorticitySpace × VorticitySpace, 3 / (2 * π) *
        (M * (k (p.1 - p.2) * ‖φ p.2‖) + ‖ω p.1‖ * ‖φ p.2‖) ∂(volume.prod volume) :=
      integral_mono_ae hK.abs hmajor hdom
    _ = _ := by
      rw [integral_const_mul, integral_add (hn.const_mul M) hf,
        integral_const_mul, hnearIntegral, hfarIntegral]
      ring

/-- If both vorticity fields are integrable and the first is bounded,
their full Biot–Savart pairing kernel is absolutely integrable even
when their supports meet. -/
theorem integrable_bsPairKernel_of_bounded {ω φ : VorticitySpace → VorticitySpace}
    (hmω : Measurable ω) (hmφ : Measurable φ) (hω : Integrable ω) (hφ : Integrable φ)
    {M : ℝ} (hbound : ∀ x, ‖ω x‖ ≤ M) :
    Integrable (fun p : VorticitySpace × VorticitySpace => bsPairKernel ω φ p.1 p.2)
      (volume.prod volume) :=
  (integrable_and_abs_crossPairing_le_of_bounded hmω hmφ hω hφ hbound).1

/-- For a fixed bounded integrable first field, a change in the second
field changes the full pairing by at most a constant times its L¹ norm. -/
theorem abs_crossPairing_sub_right_le_of_bounded {ω φ ψ : VorticitySpace → VorticitySpace}
    (hmω : Measurable ω) (hmφ : Measurable φ) (hmψ : Measurable ψ)
    (hω : Integrable ω) (hφ : Integrable φ) (hψ : Integrable ψ)
    {M : ℝ} (hbound : ∀ x, ‖ω x‖ ≤ M) :
    |crossPairing ω φ - crossPairing ω ψ| ≤ 3 / (2 * π) *
      (M * (∫ z in ball (0 : VorticitySpace) 1, (‖z‖ ^ 2)⁻¹) + (∫ x, ‖ω x‖)) *
      ∫ y, ‖φ y - ψ y‖ := by
  have h₁ := integrable_bsPairKernel_of_bounded hmω hmφ hω hφ hbound
  have h₂ := integrable_bsPairKernel_of_bounded hmω hmψ hω hψ hbound
  have hsub : crossPairing ω φ - crossPairing ω ψ = crossPairing ω (φ - ψ) := by
    rw [crossPairing, crossPairing, crossPairing, ← integral_sub h₁ h₂]
    apply integral_congr_ae
    filter_upwards with p
    rw [bsPairKernel, bsPairKernel, bsPairKernel, ← sub_div]
    congr 1
    simp [dot3, cross3, Pi.sub_apply]
    ring
  rw [hsub]
  exact (integrable_and_abs_crossPairing_le_of_bounded hmω (hmφ.sub hmψ) hω
    (hφ.sub hψ) hbound).2

/-- Integrable fields converging in L¹ pair continuously against a fixed
bounded integrable field, with overlapping supports allowed. -/
theorem tendsto_crossPairing_right_of_bounded {ι : Type*} {l : Filter ι}
    {ω φ : VorticitySpace → VorticitySpace} (F : ι → VorticitySpace → VorticitySpace)
    (hmω : Measurable ω) (hmφ : Measurable φ) (hmF : ∀ i, Measurable (F i))
    (hω : Integrable ω) (hφ : Integrable φ) (hF : ∀ i, Integrable (F i))
    {M : ℝ} (hbound : ∀ x, ‖ω x‖ ≤ M)
    (hL1 : Tendsto (fun i => ∫ y, ‖F i y - φ y‖) l (𝓝 0)) :
    Tendsto (fun i => crossPairing ω (F i)) l (𝓝 (crossPairing ω φ)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simp only [Real.dist_eq]
  apply squeeze_zero' (Eventually.of_forall fun _ => abs_nonneg _)
    (Eventually.of_forall fun i =>
      abs_crossPairing_sub_right_le_of_bounded hmω (hmF i) hmφ hω (hF i) hφ hbound)
  simpa only [mul_zero] using tendsto_const_nhds.mul hL1

/-- The truncation converges for a continuous compactly supported vorticity
field, without a separate assumption on the singular pairing kernel. -/
theorem tendsto_bsHelicityTrunc_of_continuous_compactSupport
    {ω : VorticitySpace → VorticitySpace} (hc : Continuous ω) (hs : HasCompactSupport ω) :
    Filter.Tendsto (fun δ => bsHelicityTrunc ω δ) (nhdsWithin 0 (Ioi 0))
      (nhds (crossPairing ω ω)) := by
  have hL1 : Integrable ω volume := hc.integrable_of_hasCompactSupport hs
  obtain ⟨M, hM⟩ := hc.norm.bddAbove_range_of_hasCompactSupport hs.norm
  have hb (x : VorticitySpace) : ‖ω x‖ ≤ M := hM ⟨x, rfl⟩
  exact tendsto_bsHelicityTrunc hc.measurable hL1
    (integrable_bsPairKernel_of_bounded hc.measurable hc.measurable hL1 hL1 hb)

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
