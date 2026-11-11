/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierSummability

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Regularity

Torus Fourier constructions for Effective Gauge.
Proves `smooth_pureWord_cube_bound`, `unitFourierCoefficient_radius_decay`, `unitFourierCoefficient_weighted_summable`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Pure derivatives of any fixed order have a compact-cube bound. This is
 qualitative and does not add a runtime query or a stored numerical modulus. -/
theorem smooth_pureWord_cube_bound (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f) (n : ℕ) :
    ∃ M : ℝ, 0≤M ∧ ∀ i x, InUnitCube x →
      ‖spatialWordPartial f (List.replicate n i) x‖ ≤ M := by
  let F : (Fin 3 → ℝ) → ℝ := fun x =>
    ∑ i : Fin 3, ‖spatialWordPartial f (List.replicate n i) (WithLp.toLp 2 x)‖
  have hF : Continuous F := by
    apply continuous_finsetSum
    intro i hi
    exact ((contDiff_spatialWordPartial f hf (List.replicate n i)).continuous.comp
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm.continuous).norm
  obtain ⟨M,hM⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : Fin 3 → ℝ) 1)).exists_bound_of_continuousOn
    hF.continuousOn
  refine ⟨max 0 M,le_max_left _ _,?_⟩
  intro i x hx
  have hbox : WithLp.ofLp x ∈ Set.Icc (0 : Fin 3 → ℝ) 1 :=
    ⟨fun j => (hx j).1,fun j => (hx j).2⟩
  calc
    _ ≤ F (WithLp.ofLp x) := by
      change ‖spatialWordPartial f (List.replicate n i) x‖ ≤
        ∑ j : Fin 3, ‖spatialWordPartial f (List.replicate n j) x‖
      exact Finset.single_le_sum
        (fun j _ => norm_nonneg (spatialWordPartial f (List.replicate n j) x)) (Finset.mem_univ i)
    _ ≤ ‖F (WithLp.ofLp x)‖ := le_abs_self _
    _ ≤ M := hM _ hbox
    _ ≤ max 0 M := le_max_right _ _

/-- Original `unitFourierCoefficient_radius_decay` guarantee for the `FourierRegularity` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_radius_decay (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (k : SpatialFrequency) (hk : k≠0) (n : ℕ) (M : ℝ)
    (hb : ∀ i x, InUnitCube x → ‖spatialWordPartial f (List.replicate n i) x‖ ≤ M) :
    ‖unitFourierCoefficient f hf.continuous hp k‖ ≤
      (M/physicalPeriod^n)*(frequencyRadius k : ℝ)^(-(n : ℝ)) := by
  obtain ⟨i,hiRadius⟩ := frequencyRadius_attained k
  have hi : k i≠0 := by
    intro h
    rw [h,Int.natAbs_zero] at hiRadius
    exact (frequencyRadius_pos k hk).ne' hiRadius.symm
  have habs : |(k i : ℝ)|=(frequencyRadius k : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using congrArg (fun n : ℕ => (n : ℝ)) hiRadius
  have hbound := unitFourierCoefficient_decay f hf hp k i hi n M (hb i)
  rw [habs] at hbound
  apply hbound.trans_eq
  rw [Real.rpow_neg (Nat.cast_nonneg _) (n : ℝ),Real.rpow_natCast]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Weighted coefficient summability uses the supplied derivative order,
 keeping the effective sixth-order consumer separate from smoothness. -/
theorem unitFourierCoefficient_weighted_summable (f : SpatialPoint → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : IsUnitPeriodicField f) (n t : ℕ) (ht : t+3<n)
    (M : ℝ) (hb : ∀ i x, InUnitCube x → ‖spatialWordPartial f (List.replicate n i) x‖ ≤ M) :
    Summable (fun k : SpatialFrequency =>
      (frequencyRadius k : ℝ)^t*‖unitFourierCoefficient f hf.continuous hp k‖) := by
  have hExp : (t : ℝ)-(n : ℝ)< -3 := by exact_mod_cast (show (t : ℤ)-(n : ℤ)< -3 by omega)
  have hs := (summable_frequencyRadius_rpow ((t : ℝ)-(n : ℝ)) hExp).mul_left (M/physicalPeriod^n)
  apply hs.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : SpatialFrequency)] with k hk
  rw [Real.norm_of_nonneg (by positivity)]
  calc
    _ ≤ (frequencyRadius k : ℝ)^t*((M/physicalPeriod^n)*
        (frequencyRadius k : ℝ)^(-(n : ℝ))) :=
      mul_le_mul_of_nonneg_left (unitFourierCoefficient_radius_decay f hf hp k hk n M hb)
        (by positivity)
    _ = (M/physicalPeriod^n)*(frequencyRadius k : ℝ)^((t : ℝ)-(n : ℝ)) := by
      rw [sub_eq_add_neg,Real.rpow_add (Nat.cast_pos.mpr (frequencyRadius_pos k hk)),
        Real.rpow_natCast]
      ring

end Qatlib.Concepts.EffectiveGauge.TorusFourier
