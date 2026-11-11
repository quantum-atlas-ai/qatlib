/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierDecay
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FrequencyShell
import Mathlib.Analysis.PSeries

set_option backward.isDefEq.respectTransparency false

/-!
# Fourier Summability

Torus Fourier constructions for Effective Gauge.
Proves `summable_frequencyRadius_rpow`, `unitFourierCoefficient_summable`, `unitFourier_hasSum_of_summable`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Exact three-dimensional shells reduce lattice summability to the ordinary
p-series threshold r<-3. The zero frequency is included with its actual value. -/
theorem summable_frequencyRadius_rpow (r : ℝ) (hr : r < -3) :
    Summable (fun k : SpatialFrequency => (frequencyRadius k : ℝ)^r) := by
  rw [summable_partition (s := fun n : ℕ => ((Finset.box n : Finset SpatialFrequency) : Set SpatialFrequency))
    (fun k => Real.rpow_nonneg (Nat.cast_nonneg _) r) frequencyShell_partition]
  constructor
  · intro n
    exact (hasSum_fintype (β := (Finset.box n : Finset SpatialFrequency)) _).summable
  · have hterm (n : ℕ) : (∑' k : (Finset.box n : Finset SpatialFrequency), (frequencyRadius k.val : ℝ)^r)=
        (#(Finset.box n : Finset SpatialFrequency) : ℝ)*(n : ℝ)^r := by
      have heach (k : (Finset.box n : Finset SpatialFrequency)) : frequencyRadius k.val=n :=
        (frequency_mem_shell k.val n).mp k.prop
      simp only [heach,tsum_fintype,Finset.sum_const,Finset.card_univ,Fintype.card_coe,nsmul_eq_mul]
    suffices hsum : Summable (fun n : ℕ => (#(Finset.box n : Finset SpatialFrequency) : ℝ)*(n : ℝ)^r) from
      hsum.congr (fun n => (hterm n).symm)
    have hs := (Real.summable_nat_rpow.mpr (show 2+r < -1 by linarith)).mul_left (26 : ℝ)
    apply hs.of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
    rw [frequencyShell_card n hn,Real.norm_of_nonneg (by positivity)]
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      (((24*n^2+2 : ℕ) : ℝ))*(n : ℝ)^r ≤ 26*(n : ℝ)^2*(n : ℝ)^r := by
        push_cast
        gcongr
        nlinarith
      _ = 26*(n : ℝ)^(2+r) := by
        rw [Real.rpow_add (Nat.cast_pos.mpr hn),Real.rpow_two]
        ring

/-- Six true pure-derivative bounds imply absolute summability of the
actual Fourier coefficients; no coefficient or inverse bound is input. -/
theorem unitFourierCoefficient_summable (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (M : ℝ)
    (hb : ∀ i x, InUnitCube x → ‖spatialWordPartial f (List.replicate 6 i) x‖ ≤ M) :
    Summable (unitFourierCoefficient f hf.continuous hp) := by
  have hs := (summable_frequencyRadius_rpow (-6) (by norm_num)).mul_left (M/physicalPeriod^6)
  apply hs.of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : SpatialFrequency)] with k hk
  obtain ⟨i,hiRadius⟩ := frequencyRadius_attained k
  have hrad : frequencyRadius k≠0 := fun h => hk ((frequencyRadius_eq_zero_iff k).mp h)
  have hi : k i≠0 := by
    intro h
    rw [h,Int.natAbs_zero] at hiRadius
    exact hrad hiRadius.symm
  have habs : |(k i : ℝ)|=(frequencyRadius k : ℝ) := by
    simpa only [Nat.cast_natAbs,Int.cast_abs] using congrArg (fun n : ℕ => (n : ℝ)) hiRadius
  have hbound := unitFourierCoefficient_decay f hf hp k i hi 6 M (hb i)
  rw [habs] at hbound
  apply hbound.trans_eq
  change M/(physicalPeriod^(6 : ℕ)*(frequencyRadius k : ℝ)^(6 : ℕ))=
    (M/physicalPeriod^(6 : ℕ))*(frequencyRadius k : ℝ)^(-6 : ℝ)
  have hpower : (frequencyRadius k : ℝ)^(-6 : ℝ)=
      ((frequencyRadius k : ℝ)^(6 : ℕ))⁻¹ :=
    (Real.rpow_neg (Nat.cast_nonneg _) (6 : ℝ)).trans
      (congrArg (fun a : ℝ => a⁻¹) (Real.rpow_natCast (frequencyRadius k : ℝ) 6))
  rw [hpower]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

/-- Pinned torus Fourier inversion reconstructs the actual original
coordinate function, using the proved coefficient summability. -/
theorem unitFourier_hasSum_of_summable (f : SpatialPoint → ℂ) (hf : Continuous f)
    (hp : IsUnitPeriodicField f) (hs : Summable (unitFourierCoefficient f hf hp))
    (x : SpatialPoint) :
    HasSum (fun k : SpatialFrequency => unitFourierMode k x*unitFourierCoefficient f hf hp k) (f x) := by
  let F := unitTorusContinuousLift f hf hp
  have h := UnitAddTorus.hasSum_mFourier_series_apply_of_summable hs (unitTorusProjection x)
  have hterm (k : SpatialFrequency) : UnitAddTorus.mFourierCoeff F k •
      UnitAddTorus.mFourier k (unitTorusProjection x)=
      unitFourierMode k x*unitFourierCoefficient f hf hp k := by
    have heq : UnitAddTorus.mFourier k (unitTorusProjection x)=unitFourierMode k x :=
      (unitFourierMode_eq_mFourier k x).symm
    rw [heq]
    change unitFourierCoefficient f hf hp k*unitFourierMode k x=_
    exact mul_comm _ _
  have hvalue : F (unitTorusProjection x)=f x := unitTorusContinuousLift_apply f hf hp x
  rw [hvalue] at h
  exact h.congr_fun (fun k => (hterm k).symm)

/-- Six actual derivatives provide the summability premise of inversion. -/
theorem unitFourier_hasSum (f : SpatialPoint → ℂ) (hf : ContDiff ℝ ∞ f)
    (hp : IsUnitPeriodicField f) (M : ℝ)
    (hb : ∀ i x, InUnitCube x → ‖spatialWordPartial f (List.replicate 6 i) x‖ ≤ M)
    (x : SpatialPoint) :
    HasSum (fun k : SpatialFrequency => unitFourierMode k x*unitFourierCoefficient f hf.continuous hp k) (f x) :=
  unitFourier_hasSum_of_summable f hf.continuous hp
    (unitFourierCoefficient_summable f hf hp M hb) x

end Qatlib.Concepts.EffectiveGauge.TorusFourier
