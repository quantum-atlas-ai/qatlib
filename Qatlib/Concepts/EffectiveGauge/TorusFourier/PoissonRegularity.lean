/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierRegularity
import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierSeries
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonCoefficient

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Regularity

Torus Fourier constructions for Effective Gauge.
Defines `unitComplexPoisson`, `unitRealPoisson`.
Proves `unitFourierCoefficient_rapidlySummable`, `unitPoissonCoefficient_rapidlySummable`, `unitComplexPoisson_contDiff`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `unitFourierCoefficient_rapidlySummable` guarantee for the `PoissonRegularity` construction; the complete source hypotheses are retained. -/
theorem unitFourierCoefficient_rapidlySummable (f : SpatialPoint → ℂ)
    (hf : ContDiff ℝ ∞ f) (hp : IsUnitPeriodicField f) :
    FourierRapidlySummable (unitFourierCoefficient f hf.continuous hp) := by
  intro n
  obtain ⟨M,_,hb⟩ := smooth_pureWord_cube_bound f hf (n+4)
  exact unitFourierCoefficient_weighted_summable f hf hp (n+4) n (by omega) M hb

/-- Inverting the nonzero lattice eigenvalue preserves rapid absolute
 convergence. The zero coefficient is separately exactly zero. -/
theorem unitPoissonCoefficient_rapidlySummable (a : Fin 3 → SpatialFrequency → ℂ)
    (ha : ∀ j, FourierRapidlySummable (a j)) :
    FourierRapidlySummable (unitPoissonCoefficient a) := by
  intro n
  have hs : Summable (fun k : SpatialFrequency =>
      ∑ j : Fin 3, (frequencyRadius k : ℝ)^n*‖a j k‖) := by
    simpa only [Fin.sum_univ_three] using ((ha 0 n).add (ha 1 n)).add (ha 2 n)
  apply (hs.mul_left (3/physicalPeriod)).of_norm_bounded_eventually
  filter_upwards [Filter.eventually_cofinite_ne (0 : SpatialFrequency)] with k hk
  rw [Real.norm_of_nonneg (by positivity)]
  let B : ℝ := ∑ j : Fin 3, ‖a j k‖
  have hB : 0≤B := Finset.sum_nonneg (fun j _ => norm_nonneg _)
  have hb (j : Fin 3) : ‖a j k‖ ≤ B :=
    Finset.single_le_sum (fun j _ => norm_nonneg (a j k)) (Finset.mem_univ j)
  have hr : (1 : ℝ) ≤ (frequencyRadius k : ℝ) := by
    have hrN : 1≤frequencyRadius k := frequencyRadius_pos k hk
    exact_mod_cast hrN
  have hc : ‖unitPoissonCoefficient a k‖ ≤ (3/physicalPeriod)*B := by
    calc
      _ ≤ 3*B/(physicalPeriod*(frequencyRadius k : ℝ)) := unitPoissonCoefficient_norm_le a k hk B hb
      _ ≤ 3*B/physicalPeriod :=
        div_le_div₀ (by positivity) le_rfl physicalPeriod_pos
          (by simpa using mul_le_mul_of_nonneg_left hr physicalPeriod_pos.le)
      _ = _ := by ring
  calc
    _ ≤ (frequencyRadius k : ℝ)^n*((3/physicalPeriod)*B) :=
      mul_le_mul_of_nonneg_left hc (by positivity)
    _ = (3/physicalPeriod)*(∑ j : Fin 3, (frequencyRadius k : ℝ)^n*‖a j k‖) := by
      rw [← Finset.mul_sum]
      dsimp only [B]
      ring

/-- Definition of unit Complex Poisson in the Torus Fourier construction. -/
def unitComplexPoisson (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) : SpatialPoint → ℂ :=
  unitFourierSeries (unitPoissonCoefficient (fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j)))

/-- Definition of unit Real Poisson in the Torus Fourier construction. -/
def unitRealPoisson (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) : SpatialPoint → ℝ :=
  fun x => Complex.reCLM (unitComplexPoisson f hf hp x)

/-- Original `unitComplexPoisson_contDiff` guarantee for the `PoissonRegularity` construction; the complete source hypotheses are retained. -/
theorem unitComplexPoisson_contDiff (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) :
    ContDiff ℝ ∞ (unitComplexPoisson f hf hp) :=
  unitFourierSeries_contDiff _ (unitPoissonCoefficient_rapidlySummable _
    (fun j => unitFourierCoefficient_rapidlySummable (f j) (hf j) (hp j)))

/-- Original `unitRealPoisson_contDiff` guarantee for the `PoissonRegularity` construction; the complete source hypotheses are retained. -/
theorem unitRealPoisson_contDiff (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) :
    ContDiff ℝ ∞ (unitRealPoisson f hf hp) :=
  Complex.reCLM.contDiff.comp (unitComplexPoisson_contDiff f hf hp)

/-- Original `unitRealPoisson_periodic` guarantee for the `PoissonRegularity` construction; the complete source hypotheses are retained. -/
theorem unitRealPoisson_periodic (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) :
    IsUnitPeriodicField (unitRealPoisson f hf hp) := by
  intro x n
  apply congrArg Complex.reCLM
  exact unitFourierSeries_periodic _ x n

end Qatlib.Concepts.EffectiveGauge.TorusFourier
