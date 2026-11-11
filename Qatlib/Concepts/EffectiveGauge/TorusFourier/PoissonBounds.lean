/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonEquation
import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonEffective
import Qatlib.Concepts.EffectiveGauge.TorusFourier.LatticeSumBound

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Bounds

Torus Fourier constructions for Effective Gauge.
Proves `unitPoisson_word_coefficient_bound`, `unitComplexPoisson_word_bound`, `unitRealPoisson_word_bound`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Original `unitPoisson_word_coefficient_bound` guarantee for the `PoissonBounds` construction; the complete source hypotheses are retained. -/
theorem unitPoisson_word_coefficient_bound (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x → ‖spatialWordPartial (f j) (List.replicate 6 i) x‖ ≤ M)
    (w : List (Fin 3)) (hw : w.length≤2) (k : SpatialFrequency) :
    ‖unitModeWordFactor k w*
      unitPoissonCoefficient (fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j)) k‖ ≤
      3*M*(frequencyRadius k : ℝ)^(-5 : ℝ) := by
  have hM : 0≤M := (norm_nonneg _).trans (hb 0 0 0 (by intro j; norm_num))
  by_cases hk : k=0
  · subst k
    simp only [unitPoissonCoefficient_zero,mul_zero,norm_zero,frequencyRadius,
      Pi.zero_apply,Int.natAbs_zero,max_self,Nat.cast_zero,
      Real.zero_rpow (by norm_num : (-5 : ℝ)≠0),mul_zero,le_refl]
  · have hL : 1≤physicalPeriod := by dsimp [physicalPeriod]; linarith [Real.pi_gt_three]
    have hr : (1 : ℝ)≤frequencyRadius k := by
      exact_mod_cast (show 1≤frequencyRadius k from frequencyRadius_pos k hk)
    have hrpos : (0 : ℝ)<frequencyRadius k := lt_of_lt_of_le zero_lt_one hr
    have hLp : 0<physicalPeriod := physicalPeriod_pos
    have hbase : 1≤physicalPeriod*(frequencyRadius k : ℝ) := by
      simpa using mul_le_mul hL hr zero_le_one (le_trans zero_le_one hL)
    have hfactor := (unitModeWordFactor_norm_le k w).trans (pow_le_pow_right₀ hbase hw)
    have hc := unitPoissonCoefficient_sixthOrder_decay f hf hp M hb k hk
    have hden : (frequencyRadius k : ℝ)^5 ≤ physicalPeriod^5*(frequencyRadius k : ℝ)^5 := by
      have h := mul_le_mul_of_nonneg_right (one_le_pow₀ hL : 1≤physicalPeriod^5)
        (show 0≤(frequencyRadius k : ℝ)^5 by positivity)
      simpa using h
    rw [norm_mul]
    calc
      _ ≤ (physicalPeriod*(frequencyRadius k : ℝ))^2*
          (3*M/(physicalPeriod^7*(frequencyRadius k : ℝ)^7)) :=
        mul_le_mul hfactor hc (norm_nonneg _) (by positivity)
      _ = 3*M/(physicalPeriod^5*(frequencyRadius k : ℝ)^5) := by
        field_simp [hLp.ne',hrpos.ne']
      _ ≤ 3*M/(frequencyRadius k : ℝ)^5 :=
        div_le_div₀ (by positivity) le_rfl (by positivity) hden
      _ = 3*M*(frequencyRadius k : ℝ)^(-5 : ℝ) := by
        have hpower : (frequencyRadius k : ℝ)^(-5 : ℝ)=
            ((frequencyRadius k : ℝ)^(5 : ℕ))⁻¹ :=
          (Real.rpow_neg (Nat.cast_nonneg _) (5 : ℝ)).trans
            (congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast (frequencyRadius k : ℝ) 5))
        rw [hpower,div_eq_mul_inv]

/-- The actual value and every first/second coordinate word obey the
 constant used by the numerical program. The dimension/shell factor is 156. -/
theorem unitComplexPoisson_word_bound (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x → ‖spatialWordPartial (f j) (List.replicate 6 i) x‖ ≤ M)
    (w : List (Fin 3)) (hw : w.length≤2) (x : SpatialPoint) :
    ‖spatialWordPartial (unitComplexPoisson f hf hp) w x‖ ≤ 156*M := by
  let a := unitPoissonCoefficient (fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j))
  have ha : FourierRapidlySummable a := unitPoissonCoefficient_rapidlySummable _
    (fun j => unitFourierCoefficient_rapidlySummable (f j) (hf j) (hp j))
  have hM : 0≤M := (norm_nonneg _).trans (hb 0 0 0 (by intro j; norm_num))
  have hsN : Summable (fun k : SpatialFrequency =>
      ‖(unitModeWordFactor k w*a k)*unitFourierMode k x‖) := by
    simpa only [norm_mul,unitFourierMode_norm,mul_one,pow_zero,one_mul] using ha.word w 0
  have hsB : Summable (fun k : SpatialFrequency => 3*M*(frequencyRadius k : ℝ)^(-5 : ℝ)) :=
    (summable_frequencyRadius_rpow (-5) (by norm_num)).mul_left (3*M)
  change ‖spatialWordPartial (unitFourierSeries a) w x‖ ≤ _
  rw [unitFourierSeries_word a ha w]
  calc
    _ ≤ ∑' k : SpatialFrequency, ‖(unitModeWordFactor k w*a k)*unitFourierMode k x‖ :=
      norm_tsum_le_tsum_norm hsN
    _ ≤ ∑' k : SpatialFrequency, 3*M*(frequencyRadius k : ℝ)^(-5 : ℝ) :=
      hsN.tsum_mono hsB (fun k => by
        change ‖(unitModeWordFactor k w*a k)*unitFourierMode k x‖ ≤ _
        rw [norm_mul,unitFourierMode_norm,mul_one]
        exact unitPoisson_word_coefficient_bound f hf hp M hb w hw k)
    _ = 3*M*(∑' k : SpatialFrequency, (frequencyRadius k : ℝ)^(-5 : ℝ)) := tsum_mul_left
    _ ≤ 3*M*52 := mul_le_mul_of_nonneg_left (tsum_frequencyRadius_rpow_le 5 (by norm_num)) (by positivity)
    _ = 156*M := by ring

/-- Original `unitRealPoisson_word_bound` guarantee for the `PoissonBounds` construction; the complete source hypotheses are retained. -/
theorem unitRealPoisson_word_bound (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x → ‖spatialWordPartial (f j) (List.replicate 6 i) x‖ ≤ M)
    (w : List (Fin 3)) (hw : w.length≤2) (x : SpatialPoint) :
    ‖spatialWordPartial (unitRealPoisson f hf hp) w x‖ ≤ 156*M := by
  change ‖spatialWordPartial (fun y => Complex.reCLM (unitComplexPoisson f hf hp y)) w x‖ ≤ _
  rw [spatialWordPartial_clm Complex.reCLM (unitComplexPoisson f hf hp)
    (unitComplexPoisson_contDiff f hf hp)]
  exact (Complex.abs_re_le_norm _).trans (unitComplexPoisson_word_bound f hf hp M hb w hw x)

end Qatlib.Concepts.EffectiveGauge.TorusFourier
