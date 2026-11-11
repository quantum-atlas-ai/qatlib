/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.PoissonRegularity

set_option backward.isDefEq.respectTransparency false

/-!
# Poisson Effective

Torus Fourier constructions for Effective Gauge.
Proves `unitPoissonCoefficient_sixthOrder_decay`, `unitModeWordFactor_norm_le`.
-/


set_option autoImplicit false
noncomputable section
open Finset
open scoped ContDiff Topology
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Effective inverse-Laplacian decay uses the supplied actual sixth
 derivative bound, rather than the qualitative compactness bounds. -/
theorem unitPoissonCoefficient_sixthOrder_decay (f : Fin 3 → SpatialPoint → ℂ)
    (hf : ∀ j, ContDiff ℝ ∞ (f j)) (hp : ∀ j, IsUnitPeriodicField (f j)) (M : ℝ)
    (hb : ∀ j i x, InUnitCube x → ‖spatialWordPartial (f j) (List.replicate 6 i) x‖ ≤ M)
    (k : SpatialFrequency) (hk : k≠0) :
    ‖unitPoissonCoefficient (fun j => unitFourierCoefficient (f j) (hf j).continuous (hp j)) k‖ ≤
      3*M/(physicalPeriod^7*(frequencyRadius k : ℝ)^7) := by
  have hr : (frequencyRadius k : ℝ)≠0 :=
    (Nat.cast_pos.mpr (frequencyRadius_pos k hk)).ne'
  have hc (j : Fin 3) : ‖unitFourierCoefficient (f j) (hf j).continuous (hp j) k‖ ≤
      M/(physicalPeriod^6*(frequencyRadius k : ℝ)^6) := by
    have h := unitFourierCoefficient_radius_decay (f j) (hf j) (hp j) k hk 6 M (hb j)
    apply h.trans_eq
    change (M/physicalPeriod^(6 : ℕ))*(frequencyRadius k : ℝ)^(-(6 : ℝ))=
      M/(physicalPeriod^(6 : ℕ)*(frequencyRadius k : ℝ)^(6 : ℕ))
    have hpower : (frequencyRadius k : ℝ)^(-6 : ℝ)=
        ((frequencyRadius k : ℝ)^(6 : ℕ))⁻¹ :=
      (Real.rpow_neg (Nat.cast_nonneg _) (6 : ℝ)).trans
        (congrArg (fun z : ℝ => z⁻¹) (Real.rpow_natCast (frequencyRadius k : ℝ) 6))
    rw [hpower]
    simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  have h := unitPoissonCoefficient_norm_le _ k hk _ hc
  apply h.trans_eq
  field_simp [hr,physicalPeriod_pos.ne']

/-- Original `unitModeWordFactor_norm_le` guarantee for the `PoissonEffective` construction; the complete source hypotheses are retained. -/
theorem unitModeWordFactor_norm_le (k : SpatialFrequency) (w : List (Fin 3)) :
    ‖unitModeWordFactor k w‖ ≤ (physicalPeriod*(frequencyRadius k : ℝ))^w.length := by
  have hL : 0≤physicalPeriod := physicalPeriod_pos.le
  induction w with
  | nil => simp [unitModeWordFactor]
  | cons i w ih =>
    have hfactor : ‖(physicalPeriod : ℂ)*Complex.I*(k i : ℂ)‖ ≤
        physicalPeriod*(frequencyRadius k : ℝ) := by
      rw [norm_mul,norm_mul,Complex.norm_I,mul_one,Complex.norm_real,Real.norm_of_nonneg hL]
      apply mul_le_mul_of_nonneg_left _ hL
      simpa only [← Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs] using
        frequency_coordinate_abs_le_radius k i
    change ‖((physicalPeriod : ℂ)*Complex.I*(k i : ℂ))*unitModeWordFactor k w‖ ≤
      (physicalPeriod*(frequencyRadius k : ℝ))^(w.length+1)
    rw [norm_mul,pow_succ]
    exact (mul_le_mul hfactor ih (norm_nonneg _) (by positivity)).trans_eq (mul_comm _ _)

end Qatlib.Concepts.EffectiveGauge.TorusFourier
