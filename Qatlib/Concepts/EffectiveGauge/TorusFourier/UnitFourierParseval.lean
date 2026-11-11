/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.TorusFourier.FourierCoefficient

set_option backward.isDefEq.respectTransparency false

/-!
# Unit Fourier Parseval

Torus Fourier constructions for Effective Gauge.
Proves `unitFourierCoefficient_parseval`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
namespace Qatlib.Concepts.EffectiveGauge.TorusFourier
open Qatlib.Concepts.EffectiveGauge.HopfAtlas Qatlib.Concepts.EffectiveGauge.RationalFlow

/-- Normalized Haar measure on the unit additive circle. -/
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
/-- The unit-circle Haar measure has total mass one. -/
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Parseval for the actual Lebesgue unit box and the existing true
coefficient definition, including DC. -/
theorem unitFourierCoefficient_parseval (f : SpatialPoint → ℂ) (hf : Continuous f)
    (hp : IsUnitPeriodicField f) :
    HasSum (fun k : SpatialFrequency => ‖unitFourierCoefficient f hf hp k‖^2)
      (∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1),
        ‖f (WithLp.toLp 2 u)‖^2) := by
  let F := unitTorusContinuousLift f hf hp
  have hs := UnitAddTorus.hasSum_sq_mFourierCoeff (d := Fin 3) (F.toLp 2 volume ℂ)
  have hcoeff (k : SpatialFrequency) :
      UnitAddTorus.mFourierCoeff (F.toLp 2 volume ℂ) k=unitFourierCoefficient f hf hp k :=
    UnitAddTorus.mFourierCoeff_toLp F k
  have hs' : HasSum (fun k : SpatialFrequency => ‖unitFourierCoefficient f hf hp k‖^2)
      (∫ z : UnitAddTorus (Fin 3), ‖(F.toLp 2 volume ℂ) z‖^2) :=
    HasSum.congr_fun hs (fun k => by rw [hcoeff])
  have hint : (∫ z : UnitAddTorus (Fin 3), ‖(F.toLp 2 volume ℂ) z‖^2)=
      ∫ z : UnitAddTorus (Fin 3), ‖F z‖^2 := by
    apply integral_congr_ae
    filter_upwards [ContinuousMap.coeFn_toLp (𝕜 := ℂ) (p := 2) volume F] with z hz
    rw [hz]
  rw [hint,UnitAddTorus.integral_preimage (fun z => ‖F z‖^2) (fun _ => 0)] at hs'
  have hset : {u : Fin 3 → ℝ | ∀ i, u i∈Ioc (0 : ℝ) (0+1)}=
      Set.pi Set.univ (fun _ : Fin 3 => Ioc (0 : ℝ) 1) := by
    ext u
    simp only [zero_add,Set.mem_setOf_eq,Set.mem_pi,Set.mem_univ,true_implies]
  rw [hset] at hs'
  have hintBox : (∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1),
      ‖F (fun i => (u i : UnitAddCircle))‖^2)=
      ∫ u : Fin 3 → ℝ in Set.pi Set.univ (fun _ => Ioc (0 : ℝ) 1), ‖f (WithLp.toLp 2 u)‖^2 := by
    apply integral_congr_ae
    filter_upwards [] with u
    change ‖unitTorusContinuousLift f hf hp (unitTorusProjection (WithLp.toLp 2 u))‖^2=_
    rw [unitTorusContinuousLift_apply]
  rwa [hintBox] at hs'

end Qatlib.Concepts.EffectiveGauge.TorusFourier
