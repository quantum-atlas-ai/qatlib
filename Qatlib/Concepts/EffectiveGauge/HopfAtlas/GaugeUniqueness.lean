/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.EffectiveGauge.HopfAtlas.HarmonicConnection
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.LinearGaugeClassification
import Qatlib.Concepts.EffectiveGauge.HopfAtlas.IntegerGauge

set_option backward.isDefEq.respectTransparency false

/-!
# Gauge Uniqueness

Hopf Atlas constructions for Effective Gauge.
Proves `sameSource_solenoidal_classification`, `sameSource_solenoidal_eq_of_mean_cell_origin`, `selectedPoissonGauge_unique`.
-/


set_option autoImplicit false
noncomputable section
open scoped Quaternion ContDiff
namespace Qatlib.Concepts.EffectiveGauge.HopfAtlas
open Qatlib.Concepts.EffectiveGauge.RationalFlow Qatlib.Concepts.EffectiveGauge.TorusFourier

/-- Quaternion conjugation commutes with real scalar multiplication. -/
local instance : StarModule ℝ ℍ where
  star_smul r q := by ext <;> simp

/-- Full residual freedom for two actual smooth periodic solenoidal lifts:
an integer linear phase and the explicitly determined constant fibre ratio. -/
theorem sameSource_solenoidal_classification
    (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q r : QuaternionField) (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (huq : ∀ x, ‖q x‖=1) (hur : ∀ x, ‖r x‖=1)
    (hpq : IsPeriodicField q) (hpr : IsPeriodicField r)
    (hhq : ∀ x, hopf (q x)=spinOfVector (v x))
    (hhr : ∀ x, hopf (r x)=spinOfVector (v x))
    (hsq : IsSolenoidal q) (hsr : IsSolenoidal r) :
    ∃ n : SpatialFrequency,
      (∀ x j, connection r x j=connection q x j+(n j : ℝ)) ∧
      (∀ x, r x=phase (windingLinear n x)*(r 0*star (q 0))*q x) := by
  let z : QuaternionField := fun x => r x*star (q x)
  let b : Fin 3 → ℝ := fun j => connection r 0 j-connection q 0 j
  have hz : ContDiff ℝ ∞ z := hr.mul ((starL' ℝ : ℍ ≃L[ℝ] ℍ).contDiff.comp hq)
  have hzu : ∀ x, ‖z x‖=1 := fun x => sameHopf_ratio_norm _ _ (huq x) (hur x)
  have hzp : IsPeriodicField z := by
    intro x n
    dsimp only [z]
    rw [hpr x n,hpq x n]
  have hdiff (x : SpatialPoint) (j : Fin 3) : connection r x j-connection q x j=b j :=
    sameSource_solenoidal_connection_difference_constant v hv q r hq hr huq hur hpq hpr hhq hhr hsq hsr j x
  have hdz (x : SpatialPoint) (j : Fin 3) : spatialPartial z x j=b j • (iAxis*z x) := by
    have h := sameHopf_ratio_partial q r hq hr huq hur (fun y => (hhr y).trans (hhq y).symm) x j
    rw [hdiff] at h
    exact h
  obtain ⟨n,hn⟩ := periodic_constantFibreDerivative_integer z hz hzu hzp b hdz
  have hlin : realGaugeLinear b=windingLinear n := by
    have heq : b=fun j => (n j : ℝ) := funext hn
    rw [heq]
    rfl
  refine ⟨n,?_,?_⟩
  · intro x j
    have h := hdiff x j
    rw [hn j] at h
    linarith
  · intro x
    have h := constantFibreDerivative_classification z hz b hdz x
    rw [hlin] at h
    calc
      r x = z x*q x := (sameHopf_ratio_action (q x) (r x) (huq x)).symm
      _ = _ := by rw [h]

/-- The same open cell (width 3/4) and the same fixed origin value remove
all residual freedom, even for nonflat competing lifts. -/
theorem sameSource_solenoidal_eq_of_mean_cell_origin
    (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q r : QuaternionField) (hq : ContDiff ℝ ∞ q) (hr : ContDiff ℝ ∞ r)
    (huq : ∀ x, ‖q x‖=1) (hur : ∀ x, ‖r x‖=1)
    (hpq : IsPeriodicField q) (hpr : IsPeriodicField r)
    (hhq : ∀ x, hopf (q x)=spinOfVector (v x))
    (hhr : ∀ x, hopf (r x)=spinOfVector (v x))
    (hsq : IsSolenoidal q) (hsr : IsSolenoidal r) (shift : Fin 3 → ℝ)
    (hmq : ∀ j, shift j+1/8<physicalCubeMean (fun x => connection q x j) ∧
      physicalCubeMean (fun x => connection q x j)<shift j+7/8)
    (hmr : ∀ j, shift j+1/8<physicalCubeMean (fun x => connection r x j) ∧
      physicalCubeMean (fun x => connection r x j)<shift j+7/8)
    (h0 : r 0=q 0) : r=q := by
  obtain ⟨n,hconn,hfield⟩ := sameSource_solenoidal_classification v hv q r hq hr huq hur hpq hpr hhq hhr hsq hsr
  have hmean (j : Fin 3) : physicalCubeMean (fun x => connection r x j)=
      physicalCubeMean (fun x => connection q x j)+(n j : ℝ) := by
    have heq : (fun x => connection r x j)=(fun x => connection q x j+(n j : ℝ)) :=
      funext (fun x => hconn x j)
    rw [heq,physicalCubeMean_add _ _ (contDiff_connection q hq j).continuous continuous_const,
      physicalCubeMean_const]
  have hn (j : Fin 3) : n j=0 := by
    have hqM := hmq j
    have hrM := hmr j
    rw [hmean j] at hrM
    have hlo : (-1 : ℝ)<(n j : ℝ) := by linarith
    have hhi : (n j : ℝ)<(1 : ℝ) := by linarith
    have hloZ : (-1 : ℤ)<n j := by exact_mod_cast hlo
    have hhiZ : n j<(1 : ℤ) := by exact_mod_cast hhi
    omega
  have hn0 : n=0 := funext hn
  funext x
  have h := hfield x
  have hlin0 : windingLinear (0 : SpatialFrequency) x=0 := by simp [windingLinear_apply]
  rw [hn0,hlin0] at h
  simpa [phase,h0,unit_self_mul_star (q 0) (huq 0)] using h

/-- Original `selectedPoissonGauge_unique` guarantee for the `GaugeUniqueness` construction; the complete source hypotheses are retained. -/
theorem selectedPoissonGauge_unique (v : SpatialPoint → SpatialPoint) (hv : ContDiff ℝ ∞ v)
    (q : QuaternionField) (hq : ContDiff ℝ ∞ q) (hp : IsPeriodicField q) (hu : ∀ x, ‖q x‖=1)
    (hh : ∀ x, hopf (q x)=spinOfVector (v x)) (result : SourceMeanSectorResult)
    (hc : SourceMeanSectorCertificate (fun j => physicalCubeMean (fun x => connection q x j)) result)
    (r : QuaternionField) (hr : ContDiff ℝ ∞ r) (hur : ∀ x, ‖r x‖=1)
    (hhr : ∀ x, hopf (r x)=spinOfVector (v x)) (hpr : IsPeriodicField r) (hsr : IsSolenoidal r)
    (hr0 : r 0=q 0)
    (hmr : ∀ j, ((result.choices j).shift : ℝ)+1/8<physicalCubeMean (fun x => connection r x j) ∧
      physicalCubeMean (fun x => connection r x j)<((result.choices j).shift : ℝ)+7/8) :
    r=selectedPoissonGauge q hq hp result := by
  apply sameSource_solenoidal_eq_of_mean_cell_origin v hv
    (selectedPoissonGauge q hq hp result) r (selectedPoissonGauge_contDiff q hq hp result) hr
    (selectedPoissonGauge_norm q hq hp hu result) hur (selectedPoissonGauge_periodic q hq hp result) hpr
    (fun x => (selectedPoissonGauge_hopf q hq hp result x).trans (hh x)) hhr
    (selectedPoissonGauge_solenoidal q hq hp hu result) hsr (fun j => ((result.choices j).shift : ℝ))
    (selectedPoissonGauge_mean_cell q hq hp hu result hc) hmr
  exact hr0.trans (selectedPoissonGauge_origin q hq hp result).symm

end Qatlib.Concepts.EffectiveGauge.HopfAtlas
