/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.Waterfill.LevelSearch.WaterFillingOptimization

/-!
# Error bounds for computed water-fill preparations

This module transfers rational bisection estimates to mass error and to the event probability of
numeric water-fill state preparation. The latter combines the level-search error with a
precision contribution of `64 / 2 ^ b` for the rejection-sampling construction associated with
[OzolsRoettelerRoland2013].

## Main statements

* `computedWaterLevel_mass_error`: Bound mass error after a fixed number of bisections.
* `computed_waterlevel_same_unknown_state_numeric_mass`: Bound the event-probability error of
  numeric preparation.

## References

* [Ozols et al., 2013][OzolsRoettelerRoland2013]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.NativeNumerics.WaterFilling

namespace Qatlib.Concepts.Waterfill.LevelSearch
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The mass error at the computed upper bisection endpoint is at most twice the source-target
overlap times the initial upper level divided by `2 ^ k`. -/
theorem computedWaterLevel_mass_error (m k : ℕ) (π σ : Fin m → ℚ) (q : ℚ)
    (h : ∀ j, 0 ≤ π j ∧ 0 < σ j) (hq : 0 ≤ q) (hqmax : q ≤ ∑ j, (π j)^2) :
    |waterMass π σ (computedWaterLevel π σ q k)-(q : ℝ)| ≤
      2*(∑ j, (π j : ℝ)*(σ j : ℝ))*(computedWaterHigh π σ : ℝ)/(2:ℝ)^k := by
  let a := (computedWaterBracket π σ q k).1
  let γ := computedWaterLevel π σ q k
  have hb := computed_waterlevel_actual_bracket_and_work m k π σ q h hq hqmax
  (try dsimp only at hb)
  have ha : 0 ≤ a := hb.1
  have hag : a ≤ γ := hb.2.1
  have hlow : waterMass π σ a ≤ (q : ℝ) := by
    rw [← computedWaterEnergy_cast]; exact_mod_cast hb.2.2.1
  have hhigh : (q : ℝ) ≤ waterMass π σ γ := by
    rw [← computedWaterEnergy_cast]; exact_mod_cast hb.2.2.2.1
  have he := computedWaterEnergy_increment π σ (fun j => ⟨(h j).1, (h j).2.le⟩) ha hag
  have her : waterMass π σ γ-waterMass π σ a ≤
      2*(∑ j, (π j : ℝ)*(σ j : ℝ))*((γ-a : ℚ) : ℝ) := by
    rw [← computedWaterEnergy_cast, ← computedWaterEnergy_cast]
    exact_mod_cast he
  have hw : ((γ-a : ℚ) : ℝ) = (computedWaterHigh π σ : ℝ)/(2:ℝ)^k := by
    exact_mod_cast hb.2.2.2.2
  change |waterMass π σ γ-(q : ℝ)| ≤ _
  rw [abs_of_nonneg (sub_nonneg.mpr hhigh)]
  calc
    _ ≤ waterMass π σ γ-waterMass π σ a := sub_le_sub_left hlow _
    _ ≤ 2*(∑ j, (π j : ℝ)*(σ j : ℝ))*((γ-a : ℚ) : ℝ) := her
    _ = _ := by rw [hw]; ring

/-- For normalized component states and a unitary source preparation, the event probability of
the numeric water-fill preparation differs from `q` by at most the bisection mass bound plus
`64 / 2 ^ b`; see [OzolsRoettelerRoland2013]. -/
theorem computed_waterlevel_same_unknown_state_numeric_mass
    (m D k b : ℕ) (π σ : Fin m → ℚ) (q : ℚ)
    (ξ : Fin m → QState (Fin D)) (A : Matrix (Fin m×Fin D) (Fin m×Fin D) ℂ)
    (j : Fin m×Fin D) (h : ∀ i, 0 ≤ π i ∧ 0 < σ i) (hq : 0 < q)
    (hqmax : q ≤ ∑ i, (π i)^2) (hξ : ∀ i, Normalized (ξ i))
    (hA : A ∈ Matrix.unitaryGroup _ ℂ) (hsource : A.mulVec (Ket j) = waterSource π ξ) :
    let γ := computedWaterLevel π σ q k
    |MeasureProb ((waterNumericPrepare π σ γ b A).mulVec (Ket (j,false)))
      (waterEvent m D)-(q : ℝ)| ≤
      2*(∑ i, (π i : ℝ)*(σ i : ℝ))*(computedWaterHigh π σ : ℝ)/(2:ℝ)^k+64/(2:ℝ)^b := by
  (try dsimp only)
  let γ := computedWaterLevel π σ q k
  have hb := computed_waterlevel_actual_bracket_and_work m k π σ q h hq.le hqmax
  have hg : 0 ≤ γ := hb.1.trans hb.2.1
  have hn := (coherent_waterfill_same_unknown_state_flag_mass m D b π σ γ ξ A j
    (fun i => ⟨(h i).1, (h i).2.le⟩) hg hξ hA hsource).2
  have he := computedWaterLevel_mass_error m k π σ q h hq.le hqmax
  have ht := abs_sub_le
    (MeasureProb ((waterNumericPrepare π σ γ b A).mulVec (Ket (j,false))) (waterEvent m D))
    (waterMass π σ γ) (q : ℝ)
  linarith

end Qatlib.Concepts.Waterfill.LevelSearch
