/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanJacobian
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPoyntingRays
public import Qatlib.Papers.KnotLight13.TorusFamily.NormalizedHelicity

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

/-!
# Physical energy transport in the Bateman power family

[Kedia2013TyingKnots], equation (6) and the conserved quantities on page 150404-3,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The exact field magnitude and the ray Jacobian give an energy-density
change of variables. This preserves the whole-space energy for every
power pair and allows an energy normalization on any time slice.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta)
open Filter MeasureTheory Set
open scoped BigOperators

local notation "EnergySpace" => ℝ × ℝ × ℝ

/-- The full physical energy in product Lebesgue coordinates. -/
noncomputable def batemanEnergy (p q : ℕ) (t : ℝ) : ℝ :=
  ∫ s : EnergySpace, batemanEnergyDensity p q t s

/-- The actual Bateman field is divided by the ray's complex multiplier
between the initial point and its image. -/
theorem rationalField_batemanRay (t : ℝ) (s : EnergySpace) (j : Fin 3) :
    let r := batemanRay t s
    rationalField r.1 r.2.1 r.2.2 t j =
      rationalField s.1 s.2.1 s.2.2 0 j / batemanRayMultiplier t s := by
  let r := batemanRay t s
  let m := batemanRayMultiplier t s
  let g := alphaCommonFactor s.2.2 0
  let h := betaReducedNumerator s.1 s.2.1
  let W := complexDenominator s.1 s.2.1 s.2.2 0
  have hm := batemanRayMultiplier_ne_zero t s
  have hW := complex_denominator_ne_zero s.1 s.2.1 s.2.2 0
  obtain ⟨hw, hg, hb⟩ := batemanRay_factors t s
  change complexDenominator r.1 r.2.1 r.2.2 t = W * m at hw
  change alphaCommonFactor r.2.2 t = g * m at hg
  change betaReducedNumerator r.1 r.2.1 = h * m at hb
  have hSpinor : spinorField (g * m) (h * m) j = m ^ 2 * spinorField g h j := by
    fin_cases j <;> simp [spinorField] <;> ring
  change rationalField r.1 r.2.1 r.2.2 t j = rationalField s.1 s.2.1 s.2.2 0 j / m
  simp only [rationalField_eq_spinorField]
  rw [hw, hg, hb, hSpinor]
  change (4 / (W * m) ^ 3) * (m ^ 2 * spinorField g h j) =
    (4 / W ^ 3 * spinorField g h j) / m
  field_simp [show W ≠ 0 from hW, show m ≠ 0 from hm]

/-- The power reparametrization factor depends only on the two scalar
labels and thus is constant along each ray. -/
private theorem rationalPowerFactor_batemanRay (p q : ℕ) (t : ℝ) (s : EnergySpace) :
    let r := batemanRay t s
    rationalPowerFactor p q r.1 r.2.1 r.2.2 t =
      rationalPowerFactor p q s.1 s.2.1 s.2.2 0 := by
  let r := batemanRay t s
  have hα := congrArg Prod.fst (batemanPairAt_batemanRay t s)
  have hβ := congrArg Prod.snd (batemanPairAt_batemanRay t s)
  change rationalAlpha r.1 r.2.1 r.2.2 t = rationalAlpha s.1 s.2.1 s.2.2 0 at hα
  change rationalBeta r.1 r.2.1 r.2.2 t = rationalBeta s.1 s.2.1 s.2.2 0 at hβ
  change rationalPowerFactor p q r.1 r.2.1 r.2.2 t =
    rationalPowerFactor p q s.1 s.2.1 s.2.2 0
  unfold rationalPowerFactor
  rw [hα, hβ]

/-- The powered field has the same complex transport factor because its
polynomial multiplier is constant along the ray. -/
theorem rationalPowerField_batemanRay (p q : ℕ) (t : ℝ) (s : EnergySpace) (j : Fin 3) :
    let r := batemanRay t s
    rationalPowerField p q r.1 r.2.1 r.2.2 t j =
      rationalPowerField p q s.1 s.2.1 s.2.2 0 j / batemanRayMultiplier t s := by
  simp only [rationalPowerField_eq, rationalPowerFactor_batemanRay, rationalField_batemanRay]
  ring

/-- The energy density of every powered field pulls back with the spatial
Jacobian to its initial value under the actual ray map. -/
theorem batemanEnergyDensity_jacobian (p q : ℕ) (t : ℝ) (s : EnergySpace) :
    LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap *
      batemanEnergyDensity p q t (batemanRay t s) = batemanEnergyDensity p q 0 s := by
  rw [det_batemanRay_eq_normSq_multiplier]
  simp only [batemanEnergyDensity, rationalPowerField_batemanRay, Complex.normSq_div, ← Finset.sum_div]
  field_simp [(Complex.normSq_pos.mpr (batemanRayMultiplier_ne_zero t s)).ne']

/-- The physical energy is absolutely integrable and equals its initial
whole-space value at each real time. -/
theorem integrable_and_conserved_batemanEnergy (p q : ℕ) (t : ℝ) :
    Integrable (batemanEnergyDensity p q t) ∧ batemanEnergy p q t = batemanInitialEnergy p q :=
  integrable_and_integral_of_batemanRay t _ _ (batemanEnergyDensity_jacobian p q t)
    (integrable_batemanInitialEnergyDensity p q)

/-- The full energy on each time slice is strictly positive for positive
power pairs. -/
theorem batemanEnergy_pos {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    0 < batemanEnergy p q t := by
  rw [(integrable_and_conserved_batemanEnergy p q t).2]
  exact batemanInitialEnergy_pos hp hq

/-- Normalizing each physical slice by its actual total energy gives
the value 1/(p+q) for both full-space helicities. -/
theorem bateman_helicities_div_energy {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    ((∫ s : EnergySpace, batemanElectricHelicityDensity p q t s) / batemanEnergy p q t =
        1 / ((p : ℝ) + (q : ℝ))) ∧
      ((∫ s : EnergySpace, batemanMagneticHelicityDensity p q t s) / batemanEnergy p q t =
        1 / ((p : ℝ) + (q : ℝ))) := by
  rw [(integrable_and_conserved_batemanEnergy p q t).2]
  exact bateman_normalized_helicities hp hq t

end Qatlib.Papers.KnotLight13.TorusFamily
