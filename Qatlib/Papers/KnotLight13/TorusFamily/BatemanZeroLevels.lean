/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalTori

import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith

/-!
# The shared zero locus of the Bateman field-line labels

[Kedia2013TyingKnots], page 150404-2,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The zero electric and magnetic levels intersect along a circle and
the complete spatial axis, at every physical time. Each level is
closed and noncompact.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily (radialAux rationalAlpha rationalBeta)

/-- The first Bateman scalar vanishes precisely on the circle of
squared radius (1+t^2) in the equatorial plane. -/
theorem rationalAlpha_eq_zero_iff (x y z t : ℝ) :
    rationalAlpha x y z t = 0 ↔ z = 0 ∧ x ^ 2 + y ^ 2 = 1 + t ^ 2 := by
  change alphaNumerator x y z t / complexDenominator x y z t = 0 ↔ _
  rw [div_eq_zero_iff, or_iff_left (complex_denominator_ne_zero x y z t)]
  constructor
  · intro h
    have hz := congrArg Complex.im h
    have hr := congrArg Complex.re h
    simp [alphaNumerator, Complex.mul_im] at hz
    simp [alphaNumerator, Complex.mul_re] at hr
    refine ⟨hz, ?_⟩
    simp [radialAux, hz] at hr
    linarith
  · rintro ⟨rfl, h⟩
    have hA : radialAux x y 0 t - 2 = 0 := by
      unfold radialAux
      norm_num
      linarith
    simp [alphaNumerator, hA]

/-- The second Bateman scalar vanishes precisely on the entire axial line. -/
theorem rationalBeta_eq_zero_iff (x y z t : ℝ) :
    rationalBeta x y z t = 0 ↔ x = 0 ∧ y = 0 := by
  rw [rationalBeta_eq_reduced, div_eq_zero_iff, or_iff_left (complex_denominator_ne_zero x y z t),
    mul_eq_zero, or_iff_right (by norm_num : (2 : ℂ) ≠ 0)]
  constructor
  · intro h
    have hx := congrArg Complex.re h
    have hy := congrArg Complex.im h
    simpa [betaReducedNumerator, Complex.mul_re, Complex.mul_im] using And.intro hx hy
  · rintro ⟨rfl, rfl⟩
    simp [betaReducedNumerator]

/-- The real and imaginary label levels at zero meet exactly along
the equatorial circle and the axis. -/
theorem mem_poweredPhysicalZeroLevels_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (x y z t : ℝ) :
    (x, y, z) ∈ poweredPhysicalRealLevel p q t 0 ∩ poweredPhysicalImagLevel p q t 0 ↔
      (z = 0 ∧ x ^ 2 + y ^ 2 = 1 + t ^ 2) ∨ (x = 0 ∧ y = 0) := by
  have h : (batemanPoweredLabel p q t (x, y, z)).re = 0 ∧
      (batemanPoweredLabel p q t (x, y, z)).im = 0 ↔ batemanPoweredLabel p q t (x, y, z) = 0 := by
    constructor
    · rintro ⟨hr, hi⟩
      exact Complex.ext hr hi
    · rintro h
      simp [h]
  change ((batemanPoweredLabel p q t (x, y, z)).re = 0 ∧
    (batemanPoweredLabel p q t (x, y, z)).im = 0) ↔ _
  rw [h]
  change rationalAlpha x y z t ^ p * rationalBeta x y z t ^ q = 0 ↔ _
  rw [mul_eq_zero, pow_eq_zero_iff hp.ne', pow_eq_zero_iff hq.ne',
    rationalAlpha_eq_zero_iff, rationalBeta_eq_zero_iff]

/-- The first potential contributes a zero to the powered field only
when its exponent exceeds one, and likewise for the second potential. -/
theorem rationalPowerFactor_zero_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (x y z t : ℝ) :
    rationalPowerFactor p q x y z t = 0 ↔
      (1 < p ∧ z = 0 ∧ x ^ 2 + y ^ 2 = 1 + t ^ 2) ∨ (1 < q ∧ x = 0 ∧ y = 0) := by
  have hp₀ : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hq₀ : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hpow (r : ℕ) (u : ℂ) : u ^ (r - 1) = 0 ↔ 1 < r ∧ u = 0 := by
    by_cases h : 1 < r
    · simp [h, pow_eq_zero_iff (show r - 1 ≠ 0 by omega)]
    · simp [h, show r - 1 = 0 by omega]
  simp only [rationalPowerFactor, mul_eq_zero, hp₀, hq₀, false_or, hpow,
    rationalAlpha_eq_zero_iff, rationalBeta_eq_zero_iff]

/-- The actual electric and magnetic fields have the same zeros. For
positive powers these are the equatorial circle when `p > 1` and the
axial line when `q > 1`. -/
theorem poweredFields_zero_iff {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (x y z t : ℝ) :
    let N := (1 < p ∧ z = 0 ∧ x ^ 2 + y ^ 2 = 1 + t ^ 2) ∨ (1 < q ∧ x = 0 ∧ y = 0)
    ((fun j => (rationalPowerField p q x y z t j).re) = 0 ↔ N) ∧
      ((fun j => (rationalPowerField p q x y z t j).im) = 0 ↔ N) := by
  dsimp only
  rw [← rationalPowerFactor_zero_iff hp hq]
  by_cases h : rationalPowerFactor p q x y z t = 0
  · simp [rationalPowerField_eq, h, Pi.zero_def]
  · obtain ⟨he, hb⟩ := powered_fields_nonzero_of_factor_ne_zero p q x y z t h
    simp [he, hb, h]

/-- Both zero levels are unbounded, since they contain the complete axial line. -/
theorem poweredPhysicalZeroLevels_unbounded {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    ¬ Bornology.IsBounded (poweredPhysicalRealLevel p q t 0) ∧
      ¬ Bornology.IsBounded (poweredPhysicalImagLevel p q t 0) := by
  let axis : Set (ℝ × ℝ × ℝ) := Set.range (fun z => (0, 0, z))
  have ha : axis ⊆ poweredPhysicalRealLevel p q t 0 ∩ poweredPhysicalImagLevel p q t 0 := by
    rintro _ ⟨z, rfl⟩
    exact (mem_poweredPhysicalZeroLevels_iff hp hq 0 0 z t).2 (Or.inr ⟨rfl, rfl⟩)
  have h : ¬ Bornology.IsBounded axis := by
    intro hb
    obtain ⟨R, hR⟩ := isBounded_iff_forall_norm_le.mp hb
    have hle := hR (0, 0, |R| + 1) ⟨|R| + 1, rfl⟩
    have hn : 0 ≤ |R| + 1 := by positivity
    simp [Prod.norm_def, Real.norm_eq_abs, abs_of_nonneg hn, max_eq_right hn] at hle
    linarith [le_abs_self R]
  exact ⟨fun hb => h (hb.subset (ha.trans Set.inter_subset_left)),
    fun hb => h (hb.subset (ha.trans Set.inter_subset_right))⟩

/-- The closed zero levels are noncompact at every physical time. -/
theorem poweredPhysicalZeroLevels_closed_noncompact {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (t : ℝ) :
    (IsClosed (poweredPhysicalRealLevel p q t 0) ∧ ¬ IsCompact (poweredPhysicalRealLevel p q t 0)) ∧
    (IsClosed (poweredPhysicalImagLevel p q t 0) ∧ ¬ IsCompact (poweredPhysicalImagLevel p q t 0)) := by
  have h := (contDiff_batemanPoweredLabel p q t).continuous
  obtain ⟨hR, hI⟩ := poweredPhysicalZeroLevels_unbounded hp hq t
  exact ⟨⟨isClosed_eq (Complex.continuous_re.comp h) continuous_const, fun hK => hR hK.isBounded⟩,
    ⟨isClosed_eq (Complex.continuous_im.comp h) continuous_const, fun hK => hI hK.isBounded⟩⟩

end Qatlib.Papers.KnotLight13.TorusFamily
