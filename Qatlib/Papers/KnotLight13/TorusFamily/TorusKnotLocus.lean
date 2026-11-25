/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PolynomialFamily
public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Topology.Homeomorph.Lemmas

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Int.GCD
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

/-!
# The standard torus-knot locus of the Bateman polynomial

[Kedia2013TyingKnots], Eq. (6) and Fig. 2,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
For positive coprime exponents, the polynomial zero set on the unit
three-sphere is the image of the embedded unit circle that winds
around the two factors of a product torus. The radii are uniquely fixed
by the sphere equation and the power equation. Bézout's identity
recovers the single phase from the two coordinate phases.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Qatlib.Papers.KnotLight13.TorusFamily
  (torusPolynomial rationalAlpha rationalBeta complex_rational_pair_unit)

/-- The polynomial zero set on the unit three-sphere in complex coordinates. -/
def unitTorusKnotLocus (p q : ℕ) : Set (ℂ × ℂ) :=
  {z | ‖z.1‖ ^ 2 + ‖z.2‖ ^ 2 = 1 ∧ torusPolynomial p q z.1 z.2 = 0}

/-- The standard parameter circle on the product torus with radii `a,b`.
The winding of the first coordinate is `q` and that of the second is `p`. -/
noncomputable def torusKnotParam (p q : ℕ) (a b : ℝ) (w : Circle) : ℂ × ℂ :=
  ((a : ℂ) * (w : ℂ) ^ q, (b : ℂ) * (w : ℂ) ^ p)

/-- The two-coordinate torus parametrization is continuous. -/
theorem continuous_torusKnotParam (p q : ℕ) (a b : ℝ) :
    Continuous (torusKnotParam p q a b) := by
  have hco : Continuous (fun w : Circle => (w : ℂ)) := continuous_subtype_val
  exact (continuous_const.mul (hco.pow q)).prodMk (continuous_const.mul (hco.pow p))

/-- Bézout recovers the phase of a common power pair, including uniqueness.
The multiplicative statement applies in particular to the complex unit circle. -/
theorem exists_unique_common_phase {G : Type*} [CommGroup G] {p q : ℕ}
    (hpq : Nat.Coprime p q) (u v : G) (h : u ^ p = v ^ q) :
    ∃! w : G, w ^ q = u ∧ w ^ p = v := by
  let m := Nat.gcdA q p
  let n := Nat.gcdB q p
  have hbez : (q : ℤ) * m + (p : ℤ) * n = 1 := by
    simpa only [hpq.symm.gcd_eq_one, Nat.cast_one, m, n] using (Nat.gcd_eq_gcd_ab q p).symm
  have hpow : u ^ (p : ℤ) = v ^ (q : ℤ) := by simpa only [zpow_natCast] using h
  let w := u ^ m * v ^ n
  refine ⟨w, ⟨?_, ?_⟩, ?_⟩
  · calc
      w ^ q = (u ^ m * v ^ n) ^ (q : ℤ) := by rw [zpow_natCast]
      _ = u ^ ((q : ℤ) * m) * v ^ ((q : ℤ) * n) := by
        rw [mul_zpow, zpow_mul', zpow_mul']
      _ = u ^ ((q : ℤ) * m) * u ^ ((p : ℤ) * n) := by
        rw [zpow_mul v, ← hpow, ← zpow_mul]
      _ = u := by rw [← zpow_add, hbez, zpow_one]
  · calc
      w ^ p = (u ^ m * v ^ n) ^ (p : ℤ) := by rw [zpow_natCast]
      _ = u ^ ((p : ℤ) * m) * v ^ ((p : ℤ) * n) := by
        rw [mul_zpow, zpow_mul', zpow_mul']
      _ = v ^ ((q : ℤ) * m) * v ^ ((p : ℤ) * n) := by
        rw [zpow_mul u, hpow, ← zpow_mul]
      _ = v := by rw [← zpow_add, hbez, zpow_one]
  · intro z hz
    have hzq : z ^ (q : ℤ) = u := by simpa only [zpow_natCast] using hz.1
    have hzp : z ^ (p : ℤ) = v := by simpa only [zpow_natCast] using hz.2
    change z = u ^ m * v ^ n
    rw [← hzq, ← hzp, ← zpow_mul, ← zpow_mul, ← zpow_add, hbez, zpow_one]

/-- Positive torus radii satisfying the sphere equation and the balanced
power equation exist for every positive pair of exponents. -/
theorem exists_balanced_torus_radii {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = 1 ∧ a ^ p = b ^ q := by
  let f := fun a : ℝ => a ^ p - (Real.sqrt (1 - a ^ 2)) ^ q
  have hf : Continuous f :=
    (continuous_id.pow p).sub ((Real.continuous_sqrt.comp
      (continuous_const.sub (continuous_id.pow 2))).pow q)
  have h0 : f 0 = -1 := by simp [f, zero_pow hp.ne']
  have h1 : f 1 = 1 := by simp [f, zero_pow hq.ne']
  obtain ⟨a, ha, ha0⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1) hf.continuousOn
    (show (0 : ℝ) ∈ Set.Icc (f 0) (f 1) by rw [h0, h1]; norm_num)
  have hapos : 0 < a := ha.1.lt_of_ne fun h => by rw [← h, h0] at ha0; norm_num at ha0
  have haalt : a < 1 := ha.2.lt_of_ne fun h => by rw [h, h1] at ha0; norm_num at ha0
  have hb : 0 < 1 - a ^ 2 := sub_pos.mpr (by
    simpa using pow_lt_pow_left₀ haalt hapos.le (by norm_num : (2 : ℕ) ≠ 0))
  refine ⟨a, Real.sqrt (1 - a ^ 2), hapos, Real.sqrt_pos.2 hb, ?_, sub_eq_zero.mp ha0⟩
  rw [Real.sq_sqrt hb.le]
  linarith

/-- The first radius is ordered uniquely by the sphere and power equations. -/
private theorem balanced_left_radius_le {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {a b a' b' : ℝ} (ha' : 0 ≤ a') (hb : 0 ≤ b) (hb' : 0 ≤ b')
    (hs : a ^ 2 + b ^ 2 = 1) (hs' : a' ^ 2 + b' ^ 2 = 1)
    (he : a ^ p = b ^ q) (he' : a' ^ p = b' ^ q) : a ≤ a' := by
  by_contra! h
  have ha2 := pow_lt_pow_left₀ h ha' (by norm_num : (2 : ℕ) ≠ 0)
  have hbr : b < b' := by
    by_contra! hbr
    have hb2 := pow_le_pow_left₀ hb' hbr 2
    linarith
  have hap := pow_lt_pow_left₀ h ha' hp.ne'
  have hbq := pow_lt_pow_left₀ hbr hb hq.ne'
  rw [he, he'] at hap
  exact (lt_asymm hap) hbq

/-- The sphere and balanced power equations select a single pair of
nonnegative radii for positive exponents. -/
theorem balanced_torus_radii_unique {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a') (hb' : 0 ≤ b')
    (hs : a ^ 2 + b ^ 2 = 1) (hs' : a' ^ 2 + b' ^ 2 = 1)
    (he : a ^ p = b ^ q) (he' : a' ^ p = b' ^ q) : a = a' ∧ b = b' := by
  have h := le_antisymm (balanced_left_radius_le hp hq ha' hb hb' hs hs' he he')
    (balanced_left_radius_le hp hq ha hb' hb hs' hs he' he)
  exact ⟨h, (pow_left_inj₀ hb hb' (by norm_num : (2 : ℕ) ≠ 0)).1 (by rw [h] at hs; linarith)⟩

/-- Every point of the standard parameter circle lies in the polynomial
zero set when the radii obey the two defining equations. -/
theorem torusKnotParam_mem_unitTorusKnotLocus (p q : ℕ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs : a ^ 2 + b ^ 2 = 1) (he : a ^ p = b ^ q)
    (w : Circle) : torusKnotParam p q a b w ∈ unitTorusKnotLocus p q := by
  have hec : (a : ℂ) ^ p = (b : ℂ) ^ q := by exact_mod_cast he
  refine ⟨?_, sub_eq_zero.mpr ?_⟩
  · simpa [torusKnotParam, norm_mul, norm_pow, Complex.norm_real, abs_of_nonneg ha,
      abs_of_nonneg hb] using hs
  · change ((a : ℂ) * (w : ℂ) ^ q) ^ p = ((b : ℂ) * (w : ℂ) ^ p) ^ q
    rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, hec, mul_comm q p]

/-- The parameter circle is injective for positive radii and coprime
windings. -/
theorem torusKnotParam_injective {p q : ℕ} (hpq : Nat.Coprime p q) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) : Function.Injective (torusKnotParam p q a b) := by
  intro x y h
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hq : x ^ q = y ^ q := Circle.ext (mul_left_cancel₀ hac (congrArg Prod.fst h))
  have hp : x ^ p = y ^ p := Circle.ext (mul_left_cancel₀ hbc (congrArg Prod.snd h))
  have hz : (x ^ q) ^ p = (x ^ p) ^ q := by rw [← pow_mul, ← pow_mul, mul_comm q p]
  obtain ⟨z, _, hzuniq⟩ := exists_unique_common_phase hpq (x ^ q) (x ^ p) hz
  exact (hzuniq x ⟨rfl, rfl⟩).trans (hzuniq y ⟨hq.symm, hp.symm⟩).symm

/-- Every polynomial zero on the unit sphere lies on the standard
parameter circle with the balanced positive radii. -/
theorem exists_torusKnotParam_eq {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : a ^ 2 + b ^ 2 = 1) (he : a ^ p = b ^ q)
    {z : ℂ × ℂ} (hz : z ∈ unitTorusKnotLocus p q) :
    ∃ w : Circle, torusKnotParam p q a b w = z := by
  rcases hz with ⟨hzs, hpoly⟩
  have hzpow : z.1 ^ p = z.2 ^ q := sub_eq_zero.mp hpoly
  have hzabs : ‖z.1‖ ^ p = ‖z.2‖ ^ q := by simpa only [norm_pow] using congrArg norm hzpow
  obtain ⟨hza, hzb⟩ := balanced_torus_radii_unique hp hq
    (norm_nonneg z.1) (norm_nonneg z.2) ha.le hb.le hzs hs hzabs he
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbc : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  let u : Circle := ⟨z.1 / (a : ℂ), by
    change z.1 / (a : ℂ) ∈ Metric.sphere 0 1
    simp [Complex.norm_real, abs_of_pos ha, hza, ha.ne']⟩
  let v : Circle := ⟨z.2 / (b : ℂ), by
    change z.2 / (b : ℂ) ∈ Metric.sphere 0 1
    simp [Complex.norm_real, abs_of_pos hb, hzb, hb.ne']⟩
  have hec : (a : ℂ) ^ p = (b : ℂ) ^ q := by exact_mod_cast he
  have huv : u ^ p = v ^ q := by
    apply Circle.ext
    change (z.1 / (a : ℂ)) ^ p = (z.2 / (b : ℂ)) ^ q
    rw [div_pow, div_pow, hec, hzpow]
  obtain ⟨w, ⟨hwu, hwv⟩, _⟩ := exists_unique_common_phase hpq u v huv
  refine ⟨w, Prod.ext ?_ ?_⟩
  · change (a : ℂ) * (w : ℂ) ^ q = _
    rw [← Circle.coe_pow, hwu]
    change (a : ℂ) * (z.1 / (a : ℂ)) = z.1
    rw [mul_comm, div_mul_cancel₀ _ hac]
  · change (b : ℂ) * (w : ℂ) ^ p = _
    rw [← Circle.coe_pow, hwv]
    change (b : ℂ) * (z.2 / (b : ℂ)) = z.2
    rw [mul_comm, div_mul_cancel₀ _ hbc]

/-- The polynomial zero set is exactly the standard torus-knot image in
the ambient complex coordinates. -/
theorem unitTorusKnotLocus_eq_range {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : a ^ 2 + b ^ 2 = 1) (he : a ^ p = b ^ q) :
    unitTorusKnotLocus p q = Set.range (torusKnotParam p q a b) := by
  ext z
  exact ⟨exists_torusKnotParam_eq hp hq hpq ha hb hs he, by
    rintro ⟨w, rfl⟩
    exact torusKnotParam_mem_unitTorusKnotLocus p q ha.le hb.le hs he w⟩

/-- The torus-knot parameter map is a homeomorphism onto the zero
set, with its subspace topology from complex two-space. -/
noncomputable def torusKnotLocusHomeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (hs : a ^ 2 + b ^ 2 = 1) (he : a ^ p = b ^ q) :
    Circle ≃ₜ ↥(unitTorusKnotLocus p q) := by
  let f : Circle → ↥(unitTorusKnotLocus p q) := fun w =>
    ⟨torusKnotParam p q a b w, torusKnotParam_mem_unitTorusKnotLocus p q ha.le hb.le hs he w⟩
  have hinj : Function.Injective f := fun _ _ h =>
    torusKnotParam_injective hpq ha hb (congrArg Subtype.val h)
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨w, hw⟩ := exists_torusKnotParam_eq hp hq hpq ha hb hs he z.property
    exact ⟨w, Subtype.ext hw⟩
  have hc : Continuous f := (continuous_torusKnotParam p q a b).subtype_mk _
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨hinj, hsurj⟩) hc

/-- The actual rational Bateman pair lies on the torus knot exactly at
space-time points where the associated torus polynomial vanishes. -/
theorem rational_pair_mem_unitTorusKnotLocus_iff (p q : ℕ) (x y z t : ℝ) :
    (rationalAlpha x y z t, rationalBeta x y z t) ∈ unitTorusKnotLocus p q ↔
      torusPolynomial p q (rationalAlpha x y z t) (rationalBeta x y z t) = 0 := by
  have hunit : ‖rationalAlpha x y z t‖ ^ 2 + ‖rationalBeta x y z t‖ ^ 2 = 1 := by
    simpa only [Complex.normSq_eq_norm_sq] using complex_rational_pair_unit x y z t
  exact ⟨fun h => h.2, fun h => ⟨hunit, h⟩⟩

end Qatlib.Papers.KnotLight13.TorusFamily
