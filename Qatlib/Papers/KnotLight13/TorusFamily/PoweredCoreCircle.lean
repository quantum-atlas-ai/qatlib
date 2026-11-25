/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PowerCoreLevels

import Mathlib.Topology.Algebra.Group.ZPow

/-!
# The actual extremal Bateman curves on the sphere

For positive coprime powers, fixing the phase at the maximum modulus of
the true field-line product label gives a single embedded torus circle.
The two windings in these scalar coordinates are `q` and `-p`. The
normalized radii are fixed by the strict maximum of the product modulus.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta complex_rational_pair_unit)

/-- The two positive radii of the extremal product torus. -/
noncomputable def poweredCoreRadii (p q : ℕ) : ℝ × ℝ :=
  (Real.sqrt (poweredPeakRadius p q), Real.sqrt (1 - poweredPeakRadius p q))

/-- The two radii are positive and their squares sum to one. -/
theorem poweredCoreRadii_spec {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    0 < (poweredCoreRadii p q).1 ∧ 0 < (poweredCoreRadii p q).2 ∧
      (poweredCoreRadii p q).1 ^ 2 = poweredPeakRadius p q ∧
      (poweredCoreRadii p q).2 ^ 2 = 1 - poweredPeakRadius p q := by
  have hr := poweredPeakRadius_mem hp hq
  exact ⟨Real.sqrt_pos.2 hr.1, Real.sqrt_pos.2 (sub_pos.mpr hr.2),
    Real.sq_sqrt hr.1.le, Real.sq_sqrt (sub_nonneg.mpr hr.2.le)⟩

/-- The radial amplitude equals the product of the two radii to their powers. -/
theorem poweredPeakAmplitude_eq_radii {p q : ℕ} (hp : 0 < p) (hq : 0 < q) :
    poweredPeakAmplitude p q = (poweredCoreRadii p q).1 ^ p * (poweredCoreRadii p q).2 ^ q := by
  obtain ⟨ha, hb, hₐ, hᵦ⟩ := poweredCoreRadii_spec hp hq
  apply (pow_left_inj₀ (poweredPeakAmplitude_pos hp hq).le
    (mul_nonneg (pow_nonneg ha.le _) (pow_nonneg hb.le _)) (by decide : (2 : ℕ) ≠ 0)).1
  rw [poweredPeakAmplitude_sq hp hq, mul_pow, pow_right_comm _ p 2, pow_right_comm _ q 2, hₐ, hᵦ]
  rfl

/-- The exact product-label fiber of maximal modulus on the unit sphere. -/
def poweredSphereCore (p q : ℕ) (phase : Circle) : Set (ℂ × ℂ) :=
  {z | Complex.normSq z.1 + Complex.normSq z.2 = 1 ∧
    z.1 ^ p * z.2 ^ q = (poweredPeakAmplitude p q : ℂ) * (phase : ℂ)}

/-- The norm of each coordinate of a point of the phase fiber is its
corresponding core radius. -/
theorem poweredSphereCore_norms {p q : ℕ} (hp : 0 < p) (hq : 0 < q) {phase : Circle}
    {z : ℂ × ℂ} (hz : z ∈ poweredSphereCore p q phase) :
    ‖z.1‖ = (poweredCoreRadii p q).1 ∧ ‖z.2‖ = (poweredCoreRadii p q).2 := by
  obtain ⟨ha, hb, hₐ, hᵦ⟩ := poweredCoreRadii_spec hp hq
  obtain ⟨hu, hphase⟩ := hz
  have hc : Complex.normSq (z.1 ^ p * z.2 ^ q) = poweredPeakAmplitude p q ^ 2 := by
    rw [hphase, map_mul, Circle.normSq_coe, mul_one, Complex.normSq_ofReal, pow_two]
  have h₁ := (normSq_poweredProduct_eq_peak_iff hp hq hu).1 hc
  have h₂ : Complex.normSq z.2 = 1 - poweredPeakRadius p q := by linarith
  rw [Complex.normSq_eq_norm_sq] at h₁ h₂
  exact ⟨(pow_left_inj₀ (norm_nonneg _) ha.le (by decide : (2 : ℕ) ≠ 0)).1 (h₁.trans hₐ.symm),
    (pow_left_inj₀ (norm_nonneg _) hb.le (by decide : (2 : ℕ) ≠ 0)).1 (h₂.trans hᵦ.symm)⟩

/-- Bézout's coefficients give one phase pair with the prescribed product. -/
private theorem core_phase_base {p q : ℕ} (hpq : Nat.Coprime p q) (phase : Circle) :
    (phase ^ Nat.gcdA p q) ^ p * (phase ^ Nat.gcdB p q) ^ q = phase := by
  have hb : (p : ℤ) * Nat.gcdA p q + (q : ℤ) * Nat.gcdB p q = 1 := by
    simpa only [hpq.gcd_eq_one, Nat.cast_one] using (Nat.gcd_eq_gcd_ab p q).symm
  calc
    _ = (phase ^ Nat.gcdA p q) ^ (p : ℤ) *
        (phase ^ Nat.gcdB p q) ^ (q : ℤ) := by rw [zpow_natCast, zpow_natCast]
    _ = _ := by rw [← zpow_mul', ← zpow_mul', ← zpow_add, hb, zpow_one]


/-- A phase fiber with radii `a,b` winds positively in the first
coordinate and negatively in the second. The constant phases select
the desired normalized product. -/
noncomputable def poweredTorusPhaseParam (p q : ℕ) (a b : ℝ) (phase w : Circle) : ℂ × ℂ :=
  ((a : ℂ) * ((phase ^ Nat.gcdA p q * w ^ q : Circle) : ℂ),
    (b : ℂ) * ((phase ^ Nat.gcdB p q / w ^ p : Circle) : ℂ))

/-- The parametrization is jointly continuous in the radii and the two phases. -/
theorem continuous_poweredTorusPhaseParam (p q : ℕ) :
    Continuous (fun z : (ℝ × ℝ) × Circle × Circle =>
      poweredTorusPhaseParam p q z.1.1 z.1.2 z.2.1 z.2.2) := by
  have hc : Continuous (fun w : Circle => (w : ℂ)) := continuous_subtype_val
  have hu : Continuous (fun z : (ℝ × ℝ) × Circle × Circle => z.2.1) :=
    continuous_fst.comp continuous_snd
  have hw : Continuous (fun z : (ℝ × ℝ) × Circle × Circle => z.2.2) :=
    continuous_snd.comp continuous_snd
  exact ((Complex.continuous_ofReal.comp (continuous_fst.comp continuous_fst)).mul
      (hc.comp ((hu.zpow (Nat.gcdA p q)).mul (hw.pow q)))).prodMk
    ((Complex.continuous_ofReal.comp (continuous_snd.comp continuous_fst)).mul
      (hc.comp ((hu.zpow (Nat.gcdB p q)).div' (hw.pow p))))

/-- The two radii and actual product are exact for every parameter point. -/
theorem poweredTorusPhaseParam_spec {p q : ℕ} (hpq : Nat.Coprime p q) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (phase w : Circle) :
    let z := poweredTorusPhaseParam p q a b phase w
    ‖z.1‖ = a ∧ ‖z.2‖ = b ∧
      z.1 ^ p * z.2 ^ q = ((a ^ p * b ^ q : ℝ) : ℂ) * (phase : ℂ) := by
  let u := phase ^ Nat.gcdA p q * w ^ q
  let v := phase ^ Nat.gcdB p q / w ^ p
  have huv : u ^ p * v ^ q = phase := by
    dsimp only [u, v]
    rw [mul_pow, div_pow, ← pow_mul, ← pow_mul, mul_comm q p]
    calc
      _ = (phase ^ Nat.gcdA p q) ^ p *
          ((phase ^ Nat.gcdB p q) ^ q / w ^ (p * q) * w ^ (p * q)) := by
        rw [mul_assoc, mul_comm (w ^ (p * q)) ((phase ^ Nat.gcdB p q) ^ q / w ^ (p * q))]
      _ = (phase ^ Nat.gcdA p q) ^ p * (phase ^ Nat.gcdB p q) ^ q := by rw [div_mul_cancel]
      _ = _ := core_phase_base hpq phase
  refine ⟨?_, ?_, ?_⟩
  · change ‖(a : ℂ) * (u : ℂ)‖ = a
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg ha]
  · change ‖(b : ℂ) * (v : ℂ)‖ = b
    rw [norm_mul, Circle.norm_coe, mul_one, Complex.norm_real, Real.norm_of_nonneg hb]
  · change ((a : ℂ) * (u : ℂ)) ^ p * ((b : ℂ) * (v : ℂ)) ^ q = _
    rw [mul_pow, mul_pow, mul_mul_mul_comm, ← Circle.coe_pow, ← Circle.coe_pow, ← Circle.coe_mul, huv]
    push_cast
    rfl

/-- The phase circle covers the entire fiber with the given positive
radii, and traces it exactly once for coprime powers. -/
theorem poweredTorusPhaseParam_bijective {p q : ℕ} (hpq : Nat.Coprime p q) {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (phase : Circle) :
    Function.Injective (poweredTorusPhaseParam p q a b phase) ∧
      Set.range (poweredTorusPhaseParam p q a b phase) =
        {z : ℂ × ℂ | ‖z.1‖ = a ∧ ‖z.2‖ = b ∧
          z.1 ^ p * z.2 ^ q = ((a ^ p * b ^ q : ℝ) : ℂ) * (phase : ℂ)} := by
  let u₀ := phase ^ Nat.gcdA p q
  let v₀ := phase ^ Nat.gcdB p q
  have ha₀ : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hb₀ : (b : ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hbase : u₀ ^ p * v₀ ^ q = phase := core_phase_base hpq phase
  constructor
  · intro x y h
    have hx : u₀ * x ^ q = u₀ * y ^ q :=
      Circle.ext (mul_left_cancel₀ ha₀ (congrArg Prod.fst h))
    have hy : v₀ / x ^ p = v₀ / y ^ p :=
      Circle.ext (mul_left_cancel₀ hb₀ (congrArg Prod.snd h))
    have hq' := mul_left_cancel hx
    have hp' : x ^ p = y ^ p := by
      have hv := mul_left_cancel (a := v₀) (by simpa only [div_eq_mul_inv] using hy)
      exact inv_injective hv
    have hxp : (x ^ q) ^ p = (x ^ p) ^ q := by rw [← pow_mul, ← pow_mul, mul_comm q p]
    obtain ⟨_, _, huniq⟩ := exists_unique_common_phase hpq (x ^ q) (x ^ p) hxp
    exact (huniq x ⟨rfl, rfl⟩).trans (huniq y ⟨hq'.symm, hp'.symm⟩).symm
  · ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact poweredTorusPhaseParam_spec hpq ha.le hb.le phase w
    · rintro ⟨hza, hzb, hprod⟩
      have hnorm₁ : ‖z.1 / (a : ℂ)‖ = 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg ha.le, hza]
        exact div_self ha.ne'
      have hnorm₂ : ‖z.2 / (b : ℂ)‖ = 1 := by
        rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hb.le, hzb]
        exact div_self hb.ne'
      let u : Circle := ⟨z.1 / (a : ℂ), by
        change _ ∈ Metric.sphere 0 1
        simpa only [Metric.mem_sphere, dist_zero_right] using hnorm₁⟩
      let v : Circle := ⟨z.2 / (b : ℂ), by
        change _ ∈ Metric.sphere 0 1
        simpa only [Metric.mem_sphere, dist_zero_right] using hnorm₂⟩
      have hzu : (a : ℂ) * (u : ℂ) = z.1 := by
        change (a : ℂ) * (z.1 / (a : ℂ)) = z.1
        rw [mul_comm, div_mul_cancel₀ _ ha₀]
      have hzv : (b : ℂ) * (v : ℂ) = z.2 := by
        change (b : ℂ) * (z.2 / (b : ℂ)) = z.2
        rw [mul_comm, div_mul_cancel₀ _ hb₀]
      have huv : u ^ p * v ^ q = phase := by
        rw [← hzu, ← hzv, mul_pow, mul_pow, mul_mul_mul_comm] at hprod
        push_cast at hprod
        exact Circle.ext (mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ ha₀)
          (pow_ne_zero _ hb₀)) hprod)
      have hcommon : (u / u₀) ^ p = (v₀ / v) ^ q := by
        rw [div_pow, div_pow, div_eq_div_iff_mul_eq_mul, huv, mul_comm, hbase]
      obtain ⟨w, ⟨hwu, hwv⟩, _⟩ := exists_unique_common_phase hpq
        (u / u₀) (v₀ / v) hcommon
      have hleft : u₀ * w ^ q = u := by rw [hwu, mul_comm, div_mul_cancel]
      have hright : v₀ / w ^ p = v := by rw [hwv, div_div_cancel]
      refine ⟨w, Prod.ext ?_ ?_⟩
      · change (a : ℂ) * ((u₀ * w ^ q : Circle) : ℂ) = _
        rw [hleft, hzu]
      · change (b : ℂ) * ((v₀ / w ^ p : Circle) : ℂ) = _
        rw [hright, hzv]

/-- The phase parametrization at the peak radii. -/
noncomputable def poweredCoreSphereParam (p q : ℕ) (phase w : Circle) : ℂ × ℂ :=
  poweredTorusPhaseParam p q (poweredCoreRadii p q).1 (poweredCoreRadii p q).2 phase w

/-- The core parametrization is continuous. -/
theorem continuous_poweredCoreSphereParam (p q : ℕ) (phase : Circle) :
    Continuous (poweredCoreSphereParam p q phase) :=
  (continuous_poweredTorusPhaseParam p q).comp
    (continuous_const.prodMk (continuous_const.prodMk continuous_id))

/-- An arbitrary parameter point has the desired radius and product phase. -/
theorem poweredCoreSphereParam_mem {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase w : Circle) :
    poweredCoreSphereParam p q phase w ∈ poweredSphereCore p q phase := by
  obtain ⟨ha, hb, hₐ, hᵦ⟩ := poweredCoreRadii_spec hp hq
  obtain ⟨hza, hzb, hprod⟩ := poweredTorusPhaseParam_spec hpq ha.le hb.le phase w
  refine ⟨?_, ?_⟩
  · unfold poweredCoreSphereParam
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, hza, hzb, hₐ, hᵦ]
    ring
  · rw [poweredPeakAmplitude_eq_radii hp hq]
    exact hprod

/-- The complete peak phase fiber is traced once at coprime powers. -/
theorem poweredCoreSphereParam_bijective {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (phase : Circle) :
    Function.Injective (poweredCoreSphereParam p q phase) ∧
      Set.range (poweredCoreSphereParam p q phase) = poweredSphereCore p q phase := by
  obtain ⟨ha, hb, _, _⟩ := poweredCoreRadii_spec hp hq
  obtain ⟨hinj, hrange⟩ := poweredTorusPhaseParam_bijective hpq ha hb phase
  refine ⟨hinj, Set.ext fun z => ⟨?_, ?_⟩⟩
  · rintro ⟨w, rfl⟩
    exact poweredCoreSphereParam_mem hp hq hpq phase w
  · intro hz
    change z ∈ Set.range (poweredTorusPhaseParam p q _ _ phase)
    rw [hrange]
    have h := poweredSphereCore_norms hp hq hz
    exact ⟨h.1, h.2, poweredPeakAmplitude_eq_radii hp hq ▸ hz.2⟩

end Qatlib.Papers.KnotLight13.TorusFamily
