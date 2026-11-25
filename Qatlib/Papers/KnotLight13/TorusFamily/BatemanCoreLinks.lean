/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalCores
public import Mathlib.Topology.Order

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp

/-!
# Phase components of the Bateman field-line cores

[Kedia2013TyingKnots], p. 150404-2 and Fig. 2,
[DOI](https://doi.org/10.1103/PhysRevLett.111.150404).
Multiplying the two exponents by the same integer preserves the peak
radii and divides the extremal level into the phase roots of its label.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set

/-- A common positive multiplier of the exponents leaves the peak
radius unchanged and raises the peak amplitude to that power. -/
theorem poweredPeakAmplitude_mul_exponents {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hd : 0 < d) : poweredPeakAmplitude (p * d) (q * d) = poweredPeakAmplitude p q ^ d := by
  have hd₀ : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hr : poweredPeakRadius (p * d) (q * d) = poweredPeakRadius p q := by
    simp only [poweredPeakRadius, Nat.cast_mul, ← add_mul]
    exact mul_div_mul_right _ _ hd₀
  have hradii : poweredCoreRadii (p * d) (q * d) = poweredCoreRadii p q := by
    simp only [poweredCoreRadii, hr]
  rw [poweredPeakAmplitude_eq_radii (Nat.mul_pos hp hd) (Nat.mul_pos hq hd),
    poweredPeakAmplitude_eq_radii hp hq, hradii, pow_mul, pow_mul, mul_pow]

/-- At every physical time, the extremal core of two scaled exponents
is the union of the extremal phase cores of the reduced exponents. -/
theorem poweredPhysicalCore_mul_exponents {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hd : 0 < d) (t : ℝ) (phase : Circle) :
    poweredPhysicalCore (p * d) (q * d) t phase =
      ⋃ w : {w : Circle // w ^ d = phase}, poweredPhysicalCore p q t w.1 := by
  have hA₀ := poweredPeakAmplitude_pos hp hq
  have hA : (poweredPeakAmplitude p q : ℂ) ≠ 0 := by exact_mod_cast hA₀.ne'
  have hlabel (s : ℝ × ℝ × ℝ) :
      batemanPoweredLabel (p * d) (q * d) t s = batemanPoweredLabel p q t s ^ d := by
    simp only [batemanPoweredLabel, batemanAlphaPower, batemanBetaPower, pow_mul, mul_pow]
  ext s
  simp only [poweredPhysicalCore, mem_ofPred_eq, mem_iUnion, hlabel,
    poweredPeakAmplitude_mul_exponents hp hq hd, Complex.ofReal_pow]
  constructor
  · intro h
    let z := batemanPoweredLabel p q t s
    have hz : ‖z‖ ^ d = poweredPeakAmplitude p q ^ d := by
      simpa [z, norm_pow, norm_mul, Complex.norm_real, Real.norm_of_nonneg hA₀.le] using congrArg norm h
    have hnorm := (pow_left_inj₀ (norm_nonneg z) hA₀.le hd.ne').mp hz
    let w : Circle := ⟨z / (poweredPeakAmplitude p q : ℂ), by
      change z / (poweredPeakAmplitude p q : ℂ) ∈ Metric.sphere 0 1
      rw [Metric.mem_sphere, dist_zero_right, norm_div, hnorm, Complex.norm_real,
        Real.norm_of_nonneg hA₀.le, div_self hA₀.ne']⟩
    have hw : w ^ d = phase := by
      apply Circle.ext
      change (z / (poweredPeakAmplitude p q : ℂ)) ^ d = (phase : ℂ)
      rw [div_pow, div_eq_iff (pow_ne_zero _ hA), mul_comm]
      exact h
    refine ⟨⟨w, hw⟩, ?_⟩
    change z = (poweredPeakAmplitude p q : ℂ) * (z / (poweredPeakAmplitude p q : ℂ))
    rw [mul_comm, div_mul_cancel₀ _ hA]
  · rintro ⟨w, hw⟩
    rw [hw, mul_pow, ← Circle.coe_pow, w.property]

/-- Two distinct phases label disjoint extremal cores. -/
theorem poweredPhysicalCore_phase_disjoint {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {v w : Circle} (hvw : v ≠ w) :
    Disjoint (poweredPhysicalCore p q t v) (poweredPhysicalCore p q t w) := by
  have hA : (poweredPeakAmplitude p q : ℂ) ≠ 0 := by
    exact_mod_cast (poweredPeakAmplitude_pos hp hq).ne'
  refine Set.disjoint_left.mpr (fun x hv hw => hvw (Circle.ext ?_))
  exact mul_left_cancel₀ hA (hv.symm.trans hw)

/-- Every unit phase has exactly `d` distinct `d`-th roots on the unit
circle. They are obtained by multiplying a chosen root by the `d`
successive powers of a primitive root of unity. -/
theorem circlePhaseRoots_equiv_fin {d : ℕ} (hd : 0 < d) (phase : Circle) :
    Nonempty (Fin d ≃ {w : Circle // w ^ d = phase}) := by
  have : NeZero d := ⟨hd.ne'⟩
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_pow_nat_eq (phase : ℂ) hd
  have ha₀ : a ≠ 0 := by
    intro h
    rw [h, zero_pow hd.ne'] at ha
    exact Circle.coe_ne_zero phase ha.symm
  let ζ := Complex.exp (2 * Real.pi * Complex.I / d)
  have hζ : IsPrimitiveRoot ζ d := Complex.isPrimitiveRoot_exp d hd.ne'
  have hpow (i : Fin d) : (ζ ^ (i : ℕ) * a) ^ d = (phase : ℂ) := by
    rw [mul_pow, pow_right_comm ζ (i : ℕ) d, hζ.pow_eq_one, one_pow, one_mul, ha]
  let w (i : Fin d) : Circle := ⟨ζ ^ (i : ℕ) * a, by
    change ζ ^ (i : ℕ) * a ∈ Metric.sphere 0 1
    rw [Metric.mem_sphere, dist_zero_right]
    apply (pow_left_inj₀ (norm_nonneg _) zero_le_one hd.ne').mp
    rw [← norm_pow, hpow, Circle.norm_coe, one_pow]⟩
  let f (i : Fin d) : {w : Circle // w ^ d = phase} := ⟨w i, Circle.ext (hpow i)⟩
  refine ⟨Equiv.ofBijective f ⟨?_, ?_⟩⟩
  · intro i j h
    have he : ζ ^ (i : ℕ) * a = ζ ^ (j : ℕ) * a := congrArg (fun u => (u.1 : ℂ)) h
    exact Fin.ext (hζ.injOn_pow_mul ha₀ (Finset.mem_range.mpr i.isLt) (Finset.mem_range.mpr j.isLt) he)
  · intro u
    have hu : (u.1 : ℂ) ^ d = (phase : ℂ) := congrArg (fun v : Circle => (v : ℂ)) u.property
    have hratio : ((u.1 : ℂ) / a) ^ d = 1 := by
      rw [div_pow, hu, ha, div_self (Circle.coe_ne_zero phase)]
    obtain ⟨i, hi, h⟩ := hζ.eq_pow_of_pow_eq_one hratio
    refine ⟨⟨i, hi⟩, Subtype.ext (Circle.ext ?_)⟩
    change ζ ^ i * a = (u.1 : ℂ)
    rw [h, div_mul_cancel₀ _ ha₀]

/-- Scaling coprime exponents by `d` gives exactly `d` embedded
circle components in the physical extremal phase fiber. -/
noncomputable def poweredPhysicalCoreComponents {p q d : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hc : Nat.Coprime p q) (hd : 0 < d) (t : ℝ) (phase : Circle) :
    Fin d × Circle ≃ₜ ↥(poweredPhysicalCore (p * d) (q * d) t phase) := by
  let phases := Classical.choice (circlePhaseRoots_equiv_fin hd phase)
  let core (i : Fin d) := poweredPhysicalCoreHomeomorph hp hq hc t (phases i).1
  have hsplit := poweredPhysicalCore_mul_exponents hp hq hd t phase
  let f (x : Fin d × Circle) : ↥(poweredPhysicalCore (p * d) (q * d) t phase) :=
    ⟨(core x.1 x.2).val, hsplit ▸ mem_iUnion.mpr ⟨phases x.1, (core x.1 x.2).property⟩⟩
  have hcont : Continuous f := by
    apply continuous_prod_of_discrete_left.mpr
    intro i
    exact (continuous_subtype_val.comp (core i).continuous).subtype_mk _
  refine hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective f ⟨?_, ?_⟩)
  · rintro ⟨i, v⟩ ⟨j, w⟩ h
    have he : (core i v).val = (core j w).val := congrArg Subtype.val h
    have hij : i = j := by
      by_contra hn
      have hp' : (phases i).1 ≠ (phases j).1 :=
        fun h => hn (phases.injective (Subtype.ext h))
      have hd' := poweredPhysicalCore_phase_disjoint hp hq t hp'
      exact Set.disjoint_left.mp hd' (core i v).property (he.symm ▸ (core j w).property)
    subst j
    exact Prod.ext rfl ((core i).injective (Subtype.ext he))
  · intro x
    have hmem : x.val ∈ ⋃ w : {w : Circle // w ^ d = phase}, poweredPhysicalCore p q t w.1 := by
      rw [← hsplit]
      exact x.property
    obtain ⟨w, hw⟩ := mem_iUnion.mp hmem
    let i := phases.symm w
    have hi : phases i = w := phases.apply_symm_apply w
    have hx : x.val ∈ poweredPhysicalCore p q t (phases i).1 := hi.symm ▸ hw
    obtain ⟨v, hv⟩ := (core i).surjective ⟨x.val, hx⟩
    refine ⟨(i, v), Subtype.ext ?_⟩
    change (core i v).val = x.val
    exact congrArg Subtype.val hv

/-- For arbitrary positive exponents, each fixed extremal phase contains
one circle for each root of unity of order `gcd p q`. -/
noncomputable def poweredPhysicalCoreGcdComponents {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) (phase : Circle) :
    Fin (p.gcd q) × Circle ≃ₜ ↥(poweredPhysicalCore p q t phase) := by
  let d := p.gcd q
  have hd : 0 < d := Nat.gcd_pos_of_pos_left q hp
  have hp' : p / d * d = p := Nat.div_mul_cancel (Nat.gcd_dvd_left p q)
  have hq' : q / d * d = q := Nat.div_mul_cancel (Nat.gcd_dvd_right p q)
  have hp₀ : 0 < p / d := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, zero_mul] at hp'
    exact hp.ne' hp'.symm
  have hq₀ : 0 < q / d := by
    by_contra! h
    rw [Nat.eq_zero_of_le_zero h, zero_mul] at hq'
    exact hq.ne' hq'.symm
  have hc : Nat.Coprime (p / d) (q / d) := Nat.coprime_div_gcd_div_gcd hd
  have he := congrArg₂ (fun a b => poweredPhysicalCore a b t phase) hp' hq'
  exact (poweredPhysicalCoreComponents hp₀ hq₀ hc hd t phase).trans (Homeomorph.setCongr he)

/-- Two distinct extremal phases, in particular the two signed magnetic
or electric phases, give two disjoint groups of `gcd p q` core circles. -/
noncomputable def poweredPhysicalCorePairComponents {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {v w : Circle} (hvw : v ≠ w) :
    ((Fin (p.gcd q) × Circle) ⊕ (Fin (p.gcd q) × Circle)) ≃ₜ
      ↥(poweredPhysicalCore p q t v ∪ poweredPhysicalCore p q t w) := by
  classical
  let e := (Equiv.Set.union (poweredPhysicalCore_phase_disjoint hp hq t hvw)).symm
  let f := Homeomorph.sumCongr (poweredPhysicalCoreGcdComponents hp hq t v)
    (poweredPhysicalCoreGcdComponents hp hq t w)
  have he : Continuous e :=
    continuous_sum_dom.mpr ⟨continuous_subtype_val.subtype_mk _, continuous_subtype_val.subtype_mk _⟩
  exact (he.comp f.continuous).homeoOfEquivCompactToT2 (f := f.toEquiv.trans e)

end Qatlib.Papers.KnotLight13.TorusFamily
