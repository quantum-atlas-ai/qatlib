/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PoweredSphereTori
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalCores
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanAxialRotation

import Mathlib.Tactic.LinearCombination

/-!
# Entire intermediate Bateman field-line tori in physical space

[Kedia2013TyingKnots], discussion of Fig. 2.
The sphere parametrization passes through the stereographic chart
without touching its pole and then follows the ray homeomorphism.
The actual axial rotation gives the imaginary-label tori from the
real-label tori, with the sign fixed by the Maxwell-duality phase.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open scoped Real
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha complex_rational_pair_unit)

/-- The full magnetic level on a physical time slice. -/
def poweredPhysicalRealLevel (p q : ℕ) (t c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {s | (batemanPoweredLabel p q t s).re = c}

/-- The full electric level on a physical time slice. -/
def poweredPhysicalImagLevel (p q : ℕ) (t c : ℝ) : Set (ℝ × ℝ × ℝ) :=
  {s | (batemanPoweredLabel p q t s).im = c}

/-- A nonzero real level with positive second power misses the stereographic pole. -/
theorem poweredSphereRealLevel_re_lt_one {p q : ℕ} (hq : 0 < q) {c : ℝ} (hn : c ≠ 0)
    {z : ℂ × ℂ} (hz : z ∈ poweredSphereRealLevel p q c) : z.1.re < 1 := by
  have hz₂ : z.2 ≠ 0 := by
    intro h
    exact hn (by simpa [h, zero_pow hq.ne'] using hz.2.symm)
  have hβ := Complex.normSq_pos.mpr hz₂
  have hα := hz.1
  rw [Complex.normSq_apply] at hα
  by_contra! h
  nlinarith [mul_nonneg (sub_nonneg.mpr h) (by linarith : 0 ≤ z.1.re + 1), sq_nonneg z.1.im]

/-- The stereographic chart followed by the ray map is an explicit
homeomorphism from the sphere level to the entire physical level. -/
noncomputable def poweredSphereRealLevelToPhysical {p q : ℕ} (hq : 0 < q) (t : ℝ)
    {c : ℝ} (hn : c ≠ 0) :
    ↥(poweredSphereRealLevel p q c) ≃ₜ ↥(poweredPhysicalRealLevel p q t c) := by
  let ray := batemanSliceHomeomorph t
  have hh (z : ↥(poweredSphereRealLevel p q c)) :
      batemanPairAt t (ray (initialCartesianPoint z.val)) = z.val := by
    change batemanPairAt t (batemanRay t (initialCartesianPoint z.val)) = _
    rw [batemanPairAt_batemanRay]
    apply initialBatemanPair_initialCartesianPoint
    · simpa only [Complex.normSq_eq_norm_sq] using z.property.1
    · exact poweredSphereRealLevel_re_lt_one hq hn z.property
  let f (z : ↥(poweredSphereRealLevel p q c)) : ↥(poweredPhysicalRealLevel p q t c) :=
    ⟨ray (initialCartesianPoint z.val), by
      change ((batemanPairAt t (ray (initialCartesianPoint z.val))).1 ^ p *
        (batemanPairAt t (ray (initialCartesianPoint z.val))).2 ^ q).re = c
      rw [hh]
      exact z.property.2⟩
  let g (s : ↥(poweredPhysicalRealLevel p q t c)) : ↥(poweredSphereRealLevel p q c) :=
    ⟨batemanPairAt t s.val,
      ⟨complex_rational_pair_unit s.val.1 s.val.2.1 s.val.2.2 t, s.property⟩⟩
  have h₁ : Continuous (fun z : ↥(poweredSphereRealLevel p q c) => z.val.1) :=
    continuous_fst.comp continuous_subtype_val
  have h₂ : Continuous (fun z : ↥(poweredSphereRealLevel p q c) => z.val.2) :=
    continuous_snd.comp continuous_subtype_val
  have hd : Continuous (fun z : ↥(poweredSphereRealLevel p q c) => 1 - z.val.1.re) :=
    continuous_const.sub (Complex.continuous_re.comp h₁)
  have hne (z : ↥(poweredSphereRealLevel p q c)) : 1 - z.val.1.re ≠ 0 :=
    (sub_pos.mpr (poweredSphereRealLevel_re_lt_one hq hn z.property)).ne'
  have hx := (Complex.continuous_re.comp h₂).div hd hne
  have hy := (Complex.continuous_im.comp h₂).neg.div hd hne
  have hz := (Complex.continuous_im.comp h₁).div hd hne
  have hchart : Continuous (fun z : ↥(poweredSphereRealLevel p q c) => initialCartesianPoint z.val) :=
    hx.prodMk (hy.prodMk hz)
  have hargs : Continuous (fun s : ℝ × ℝ × ℝ => (s.1, s.2.1, s.2.2, t)) := by fun_prop
  have hpair : Continuous (batemanPairAt t) :=
    (contDiff_rationalAlpha.continuous.comp hargs).prodMk (contDiff_rationalBeta.continuous.comp hargs)
  exact
    { toEquiv := {
        toFun := f
        invFun := g
        left_inv := fun z => Subtype.ext (hh z)
        right_inv := fun s => Subtype.ext (batemanRay_initialCartesianPoint_batemanPairAt t s.val) }
      continuous_toFun := (ray.continuous.comp hchart).subtype_mk _
      continuous_invFun := (hpair.comp continuous_subtype_val).subtype_mk _ }

/-- Every whole nonzero intermediate magnetic level is an embedded
topological torus on its physical time slice. -/
noncomputable def poweredPhysicalRealLevelHomeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (t : ℝ) {c : ℝ} (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) :
    (Circle × Circle) ≃ₜ ↥(poweredPhysicalRealLevel p q t c) :=
  (poweredSphereRealLevelHomeomorph hp hq hpq hn hc).trans (poweredSphereRealLevelToPhysical hq t hn)

/-- The negative angle is the inverse of the explicit axial rotation. -/
theorem batemanAxialRotation_neg_cancel (θ : ℝ) (s : ℝ × ℝ × ℝ) :
    batemanAxialRotation (-θ) (batemanAxialRotation θ s) = s := by
  rcases s with ⟨x, y, z⟩
  simp only [batemanAxialRotation, Real.cos_neg, Real.sin_neg, Prod.mk.injEq]
  refine ⟨?_, ?_, trivial⟩
  · linear_combination x * Real.sin_sq_add_cos_sq θ
  · linear_combination y * Real.sin_sq_add_cos_sq θ

/-- Axial rotation is a homeomorphism of the physical slice. -/
noncomputable def batemanAxialHomeomorph (θ : ℝ) : (ℝ × ℝ × ℝ) ≃ₜ (ℝ × ℝ × ℝ) where
  toFun := batemanAxialRotation θ
  invFun := batemanAxialRotation (-θ)
  left_inv := batemanAxialRotation_neg_cancel θ
  right_inv := fun s => by simpa only [neg_neg] using batemanAxialRotation_neg_cancel (-θ) s
  continuous_toFun := by unfold batemanAxialRotation; fun_prop
  continuous_invFun := by unfold batemanAxialRotation; fun_prop

/-- The signed duality angle maps the entire real level `-c` onto
the imaginary level `c`. -/
theorem poweredPhysicalLevel_axial_iff {p q : ℕ} (hq : 0 < q) (t c : ℝ)
    (s : ℝ × ℝ × ℝ) :
    s ∈ poweredPhysicalRealLevel p q t (-c) ↔
      batemanAxialRotation (π / (2 * (q : ℝ))) s ∈ poweredPhysicalImagLevel p q t c := by
  rcases s with ⟨x, y, z⟩
  let θ := π / (2 * (q : ℝ))
  have h := poweredProductLabel_axialRotation p q θ x y z t
  rw [batemanAxialPhase_special hq] at h
  change (batemanPoweredLabel p q t (x, y, z)).re = -c ↔
    (batemanPoweredLabel p q t (batemanAxialRotation θ (x, y, z))).im = c
  change batemanPoweredLabel p q t (batemanAxialRotation θ (x, y, z)) =
    -Complex.I * batemanPoweredLabel p q t (x, y, z) at h
  rw [h]
  simp [Complex.mul_im, neg_eq_iff_eq_neg]

/-- Every whole nonzero intermediate electric level is an embedded
topological torus on its physical time slice. -/
noncomputable def poweredPhysicalImagLevelHomeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (t : ℝ) {c : ℝ} (hn : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q) :
    (Circle × Circle) ≃ₜ ↥(poweredPhysicalImagLevel p q t c) :=
  (poweredPhysicalRealLevelHomeomorph hp hq hpq t (neg_ne_zero.mpr hn) (by rwa [abs_neg])).trans
    ((batemanAxialHomeomorph (π / (2 * (q : ℝ)))).subtype (poweredPhysicalLevel_axial_iff hq t c))

/-- The ray homeomorphism carries the entire real level to the real
level at the later time. -/
theorem batemanSliceHomeomorph_realLevel_iff (p q : ℕ) (t c : ℝ) (s : ℝ × ℝ × ℝ) :
    s ∈ poweredPhysicalRealLevel p q 0 c ↔
      batemanSliceHomeomorph t s ∈ poweredPhysicalRealLevel p q t c := by
  change (batemanPoweredLabel p q 0 s).re = c ↔
    (batemanPoweredLabel p q t (batemanRay t s)).re = c
  have h := poweredProductLabel_batemanRay p q t s
  change batemanPoweredLabel p q t (batemanRay t s) = batemanPoweredLabel p q 0 s at h
  rw [h]

/-- The ray homeomorphism carries the entire imaginary level to the
imaginary level at the later time. -/
theorem batemanSliceHomeomorph_imagLevel_iff (p q : ℕ) (t c : ℝ) (s : ℝ × ℝ × ℝ) :
    s ∈ poweredPhysicalImagLevel p q 0 c ↔
      batemanSliceHomeomorph t s ∈ poweredPhysicalImagLevel p q t c := by
  change (batemanPoweredLabel p q 0 s).im = c ↔
    (batemanPoweredLabel p q t (batemanRay t s)).im = c
  have h := poweredProductLabel_batemanRay p q t s
  change batemanPoweredLabel p q t (batemanRay t s) = batemanPoweredLabel p q 0 s at h
  rw [h]

/-- In the positive real-label half of the field, superlevels are the
preimages of nested disks in the radial and imaginary coordinates. -/
theorem poweredReal_superlevel_iff_radialDisk {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t c : ℝ) (hc : 0 ≤ c) (x y z : ℝ)
    (hg : 0 ≤ (poweredProductLabel p q x y z t).re) :
    c ≤ (poweredProductLabel p q x y z t).re ↔
      poweredRadialHeight p q (Complex.normSq (rationalAlpha x y z t)) ^ 2 +
          (poweredProductLabel p q x y z t).im ^ 2 ≤ poweredPeakAmplitude p q ^ 2 - c ^ 2 := by
  rw [poweredProduct_radial_circle hp hq x y z t]
  constructor
  · intro h
    have hs := pow_le_pow_left₀ hc h 2
    linarith
  · intro h
    apply le_of_pow_le_pow_left₀ (n := 2) (by decide) hg
    linarith

end Qatlib.Papers.KnotLight13.TorusFamily
