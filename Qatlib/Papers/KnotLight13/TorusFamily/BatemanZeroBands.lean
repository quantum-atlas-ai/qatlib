/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanOpenPhaseBand
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanZeroLevels

/-!
# The open branches of the physical zero levels

Away from the coordinate zeros, a zero real product label has purely
imaginary phase. Its two signs give cylinders on each time slice.
The signed axial rotation transfers these branches to the electric level.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open Qatlib.Papers.KnotLight13.TorusFamily (complex_rational_pair_unit)

/-- A purely imaginary phase selects the branch of the real zero level
where the nonzero imaginary product has the same sign. -/
theorem mem_poweredSphereOpenPhaseBand_iff_imag_sign {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {phase : Circle} (hphase : (phase : ℂ).re = 0) (z : ℂ × ℂ) :
    z ∈ poweredSphereOpenPhaseBand p q phase ↔
      z ∈ poweredSphereRealLevel p q 0 ∧
        0 < (phase : ℂ).im * (z.1 ^ p * z.2 ^ q).im := by
  let a := ‖z.1‖ ^ p * ‖z.2‖ ^ q
  let g := z.1 ^ p * z.2 ^ q
  have hnorm : ‖g‖ = a := by simp [g, a, norm_pow]
  have hphaseAbs : |(phase : ℂ).im| = 1 :=
    (Complex.abs_im_eq_norm.mpr hphase).trans (Circle.norm_coe _)
  have hphaseNonzero : (phase : ℂ).im ≠ 0 := by
    intro h
    rw [h, abs_zero] at hphaseAbs
    exact zero_ne_one hphaseAbs
  change (_ ∧ Complex.normSq z.1 ∈ Ioo (0 : ℝ) 1 ∧ g = (a : ℂ) * (phase : ℂ)) ↔
    (_ ∧ g.re = 0) ∧ 0 < (phase : ℂ).im * g.im
  constructor
  · rintro ⟨hunit, hr, hlabel⟩
    have ha₁ : z.1 ≠ 0 := Complex.normSq_pos.mp hr.1
    have ha₂ : z.2 ≠ 0 := Complex.normSq_pos.mp (by linarith [hr.2])
    have ha : 0 < a := mul_pos (pow_pos (norm_pos_iff.mpr ha₁) _) (pow_pos (norm_pos_iff.mpr ha₂) _)
    rw [hlabel, Complex.re_ofReal_mul, Complex.im_ofReal_mul, hphase, mul_zero]
    exact ⟨⟨hunit, rfl⟩, by rw [mul_left_comm]; exact mul_pos ha (mul_self_pos.mpr hphaseNonzero)⟩
  · rintro ⟨⟨hunit, hgRe⟩, hsign⟩
    have hg : g ≠ 0 := by
      intro h
      rw [h, Complex.zero_im, mul_zero] at hsign
      exact lt_irrefl _ hsign
    have hz₁ : z.1 ≠ 0 := by
      intro h
      exact hg (by simp [g, h, zero_pow hp.ne'])
    have hz₂ : z.2 ≠ 0 := by
      intro h
      exact hg (by simp [g, h, zero_pow hq.ne'])
    have hgAbs : |g.im| = a := (Complex.abs_im_eq_norm.mpr hgRe).trans hnorm
    have hgIm : g.im = a * (phase : ℂ).im := by
      rcases (mul_pos_iff.mp hsign) with ⟨hph, him⟩ | ⟨hph, him⟩
      · rw [abs_of_pos hph] at hphaseAbs
        rwa [hphaseAbs, mul_one, ← abs_of_pos him]
      · rw [abs_of_neg hph] at hphaseAbs
        have hph' : (phase : ℂ).im = -1 := by linarith
        rw [hph', mul_neg, mul_one]
        rw [abs_of_neg him] at hgAbs
        linarith
    refine ⟨hunit, ⟨Complex.normSq_pos.mpr hz₁, ?_⟩, ?_⟩
    · linarith [Complex.normSq_pos.mpr hz₂]
    · exact Complex.ext (by rw [Complex.re_ofReal_mul, hphase, mul_zero]; exact hgRe)
        (by rw [Complex.im_ofReal_mul]; exact hgIm)

/-- One signed branch of the physical magnetic zero set on a time slice. -/
def poweredPhysicalZeroBand (p q : ℕ) (t : ℝ) (phase : Circle) : Set (ℝ × ℝ × ℝ) :=
  {x | x ∈ poweredPhysicalRealLevel p q t 0 ∧
    0 < (phase : ℂ).im * (batemanPoweredLabel p q t x).im}

/-- Each signed branch of the physical magnetic zero level, with the coordinate
zeros removed, is homeomorphic to an open cylinder. -/
noncomputable def poweredPhysicalZeroBandHomeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (t : ℝ) {phase : Circle} (hphase : (phase : ℂ).re = 0) :
    (↥(Ioo (0 : ℝ) 1) × Circle) ≃ₜ ↥(poweredPhysicalZeroBand p q t phase) := by
  let X := ↥(poweredSphereOpenPhaseBand p q phase)
  let Y := ↥(poweredPhysicalZeroBand p q t phase)
  let ray := batemanSliceHomeomorph t
  have hmem (s : ℝ × ℝ × ℝ) :
      batemanPairAt t s ∈ poweredSphereOpenPhaseBand p q phase ↔
        s ∈ poweredPhysicalZeroBand p q t phase := by
    rw [mem_poweredSphereOpenPhaseBand_iff_imag_sign hp hq hphase]
    have hs := complex_rational_pair_unit s.1 s.2.1 s.2.2 t
    exact ⟨fun h => ⟨h.1.2, h.2⟩, fun h => ⟨⟨hs, h.1⟩, h.2⟩⟩
  have hα (z : X) : z.val.1.re < 1 := by
    have h := z.property.2.1.2
    rw [Complex.normSq_apply] at h
    by_contra! hb
    nlinarith [mul_nonneg (sub_nonneg.mpr hb) (by linarith : 0 ≤ z.val.1.re + 1),
      sq_nonneg z.val.1.im]
  have hchartInverse (z : X) :
      batemanPairAt t (ray (initialCartesianPoint z.val)) = z.val := by
    change batemanPairAt t (batemanRay t (initialCartesianPoint z.val)) = _
    rw [batemanPairAt_batemanRay]
    apply initialBatemanPair_initialCartesianPoint
    · simpa only [Complex.normSq_eq_norm_sq] using z.property.1
    · exact hα z
  let f (z : X) : Y := ⟨ray (initialCartesianPoint z.val),
    (hmem _).1 (by rw [hchartInverse z]; exact z.property)⟩
  let g (s : Y) : X := ⟨batemanPairAt t s.val, (hmem s.val).2 s.property⟩
  have h₁ : Continuous (fun z : X => z.val.1) := continuous_fst.comp continuous_subtype_val
  have h₂ : Continuous (fun z : X => z.val.2) := continuous_snd.comp continuous_subtype_val
  have hd : Continuous (fun z : X => 1 - z.val.1.re) :=
    continuous_const.sub (Complex.continuous_re.comp h₁)
  have hden (z : X) : 1 - z.val.1.re ≠ 0 := (sub_pos.mpr (hα z)).ne'
  have hx := (Complex.continuous_re.comp h₂).div hd hden
  have hy := (Complex.continuous_im.comp h₂).neg.div hd hden
  have hz := (Complex.continuous_im.comp h₁).div hd hden
  have hchart : Continuous (fun z : X => initialCartesianPoint z.val) := hx.prodMk (hy.prodMk hz)
  have hargs : Continuous (fun s : ℝ × ℝ × ℝ => (s.1, s.2.1, s.2.2, t)) := by fun_prop
  have hpair : Continuous (batemanPairAt t) :=
    (contDiff_rationalAlpha.continuous.comp hargs).prodMk (contDiff_rationalBeta.continuous.comp hargs)
  let chart : X ≃ₜ Y :=
    { toFun := f
      invFun := g
      left_inv := fun z => Subtype.ext (hchartInverse z)
      right_inv := fun s => Subtype.ext (batemanRay_initialCartesianPoint_batemanPairAt t s.val)
      continuous_toFun := (ray.continuous.comp hchart).subtype_mk _
      continuous_invFun := (hpair.comp continuous_subtype_val).subtype_mk _ }
  exact (poweredSphereOpenPhaseBandHomeomorph hpq phase).trans chart

/-- The positive imaginary unit as a phase of the powered label. -/
def batemanImaginaryUnit : Circle :=
  ⟨Complex.I, by
    change dist Complex.I (0 : ℂ) = 1
    rw [dist_zero_right, Complex.norm_I]⟩

/-- Removing the common zero loci from the physical magnetic zero level
leaves exactly the positive and negative imaginary branches. -/
theorem poweredPhysicalRealZero_diff_eq_bands (p q : ℕ) (t : ℝ) :
    poweredPhysicalRealLevel p q t 0 \ poweredPhysicalImagLevel p q t 0 =
      poweredPhysicalZeroBand p q t batemanImaginaryUnit ∪
        poweredPhysicalZeroBand p q t (-batemanImaginaryUnit) := by
  ext x
  let g := batemanPoweredLabel p q t x
  change (g.re = 0 ∧ g.im ≠ 0) ↔
    (g.re = 0 ∧ 0 < Complex.I.im * g.im) ∨
      (g.re = 0 ∧ 0 < (-Complex.I).im * g.im)
  rw [Complex.neg_im, Complex.I_im, one_mul, neg_one_mul, neg_pos]
  constructor
  · rintro ⟨hRe, hIm⟩
    rcases lt_or_gt_of_ne hIm with h | h
    · exact Or.inr ⟨hRe, h⟩
    · exact Or.inl ⟨hRe, h⟩
  · rintro (⟨hRe, hIm⟩ | ⟨hRe, hIm⟩)
    · exact ⟨hRe, ne_of_gt hIm⟩
    · exact ⟨hRe, ne_of_lt hIm⟩

/-- The two signed physical bands are disjoint. -/
theorem disjoint_poweredPhysicalZeroBands (p q : ℕ) (t : ℝ) :
    Disjoint (poweredPhysicalZeroBand p q t batemanImaginaryUnit)
      (poweredPhysicalZeroBand p q t (-batemanImaginaryUnit)) := by
  apply Set.disjoint_left.2
  intro x hp hn
  have hp' : 0 < Complex.I.im * (batemanPoweredLabel p q t x).im := hp.2
  have hn' : 0 < (-Complex.I).im * (batemanPoweredLabel p q t x).im := hn.2
  rw [Complex.I_im, one_mul] at hp'
  rw [Complex.neg_im, Complex.I_im, neg_one_mul, neg_pos] at hn'
  exact lt_asymm hp' hn'

/-- A signed branch of the physical electric zero set on a time slice. -/
def poweredPhysicalElectricZeroBand (p q : ℕ) (t : ℝ) (phase : Circle) : Set (ℝ × ℝ × ℝ) :=
  {x | x ∈ poweredPhysicalImagLevel p q t 0 ∧
    0 < (phase : ℂ).im * (batemanPoweredLabel p q t x).re}

/-- The signed axial rotation carries each magnetic zero band to the
electric band with the same transverse sign. -/
theorem poweredPhysicalZeroBand_axial_iff {p q : ℕ} (hq : 0 < q) (t : ℝ)
    (phase : Circle) (s : ℝ × ℝ × ℝ) :
    s ∈ poweredPhysicalZeroBand p q t phase ↔
      batemanAxialRotation (Real.pi / (2 * (q : ℝ))) s ∈ poweredPhysicalElectricZeroBand p q t phase := by
  rcases s with ⟨x, y, z⟩
  let θ := Real.pi / (2 * (q : ℝ))
  have h := poweredProductLabel_axialRotation p q θ x y z t
  rw [batemanAxialPhase_special hq] at h
  let g := batemanPoweredLabel p q t (x, y, z)
  let g' := batemanPoweredLabel p q t (batemanAxialRotation θ (x, y, z))
  change g' = -Complex.I * g at h
  change (g.re = 0 ∧ 0 < (phase : ℂ).im * g.im) ↔
    (g'.im = 0 ∧ 0 < (phase : ℂ).im * g'.re)
  rw [h]
  simp [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im]

/-- Each signed branch of the physical electric zero level is a cylinder. -/
noncomputable def poweredPhysicalElectricZeroBandHomeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (t : ℝ) {phase : Circle} (hphase : (phase : ℂ).re = 0) :
    (↥(Ioo (0 : ℝ) 1) × Circle) ≃ₜ ↥(poweredPhysicalElectricZeroBand p q t phase) :=
  (poweredPhysicalZeroBandHomeomorph hp hq hpq t hphase).trans
    ((batemanAxialHomeomorph (Real.pi / (2 * (q : ℝ)))).subtype
      (poweredPhysicalZeroBand_axial_iff hq t phase))

/-- The electric zero level outside the common zero set is the union of its
positive and negative real branches. -/
theorem poweredPhysicalImagZero_diff_eq_bands (p q : ℕ) (t : ℝ) :
    poweredPhysicalImagLevel p q t 0 \ poweredPhysicalRealLevel p q t 0 =
      poweredPhysicalElectricZeroBand p q t batemanImaginaryUnit ∪
        poweredPhysicalElectricZeroBand p q t (-batemanImaginaryUnit) := by
  ext x
  let g := batemanPoweredLabel p q t x
  change (g.im = 0 ∧ g.re ≠ 0) ↔
    (g.im = 0 ∧ 0 < Complex.I.im * g.re) ∨
      (g.im = 0 ∧ 0 < (-Complex.I).im * g.re)
  rw [Complex.neg_im, Complex.I_im, one_mul, neg_one_mul, neg_pos]
  constructor
  · rintro ⟨hIm, hRe⟩
    rcases lt_or_gt_of_ne hRe with h | h
    · exact Or.inr ⟨hIm, h⟩
    · exact Or.inl ⟨hIm, h⟩
  · rintro (⟨hIm, hRe⟩ | ⟨hIm, hRe⟩)
    · exact ⟨hIm, ne_of_gt hRe⟩
    · exact ⟨hIm, ne_of_lt hRe⟩

end Qatlib.Papers.KnotLight13.TorusFamily
