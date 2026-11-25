/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PoweredCoreCircle
public import Qatlib.Papers.KnotLight13.TorusFamily.PowerIntegralCurves

/-!
# Physical extremal field-line cores on every time slice

[Kedia2013TyingKnots], Fig. 2. Each of the four signed extremal
projected labels has its own phase fiber. The stereographic chart
and ray diffeomorphism give an embedded circle on every physical
slice for coprime positive powers. The first-integral theorems show
that a path tangent to the corresponding physical field remains on
that extremal circle if it starts there.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set
open Qatlib.Papers.KnotLight13.TorusFamily (rationalAlpha rationalBeta complex_rational_pair_unit)

local notation "SpatialCorePoint" => ℝ × ℝ × ℝ

/-- The physical points with the given extremal product-label phase. -/
def poweredPhysicalCore (p q : ℕ) (t : ℝ) (phase : Circle) : Set SpatialCorePoint :=
  {s | batemanPoweredLabel p q t s = (poweredPeakAmplitude p q : ℂ) * (phase : ℂ)}

/-- The chart misses its pole on the entire extremal torus. -/
theorem poweredSphereCore_re_lt_one {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    {phase : Circle} {z : ℂ × ℂ} (h : z ∈ poweredSphereCore p q phase) : z.1.re < 1 := by
  have ha : (poweredCoreRadii p q).1 < 1 := by
    obtain ⟨ha, _, hs, _⟩ := poweredCoreRadii_spec hp hq
    have hr := (poweredPeakRadius_mem hp hq).2
    by_contra! hh
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (add_nonneg ha.le zero_le_one)]
  exact (Complex.re_le_norm z.1).trans_lt ((poweredSphereCore_norms hp hq h).1.symm ▸ ha)

/-- The initial chart pulls back each core phase exactly, at every later time. -/
private theorem batemanPairAt_core_chart {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {phase : Circle} {z : ℂ × ℂ} (h : z ∈ poweredSphereCore p q phase) :
    batemanPairAt t (batemanRay t (initialCartesianPoint z)) = z := by
  rw [batemanPairAt_batemanRay]
  apply initialBatemanPair_initialCartesianPoint
  · simpa only [Complex.normSq_eq_norm_sq] using h.1
  · exact poweredSphereCore_re_lt_one hp hq h

/-- The explicit product-torus circle mapped into the physical slice. -/
noncomputable def poweredPhysicalCoreParam (p q : ℕ) (t : ℝ) (phase : Circle) (w : Circle) :
    SpatialCorePoint :=
  batemanRay t (initialCartesianPoint (poweredCoreSphereParam p q phase w))

/-- The signed extremal core in physical space is the complete injectively
parametrized torus circle, with no part lost at stereographic infinity. -/
theorem poweredPhysicalCoreParam_bijective {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (t : ℝ) (phase : Circle) :
    Function.Injective (poweredPhysicalCoreParam p q t phase) ∧
      Set.range (poweredPhysicalCoreParam p q t phase) = poweredPhysicalCore p q t phase := by
  have hparam := poweredCoreSphereParam_bijective hp hq hpq phase
  have hmem w := poweredCoreSphereParam_mem hp hq hpq phase w
  have hrecover (w : Circle) :
      batemanPairAt t (poweredPhysicalCoreParam p q t phase w) =
        poweredCoreSphereParam p q phase w := batemanPairAt_core_chart hp hq t (hmem w)
  constructor
  · intro u v h
    apply hparam.1
    simpa only [hrecover] using congrArg (batemanPairAt t) h
  · ext s
    constructor
    · rintro ⟨w, rfl⟩
      change (batemanPairAt t (poweredPhysicalCoreParam p q t phase w)).1 ^ p *
        (batemanPairAt t (poweredPhysicalCoreParam p q t phase w)).2 ^ q = _
      rw [hrecover]
      exact (hmem w).2
    · intro hs
      have hm : batemanPairAt t s ∈ poweredSphereCore p q phase := by
        exact ⟨complex_rational_pair_unit s.1 s.2.1 s.2.2 t, hs⟩
      rw [← hparam.2] at hm
      obtain ⟨w, hw⟩ := hm
      refine ⟨w, (batemanPairAt_injective t) ?_⟩
      exact (hrecover w).trans hw

/-- The physical core is a topologically embedded circle, with the
subspace topology inherited from ordinary three-space. -/
noncomputable def poweredPhysicalCoreHomeomorph {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (t : ℝ) (phase : Circle) :
    Circle ≃ₜ ↥(poweredPhysicalCore p q t phase) := by
  obtain ⟨hinj, hrange⟩ := poweredPhysicalCoreParam_bijective hp hq hpq t phase
  have hcont := continuous_poweredCoreSphereParam p q phase
  have hd : Continuous (fun w : Circle => 1 - (poweredCoreSphereParam p q phase w).1.re) :=
    continuous_const.sub (Complex.continuous_re.comp hcont.fst)
  have hne (w : Circle) : 1 - (poweredCoreSphereParam p q phase w).1.re ≠ 0 :=
    (sub_pos.mpr (poweredSphereCore_re_lt_one hp hq (poweredCoreSphereParam_mem hp hq hpq phase w))).ne'
  have hx := (Complex.continuous_re.comp hcont.snd).div hd hne
  have hy := (Complex.continuous_im.comp hcont.snd).neg.div hd hne
  have hz := (Complex.continuous_im.comp hcont.fst).div hd hne
  have hchart : Continuous (initialCartesianPoint ∘ poweredCoreSphereParam p q phase) :=
    hx.prodMk (hy.prodMk hz)
  have hc : Continuous (poweredPhysicalCoreParam p q t phase) :=
    (batemanSliceHomeomorph t).continuous.comp hchart
  let f : Circle → ↥(poweredPhysicalCore p q t phase) := fun w =>
    ⟨poweredPhysicalCoreParam p q t phase w, hrange ▸ mem_range_self w⟩
  refine Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective f ⟨fun _ _ he => hinj (congrArg Subtype.val he), ?_⟩)
    (hc.subtype_mk _)
  intro s
  have hs : s.val ∈ Set.range (poweredPhysicalCoreParam p q t phase) := by
    rw [hrange]
    exact s.property
  obtain ⟨w, hw⟩ := hs
  exact ⟨w, Subtype.ext hw⟩

/-- A real unit phase gives exactly the associated signed extremal
magnetic label level. -/
theorem mem_poweredPhysicalCore_iff_real {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {phase : Circle} (hphase : (phase : ℂ).im = 0) (s : SpatialCorePoint) :
    s ∈ poweredPhysicalCore p q t phase ↔
      (batemanPoweredLabel p q t s).re = poweredPeakAmplitude p q * (phase : ℂ).re := by
  let g := batemanPoweredLabel p q t s
  have hr : |(phase : ℂ).re| = 1 := by
    have hn := Circle.normSq_coe phase
    rw [Complex.normSq_apply, hphase] at hn
    exact (pow_left_inj₀ (abs_nonneg _) zero_le_one (by decide : (2 : ℕ) ≠ 0)).1 (by
      rw [sq_abs, one_pow]; nlinarith)
  change g = _ ↔ g.re = _
  constructor
  · intro h
    rw [h, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  · intro h
    have habs : |g.re| = poweredPeakAmplitude p q := by
      rw [h, abs_mul, abs_of_pos (poweredPeakAmplitude_pos hp hq), hr, mul_one]
    have him : g.im = 0 :=
      (poweredProductLabel_real_extreme hp hq s.1 s.2.1 s.2.2 t habs).1
    apply Complex.ext
    · simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using h
    · simp only [him, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hphase,
        mul_zero, zero_mul, add_zero]

/-- A purely imaginary unit phase gives exactly the associated signed
extremal electric label level. -/
theorem mem_poweredPhysicalCore_iff_imaginary {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {phase : Circle} (hphase : (phase : ℂ).re = 0) (s : SpatialCorePoint) :
    s ∈ poweredPhysicalCore p q t phase ↔
      (batemanPoweredLabel p q t s).im = poweredPeakAmplitude p q * (phase : ℂ).im := by
  let g := batemanPoweredLabel p q t s
  have hi : |(phase : ℂ).im| = 1 := by
    have hn := Circle.normSq_coe phase
    rw [Complex.normSq_apply, hphase] at hn
    exact (pow_left_inj₀ (abs_nonneg _) zero_le_one (by decide : (2 : ℕ) ≠ 0)).1 (by
      rw [sq_abs, one_pow]; nlinarith)
  change g = _ ↔ g.im = _
  constructor
  · intro h
    rw [h, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  · intro h
    have habs : |g.im| = poweredPeakAmplitude p q := by
      rw [h, abs_mul, abs_of_pos (poweredPeakAmplitude_pos hp hq), hi, mul_one]
    have hre : g.re = 0 :=
      (poweredProductLabel_imaginary_extreme hp hq s.1 s.2.1 s.2.2 t habs).1
    apply Complex.ext
    · simp only [hre, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hphase,
        mul_zero, zero_mul, sub_zero]
    · simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero] using h

/-- The ray homeomorphism sends the whole initial physical core onto the
same phase core at time `t`. -/
theorem batemanSliceHomeomorph_image_poweredPhysicalCore (p q : ℕ) (t : ℝ) (phase : Circle) :
    batemanSliceHomeomorph t '' poweredPhysicalCore p q 0 phase = poweredPhysicalCore p q t phase := by
  ext s
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (poweredProductLabel_batemanRay p q t x).trans hx
  · intro hs
    let x := (batemanSliceHomeomorph t).symm s
    have hx : batemanRay t x = s := (batemanSliceHomeomorph t).apply_symm_apply s
    refine ⟨x, ?_, hx⟩
    have h := poweredProductLabel_batemanRay p q t x
    change (batemanPoweredLabel p q t (batemanRay t x)) = batemanPoweredLabel p q 0 x at h
    rw [hx] at h
    exact h.symm.trans hs

/-- The physical fields do not vanish anywhere on an extremal core. -/
theorem fields_nonzero_on_poweredPhysicalCore {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {phase : Circle} {s : SpatialCorePoint} (h : s ∈ poweredPhysicalCore p q t phase) :
    (fun j => (rationalPowerField p q s.1 s.2.1 s.2.2 t j).re) ≠ 0 ∧
      (fun j => (rationalPowerField p q s.1 s.2.1 s.2.2 t j).im) ≠ 0 := by
  apply powered_fields_nonzero_of_label_ne_zero hp hq
  change batemanPoweredLabel p q t s ≠ 0
  change batemanPoweredLabel p q t s = _ at h
  rw [h]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (poweredPeakAmplitude_pos hp hq).ne')
    (Circle.coe_ne_zero phase)

/-- An actual magnetic line segment starting on a signed magnetic core
stays on that core for the entire parameter interval. -/
theorem magnetic_line_mapsTo_poweredPhysicalCore {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {phase : Circle} (hphase : (phase : ℂ).im = 0) {a b : ℝ} (hab : a < b)
    {curve : ℝ → SpatialCorePoint} (speed : ℝ → ℝ)
    (hcurve : ∀ s ∈ Icc a b, HasDerivWithinAt curve
      (speed s • batemanCartesianCoordinates.symm (fun j =>
        (rationalPowerField p q (curve s).1 (curve s).2.1 (curve s).2.2 t j).im))
      (Icc a b) s) (ha : curve a ∈ poweredPhysicalCore p q t phase) :
    MapsTo curve (Icc a b) (poweredPhysicalCore p q t phase) := by
  intro s hs
  apply (mem_poweredPhysicalCore_iff_real hp hq t hphase (curve s)).2
  exact (magnetic_line_preserves_label p q t hab speed hcurve hs).trans
    ((mem_poweredPhysicalCore_iff_real hp hq t hphase (curve a)).1 ha)

/-- An actual electric line segment starting on a signed electric core
stays on that core for the entire parameter interval. -/
theorem electric_line_mapsTo_poweredPhysicalCore {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (t : ℝ) {phase : Circle} (hphase : (phase : ℂ).re = 0) {a b : ℝ} (hab : a < b)
    {curve : ℝ → SpatialCorePoint} (speed : ℝ → ℝ)
    (hcurve : ∀ s ∈ Icc a b, HasDerivWithinAt curve
      (speed s • batemanCartesianCoordinates.symm (fun j =>
        (rationalPowerField p q (curve s).1 (curve s).2.1 (curve s).2.2 t j).re))
      (Icc a b) s) (ha : curve a ∈ poweredPhysicalCore p q t phase) :
    MapsTo curve (Icc a b) (poweredPhysicalCore p q t phase) := by
  intro s hs
  apply (mem_poweredPhysicalCore_iff_imaginary hp hq t hphase (curve s)).2
  exact (electric_line_preserves_label p q t hab speed hcurve hs).trans
    ((mem_poweredPhysicalCore_iff_imaginary hp hq t hphase (curve a)).1 ha)

end Qatlib.Papers.KnotLight13.TorusFamily
