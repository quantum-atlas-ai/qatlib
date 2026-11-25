/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanFiberReturn
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanOrbitClock
public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPhysicalTori

import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Periodic and dense field lines on the physical Bateman tori

[Kedia2013TyingKnots], discussion of Fig. 2.
The Bateman chart pushes the physical magnetic field to the normalized
sphere field times a positive speed. Compactness of an intermediate
torus makes the corresponding time change global. Periodic or dense
sphere trajectories then give the same alternatives in physical space.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

local notation "PhysicalSpace" => ℝ × ℝ × ℝ
open Set Topology
open Qatlib.Papers.KnotLight13.TorusFamily (complex_rational_pair_unit)

/-- The positive multiplier taking the physical fields to the sphere
fields, on any fixed physical slice. -/
noncomputable def batemanPhysicalSphereScale (t : ℝ) (x : PhysicalSpace) : ℝ :=
  let s := (batemanSliceHomeomorph t).symm x
  batemanStereoScale s ^ 3 / LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap

/-- The multiplier is strictly positive at every physical point. -/
theorem batemanPhysicalSphereScale_pos (t : ℝ) (x : PhysicalSpace) :
    0 < batemanPhysicalSphereScale t x :=
  div_pos (pow_pos (batemanStereoScale_pos _) _) (det_bateman_ray_pos t _)

/-- The physical sphere multiplier is continuous in space. -/
theorem continuous_batemanPhysicalSphereScale (t : ℝ) :
    Continuous (batemanPhysicalSphereScale t) := by
  have hs : Continuous batemanStereoScale := by
    unfold batemanStereoScale
    exact continuous_const.div
      ((((continuous_fst.pow 2).add ((continuous_fst.comp continuous_snd).pow 2)).add
        ((continuous_snd.comp continuous_snd).pow 2)).add_const 1) (fun _ => by positivity)
  have hc := (hs.pow 3).div (continuous_batemanRayJacobian t)
    (fun x => (det_bateman_ray_pos t x).ne')
  exact hc.comp (batemanSliceHomeomorph t).symm.continuous

/-- The Bateman pair on a fixed physical slice is smooth. -/
private theorem contDiff_batemanPairSlice (t : ℝ) : ContDiff ℝ ⊤ (batemanPairAt t) := by
  simpa only [batemanAlphaPower, batemanBetaPower, pow_one, Prod.mk.eta] using
    (contDiff_batemanAlphaPower 1 t).prodMk (contDiff_batemanBetaPower 1 t)

/-- The magnetic chart differential formula at an arbitrary physical point. -/
theorem fderiv_batemanPairAt_magnetic (p q : ℕ) (t : ℝ) (x : PhysicalSpace) :
    fderiv ℝ (batemanPairAt t) x (batemanMagneticVector p q t x) =
      batemanPhysicalSphereScale t x • batemanSphereMagnetic p q (batemanPairAt t x) := by
  let s := (batemanSliceHomeomorph t).symm x
  have hs : batemanRay t s = x := (batemanSliceHomeomorph t).apply_symm_apply x
  have h := (fderiv_batemanPairAt_transported_fields p q t s).2
  rw [hs] at h
  exact h

/-- A complete magnetic trajectory stays on the real level of its initial point. -/
theorem batemanMagneticIntegralCurve_level (p q : ℕ) (t : ℝ) {γ : ℝ → PhysicalSpace}
    (hγ : IsIntegralCurve γ (fun _ => batemanMagneticVector p q t))
    {c : ℝ} (h₀ : γ 0 ∈ poweredPhysicalRealLevel p q t c) (s : ℝ) :
    γ s ∈ poweredPhysicalRealLevel p q t c := by
  change (batemanPoweredLabel p q t (γ 0)).re = c at h₀
  change (batemanPoweredLabel p q t (γ s)).re = c
  have hder {a b : ℝ} (u : ℝ) :
      HasDerivWithinAt γ ((1 : ℝ) • batemanCartesianCoordinates.symm (fun j =>
        (rationalPowerField p q (γ u).1 (γ u).2.1 (γ u).2.2 t j).im)) (Icc a b) u := by
    simpa only [one_smul, batemanMagneticVector] using (hγ u).hasDerivWithinAt (s := Icc a b)
  rcases lt_trichotomy s 0 with hs | hs | hs
  · have h := magnetic_line_preserves_label p q t hs (fun _ => 1) (fun u _ => hder u)
      (show (0 : ℝ) ∈ Icc s 0 from ⟨hs.le, le_rfl⟩)
    exact h.symm.trans h₀
  · rwa [hs]
  · have h := magnetic_line_preserves_label p q t hs (fun _ => 1) (fun u _ => hder u)
      (show s ∈ Icc 0 s from ⟨hs.le, le_rfl⟩)
    exact h.trans h₀

/-- A continuous positive spatial speed has a uniform positive lower
bound on a strict intermediate physical torus. -/
private theorem positive_lower_on_physicalTorus {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (t : ℝ) {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {F : PhysicalSpace → ℝ} (hF : Continuous F) (hpos : ∀ x, 0 < F x) :
    ∃ m : ℝ, 0 < m ∧ ∀ x ∈ poweredPhysicalRealLevel p q t c, m ≤ F x := by
  let e := poweredPhysicalRealLevelHomeomorph hp hq hpq t h₀ hc
  let f := fun w : Circle × Circle => (e w).val
  have hf : Continuous f := continuous_subtype_val.comp e.continuous
  have hrange : range f = poweredPhysicalRealLevel p q t c := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (e w).property
    · intro hx
      exact ⟨e.symm ⟨x, hx⟩, congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)⟩
  have hK : IsCompact (poweredPhysicalRealLevel p q t c) := hrange ▸ isCompact_range hf
  have hne : (poweredPhysicalRealLevel p q t c).Nonempty := hrange ▸ range_nonempty f
  obtain ⟨x, _, hx⟩ := hK.exists_isMinOn hne hF.continuousOn
  exact ⟨_, hpos x, hx⟩

/-- A strictly positive global clock sends a physical magnetic trajectory
to a full normalized magnetic trajectory in the sphere chart. The inverse
clock's derivative is a positive function of the physical point. -/
theorem batemanMagneticIntegralCurve_normalized {p q : ℕ} (hp : 0 < p) (hq : 0 < q)
    (hpq : Nat.Coprime p q) (t : ℝ) {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {γ : ℝ → PhysicalSpace} (hγ : IsIntegralCurve γ (fun _ => batemanMagneticVector p q t))
    (hlevel : γ 0 ∈ poweredPhysicalRealLevel p q t c) :
    ∃ e : ℝ ≃o ℝ,
      let w := batemanPairAt t ∘ γ ∘ e.symm
      IsIntegralCurve w (fun _ => batemanSphereMagnetic p q) ∧
        (∀ u, w u ∈ poweredSphereRealLevel p q c) ∧ e.symm 0 = 0 ∧
        (∀ u, HasDerivAt (e.symm : ℝ → ℝ)
          (batemanPhysicalSphereScale t (γ (e.symm u)))⁻¹ u) := by
  let v := batemanPhysicalSphereScale t ∘ γ
  have hLv := batemanMagneticIntegralCurve_level p q t hγ hlevel
  have hv : Continuous v := (continuous_batemanPhysicalSphereScale t).comp hγ.continuous
  obtain ⟨m, hm, hbound⟩ := positive_lower_on_physicalTorus hp hq hpq t h₀ hc
    (continuous_batemanPhysicalSphereScale t) (batemanPhysicalSphereScale_pos t)
  have hb (s : ℝ) : m ≤ v s := hbound (γ s) (hLv s)
  let e := orbitClockOrderIso v hv hm hb
  let w := batemanPairAt t ∘ γ ∘ e.symm
  have hD (u : ℝ) : HasDerivAt (e.symm : ℝ → ℝ) (v (e.symm u))⁻¹ u :=
    hasDerivAt_orbitClockOrderIso_symm v hv hm hb u
  have hzero : e 0 = 0 := intervalIntegral.integral_same
  have hszero : e.symm 0 = 0 := e.injective (by rw [e.apply_symm_apply, hzero])
  refine ⟨e, ?_, ?_, hszero, hD⟩
  · intro u
    let x := γ (e.symm u)
    have hg : HasDerivAt (γ ∘ e.symm) ((v (e.symm u))⁻¹ • batemanMagneticVector p q t x) u :=
      (hγ (e.symm u)).scomp u (hD u)
    have hF := ((contDiff_batemanPairSlice t).differentiable (by simp) x).hasFDerivAt
    have h := hF.comp_hasDerivAt u hg
    change HasDerivAt w (fderiv ℝ (batemanPairAt t) x
      ((v (e.symm u))⁻¹ • batemanMagneticVector p q t x)) u at h
    rw [map_smul, fderiv_batemanPairAt_magnetic, smul_smul] at h
    change HasDerivAt w (((batemanPhysicalSphereScale t x)⁻¹ * batemanPhysicalSphereScale t x) •
      batemanSphereMagnetic p q (w u)) u at h
    rwa [inv_mul_cancel₀ (batemanPhysicalSphereScale_pos t x).ne', one_smul] at h
  · intro u
    let x := γ (e.symm u)
    exact ⟨complex_rational_pair_unit x.1 x.2.1 x.2.2 t, hLv (e.symm u)⟩
/-- A periodic path after a strictly increasing time change has a positive
period before the change when the clock rate depends on the path point. -/
private theorem periodic_of_orbitClock {X : Type*} {γ : ℝ → X} {v : X → ℝ}
    (e : ℝ ≃o ℝ) (hzero : e.symm 0 = 0)
    (hd : ∀ u, HasDerivAt (e.symm : ℝ → ℝ) (v (γ (e.symm u))) u)
    {T : ℝ} (hT : 0 < T) (hper : Function.Periodic (γ ∘ e.symm) T) :
    0 < e.symm T ∧ Function.Periodic γ (e.symm T) := by
  have hstep (u : ℝ) : e.symm (u + T) = e.symm u + e.symm T := by
    have h := orbitClock_increment_of_periodic hd (hper.comp v) u
    rw [hzero, sub_zero] at h
    linarith
  refine ⟨by simpa only [hzero] using e.symm.strictMono hT, ?_⟩
  intro s
  have h := hper (e s)
  change γ (e.symm (e s + T)) = γ (e.symm (e s)) at h
  rwa [hstep, e.symm_apply_apply] at h

/-- A full physical magnetic field line on a coprime strict intermediate
torus is periodic or has dense image in the entire torus. -/
theorem batemanMagneticIntegralCurve_periodic_or_dense
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (t : ℝ) {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {γ : ℝ → PhysicalSpace} (hγ : IsIntegralCurve γ (fun _ => batemanMagneticVector p q t))
    (hlevel : γ 0 ∈ poweredPhysicalRealLevel p q t c) :
    (∃ T : ℝ, 0 < T ∧ Function.Periodic γ T) ∨
      closure (range γ) = poweredPhysicalRealLevel p q t c := by
  obtain ⟨e, hw, hlevelw, hzero, hd⟩ :=
    batemanMagneticIntegralCurve_normalized hp hq hpq t h₀ hc hγ hlevel
  let E := poweredSphereRealLevelToPhysical (p := p) hq t h₀
  have hl := batemanMagneticIntegralCurve_level p q t hγ hlevel
  let g := fun u => (⟨γ (e.symm u), hl (e.symm u)⟩ : ↥(poweredPhysicalRealLevel p q t c))
  let Z := E.symm ∘ g
  rcases batemanSphereMagnetic_periodic_or_dense hp hq hpq h₀ hc hw hlevelw with
    ⟨T, hT, hperiod⟩ | hdense
  · have hg : Function.Periodic g T := by
      intro u
      apply E.symm.injective
      apply Subtype.ext
      exact hperiod u
    have hγp : Function.Periodic (γ ∘ e.symm) T := hg.comp Subtype.val
    exact Or.inl ⟨e.symm T, periodic_of_orbitClock (v := fun x => (batemanPhysicalSphereScale t x)⁻¹) e hzero hd hT hγp⟩
  · right
    have hClosed : IsClosed (poweredPhysicalRealLevel p q t c) :=
      isClosed_eq (Complex.continuous_re.comp (contDiff_batemanPoweredLabel p q t).continuous)
        continuous_const
    refine Subset.antisymm (closure_minimal (range_subset_iff.mpr hl) hClosed) ?_
    have hZimage : (Subtype.val : ↥(poweredSphereRealLevel p q c) → ℂ × ℂ) '' range Z =
        range (batemanPairAt t ∘ γ ∘ e.symm) := by
      rw [← range_comp]
      rfl
    have hZdense : DenseRange Z := by
      intro z
      rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, hZimage, hdense]
      exact z.property
    have hg : E ∘ Z = g := funext fun u => E.apply_symm_apply (g u)
    have hgdense : DenseRange g :=
      hg ▸ E.surjective.denseRange.comp hZdense E.continuous
    have hgrange : (Subtype.val : ↥(poweredPhysicalRealLevel p q t c) → PhysicalSpace) '' range g = range γ := by
      rw [← range_comp]
      change range (γ ∘ e.symm) = range γ
      rw [range_comp, range_eq_univ.mpr e.symm.surjective, image_univ]
    intro x hx
    have h := mem_closure_image continuous_subtype_val.continuousAt (hgdense ⟨x, hx⟩)
    rwa [hgrange] at h

/-- A fixed axial rotation rotates a differentiable curve's velocity
by the same angle. -/
theorem hasDerivAt_batemanAxialRotation_curve (θ : ℝ) {γ : ℝ → PhysicalSpace} {s : ℝ}
    {v : PhysicalSpace} (h : HasDerivAt γ v s) :
    HasDerivAt (batemanAxialRotation θ ∘ γ) (batemanAxialRotation θ v) s := by
  have h₁ : HasDerivAt (fun u => (γ u).1) v.1 s := h.fst
  have hs : HasDerivAt (fun u => (γ u).2) v.2 s := h.snd
  have h₂ : HasDerivAt (fun u => (γ u).2.1) v.2.1 s := hs.fst
  have h₃ : HasDerivAt (fun u => (γ u).2.2) v.2.2 s := hs.snd
  exact HasDerivAt.prodMk
    ((h₁.const_mul (Real.cos θ)).fun_sub (h₂.const_mul (Real.sin θ)))
    (HasDerivAt.prodMk ((h₁.const_mul (Real.sin θ)).fun_add (h₂.const_mul (Real.cos θ))) h₃)

open scoped Real in
/-- The signed duality rotation takes a magnetic velocity to the electric
velocity at the rotated point. -/
theorem batemanAxialRotation_magnetic_to_electric (p : ℕ) {q : ℕ}
    (hq : 0 < q) (t : ℝ) (x : PhysicalSpace) :
    let θ := π / (2 * (q : ℝ))
    batemanAxialRotation θ (batemanMagneticVector p q t x) =
      batemanElectricVector p q t (batemanAxialRotation θ x) := by
  rcases x with ⟨x, y, z⟩
  exact (congrArg batemanCartesianCoordinates.symm
    (rationalPowerField_axialDuality p hq x y z t).1).symm

open scoped Real in
/-- A full physical electric field line on a coprime strict intermediate
torus is periodic or has dense image in the entire torus. -/
theorem batemanElectricIntegralCurve_periodic_or_dense
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (t : ℝ) {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {γ : ℝ → PhysicalSpace} (hγ : IsIntegralCurve γ (fun _ => batemanElectricVector p q t))
    (hlevel : γ 0 ∈ poweredPhysicalImagLevel p q t c) :
    (∃ T : ℝ, 0 < T ∧ Function.Periodic γ T) ∨
      closure (range γ) = poweredPhysicalImagLevel p q t c := by
  let θ := π / (2 * (q : ℝ))
  let R := batemanAxialHomeomorph θ
  let g := R.symm ∘ γ
  have hg : IsIntegralCurve g (fun _ => batemanMagneticVector p q t) := by
    intro s
    have h := hasDerivAt_batemanAxialRotation_curve (-θ) (hγ s)
    have hv : R (batemanMagneticVector p q t (g s)) = batemanElectricVector p q t (γ s) := by
      have hv₀ := batemanAxialRotation_magnetic_to_electric p hq t (g s)
      change R (batemanMagneticVector p q t (g s)) = batemanElectricVector p q t (R (R.symm (γ s))) at hv₀
      rwa [R.apply_symm_apply] at hv₀
    change HasDerivAt g (R.symm (batemanElectricVector p q t (γ s))) s at h
    rwa [← hv, R.symm_apply_apply] at h
  have hg₀ : g 0 ∈ poweredPhysicalRealLevel p q t (-c) := by
    apply (poweredPhysicalLevel_axial_iff hq t c (g 0)).2
    change R (R.symm (γ 0)) ∈ poweredPhysicalImagLevel p q t c
    rwa [R.apply_symm_apply]
  have he : γ = R ∘ g := funext fun s => (R.apply_symm_apply (γ s)).symm
  rcases batemanMagneticIntegralCurve_periodic_or_dense hp hq hpq t
    (neg_ne_zero.mpr h₀) (by rwa [abs_neg]) hg hg₀ with ⟨T, hT, hpers⟩ | hdense
  · rw [he]
    exact Or.inl ⟨T, hT, fun s => congrArg R (hpers s)⟩
  · right
    rw [he, range_comp, ← R.image_closure, hdense]
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (poweredPhysicalLevel_axial_iff hq t c y).1 hy
    · intro hx
      refine ⟨R.symm x, (poweredPhysicalLevel_axial_iff hq t c (R.symm x)).2 ?_,
        R.apply_symm_apply x⟩
      change R (R.symm x) ∈ poweredPhysicalImagLevel p q t c
      rwa [R.apply_symm_apply]

/-- The spatial chart from the Bateman sphere is differentiable away
from its stereographic pole. -/
private theorem differentiableAt_batemanSphereToPhysical (t : ℝ) (z : ℂ × ℂ)
    (hz : z.1.re < 1) :
    DifferentiableAt ℝ (batemanRay t ∘ initialCartesianPoint) z := by
  have hpair : DifferentiableAt ℝ initialCartesianPoint z := by
    unfold initialCartesianPoint
    have hd : 1 - z.1.re ≠ 0 := (sub_pos.mpr hz).ne'
    fun_prop (disch := exact hd)
  exact ((contDiff_bateman_ray t).differentiable (by simp) _).comp z hpair

/-- The Bateman chart differential is injective because the spatial chart
from the sphere gives a differentiable left inverse. -/
private theorem injective_fderiv_batemanPairAt (t : ℝ) (x : PhysicalSpace) :
    Function.Injective (fderiv ℝ (batemanPairAt t) x) := by
  let F := batemanPairAt t
  let S := batemanRay t ∘ initialCartesianPoint
  have ht : (F x).1.re < 1 := rationalAlpha_re_lt_one _ _ _ _
  have hF := ((contDiff_batemanPairSlice t).differentiable (by simp) x).hasFDerivAt
  have hS := (differentiableAt_batemanSphereToPhysical t (F x) ht).hasFDerivAt
  have h := hS.comp x hF
  change HasFDerivAt (fun y => batemanRay t (initialCartesianPoint (batemanPairAt t y)))
    ((fderiv ℝ S (F x)).comp (fderiv ℝ F x)) x at h
  simp only [batemanRay_initialCartesianPoint_batemanPairAt] at h
  have he := h.unique (hasFDerivAt_id x)
  intro u v huv
  have hh := congrArg (fderiv ℝ S (F x)) huv
  change (((fderiv ℝ S (F x)).comp (fderiv ℝ F x)) u) =
    (((fderiv ℝ S (F x)).comp (fderiv ℝ F x)) v) at hh
  rw [he] at hh
  exact hh

/-- The inverse chart and a global positive change of time realize a
complete sphere orbit as a complete physical magnetic orbit. -/
theorem batemanSphereMagneticIntegralCurve_physical
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : Nat.Coprime p q)
    (t : ℝ) {c : ℝ} (h₀ : c ≠ 0) (hc : |c| < poweredPeakAmplitude p q)
    {w : ℝ → ℂ × ℂ} (hw : IsIntegralCurve w (fun _ => batemanSphereMagnetic p q))
    (hlevel : ∀ u, w u ∈ poweredSphereRealLevel p q c) :
    ∃ e : ℝ ≃o ℝ,
      let γ := batemanRay t ∘ initialCartesianPoint ∘ w ∘ e.symm
      IsIntegralCurve γ (fun _ => batemanMagneticVector p q t) ∧
        γ 0 = batemanRay t (initialCartesianPoint (w 0)) ∧
        ∀ u, γ u ∈ poweredPhysicalRealLevel p q t c := by
  let S := batemanRay t ∘ initialCartesianPoint
  let E := poweredSphereRealLevelToPhysical (p := p) hq t h₀
  let g := S ∘ w
  let scale := batemanPhysicalSphereScale t
  have hg (u : ℝ) : g u ∈ poweredPhysicalRealLevel p q t c :=
    (E ⟨w u, hlevel u⟩).property
  have hPair (u : ℝ) : batemanPairAt t (g u) = w u :=
    congrArg Subtype.val (E.symm_apply_apply ⟨w u, hlevel u⟩)
  have hS (u : ℝ) : DifferentiableAt ℝ S (w u) :=
    differentiableAt_batemanSphereToPhysical t (w u) (poweredSphereRealLevel_re_lt_one hq h₀ (hlevel u))
  have hdg (u : ℝ) : HasDerivAt g ((scale (g u))⁻¹ • batemanMagneticVector p q t (g u)) u := by
    have h := ((hS u).hasFDerivAt.comp_hasDerivAt u (hw u))
    have hF := ((contDiff_batemanPairSlice t).differentiable (by simp) (g u)).hasFDerivAt
    have hcomp := hF.comp_hasDerivAt u h
    change HasDerivAt (fun s => batemanPairAt t (g s)) _ u at hcomp
    simp only [hPair] at hcomp
    have hh := hcomp.unique (hw u)
    refine h.congr_deriv (injective_fderiv_batemanPairAt t (g u) ?_)
    change fderiv ℝ (batemanPairAt t) (g u)
      (fderiv ℝ S (w u) (batemanSphereMagnetic p q (w u))) =
      fderiv ℝ (batemanPairAt t) (g u) ((scale (g u))⁻¹ • batemanMagneticVector p q t (g u))
    rw [hh, map_smul, fderiv_batemanPairAt_magnetic, smul_smul]
    change batemanSphereMagnetic p q (w u) =
      ((scale (g u))⁻¹ * scale (g u)) • batemanSphereMagnetic p q (batemanPairAt t (g u))
    rw [hPair, inv_mul_cancel₀ (batemanPhysicalSphereScale_pos t (g u)).ne', one_smul]
  have hcg : Continuous g := (show Differentiable ℝ g from fun u => (hdg u).differentiableAt).continuous
  have hv : Continuous (fun x => (scale x)⁻¹) :=
    (continuous_batemanPhysicalSphereScale t).inv₀ (fun x => (batemanPhysicalSphereScale_pos t x).ne')
  have hpv (x : PhysicalSpace) : 0 < (scale x)⁻¹ :=
    inv_pos.mpr (batemanPhysicalSphereScale_pos t x)
  obtain ⟨m, hm, hbound⟩ := positive_lower_on_physicalTorus hp hq hpq t h₀ hc hv hpv
  let a := fun u => (scale (g u))⁻¹
  have hca : Continuous a := hv.comp hcg
  have hb (u : ℝ) : m ≤ a u := hbound (g u) (hg u)
  let e := orbitClockOrderIso a hca hm hb
  have he₀ : e 0 = 0 := intervalIntegral.integral_same
  have hzero : e.symm 0 = 0 := e.injective (by rw [e.apply_symm_apply, he₀])
  refine ⟨e, ?_, ?_, fun u => hg (e.symm u)⟩
  · intro u
    let x := g (e.symm u)
    have he : HasDerivAt (e.symm : ℝ → ℝ) (a (e.symm u))⁻¹ u :=
      hasDerivAt_orbitClockOrderIso_symm a hca hm hb u
    have hd := (hdg (e.symm u)).scomp u he
    have hvel : (a (e.symm u))⁻¹ • ((scale x)⁻¹ • batemanMagneticVector p q t x) =
        batemanMagneticVector p q t x := by
      change ((scale x)⁻¹)⁻¹ • ((scale x)⁻¹ • batemanMagneticVector p q t x) = _
      rw [inv_inv, smul_smul, mul_inv_cancel₀ (batemanPhysicalSphereScale_pos t x).ne', one_smul]
    exact hd.congr_deriv hvel
  · change g (e.symm 0) = g 0
    rw [hzero]

end Qatlib.Papers.KnotLight13.TorusFamily
