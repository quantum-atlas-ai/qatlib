/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.PoweredSphereTori

public import Mathlib.Topology.LocalAtTarget

/-!
# Fixed-phase bands on the Bateman sphere

A prescribed phase of the nonzero powered label cuts the unit sphere
between its two coordinate circles. The radius and the weighted
phase fiber give coordinates on this open cylinder.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

open Set

/-- The unit-sphere locus with two nonzero coordinates and a fixed
normalized complex product label. -/
def poweredSphereOpenPhaseBand (p q : ℕ) (phase : Circle) : Set (ℂ × ℂ) :=
  {z | Complex.normSq z.1 + Complex.normSq z.2 = 1 ∧
    Complex.normSq z.1 ∈ Ioo (0 : ℝ) 1 ∧
    z.1 ^ p * z.2 ^ q = ((‖z.1‖ ^ p * ‖z.2‖ ^ q : ℝ) : ℂ) * (phase : ℂ)}

/-- A fixed phase of the nonzero label gives an open cylinder whose
interval coordinate is the first squared radius. -/
noncomputable def poweredSphereOpenPhaseBandHomeomorph {p q : ℕ} (hpq : Nat.Coprime p q)
    (phase : Circle) : (↥(Ioo (0 : ℝ) 1) × Circle) ≃ₜ ↥(poweredSphereOpenPhaseBand p q phase) := by
  let X := ↥(Icc (0 : ℝ) 1) × Circle
  let Y := poweredSphereOpenPhaseBand p q phase
  let f : X → ℂ × ℂ := fun x =>
    poweredTorusPhaseParam p q (Real.sqrt x.1.val) (Real.sqrt (1 - x.1.val)) phase x.2
  have hf : Continuous f := by
    have hr : Continuous (fun x : X => x.1.val) := continuous_subtype_val.comp continuous_fst
    exact (continuous_poweredTorusPhaseParam p q).comp
      (((Real.continuous_sqrt.comp hr).prodMk
        (Real.continuous_sqrt.comp (continuous_const.sub hr))).prodMk
        (continuous_const.prodMk continuous_snd))
  have hnorm (x : X) :
      ‖(f x).1‖ = Real.sqrt x.1.val ∧ ‖(f x).2‖ = Real.sqrt (1 - x.1.val) ∧
      (f x).1 ^ p * (f x).2 ^ q =
        (((Real.sqrt x.1.val) ^ p * (Real.sqrt (1 - x.1.val)) ^ q : ℝ) : ℂ) * (phase : ℂ) :=
    poweredTorusPhaseParam_spec hpq (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) phase x.2
  have hsq (x : X) :
      Complex.normSq (f x).1 = x.1.val ∧ Complex.normSq (f x).2 = 1 - x.1.val := by
    obtain ⟨ha, hb, _⟩ := hnorm x
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq, ha, hb,
      Real.sq_sqrt x.1.property.1, Real.sq_sqrt (sub_nonneg.mpr x.1.property.2)]
    exact ⟨rfl, rfl⟩
  have hpre (x : X) : f x ∈ Y ↔ x.1.val ∈ Ioo (0 : ℝ) 1 := by
    obtain ⟨ha, hb, hlabel⟩ := hnorm x
    obtain ⟨hra, hrb⟩ := hsq x
    change (_ + _ = 1 ∧ _ ∈ Ioo (0 : ℝ) 1 ∧ _) ↔ _
    rw [hra, hrb, ha, hb, hlabel]
    exact ⟨fun h => h.2.1, fun h => ⟨by ring, h, rfl⟩⟩
  let Xcut := f ⁻¹' Y
  let fcut : ↥Xcut → ↥Y := Y.restrictPreimage f
  have hfinj : Function.Injective fcut := by
    rintro ⟨⟨r, u⟩, hu⟩ ⟨⟨s, v⟩, hv⟩ h
    have he : f (r, u) = f (s, v) := congrArg Subtype.val h
    have hrs : r = s := Subtype.ext ((hsq (r, u)).1.symm.trans
      ((congrArg (fun z : ℂ × ℂ => Complex.normSq z.1) he).trans (hsq (s, v)).1))
    subst s
    obtain ⟨hr₀, hr₁⟩ := (hpre (r, u)).1 hu
    have hu' := (poweredTorusPhaseParam_bijective hpq (Real.sqrt_pos.2 hr₀)
      (Real.sqrt_pos.2 (sub_pos.mpr hr₁)) phase).1 he
    exact Subtype.ext (Prod.ext rfl hu')
  have hfsurj : Function.Surjective fcut := by
    intro z
    have hz : z.val ∈ Y := z.property
    change _ ∧ _ ∈ Ioo (0 : ℝ) 1 ∧ _ at hz
    obtain ⟨hunit, hr, hlabel⟩ := hz
    let r : ↥(Icc (0 : ℝ) 1) := ⟨Complex.normSq z.val.1, Ioo_subset_Icc_self hr⟩
    have hsecond : 1 - r.val = Complex.normSq z.val.2 := by
      change 1 - Complex.normSq z.val.1 = _
      linarith
    have ha : ‖z.val.1‖ = Real.sqrt r.val := by
      change ‖z.val.1‖ = Real.sqrt (Complex.normSq z.val.1)
      rw [Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    have hb : ‖z.val.2‖ = Real.sqrt (1 - r.val) := by
      rw [hsecond, Complex.normSq_eq_norm_sq, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
    rw [ha, hb] at hlabel
    have hsurj := (poweredTorusPhaseParam_bijective hpq (Real.sqrt_pos.2 hr.1)
      (Real.sqrt_pos.2 (sub_pos.mpr hr.2)) phase).2
    have hz' : z.val ∈ Set.range (poweredTorusPhaseParam p q (Real.sqrt r.val)
        (Real.sqrt (1 - r.val)) phase) := by
      rw [hsurj]
      exact ⟨ha, hb, hlabel⟩
    obtain ⟨v, hv⟩ := hz'
    exact ⟨⟨(r, v), (hpre (r, v)).2 hr⟩, Subtype.ext hv⟩
  letI : CompactSpace X := inferInstanceAs (CompactSpace (↥(Icc (0 : ℝ) 1) × Circle))
  have hclosed : IsClosedMap f := hf.isClosedMap
  let e := (Equiv.ofBijective fcut ⟨hfinj, hfsurj⟩).toHomeomorphOfContinuousClosed
    (hf.restrictPreimage (s := Y)) (IsClosedMap.restrictPreimage hclosed Y)
  let domain : (↥(Ioo (0 : ℝ) 1) × Circle) ≃ₜ ↥Xcut :=
    { toFun := fun x => ⟨(⟨x.1.val, Ioo_subset_Icc_self x.1.property⟩, x.2), (hpre _).2 x.1.property⟩
      invFun := fun x => (⟨x.val.1.val, (hpre x.val).1 x.property⟩, x.val.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      continuous_toFun := by
        have hr : Continuous (fun x : ↥(Ioo (0 : ℝ) 1) × Circle => x.1.val) :=
          continuous_subtype_val.comp continuous_fst
        exact ((hr.subtype_mk _).prodMk continuous_snd).subtype_mk _
      continuous_invFun := by
        have hr : Continuous (fun x : ↥Xcut => x.val.1.val) :=
          continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
        exact (hr.subtype_mk _).prodMk (continuous_snd.comp continuous_subtype_val) }
  exact domain.trans e

end Qatlib.Papers.KnotLight13.TorusFamily
