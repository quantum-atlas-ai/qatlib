/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanJacobian
public import Qatlib.Papers.KnotLight13.TorusFamily.HelicityTransport
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Analysis.ODE.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.MonotoneContinuity

/-!
# Global reparametrization by the Bateman ray Jacobian

[Kedia2013TyingKnots], page 150404-2,
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
At a fixed physical time the positive spatial Jacobian can be integrated
along a whole orbit. Its uniform lower bound ensures that the resulting
strictly increasing curve parameter covers the entire real line. The
same monotone clock coordinate transports periodic orbits to periodic
orbits and preserves injectivity on each half-open fundamental lap
interval.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

local notation "Space" => ℝ × ℝ × ℝ
open Set

/-- The integral of a continuous speed is a differentiable clock starting at zero. -/
theorem hasDerivAt_orbitClock {v : ℝ → ℝ} (hv : Continuous v) (s : ℝ) :
    HasDerivAt (fun t => ∫ u in 0..t, v u) (v s) s :=
  intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable _ _)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt

/-- A continuous speed with a uniform positive lower bound gives a strictly
increasing clock onto the whole real line. -/
noncomputable def orbitClockOrderIso (v : ℝ → ℝ) (hv : Continuous v)
    {m : ℝ} (hm : 0 < m) (hbound : ∀ s, m ≤ v s) : ℝ ≃o ℝ := by
  let C := fun t : ℝ => ∫ u in 0..t, v u
  have hD := hasDerivAt_orbitClock hv
  have hDiff : Differentiable ℝ C := fun u => (hD u).differentiableAt
  have h0 : C 0 = 0 := intervalIntegral.integral_same
  refine (strictMono_of_hasDerivAt_pos hD (fun u => hm.trans_le (hbound u))).orderIsoOfSurjective C ?_
  intro y
  have hm' : Monotone (fun s => C s - m * s) := by
    have hf (s : ℝ) : HasDerivAt (fun u => C u - m * u) (v s - m) s := by
      simpa only [id_eq, mul_one] using (hD s).fun_sub ((hasDerivAt_id s).const_mul m)
    exact monotone_of_hasDerivAt_nonneg hf (fun s => sub_nonneg.mpr (hbound s))
  let a := -(|y| + 1) / m
  let b := (|y| + 1) / m
  have ha : a ≤ 0 := div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity)) hm.le
  have hb : 0 ≤ b := by unfold b; positivity
  have hma : m * a = -(|y| + 1) := by unfold a; field_simp [hm.ne']
  have hmb : m * b = |y| + 1 := by unfold b; field_simp [hm.ne']
  have hCa := hm' ha
  have hCb := hm' hb
  have hw : y ∈ Icc (C a) (C b) := by
    simp only [h0, mul_zero, sub_zero, hma, hmb] at hCa hCb
    exact ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
  obtain ⟨s, _, hs⟩ := intermediate_value_Icc (ha.trans hb) hDiff.continuous.continuousOn hw
  exact ⟨s, hs⟩

/-- The inverse clock has derivative equal to the reciprocal of the original
speed, evaluated at the inverse parameter. -/
theorem hasDerivAt_orbitClockOrderIso_symm (v : ℝ → ℝ) (hv : Continuous v)
    {m : ℝ} (hm : 0 < m) (hbound : ∀ s, m ≤ v s) (u : ℝ) :
    let e := orbitClockOrderIso v hv hm hbound
    HasDerivAt (e.symm : ℝ → ℝ) (v (e.symm u))⁻¹ u := by
  let e := orbitClockOrderIso v hv hm hbound
  have h (s : ℝ) : (∫ t in (0 : ℝ)..(e.symm s), v t) = s := e.apply_symm_apply s
  exact (hasDerivAt_orbitClock hv (e.symm u)).of_local_left_inverse
    e.symm.continuous.continuousAt (hm.trans_le (hbound (e.symm u))).ne'
    (Filter.Eventually.of_forall h)

/-- If the speed of a real parametrization has a period, the time change adds
the same increment over every lap. -/
theorem orbitClock_increment_of_periodic {f v : ℝ → ℝ}
    (hf : ∀ s, HasDerivAt f (v s) s) {T : ℝ} (hT : Function.Periodic v T) (s : ℝ) :
    f (s + T) - f s = f T - f 0 := by
  have hd (u : ℝ) : HasDerivAt (fun x => f (x + T) - f x) 0 u := by
    have h := ((hf (u + T)).comp u ((hasDerivAt_id u).add_const T)).fun_sub (hf u)
    simpa only [Function.comp_apply, id_eq, mul_one, hT u, sub_self] using h
  simpa only [zero_add] using
    (is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) s 0)

/-- The exact axial formula makes the ray Jacobian continuous on every slice. -/
theorem continuous_batemanRayJacobian (t : ℝ) :
    Continuous (fun s : Space => LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap) := by
  simp_rw [det_batemanRay_eq_axialRatio]
  have hR : Continuous (batemanRay t) := (contDiff_bateman_ray t).continuous
  exact (continuous_const.add (((continuous_snd.comp continuous_snd).comp hR).sub
    continuous_const |>.pow 2)).div (continuous_const.add ((continuous_snd.comp continuous_snd).pow 2))
      (fun _ => by positivity)

/-- The accumulated Jacobian along a reference curve, starting at parameter zero. -/
noncomputable def batemanOrbitClock (t : ℝ) (γ : ℝ → Space) (s : ℝ) : ℝ :=
  ∫ u in 0..s, LinearMap.det (fderiv ℝ (batemanRay t) (γ u)).toLinearMap

/-- The interval integral defining the new parameter has derivative equal
to the physical Jacobian at the corresponding point of the curve. -/
theorem hasDerivAt_batemanOrbitClock (t : ℝ) {γ : ℝ → Space} (hγ : Continuous γ) (u : ℝ) :
    HasDerivAt (batemanOrbitClock t γ) (LinearMap.det (fderiv ℝ (batemanRay t) (γ u)).toLinearMap) u := by
  exact hasDerivAt_orbitClock ((continuous_batemanRayJacobian t).comp hγ) u

/-- The positive clock has a global strictly increasing inverse, since
the physical Jacobian is uniformly bounded below on each slice. -/
noncomputable def batemanOrbitClockOrderIso (t : ℝ) {γ : ℝ → Space} (hγ : Continuous γ) : ℝ ≃o ℝ := by
  let v := fun s => LinearMap.det (fderiv ℝ (batemanRay t) (γ s)).toLinearMap
  have hv : Continuous v := (continuous_batemanRayJacobian t).comp hγ
  exact orbitClockOrderIso v hv (m := (2 + 8 * t ^ 2)⁻¹) (by positivity)
    (fun s => (det_batemanRay_uniform_bounds t (γ s)).1)

/-- The inverse parameter has derivative equal to the reciprocal of
the Jacobian at the corresponding point of the reference curve. -/
theorem hasDerivAt_batemanOrbitClockOrderIso_symm (t : ℝ) {γ : ℝ → Space} (hγ : Continuous γ) (u : ℝ) :
    let e := batemanOrbitClockOrderIso t hγ
    HasDerivAt (e.symm : ℝ → ℝ)
      (LinearMap.det (fderiv ℝ (batemanRay t) (γ (e.symm u))).toLinearMap)⁻¹ u := by
  let e := batemanOrbitClockOrderIso t hγ
  have h (v : ℝ) : batemanOrbitClock t γ (e.symm v) = v := e.apply_symm_apply v
  exact (hasDerivAt_batemanOrbitClock t hγ (e.symm u)).of_local_left_inverse
    e.symm.continuous.continuousAt (det_bateman_ray_pos t (γ (e.symm u))).ne'
    (Filter.Eventually.of_forall h)

/-- Along a periodic reference curve, the same clock increment is
accumulated during every lap. -/
theorem batemanOrbitClock_add_period (t : ℝ) {γ : ℝ → Space} (hγ : Continuous γ)
    {T : ℝ} (hT : Function.Periodic γ T) (s : ℝ) :
    batemanOrbitClock t γ (s + T) = batemanOrbitClock t γ s + batemanOrbitClock t γ T := by
  have hper : Function.Periodic (fun u => LinearMap.det (fderiv ℝ (batemanRay t) (γ u)).toLinearMap) T :=
    fun u => congrArg (fun x => LinearMap.det (fderiv ℝ (batemanRay t) x).toLinearMap) (hT u)
  have hd := orbitClock_increment_of_periodic (hasDerivAt_batemanOrbitClock t hγ) hper s
  have h0 : batemanOrbitClock t γ 0 = 0 := intervalIntegral.integral_same
  rw [h0, sub_zero] at hd
  linarith

/-- The inverse clock transports a positive period to a positive period.
The new period is the integral of the ray Jacobian over one reference lap. -/
theorem batemanRay_reparametrized_periodic (t : ℝ) {γ : ℝ → Space} (hγ : Continuous γ)
    {T : ℝ} (hT₀ : 0 < T) (hT : Function.Periodic γ T) :
    let e := batemanOrbitClockOrderIso t hγ
    0 < batemanOrbitClock t γ T ∧
      Function.Periodic (batemanRay t ∘ γ ∘ e.symm) (batemanOrbitClock t γ T) := by
  let e := batemanOrbitClockOrderIso t hγ
  have he (u : ℝ) : e u = batemanOrbitClock t γ u := rfl
  have h0 : e 0 = 0 := intervalIntegral.integral_same
  constructor
  · simpa only [h0, he T] using e.strictMono hT₀
  · intro u
    have hshift : e.symm (u + batemanOrbitClock t γ T) = e.symm u + T := by
      apply e.injective
      rw [e.apply_symm_apply, he (e.symm u + T), batemanOrbitClock_add_period t hγ hT,
        ← he (e.symm u), e.apply_symm_apply]
    change batemanRay t (γ (e.symm (u + batemanOrbitClock t γ T))) = batemanRay t (γ (e.symm u))
    rw [hshift, hT]

/-- When the spatial differential scales a field by the Jacobian, the
inverse clock cancels the scale in its usual integral-curve equation. -/
private theorem batemanRay_integralCurve_of_cofactor (t : ℝ) {V W : Space → Space}
    (hV : ∀ x, let D := fderiv ℝ (batemanRay t) x
      D (V x) = LinearMap.det D.toLinearMap • W (batemanRay t x))
    {γ : ℝ → Space} (hγ : IsIntegralCurve γ (fun _ => V)) :
    ∃ e : ℝ ≃o ℝ, IsIntegralCurve (batemanRay t ∘ γ ∘ e) (fun _ => W) ∧
      range (batemanRay t ∘ γ ∘ e) = batemanRay t '' range γ ∧
      ∀ T : ℝ, 0 < T → Function.Periodic γ T → Set.InjOn γ (Set.Ico 0 T) →
        0 < batemanOrbitClock t γ T ∧
        Function.Periodic (batemanRay t ∘ γ ∘ e) (batemanOrbitClock t γ T) ∧
        Set.InjOn (batemanRay t ∘ γ ∘ e) (Set.Ico 0 (batemanOrbitClock t γ T)) := by
  have hd : Differentiable ℝ γ := fun u => (hγ u).differentiableAt
  let E := batemanOrbitClockOrderIso t hd.continuous
  let e := E.symm
  refine ⟨e, ?_, ?_, ?_⟩
  · intro u
    let x := γ (e u)
    let D := fderiv ℝ (batemanRay t) x
    let J := LinearMap.det D.toLinearMap
    have hE : HasDerivAt (e : ℝ → ℝ) J⁻¹ u := hasDerivAt_batemanOrbitClockOrderIso_symm t hd.continuous u
    have hγ' : HasDerivAt (γ ∘ e) (J⁻¹ • V x) u := (hγ (e u)).scomp u hE
    have hR : HasFDerivAt (batemanRay t) D x :=
      ((contDiff_bateman_ray t).differentiable (by simp) x).hasFDerivAt
    have hVel : D (J⁻¹ • V x) = W (batemanRay t x) := by
      have hJ : J ≠ 0 := (det_bateman_ray_pos t x).ne'
      rw [map_smul, hV x, smul_smul]
      change (J⁻¹ * J) • W (batemanRay t x) = _
      rw [inv_mul_cancel₀ hJ, one_smul]
    exact (hR.comp_hasDerivAt u hγ').congr_deriv hVel
  · rw [range_comp, range_comp, range_eq_univ.mpr e.surjective, image_univ]
  · intro T hT₀ hT hinj
    obtain ⟨hclockpos, hper⟩ := batemanRay_reparametrized_periodic t hd.continuous hT₀ hT
    refine ⟨hclockpos, hper, ?_⟩
    intro s₁ hs₁ s₂ hs₂ hEq
    have hγeq : γ (e s₁) = γ (e s₂) := batemanRay_injective t hEq
    have hmem : ∀ s : ℝ, s ∈ Set.Ico 0 (batemanOrbitClock t γ T) → e s ∈ Set.Ico 0 T := by
      intro s hs
      have hEzero : E 0 = 0 := intervalIntegral.integral_same
      have hEe : ∀ u : ℝ, E (e u) = u := fun u => E.apply_symm_apply u
      refine ⟨?_, ?_⟩
      · refine (E.le_iff_le).mp ?_
        rw [hEzero, hEe]
        exact hs.1
      · refine (E.lt_iff_lt).mp ?_
        rw [hEe]
        exact hs.2
    exact e.injective (hinj (hmem s₁ hs₁) (hmem s₂ hs₂) hγeq)

/-- Every global integral curve of the initial electric field is carried
to a global integral curve of the actual electric field on the later
slice, by an increasing change of the entire real parameter. -/
theorem batemanRay_electricIntegralCurve (p q : ℕ) (t : ℝ) {γ : ℝ → Space}
    (hγ : IsIntegralCurve γ (fun _ => batemanElectricVector p q 0)) :
    ∃ e : ℝ ≃o ℝ, IsIntegralCurve (batemanRay t ∘ γ ∘ e) (fun _ => batemanElectricVector p q t) ∧
      range (batemanRay t ∘ γ ∘ e) = batemanRay t '' range γ := by
  obtain ⟨e, hE, hR, _⟩ :=
    batemanRay_integralCurve_of_cofactor t (fun x => (batemanRay_transports_vectors p q t x).1) hγ
  exact ⟨e, hE, hR⟩

/-- Every global integral curve of the initial magnetic field is carried
to a global integral curve of the actual magnetic field on the later
slice, by an increasing change of the entire real parameter. -/
theorem batemanRay_magneticIntegralCurve (p q : ℕ) (t : ℝ) {γ : ℝ → Space}
    (hγ : IsIntegralCurve γ (fun _ => batemanMagneticVector p q 0)) :
    ∃ e : ℝ ≃o ℝ, IsIntegralCurve (batemanRay t ∘ γ ∘ e) (fun _ => batemanMagneticVector p q t) ∧
      range (batemanRay t ∘ γ ∘ e) = batemanRay t '' range γ := by
  obtain ⟨e, hB, hR, _⟩ :=
    batemanRay_integralCurve_of_cofactor t (fun x => (batemanRay_transports_vectors p q t x).2) hγ
  exact ⟨e, hB, hR⟩

/-- A closed magnetic orbit at the initial time remains a periodic
integral curve of the actual magnetic field after ray transport; the
monotone clock coordinate also preserves injectivity on the half-open
fundamental interval of a lap. -/
theorem batemanRay_periodicMagneticIntegralCurve (p q : ℕ) (t : ℝ) {γ : ℝ → Space}
    (hγ : IsIntegralCurve γ (fun _ => batemanMagneticVector p q 0))
    {T : ℝ} (hT₀ : 0 < T) (hT : Function.Periodic γ T)
    (hinj : Set.InjOn γ (Set.Ico 0 T)) :
    ∃ e : ℝ ≃o ℝ, IsIntegralCurve (batemanRay t ∘ γ ∘ e) (fun _ => batemanMagneticVector p q t) ∧
      range (batemanRay t ∘ γ ∘ e) = batemanRay t '' range γ ∧
      0 < batemanOrbitClock t γ T ∧
      Function.Periodic (batemanRay t ∘ γ ∘ e) (batemanOrbitClock t γ T) ∧
      Set.InjOn (batemanRay t ∘ γ ∘ e) (Set.Ico 0 (batemanOrbitClock t γ T)) := by
  obtain ⟨e, hB, hR, hP⟩ :=
    batemanRay_integralCurve_of_cofactor t (fun x => (batemanRay_transports_vectors p q t x).2) hγ
  exact ⟨e, hB, hR, hP T hT₀ hT hinj⟩

/-- A closed electric orbit at the initial time remains a periodic
integral curve of the actual electric field after ray transport; the
monotone clock coordinate also preserves injectivity on the half-open
fundamental interval of a lap. -/
theorem batemanRay_periodicElectricIntegralCurve (p q : ℕ) (t : ℝ) {γ : ℝ → Space}
    (hγ : IsIntegralCurve γ (fun _ => batemanElectricVector p q 0))
    {T : ℝ} (hT₀ : 0 < T) (hT : Function.Periodic γ T)
    (hinj : Set.InjOn γ (Set.Ico 0 T)) :
    ∃ e : ℝ ≃o ℝ, IsIntegralCurve (batemanRay t ∘ γ ∘ e) (fun _ => batemanElectricVector p q t) ∧
      range (batemanRay t ∘ γ ∘ e) = batemanRay t '' range γ ∧
      0 < batemanOrbitClock t γ T ∧
      Function.Periodic (batemanRay t ∘ γ ∘ e) (batemanOrbitClock t γ T) ∧
      Set.InjOn (batemanRay t ∘ γ ∘ e) (Set.Ico 0 (batemanOrbitClock t γ T)) := by
  obtain ⟨e, hE, hR, hP⟩ :=
    batemanRay_integralCurve_of_cofactor t (fun x => (batemanRay_transports_vectors p q t x).1) hγ
  exact ⟨e, hE, hR, hP T hT₀ hT hinj⟩

end Qatlib.Papers.KnotLight13.TorusFamily
