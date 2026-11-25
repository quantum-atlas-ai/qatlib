/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanTimeSlices

public import Mathlib.LinearAlgebra.Determinant

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.IntermediateValue

/-!
# Smooth Bateman ray transport

[Kedia2013TyingKnots], equations (5) and (6),
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The explicit time-slice map and its inverse are smooth on physical space.
The Jacobian is positive for all real times because it is continuous,
never vanishes, and equals one on the initial slice.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

/-- The physical ray map is smooth in the initial position and time jointly. -/
theorem contDiff_bateman_ray_joint :
    ContDiff ℝ ⊤ (fun a : ℝ × (ℝ × ℝ × ℝ) => batemanRay a.1 a.2) := by
  have ht : ContDiff ℝ ⊤ (fun a : ℝ × (ℝ × ℝ × ℝ) => a.1) := by fun_prop
  have hx : ContDiff ℝ ⊤ (fun a : ℝ × (ℝ × ℝ × ℝ) => a.2.1) := by fun_prop
  have hy : ContDiff ℝ ⊤ (fun a : ℝ × (ℝ × ℝ × ℝ) => a.2.2.1) := by fun_prop
  have hz : ContDiff ℝ ⊤ (fun a : ℝ × (ℝ × ℝ × ℝ) => a.2.2.2) := by fun_prop
  have hL : ContDiff ℝ ⊤ (fun a : ℝ × (ℝ × ℝ × ℝ) =>
      2 * a.1 / (a.2.1 ^ 2 + a.2.2.1 ^ 2 + a.2.2.2 ^ 2 + 1)) :=
    (contDiff_const.mul ht).div
      ((((hx.pow 2).add (hy.pow 2)).add (hz.pow 2)).add contDiff_const)
      (fun _ => by positivity)
  exact (hx.add (hL.mul (hy.sub (hz.mul hx)))).prodMk
    ((hy.sub (hL.mul (hx.add (hz.mul hy)))).prodMk
      ((hz.add ht).sub (hL.mul ((hz.pow 2).add contDiff_const))))

/-- Each fixed-time ray map is smooth in physical space. -/
theorem contDiff_bateman_ray (t : ℝ) : ContDiff ℝ ⊤ (batemanRay t) :=
  contDiff_bateman_ray_joint.comp (contDiff_const.prodMk contDiff_id)

/-- The inverse of the ray map on every fixed time slice is smooth
on all of physical space. -/
theorem contDiff_bateman_slice_inverse (t : ℝ) :
    ContDiff ℝ ⊤ (fun s : ℝ × ℝ × ℝ => (batemanSliceHomeomorph t).symm s) := by
  have hi : ContDiff ℝ ⊤ (fun s : ℝ × ℝ × ℝ => (s.1, s.2.1, s.2.2, t)) := by fun_prop
  have ha := contDiff_rationalAlpha.comp hi
  have hb := contDiff_rationalBeta.comp hi
  change ContDiff ℝ ⊤ (fun s => (batemanPairAt t s).1) at ha
  change ContDiff ℝ ⊤ (fun s => (batemanPairAt t s).2) at hb
  have hre : ContDiff ℝ ⊤ Complex.re := Complex.reCLM.contDiff
  have him : ContDiff ℝ ⊤ Complex.im := Complex.imCLM.contDiff
  have hd : ContDiff ℝ ⊤ (fun s => 1 - (batemanPairAt t s).1.re) :=
    contDiff_const.sub (hre.comp ha)
  have hn (s : ℝ × ℝ × ℝ) : 1 - (batemanPairAt t s).1.re ≠ 0 :=
    (sub_pos.mpr (rationalAlpha_re_lt_one _ _ _ _)).ne'
  exact ((hre.comp hb).div hd hn).prodMk
    (((him.comp hb).neg.div hd hn).prodMk ((him.comp ha).div hd hn))

/-- The spatial differential of the ray map is continuous in both
the time of the slice and the initial position. -/
private theorem continuous_bateman_ray_spatial_differential :
    Continuous (fun a : ℝ × (ℝ × ℝ × ℝ) => fderiv ℝ (batemanRay a.1) a.2) := by
  have h : ContDiff ℝ ⊤ (Function.uncurry
      (fun a : ℝ × (ℝ × ℝ × ℝ) => batemanRay a.1)) := by
    have hp : ContDiff ℝ ⊤ (fun p : (ℝ × (ℝ × ℝ × ℝ)) × (ℝ × ℝ × ℝ) =>
      (p.1.1, p.2)) := by fun_prop
    exact contDiff_bateman_ray_joint.comp hp
  exact (h.fderiv contDiff_snd (by simp : (⊤ : WithTop ℕ∞) + 1 ≤ ⊤)).continuous

/-- The spatial derivative of the inverse slice map is a left inverse
to the spatial derivative of the ray map at the corresponding point. -/
theorem fderiv_bateman_ray_inverse_comp (t : ℝ) (s : ℝ × ℝ × ℝ) :
    (fderiv ℝ (fun q => (batemanSliceHomeomorph t).symm q) (batemanRay t s)).comp
      (fderiv ℝ (batemanRay t) s) = ContinuousLinearMap.id ℝ (ℝ × ℝ × ℝ) := by
  let inv := fun q : ℝ × ℝ × ℝ => (batemanSliceHomeomorph t).symm q
  let D := fderiv ℝ (batemanRay t) s
  let E := fderiv ℝ inv (batemanRay t s)
  have hF : HasFDerivAt (batemanRay t) D s :=
    ((contDiff_bateman_ray t).differentiable (by simp) s).hasFDerivAt
  have hI : HasFDerivAt inv E (batemanRay t s) :=
    ((contDiff_bateman_slice_inverse t).differentiable (by simp) _).hasFDerivAt
  have hcomp : (inv ∘ batemanRay t) = id :=
    funext fun q => (batemanSliceHomeomorph t).symm_apply_apply q
  have hDeriv := (hI.comp s hF).fderiv
  rw [hcomp, fderiv_id] at hDeriv
  exact hDeriv.symm

/-- The spatial ray derivative has nonzero determinant at every point. -/
private theorem det_bateman_ray_ne_zero (t : ℝ) (s : ℝ × ℝ × ℝ) :
    LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap ≠ 0 := by
  let inv := fun q : ℝ × ℝ × ℝ => (batemanSliceHomeomorph t).symm q
  let D := fderiv ℝ (batemanRay t) s
  let E := fderiv ℝ inv (batemanRay t s)
  have hdet := congrArg
    (fun L : (ℝ × ℝ × ℝ) →L[ℝ] (ℝ × ℝ × ℝ) => LinearMap.det L.toLinearMap)
    (fderiv_bateman_ray_inverse_comp t s)
  change LinearMap.det (E.toLinearMap.comp D.toLinearMap) =
    LinearMap.det (LinearMap.id : (ℝ × ℝ × ℝ) →ₗ[ℝ] (ℝ × ℝ × ℝ)) at hdet
  rw [LinearMap.det_comp, LinearMap.det_id] at hdet
  change LinearMap.det D.toLinearMap ≠ 0
  intro hD
  rw [hD, mul_zero] at hdet
  exact zero_ne_one hdet

/-- On physical space the ray map preserves orientation at every
real time. Its spatial determinant is continuous, never zero, and
equal to one at time zero. -/
theorem det_bateman_ray_pos (t : ℝ) (s : ℝ × ℝ × ℝ) :
    0 < LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap := by
  let f : ℝ → ℝ := fun q => LinearMap.det (fderiv ℝ (batemanRay q) s).toLinearMap
  have hc : Continuous f := ContinuousLinearMap.continuous_det.comp
    (continuous_bateman_ray_spatial_differential.comp (continuous_id.prodMk continuous_const))
  have h0 : f 0 = 1 := by
    have hRay : batemanRay 0 = id := funext batemanRay_zero
    unfold f
    rw [hRay, fderiv_id]
    exact LinearMap.det_id
  change 0 < f t
  by_contra! ht
  have hc' := (isPreconnected_range hc).ordConnected
  have hmem : (0 : ℝ) ∈ Set.range f :=
    hc'.out (Set.mem_range_self t) (Set.mem_range_self 0) ⟨ht, by rw [h0]; norm_num⟩
  obtain ⟨q, hq⟩ := hmem
  exact det_bateman_ray_ne_zero q s hq

end Qatlib.Papers.KnotLight13.TorusFamily
