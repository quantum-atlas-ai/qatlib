/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.Madelung.DensityFlux

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Tactic.Ring

/-!
# Spatial and temporal derivatives of the Madelung phase

The Cartesian line derivatives are directional evaluations of the
spacetime Fréchet derivative. Symmetry of the second derivative gives
the mixed derivative identity for the phase gradient.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.Madelung

open scoped BigOperators

/-- A time and its three Cartesian spatial coordinates. -/
abbrev GpeSpacetime := ℝ × GpeSpace

/-- The time direction in the product coordinates. -/
def gpeTimeAxis : GpeSpacetime := (1, 0)

/-- A spatial coordinate direction in the product coordinates. -/
def gpeSpatialAxis (i : Fin 3) : GpeSpacetime := (0, Pi.single i 1)

/-- The Cartesian section partial agrees with evaluation of the
spacetime Fréchet derivative on the spatial direction. -/
theorem gpePartial_slice_eq_fderiv {f : GpeSpacetime → ℝ} {t : ℝ} {x : GpeSpace}
    (hf : DifferentiableAt ℝ f (t, x)) (i : Fin 3) :
    gpePartial (fun y => f (t, y)) x i = fderiv ℝ f (t, x) (gpeSpatialAxis i) := by
  rw [← hf.lineDeriv_eq_fderiv]
  unfold gpePartial lineDeriv
  congr 1
  funext s
  simp [gpeCoordinateLine, gpeSpatialAxis, Function.comp_apply]

/-- The time-section derivative agrees with evaluation of the spacetime
Fréchet derivative on the time direction. -/
theorem gpeTime_slice_eq_fderiv {f : GpeSpacetime → ℝ} {t : ℝ} {x : GpeSpace}
    (hf : DifferentiableAt ℝ f (t, x)) :
    deriv (fun s => f (s, x)) t = fderiv ℝ f (t, x) gpeTimeAxis := by
  rw [← hf.lineDeriv_eq_fderiv]
  unfold lineDeriv
  have he : (fun s : ℝ => f ((t, x) + s • gpeTimeAxis)) =
      fun s => (fun u => f (u, x)) (s + t) := by
    funext s
    simp [gpeTimeAxis, add_comm]
  rw [he]
  simpa only [zero_add] using (deriv_comp_add_const (fun u => f (u, x)) t (0 : ℝ)).symm

/-- The derivative of directional evaluation is evaluation of the
second Fréchet derivative on the two directions. -/
private theorem hasFDerivAt_gpeDirectional {f : GpeSpacetime → ℝ}
    {p : GpeSpacetime} (h : DifferentiableAt ℝ (fderiv ℝ f) p) (v : GpeSpacetime) :
    HasFDerivAt (fun q => fderiv ℝ f q v)
      ((ContinuousLinearMap.apply ℝ ℝ v).comp (fderiv ℝ (fderiv ℝ f) p)) p :=
  (ContinuousLinearMap.apply ℝ ℝ v).hasFDerivAt.comp p h.hasFDerivAt

/-- The time derivative of the spatial partial of the actual phase
is the spatial partial of its time derivative. -/
theorem gpe_mixedTimePartial (φ : GpeSpacetime → ℝ) (hφ : ContDiff ℝ 2 φ)
    (t : ℝ) (x : GpeSpace) (i : Fin 3) :
    deriv (fun s => gpePartial (fun y => φ (s, y)) x i) t =
      gpePartial (fun y => deriv (fun s => φ (s, y)) t) x i := by
  have h₁ := hφ.differentiable (by norm_num)
  have h₂ := (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hSpace : (fun s => gpePartial (fun y => φ (s, y)) x i) =
      fun s => fderiv ℝ φ (s, x) (gpeSpatialAxis i) :=
    funext fun s => gpePartial_slice_eq_fderiv (h₁ (s, x)) i
  have hTime : (fun y => deriv (fun s => φ (s, y)) t) =
      fun y => fderiv ℝ φ (t, y) gpeTimeAxis :=
    funext fun y => gpeTime_slice_eq_fderiv (h₁ (t, y))
  have hS := hasFDerivAt_gpeDirectional (h₂ (t, x)) (gpeSpatialAxis i)
  have hT := hasFDerivAt_gpeDirectional (h₂ (t, x)) gpeTimeAxis
  rw [hSpace, hTime, gpeTime_slice_eq_fderiv hS.differentiableAt,
    gpePartial_slice_eq_fderiv hT.differentiableAt, hS.fderiv, hT.fderiv]
  have hs := (hφ.contDiffAt (x := (t, x))).isSymmSndFDerivAt (by simp)
    gpeTimeAxis (gpeSpatialAxis i)
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using hs

/-- The spatial derivative of the squared phase-gradient length is
twice the phase-gradient transport of that component. -/
theorem gpe_partial_gradDot_self (φ : GpeSpacetime → ℝ) (hφ : ContDiff ℝ 2 φ)
    (t : ℝ) (x : GpeSpace) (i : Fin 3) :
    gpePartial (fun y => gpeGradDot (fun z => φ (t, z)) (fun z => φ (t, z)) y) x i =
      2 * ∑ j : Fin 3, gpePartial (fun y => φ (t, y)) x j *
        gpePartial (fun y => gpePartial (fun z => φ (t, z)) y i) x j := by
  let P (p : GpeSpacetime) (j : Fin 3) := fderiv ℝ φ p (gpeSpatialAxis j)
  let D (j : Fin 3) :=
    (ContinuousLinearMap.apply ℝ ℝ (gpeSpatialAxis j)).comp (fderiv ℝ (fderiv ℝ φ) (t, x))
  have h₁ := hφ.differentiable (by norm_num)
  have h₂ := (hφ.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hD (j : Fin 3) : HasFDerivAt (fun p => P p j) (D j) (t, x) :=
    hasFDerivAt_gpeDirectional (h₂ (t, x)) (gpeSpatialAxis j)
  have hP (y : GpeSpace) (j : Fin 3) :
      gpePartial (fun z => φ (t, z)) y j = P (t, y) j :=
    gpePartial_slice_eq_fderiv (h₁ (t, y)) j
  have hInner (j : Fin 3) :
      gpePartial (fun y => gpePartial (fun z => φ (t, z)) y i) x j = D i (gpeSpatialAxis j) := by
    simp_rw [hP]
    rw [gpePartial_slice_eq_fderiv (hD i).differentiableAt, (hD i).fderiv]
  have hSquared : (fun y => gpeGradDot (fun z => φ (t, z)) (fun z => φ (t, z)) y) =
      fun y => ∑ j : Fin 3, P (t, y) j * P (t, y) j := by
    funext y
    simp only [gpeGradDot, hP]
  have hSum := HasFDerivAt.fun_sum (u := Finset.univ) (fun j _ => (hD j).fun_mul (hD j))
  have hSwap (j : Fin 3) : D j (gpeSpatialAxis i) = D i (gpeSpatialAxis j) := by
    have hs := (hφ.contDiffAt (x := (t, x))).isSymmSndFDerivAt (by simp)
      (gpeSpatialAxis i) (gpeSpatialAxis j)
    simpa only [D, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply] using hs
  rw [hSquared, gpePartial_slice_eq_fderiv hSum.differentiableAt, hSum.fderiv]
  simp_rw [hInner, hP]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul, hSwap, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end Qatlib.Papers.SuperfluidHel18.Madelung
