/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.SuperfluidHel18.CenterlineCL.GaussDirection

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The closed spherical area density in three Cartesian parameters

For a twice differentiable map to the unit sphere, the three oriented
area components form a divergence-free flux. The mixed derivatives
cancel in pairs and the remaining scalar triple products of tangent
vectors vanish. Applied to a family of Gauss maps, the third flux
component is the area density in the two curve parameters.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.SuperfluidHel18.CenterlineCL

open Qatlib.Papers.KnottedLight08.HopfField (dot3 cross3)

local notation "Vec" => (Fin 3 → ℝ)
local notation "e" => (fun i : Fin 3 => (Pi.single i (1 : ℝ) : Vec))

/-- The Cartesian partial of a map in the indicated coordinate direction. -/
noncomputable def gaussMapPartial (n : Vec → Vec) (x : Vec) (i : Fin 3) : Vec :=
  fderiv ℝ n x (e i)

/-- The oriented spherical areas of the three pairs of Cartesian partials.
The last component uses the second parameter followed by the first, as
in `gaussDirection_area_density`. -/
noncomputable def gaussAreaFlux (n : Vec → Vec) (x : Vec) : Vec :=
  let d := gaussMapPartial n x
  ![dot3 (cross3 (d 2) (d 1)) (n x), dot3 (cross3 (d 0) (d 2)) (n x),
    dot3 (cross3 (d 1) (d 0)) (n x)]

/-- Coordinate evaluation commutes with a derivative into a Cartesian vector. -/
private theorem derivative_coord {f : ℝ → Vec} {v : Vec} {t : ℝ}
    (h : HasDerivAt f v t) (i : Fin 3) :
    HasDerivAt (fun s => f s i) (v i) t := by
  let p : Vec →L[ℝ] ℝ := ContinuousLinearMap.proj i
  change HasDerivAt (p ∘ f) (p v) t
  exact p.hasFDerivAt.comp_hasDerivAt t h

/-- The scalar derivative of a Cartesian dot product satisfies the product rule. -/
private theorem derivative_dot {f g : ℝ → Vec} {u v : Vec} {t : ℝ}
    (hf : HasDerivAt f u t) (hg : HasDerivAt g v t) :
    HasDerivAt (fun s => dot3 (f s) (g s)) (dot3 u (g t) + dot3 (f t) v) t := by
  have h i := (derivative_coord hf i).fun_mul (derivative_coord hg i)
  exact ((h 0).fun_add (h 1) |>.fun_add (h 2)).congr_deriv (by
    simp only [dot3]
    ring)

/-- Along a real parameter the cross product also obeys its bilinear product rule. -/
private theorem derivative_cross {f g : ℝ → Vec} {u v : Vec} {t : ℝ}
    (hf : HasDerivAt f u t) (hg : HasDerivAt g v t) :
    HasDerivAt (fun s => cross3 (f s) (g s)) (cross3 u (g t) + cross3 (f t) v) t := by
  have h i j := (derivative_coord hf i).fun_mul (derivative_coord hg j)
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact ((h 1 2).fun_sub (h 2 1)).congr_deriv (by
      simp [cross3, Pi.add_apply]
      ring)
  · exact ((h 2 0).fun_sub (h 0 2)).congr_deriv (by
      simp [cross3, Pi.add_apply]
      ring)
  · exact ((h 0 1).fun_sub (h 1 0)).congr_deriv (by
      simp [cross3, Pi.add_apply]
      ring)

/-- The derivative of an affine line is its direction vector. -/
private theorem derivative_line (x v : Vec) :
    HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
  simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x

/-- An ambient derivative evaluated on a vector is the derivative
along the affine line in that direction. -/
private theorem derivative_along_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec → E} {x v : Vec} (hf : DifferentiableAt ℝ f x) :
    HasDerivAt (fun t : ℝ => f (x + t • v)) (fderiv ℝ f x v) 0 :=
  hf.hasFDerivAt.comp_hasDerivAt_of_eq 0 (derivative_line x v) (by simp)

/-- Every Cartesian partial of a unit-sphere-valued map is tangent to its sphere. -/
private theorem gauss_partial_tangent {n : Vec → Vec} {x : Vec}
    (hn : DifferentiableAt ℝ n x) (hu : ∀ y, dot3 (n y) (n y) = 1) (i : Fin 3) :
    dot3 (n x) (gaussMapPartial n x i) = 0 := by
  have h := derivative_along_line (v := e i) hn
  have ht := (derivative_dot h h).deriv
  have heq : (fun t : ℝ => dot3 (n (x + t • e i)) (n (x + t • e i))) = fun _ => 1 :=
    funext fun _ => hu _
  rw [heq, deriv_const] at ht
  simp only [zero_smul, add_zero] at ht
  have hc : dot3 (gaussMapPartial n x i) (n x) = dot3 (n x) (gaussMapPartial n x i) := by
    simp only [dot3]
    ring
  change 0 = dot3 (gaussMapPartial n x i) (n x) + dot3 (n x) (gaussMapPartial n x i) at ht
  rw [hc] at ht
  linarith only [ht]

/-- The full area flux is differentiable for a twice continuously
differentiable map. -/
theorem differentiable_gaussAreaFlux {n : Vec → Vec} (hn : ContDiff ℝ 2 n) :
    Differentiable ℝ (gaussAreaFlux n) := by
  have hd := (hn.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hProj (i : Fin 3) : Differentiable ℝ (fun p : Vec => p i) :=
    (show Vec →L[ℝ] ℝ from ContinuousLinearMap.proj i).differentiable
  have hN (i : Fin 3) : Differentiable ℝ (fun x => n x i) :=
    (hProj i).comp (hn.differentiable (by norm_num))
  have hD (i j : Fin 3) : Differentiable ℝ (fun x => gaussMapPartial n x i j) :=
    (hProj j).comp ((ContinuousLinearMap.apply ℝ Vec (e i)).differentiable.comp hd)
  rw [differentiable_pi]
  intro i
  unfold gaussAreaFlux
  fin_cases i <;> simp [dot3, cross3] <;> fun_prop

/-- A twice continuously differentiable unit-sphere map has zero divergence
of its oriented area flux in the three Cartesian parameters. -/
theorem gaussAreaFlux_divergence {n : Vec → Vec} (hn : ContDiff ℝ 2 n)
    (hu : ∀ y, dot3 (n y) (n y) = 1) (x : Vec) :
    (∑ i : Fin 3, fderiv ℝ (fun y => gaussAreaFlux n y i) x (e i)) = 0 := by
  let D (i : Fin 3) := gaussMapPartial n x i
  let H (i j : Fin 3) := fderiv ℝ (fderiv ℝ n) x (e i) (e j)
  have hN : DifferentiableAt ℝ n x := hn.differentiable (by norm_num) x
  have hH : DifferentiableAt ℝ (fderiv ℝ n) x :=
    (hn.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num) x
  have hLineD (i j : Fin 3) :
      HasDerivAt (fun t : ℝ => gaussMapPartial n (x + t • e i) j) (H i j) 0 :=
    (ContinuousLinearMap.apply ℝ Vec (e j)).hasFDerivAt.comp_hasDerivAt 0
      (derivative_along_line (v := e i) hH)
  have hDiff := differentiable_gaussAreaFlux hn
  have hline (i : Fin 3) :
      deriv (fun t : ℝ => gaussAreaFlux n (x + t • e i) i) 0 =
        fderiv ℝ (fun y => gaussAreaFlux n y i) x (e i) :=
    (derivative_along_line
      ((show Vec →L[ℝ] ℝ from ContinuousLinearMap.proj i).differentiable.comp hDiff x)).deriv
  have hArea (i j k : Fin 3) :
      deriv (fun t : ℝ => dot3 (cross3 (gaussMapPartial n (x + t • e i) j)
        (gaussMapPartial n (x + t • e i) k)) (n (x + t • e i))) 0 =
        dot3 (cross3 (H i j) (D k) + cross3 (D j) (H i k)) (n x) +
          dot3 (cross3 (D j) (D k)) (D i) := by
    simpa only [zero_smul, add_zero, D, gaussMapPartial] using
      (derivative_dot (derivative_cross (hLineD i j) (hLineD i k))
        (derivative_along_line (v := e i) hN)).deriv
  have hNonzero : n x ≠ 0 := by
    intro h
    have hh := hu x
    rw [h] at hh
    norm_num [dot3] at hh
  have hTriple (i j k : Fin 3) : dot3 (cross3 (D j) (D k)) (D i) = 0 :=
    dot3_cross3_eq_zero hNonzero (gauss_partial_tangent hN hu j)
      (gauss_partial_tangent hN hu k) (gauss_partial_tangent hN hu i)
  have hSym : IsSymmSndFDerivAt ℝ n x :=
    hn.contDiffAt.isSymmSndFDerivAt (by simp)
  have h01 : H 0 1 = H 1 0 := hSym _ _
  have h02 : H 0 2 = H 2 0 := hSym _ _
  have h12 : H 1 2 = H 2 1 := hSym _ _
  rw [Fin.sum_univ_three, ← hline 0, ← hline 1, ← hline 2]
  change deriv (fun t : ℝ => dot3 (cross3 (gaussMapPartial n (x + t • e 0) 2)
      (gaussMapPartial n (x + t • e 0) 1)) (n (x + t • e 0))) 0 +
    deriv (fun t : ℝ => dot3 (cross3 (gaussMapPartial n (x + t • e 1) 0)
      (gaussMapPartial n (x + t • e 1) 2)) (n (x + t • e 1))) 0 +
    deriv (fun t : ℝ => dot3 (cross3 (gaussMapPartial n (x + t • e 2) 1)
      (gaussMapPartial n (x + t • e 2) 0)) (n (x + t • e 2))) 0 = 0
  rw [hArea 0 2 1, hArea 1 0 2, hArea 2 1 0, hTriple 0 2 1, hTriple 1 0 2,
    hTriple 2 1 0, h01, h02, h12]
  simp [dot3, cross3, Pi.add_apply]
  ring

end Qatlib.Papers.SuperfluidHel18.CenterlineCL
