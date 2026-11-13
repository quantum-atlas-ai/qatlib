/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Smooth Function Gradient Readout

This module connects the finite-grid gradient construction of [Jordan2005Gradient] to twice
continuously differentiable real functions on Euclidean space. A global Hessian norm bound `H`
controls the Taylor remainder at `gradientGridOffset`, so the scaled phase differs from its
affine gradient model by at most `M*H*h*d/8`.

`gradient_smooth_function_actual_consumer` gives simultaneous signed-coordinate accuracy with
probability at least `1 - 16*d/(M*w) - pi*M*H*h*d/2`, subject to the stated coordinate and
window bounds. Affine and rank-one quadratic functions supply explicit consumers with one phase
query and `2*d` coordinate Fourier gates.

## Main statements

- `gradient_second_derivative_remainder` gives the second-order Taylor bound.
- `gradient_smooth_phase_remainder` bounds the sampled phase error.
- `gradient_smooth_function_actual_consumer` gives the signed gradient window guarantee.
* `gradient_affine_function_consumer` and `gradient_quadratic_function_consumer` instantiate
  that guarantee.

## References

* [Jordan, 2005][Jordan2005Gradient], *Fast Quantum Algorithm for Numerical Gradient
  Estimation*.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout

namespace Qatlib.Concepts.SignalPrimitive.GridGradient

open scoped Classical BigOperators

/-- A twice continuously differentiable function with Hessian norm bounded by `H` has
first-order Taylor remainder at most `H*‖v‖^2/2`, providing a rigorous remainder bound for
the local gradient model of [Jordan2005Gradient]. -/
theorem gradient_second_derivative_remainder (d : ℕ)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x v : EuclideanSpace ℝ (Fin d)) (H : ℝ)
    (hf : ContDiff ℝ 2 f) (_hH : 0 ≤ H)
    (hessian : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) :
    |f (x+v)-f x-(fderiv ℝ f x) v| ≤ H*‖v‖^2/2 := by
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  have hddf : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have hLip (y : EuclideanSpace ℝ (Fin d)) :
      ‖fderiv ℝ f y - fderiv ℝ f x‖ ≤ H * ‖y-x‖ :=
    Convex.norm_image_sub_le_of_norm_fderiv_le (fun z _ => hddf z)
      (fun z _ => hessian z) (convex_univ : Convex ℝ (Set.univ : Set _))
      (Set.mem_univ x) (Set.mem_univ y)
  let r : ℝ → ℝ := fun t => f (x+t•v)-f x-t*((fderiv ℝ f x) v)
  let r' : ℝ → ℝ := fun t => (fderiv ℝ f (x+t•v)) v - (fderiv ℝ f x) v
  have hr (t : ℝ) : HasDerivAt r (r' t) t := by
    have hline : HasDerivAt (fun t : ℝ => x+t•v) v t := by
      simpa only [Pi.add_apply, zero_add, one_smul] using!
        (hasDerivAt_const t x).add ((hasDerivAt_id t).smul_const v)
    simpa [r, r', smul_eq_mul] using!
      (((hdf (x+t•v)).hasFDerivAt.comp_hasDerivAt t hline).sub_const (f x)).sub
        ((hasDerivAt_id t).mul_const ((fderiv ℝ f x) v))
  have hbound (t : ℝ) (ht : t ∈ Set.Ico (0 : ℝ) 1) :
      ‖r' t‖ ≤ H*‖v‖^2*t := by
    calc
      ‖r' t‖ = ‖(fderiv ℝ f (x+t•v) - fderiv ℝ f x) v‖ := rfl
      _ ≤ ‖fderiv ℝ f (x+t•v) - fderiv ℝ f x‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ (H * ‖x+t•v-x‖) * ‖v‖ :=
        mul_le_mul_of_nonneg_right (hLip _) (norm_nonneg _)
      _ = H*‖v‖^2*t := by
        rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht.1]
        ring
  have hquad (t : ℝ) : HasDerivAt (fun t : ℝ => H*‖v‖^2*t^2/2)
      (H*‖v‖^2*t) t := by
    convert! (((hasDerivAt_id t).pow 2).const_mul (H*‖v‖^2)).div_const 2 using 1
    simp only [id_eq]
    ring
  have hresult := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun t _ => (hr t).continuousAt.continuousWithinAt)
    (fun t _ => (hr t).hasDerivWithinAt)
    (B := fun t : ℝ => H*‖v‖^2*t^2/2)
    (by simp [r]) hquad hbound (show (1 : ℝ) ∈ Set.Icc 0 1 by constructor <;> norm_num)
  simpa [r, Real.norm_eq_abs] using! hresult

/-- The centered Euclidean grid offset with coordinate `h*((z j).val/M - 1/2)`. -/
noncomputable def gradientGridOffset (d M : ℕ) (h : ℝ) (z : GradientGrid d M) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 (fun j => h*((z j).val/(M:ℝ)-1/2))

/-- For positive `M`, the squared Euclidean norm of a centered grid offset is at most `d*h^2/4`. -/
theorem gradient_grid_offset_norm_sq (d M : ℕ) (hM : 0 < M) (h : ℝ)
    (z : GradientGrid d M) : ‖gradientGridOffset d M h z‖^2 ≤ (d:ℝ)*h^2/4 := by
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  rw [EuclideanSpace.norm_sq_eq]
  calc
    _ ≤ ∑ _j : Fin d, h^2/4 := by
      apply Finset.sum_le_sum
      intro j _
      have hlo : 0 ≤ (z j).val/(M:ℝ) := by positivity
      have hhi : (z j).val/(M:ℝ) ≤ 1 := by
        apply (div_le_one hMr).mpr
        exact_mod_cast (z j).isLt.le
      have hs : ((z j).val/(M:ℝ)-1/2)^2 ≤ 1/4 := by nlinarith
      simp only [gradientGridOffset, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow]
      nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg h)]
    _ = (d:ℝ)*h^2/4 := by simp; ring

/-- A continuous real linear functional evaluates a coordinate vector as the sum of its
coordinates times its values on the standard basis vectors. -/
theorem gradient_linear_coordinates (d : ℕ)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (a : Fin d → ℝ) :
    L (WithLp.toLp 2 a) = ∑ j : Fin d, a j * L (EuclideanSpace.single j 1) := by
  have he : WithLp.toLp 2 a = ∑ j : Fin d, a j • EuclideanSpace.single j 1 := by
    apply WithLp.ofLp_injective
    funext i
    simp only [WithLp.ofLp_sum, Finset.sum_apply, WithLp.ofLp_smul,
      Pi.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
    simp
  rw [he, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp

/-- For positive `M` and `h`, a twice continuously differentiable function with Hessian norm
bounded by nonnegative `H` has scaled grid phase error at most `M*H*h*d/8` relative to the
affine model formed from its derivative at `x`. -/
theorem gradient_smooth_phase_remainder (d M : ℕ) (hM : 0 < M)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (H h : ℝ)
    (hf : ContDiff ℝ 2 f) (hH : 0 ≤ H)
    (hessian : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H) (hh : 0 < h)
    (z : GradientGrid d M) :
    let g := fun j : Fin d => (fderiv ℝ f x) (EuclideanSpace.single j 1)
    |(M:ℝ)/h*f (x+gradientGridOffset d M h z) -
      ((M:ℝ)/h*f x-(M:ℝ)/2*∑ j : Fin d, g j +
        ∑ j : Fin d, g j*(z j).val)| ≤ (M:ℝ)*H*h*(d:ℝ)/8 := by
  intro g
  have hMr : 0 < (M:ℝ) := by exact_mod_cast hM
  have hlinear : (fderiv ℝ f x) (gradientGridOffset d M h z) =
      ∑ j : Fin d, h*((z j).val/(M:ℝ)-1/2)*g j :=
    gradient_linear_coordinates d _ _
  have heq : (M:ℝ)/h*f (x+gradientGridOffset d M h z) -
      ((M:ℝ)/h*f x-(M:ℝ)/2*∑ j : Fin d, g j + ∑ j : Fin d, g j*(z j).val) =
      (M:ℝ)/h*(f (x+gradientGridOffset d M h z)-f x-
        (fderiv ℝ f x) (gradientGridOffset d M h z)) := by
    rw [hlinear]
    have hterm (j : Fin d) : (M:ℝ)/h*(h*((z j).val/(M:ℝ)-1/2)*g j) =
        g j*(z j).val-(M:ℝ)/2*g j := by field_simp
    have hsum : (M:ℝ)/h*(∑ j : Fin d, h*((z j).val/(M:ℝ)-1/2)*g j) =
        (∑ j : Fin d, g j*(z j).val) - (M:ℝ)/2*(∑ j : Fin d, g j) := by
      rw [Finset.mul_sum]
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [mul_sub, mul_sub, hsum]
    ring
  rw [heq, abs_mul, abs_of_pos (div_pos hMr hh)]
  calc
    _ ≤ (M:ℝ)/h*(H*‖gradientGridOffset d M h z‖^2/2) :=
      mul_le_mul_of_nonneg_left
        (gradient_second_derivative_remainder d f x _ H hf hH hessian) (by positivity)
    _ ≤ (M:ℝ)/h*(H*((d:ℝ)*h^2/4)/2) := by
      gcongr
      exact gradient_grid_offset_norm_sq d M hM h z
    _ = (M:ℝ)*H*h*(d:ℝ)/8 := by field_simp; ring

/-- Under the smoothness, Hessian, coordinate, and window hypotheses, the signed-gradient event
probability for the sampled function phase is at least the affine circular-window
probability minus `pi*M*H*h*d/2`. -/
theorem gradient_smooth_function_event_transport (d M : ℕ) (hM : 0 < M)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (H h w : ℝ)
    (hf : ContDiff ℝ 2 f) (hH : 0 ≤ H)
    (hessian : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hh : 0 < h) (hw : w ≤ 1/8) :
    let g := fun j : Fin d => (fderiv ℝ f x) (EuclideanSpace.single j 1)
    (∀ j, |g j| ≤ 1/4) →
    let φ := fun z : GradientGrid d M => (M:ℝ)/h*f (x+
      WithLp.toLp 2 (fun j : Fin d => h*((z j).val/(M:ℝ)-1/2)))
    let c := (M:ℝ)/h*f x-(M:ℝ)/2*∑ j : Fin d, g j
    MeasureProb (gradientReadout d M hM φ)
      (Finset.univ.filter (fun z => ∀ j : Fin d, |signedGridValue M (z j)-g j| ≤ w)) ≥
      MeasureProb (gradientReadout d M hM (fun z => c+∑ j : Fin d, g j*(z j).val))
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val/(M:ℝ)) (g j) ≤ w)) - Real.pi*(M:ℝ)*H*h*(d:ℝ)/2 := by
  intro g hg φ c
  let S := Finset.univ.filter (fun z : GradientGrid d M => ∀ j : Fin d,
    phaseDistance ((z j).val/(M:ℝ)) (g j) ≤ w)
  have he := gradient_actual_phase_event_error d M hM φ
    (fun z => c+∑ j : Fin d, g j*(z j).val) ((M:ℝ)*H*h*(d:ℝ)/8)
    (by positivity) (fun z => gradient_smooth_phase_remainder d M hM f x H h
      hf hH hessian hh z) S
  have hsubset : S ⊆ Finset.univ.filter (fun z : GradientGrid d M =>
      ∀ j : Fin d, |signedGridValue M (z j)-g j| ≤ w) := by
    intro z hz
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, fun j => ?_⟩
    exact gradient_signed_decode_window M hM (z j) (g j) w (hg j) hw
      ((Finset.mem_filter.mp hz).2 j)
  have hmono := measureProb_mono (gradientReadout d M hM φ) hsubset
  have hlo := (abs_le.mp he).1
  dsimp [S] at hlo hmono
  nlinarith

/-- For a twice continuously differentiable function with Hessian norm bounded by nonnegative
`H`, gradient coordinates bounded by `1/4`, positive `h`, `M ≥ 2`, and `0 < w ≤ 1/8`,
signed-coordinate readout succeeds jointly with probability at least `1 - 16*d/(M*w) -
pi*M*H*h*d/2`, quantifying the finite-grid method of [Jordan2005Gradient]. -/
theorem gradient_smooth_function_actual_consumer (d M : ℕ) (hM : 0 < M)
    (f : EuclideanSpace ℝ (Fin d) → ℝ) (x : EuclideanSpace ℝ (Fin d)) (H h w : ℝ)
    (hf : ContDiff ℝ 2 f) (hH : 0 ≤ H)
    (hessian : ∀ y, ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ H)
    (hM2 : 2 ≤ M) (hh : 0 < h) (hw0 : 0 < w) (hw : w ≤ 1/8) :
    let g := fun j : Fin d => (fderiv ℝ f x) (EuclideanSpace.single j 1)
    (∀ j, |g j| ≤ 1/4) →
    let φ := fun z : GradientGrid d M => (M:ℝ)/h*f (x+
      WithLp.toLp 2 (fun j : Fin d => h*((z j).val/(M:ℝ)-1/2)))
    MeasureProb (gradientReadout d M hM φ)
      (Finset.univ.filter (fun z => ∀ j : Fin d, |signedGridValue M (z j)-g j| ≤ w)) ≥
      1-16*(d:ℝ)/((M:ℝ)*w)-Real.pi*(M:ℝ)*H*h*(d:ℝ)/2 := by
  intro g hg φ
  have he := gradient_smooth_function_event_transport d M hM f x H h w
    hf hH hessian hh hw hg
  have hi := gradient_offgrid_joint_window d M hM g
    ((M:ℝ)/h*f x-(M:ℝ)/2*∑ j : Fin d, g j) w hM2 hw0
  linarith

/-- For an affine function with derivative coordinates bounded by `1/4`, the signed gradient
window has probability at least `1 - 16*d/(M*w)` under the stated positive scale and window
hypotheses. The circuit uses one phase query and `2*d` coordinate Fourier gates. -/
theorem gradient_affine_function_consumer (d M : ℕ) (hM : 0 < M)
    (L : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (c : ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (h w : ℝ)
    (hM2 : 2 ≤ M) (hh : 0 < h) (hw0 : 0 < w) (hw : w ≤ 1/8)
    (hg : ∀ j : Fin d, |L (EuclideanSpace.single j 1)| ≤ 1/4) :
    MeasureProb (gradientReadout d M hM (fun z => (M:ℝ)/h*
      (c+L (x+gradientGridOffset d M h z))))
      (Finset.univ.filter (fun z => ∀ j : Fin d,
        |signedGridValue M (z j)-L (EuclideanSpace.single j 1)| ≤ w)) ≥
      1-16*(d:ℝ)/((M:ℝ)*w) ∧
      QueryCount (gradientWord d M) = 1 ∧ GateCount (gradientWord d M) = 2*d := by
  have hder : fderiv ℝ (fun y => c+L y) = fun _ => L := by
    funext y
    rw [fderiv_const_add]
    exact L.hasFDerivAt.fderiv
  have hessian (y : EuclideanSpace ℝ (Fin d)) :
      ‖fderiv ℝ (fderiv ℝ (fun y => c+L y)) y‖ ≤ 0 := by
    rw [hder, fderiv_fun_const]
    exact ContinuousLinearMap.opNorm_zero.le
  have he := gradient_smooth_function_actual_consumer d M hM (fun y => c+L y)
    x 0 h w (contDiff_const.add L.contDiff) le_rfl hessian hM2 hh hw0 hw
  simp only [hder] at he
  have hprob := he hg
  simp only [zero_mul, mul_zero, zero_div, sub_zero] at hprob
  exact ⟨hprob, (gradient_coordinate_qft_word_unitarity d M hM).2⟩

/-- The rank-one quadratic function `c + L y + (a/2)*(K y)^2`. -/
noncomputable def gradientQuadraticFunction (d : ℕ) (c a : ℝ)
    (L K : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (y : EuclideanSpace ℝ (Fin d)) : ℝ :=
  c+L y+a/2*(K y)^2

/-- The derivative of `gradientQuadraticFunction` at `y` is the linear functional `L + (a*K y) •
K`. -/
theorem gradient_quadratic_fderiv (d : ℕ) (c a : ℝ)
    (L K : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    fderiv ℝ (gradientQuadraticFunction d c a L K) y = L+(a*K y)•K := by
  have hd := ((hasFDerivAt_const c y).add L.hasFDerivAt).add
    ((K.hasFDerivAt.pow 2).const_mul (a/2))
  have he : HasFDerivAt (gradientQuadraticFunction d c a L K) (L+(a*K y)•K) y := by
    convert! hd using 1
    ext v
    simp only [ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, zero_add, Nat.reduceSub, pow_one,
      two_smul]
    ring
  exact he.fderiv

/-- The Hessian operator norm of the rank-one quadratic function is bounded by `|a|*‖K‖^2` at
every point. -/
theorem gradient_quadratic_hessian (d : ℕ) (c a : ℝ)
    (L K : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ) (y : EuclideanSpace ℝ (Fin d)) :
    ‖fderiv ℝ (fderiv ℝ (gradientQuadraticFunction d c a L K)) y‖ ≤ |a| * ‖K‖^2 := by
  have hder : fderiv ℝ (gradientQuadraticFunction d c a L K) =
      fun y => L+(a*K y)•K := by
    funext z
    exact gradient_quadratic_fderiv d c a L K z
  rw [hder]
  have hd := (hasFDerivAt_const L y).add ((K.hasFDerivAt.const_mul a).smul_const K)
  have he : HasFDerivAt (fun z => L+(a*K z)•K) (a•K.smulRight K) y := by
    convert! hd using 1
    ext v u
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul,
      zero_add]
    ring
  rw [he.fderiv]
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro v
  have hev : (a•K.smulRight K) v = (a*K v)•K := by
    ext u
    simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
    ring
  rw [hev]
  calc
    _ ≤ ‖a*K v‖*‖K‖ := ContinuousLinearMap.opNorm_smul_le _ _
    _ = |a| * ‖K v‖*‖K‖ := by rw [norm_mul, Real.norm_eq_abs]
    _ ≤ |a| * (‖K‖*‖v‖)*‖K‖ := by
      gcongr
      exact K.le_opNorm v
    _ = (|a| * ‖K‖^2)*‖v‖ := by ring

/-- For the rank-one quadratic function, the stated coordinate and window bounds give
simultaneous gradient accuracy with probability at least `1 - 16*d/(M*w) -
pi*M*(|a|*‖K‖^2)*h*d/2`, instantiating the quadratic local model of [Jordan2005Gradient].
The same circuit uses one phase query and `2*d` coordinate Fourier gates. -/
theorem gradient_quadratic_function_consumer (d M : ℕ) (hM : 0 < M)
    (c a : ℝ) (L K : EuclideanSpace ℝ (Fin d) →L[ℝ] ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (h w : ℝ)
    (hM2 : 2 ≤ M) (hh : 0 < h) (hw0 : 0 < w) (hw : w ≤ 1/8)
    (hg : ∀ j : Fin d,
      |L (EuclideanSpace.single j 1)+a*K x*K (EuclideanSpace.single j 1)| ≤ 1/4) :
    MeasureProb (gradientReadout d M hM (fun z => (M:ℝ)/h*
      gradientQuadraticFunction d c a L K (x+gradientGridOffset d M h z)))
      (Finset.univ.filter (fun z => ∀ j : Fin d,
        |signedGridValue M (z j)-
          (L (EuclideanSpace.single j 1)+a*K x*K (EuclideanSpace.single j 1))| ≤ w)) ≥
      1-16*(d:ℝ)/((M:ℝ)*w)-Real.pi*(M:ℝ)*(|a| * ‖K‖^2)*h*(d:ℝ)/2 ∧
      QueryCount (gradientWord d M) = 1 ∧ GateCount (gradientWord d M) = 2*d := by
  have hf : ContDiff ℝ 2 (gradientQuadraticFunction d c a L K) :=
    (contDiff_const.add L.contDiff).add (contDiff_const.mul (K.contDiff.pow 2))
  have hessian (y : EuclideanSpace ℝ (Fin d)) :
      ‖fderiv ℝ (fderiv ℝ (gradientQuadraticFunction d c a L K)) y‖ ≤ |a| * ‖K‖^2 :=
    gradient_quadratic_hessian d c a L K y
  have he := gradient_smooth_function_actual_consumer d M hM
    (gradientQuadraticFunction d c a L K) x (|a| * ‖K‖^2) h w hf (by positivity)
      hessian hM2 hh hw0 hw
  simp only [gradient_quadratic_fderiv, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul] at he
  exact ⟨he hg, (gradient_coordinate_qft_word_unitarity d M hM).2⟩

end Qatlib.Concepts.SignalPrimitive.GridGradient
