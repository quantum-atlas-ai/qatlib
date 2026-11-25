/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnotLight13.TorusFamily.BatemanPotential

import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The exact Bateman ray Jacobian

[Kedia2013TyingKnots], equations (5) and (6),
[DOI](https://doi.org/10.1103/physrevlett.111.150404).
The spatial Jacobian of the straight-ray map equals the squared
complex multiplier of the Bateman denominator along the ray.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnotLight13.TorusFamily

/-- The spatial ray differential on an arbitrary physical increment. -/
private theorem fderiv_batemanRay_apply (t x y z u₁ u₂ u₃ : ℝ) :
    let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
    let l := 2 * t / d
    let l' := -(2 * l / d) * (x * u₁ + y * u₂ + z * u₃)
    fderiv ℝ (batemanRay t) (x, y, z) (u₁, u₂, u₃) =
      (u₁ + l' * (y - z * x) + l * (u₂ - (u₃ * x + z * u₁)),
       u₂ - l' * (x + z * y) - l * (u₁ + u₃ * y + z * u₂),
       u₃ - l' * (z ^ 2 + 1) - l * (2 * z * u₃)) := by
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let l := 2 * t / d
  let l' := -(2 * l / d) * (x * u₁ + y * u₂ + z * u₃)
  let X (h : ℝ) := x + h * u₁
  let Y (h : ℝ) := y + h * u₂
  let Z (h : ℝ) := z + h * u₃
  let L (h : ℝ) := 2 * t / (X h ^ 2 + Y h ^ 2 + Z h ^ 2 + 1)
  have hX : HasDerivAt X u₁ 0 := by
    simpa only [X, id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const u₁).const_add x
  have hY : HasDerivAt Y u₂ 0 := by
    simpa only [Y, id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const u₂).const_add y
  have hZ : HasDerivAt Z u₃ 0 := by
    simpa only [Z, id_eq, one_mul] using ((hasDerivAt_id (0 : ℝ)).mul_const u₃).const_add z
  have hx : X 0 = x := by simp [X]
  have hy : Y 0 = y := by simp [Y]
  have hz : Z 0 = z := by simp [Z]
  have hd : 0 < d := by dsimp only [d]; positivity
  have hL : HasDerivAt L l' 0 := by
    have hD := (((hX.fun_pow 2).fun_add (hY.fun_pow 2)).fun_add (hZ.fun_pow 2)).add_const 1
    have hD₀ : X 0 ^ 2 + Y 0 ^ 2 + Z 0 ^ 2 + 1 ≠ 0 := by rw [hx, hy, hz]; exact hd.ne'
    refine ((hasDerivAt_const 0 (2 * t)).fun_div hD hD₀).congr_deriv ?_
    simp only [hx, hy, hz, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one, zero_mul, zero_sub]
    change (-(2 * t * (2 * x * u₁ + 2 * y * u₂ + 2 * z * u₃))) / d ^ 2 = l'
    dsimp only [l', l]
    field_simp [hd.ne']
  have hL₀ : L 0 = l := by simp only [L, hx, hy, hz]; rfl
  have hline := hX.prodMk (hY.prodMk hZ)
  have h := (hX.fun_add (hL.fun_mul (hY.fun_sub (hZ.fun_mul hX)))).prodMk
    ((hY.fun_sub (hL.fun_mul (hX.fun_add (hZ.fun_mul hY)))).prodMk
      ((hZ.add_const t).fun_sub (hL.fun_mul ((hZ.fun_pow 2).add_const 1))))
  have hRay := (contDiff_bateman_ray t).differentiable (by simp) (x, y, z)
  have hAt := hRay.hasFDerivAt.comp_hasDerivAt_of_eq 0 hline (by simp only [hx, hy, hz])
  have h' := h.deriv
  change deriv (fun a => batemanRay t (X a, Y a, Z a)) 0 = _ at h'
  have hAt' := hAt.deriv
  change deriv (fun a => batemanRay t (X a, Y a, Z a)) 0 = _ at hAt'
  rw [hAt'] at h'
  simp only [hL₀, hx, hy, hz, Nat.cast_ofNat, Nat.reduceSubDiff, pow_one] at h'
  change fderiv ℝ (batemanRay t) (x, y, z) (u₁, u₂, u₃) = _
  rw [h']
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> ring

/-- The physical ray Jacobian is the squared norm of the common
complex multiplier from the rational Bateman pair. -/
theorem det_batemanRay_eq_normSq_multiplier (t : ℝ) (s : ℝ × ℝ × ℝ) :
    LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap =
      Complex.normSq (batemanRayMultiplier t s) := by
  rcases s with ⟨x, y, z⟩
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let l := 2 * t / d
  have hd : 0 < d := by dsimp only [d]; positivity
  rw [← LinearMap.det_toMatrix batemanCartesianBasis]
  rw [Matrix.det_fin_three]
  simp only [LinearMap.toMatrix_apply, batemanCartesianBasis_apply, ContinuousLinearMap.coe_coe,
    batemanAxis, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, fderiv_batemanRay_apply, batemanCartesianBasis_repr]
  simp only [batemanRayMultiplier, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, one_mul, add_zero, zero_add, sub_zero]
  change _ = (1 - z * l) * (1 - z * l) + l * l
  dsimp only [d] at hd
  dsimp only [l, d]
  field_simp [show x ^ 2 + y ^ 2 + z ^ 2 + 1 ≠ 0 from hd.ne']
  ring

/-- The same Jacobian is the ratio of quadratic axial weights at the
retarded image point and at the initial point. -/
theorem det_batemanRay_eq_axialRatio (t : ℝ) (s : ℝ × ℝ × ℝ) :
    LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap =
      (1 + ((batemanRay t s).2.2 - t) ^ 2) / (1 + s.2.2 ^ 2) := by
  have hnorm (z τ : ℝ) : Complex.normSq (alphaCommonFactor z τ) = 1 + (z - τ) ^ 2 := by
    simp [alphaCommonFactor, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
    ring
  have h := congrArg Complex.normSq (batemanRay_factors t s).2.1
  rw [Complex.normSq_mul, hnorm, hnorm, sub_zero] at h
  rw [det_batemanRay_eq_normSq_multiplier, eq_div_iff (by positivity)]
  rw [mul_comm, ← h]

/-- For a fixed physical slice, the spatial Jacobian is bounded above
and away from zero uniformly on all of physical space. -/
theorem det_batemanRay_uniform_bounds (t : ℝ) (s : ℝ × ℝ × ℝ) :
    (2 + 8 * t ^ 2)⁻¹ ≤ LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap ∧
      LinearMap.det (fderiv ℝ (batemanRay t) s).toLinearMap ≤ 2 + 8 * t ^ 2 := by
  rcases s with ⟨x, y, z⟩
  let u := (batemanRay t (x, y, z)).2.2 - t
  let d := x ^ 2 + y ^ 2 + z ^ 2 + 1
  let k := 2 + 8 * t ^ 2
  have hd : 0 < d := by unfold d; positivity
  have hk : 0 < k := by unfold k; positivity
  have hfrac₀ : 0 ≤ (z ^ 2 + 1) / d := by positivity
  have hfrac₁ : (z ^ 2 + 1) / d ≤ 1 := by
    rw [div_le_one hd]
    unfold d
    linarith [sq_nonneg x, sq_nonneg y]
  have hshift : (u - z) ^ 2 ≤ 4 * t ^ 2 := by
    have h : u - z = (-2 * t) * ((z ^ 2 + 1) / d) := by
      change z + t - (2 * t / d) * (z ^ 2 + 1) - t - z = _
      ring
    rw [h, mul_pow]
    calc
      _ ≤ (-2 * t) ^ 2 * 1 :=
        mul_le_mul_of_nonneg_left (by simpa using pow_le_pow_left₀ hfrac₀ hfrac₁ 2) (sq_nonneg _)
      _ = _ := by ring
  have hcontrol (a b : ℝ) (h : (a - b) ^ 2 ≤ 4 * t ^ 2) : 1 + a ^ 2 ≤ k * (1 + b ^ 2) := by
    have hsq : a ^ 2 ≤ 2 * b ^ 2 + 2 * (a - b) ^ 2 := by
      nlinarith [sq_nonneg (a - 2 * b)]
    unfold k
    nlinarith [mul_nonneg (sq_nonneg t) (sq_nonneg b)]
  rw [det_batemanRay_eq_axialRatio]
  change k⁻¹ ≤ (1 + u ^ 2) / (1 + z ^ 2) ∧ (1 + u ^ 2) / (1 + z ^ 2) ≤ k
  constructor
  · rw [← one_div, div_le_div_iff₀ hk (by positivity), one_mul]
    have h : (z - u) ^ 2 ≤ 4 * t ^ 2 := by nlinarith [hshift]
    simpa only [mul_comm] using hcontrol z u h
  · rw [div_le_iff₀ (by positivity)]
    exact hcontrol u z hshift

end Qatlib.Papers.KnotLight13.TorusFamily
