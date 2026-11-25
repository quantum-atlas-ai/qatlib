/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.KnottedLight08.CurlEigenstate.HopfPotentialTime

import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRadialBounds
import Qatlib.Papers.KnottedLight08.CurlEigenstate.CKRegularMode
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity

/-!
# A spatially uniform bound for the Hopf potential

The regular dipole estimates near zero and the elementary sine and cosine
bounds at large radius give one integrable frequency envelope independent
of the Cartesian point and time.
-/

@[expose] public section
set_option autoImplicit false

namespace Qatlib.Papers.KnottedLight08.CurlEigenstate

open MeasureTheory Set

/-- The unregularized magnetic kernel grows at most linearly in its argument. -/
private theorem abs_ckKernel_le (u : ℝ) : |ckKernel u| ≤ 1 + |u| := by
  unfold ckKernel
  calc
    _ ≤ |Real.sin u| + |u * Real.cos u| := abs_sub _ _
    _ ≤ 1 + |u| := by
      rw [abs_mul]
      exact add_le_add (Real.abs_sin_le_one u) (mul_le_of_le_one_right (abs_nonneg u)
        (Real.abs_cos_le_one u))

/-- The dimensionless magnetic radial factor absorbs one angular power. -/
private theorem abs_mul_ckRadialThree_le (u : ℝ) :
    |u| * |ckRadialThree u| ≤ 2 := by
  by_cases hu : |u| ≤ 1
  · calc
      _ ≤ 1 * (1 / 3) :=
        mul_le_mul hu (abs_ckRadialThree_le u) (abs_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  have h₁ : 1 ≤ |u| := le_of_not_ge hu
  have hp : 0 < |u| := lt_of_lt_of_le zero_lt_one h₁
  rw [ckRadialThree, ite_eq_right (abs_pos.mp hp), abs_div, abs_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (pow_pos hp _)).2
  calc
    _ ≤ |u| * (1 + |u|) := mul_le_mul_of_nonneg_left (abs_ckKernel_le u) hp.le
    _ ≤ 2 * |u| ^ 3 := by
      have h₂ := mul_le_mul_of_nonneg_left h₁ hp.le
      have h₃ := mul_le_mul_of_nonneg_left h₂ hp.le
      nlinarith

/-- The dimensionless curl radial factor absorbs two angular powers. -/
private theorem abs_sq_mul_ckRadialFive_le (u : ℝ) :
    |u| ^ 2 * |ckRadialFive u| ≤ 7 := by
  by_cases hu : |u| ≤ 1
  · calc
      _ ≤ 1 ^ 2 * (1 / 15) :=
        mul_le_mul (pow_le_pow_left₀ (abs_nonneg u) hu 2) (abs_ckRadialFive_le u)
          (abs_nonneg _) (by norm_num)
      _ ≤ _ := by norm_num
  have h₁ : 1 ≤ |u| := le_of_not_ge hu
  have hp : 0 < |u| := lt_of_lt_of_le zero_lt_one h₁
  have hkernel : |u ^ 2 * Real.sin u - 3 * ckKernel u| ≤ 7 * |u| ^ 2 := by
    calc
      _ ≤ |u ^ 2 * Real.sin u| + |3 * ckKernel u| := abs_sub _ _
      _ ≤ |u| ^ 2 + 3 * (1 + |u|) := by
        simp only [abs_mul, abs_pow, abs_of_nonneg (show 0 ≤ (3 : ℝ) by norm_num)]
        exact add_le_add (mul_le_of_le_one_right (sq_nonneg _) (Real.abs_sin_le_one u))
          (mul_le_mul_of_nonneg_left (abs_ckKernel_le u) (by norm_num))
      _ ≤ _ := by
        have h₂ := mul_le_mul_of_nonneg_left h₁ hp.le
        nlinarith
  rw [ckRadialFive, ite_eq_right (abs_pos.mp hp), abs_div, abs_pow, ← mul_div_assoc]
  apply (div_le_iff₀ (pow_pos hp _)).2
  calc
    _ ≤ |u| ^ 2 * (7 * |u| ^ 2) := mul_le_mul_of_nonneg_left hkernel (sq_nonneg _)
    _ ≤ 7 * |u| ^ 5 := by
      have h := mul_le_mul_of_nonneg_left h₁ (pow_nonneg hp.le 4)
      nlinarith

/-- Each Cartesian coordinate is bounded in absolute value by the CK radius. -/
private theorem abs_coords_le_radius (x y z : ℝ) :
    |x| ≤ ckRadius x y z ∧ |y| ≤ ckRadius x y z ∧ |z| ≤ ckRadius x y z := by
  unfold ckRadius
  rw [← Real.sqrt_sq_eq_abs x, ← Real.sqrt_sq_eq_abs y, ← Real.sqrt_sq_eq_abs z]
  exact ⟨Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y, sq_nonneg z]),
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x, sq_nonneg z]),
    Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x, sq_nonneg y])⟩

/-- A CK dipole component has a uniform cubic frequency bound. -/
theorem norm_hopfDipoleMode_le_cubic {k : ℝ} (hk : 0 < k) (x y z : ℝ) (j : Fin 3) :
    ‖hopfDipoleMode k x y z j‖ ≤ 26 * k ^ 3 := by
  let r := ckRadius x y z
  let u := k * r
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hu : 0 ≤ u := mul_nonneg hk.le hr
  obtain ⟨hx, hy, hz⟩ := abs_coords_le_radius x y z
  have hA : ‖ckAngular x y z j‖ ≤ 2 * r := by
    fin_cases j
    · simpa [ckAngular, Complex.norm_real, Real.norm_eq_abs] using
        hz.trans (show r ≤ 2 * r by linarith)
    · simpa [ckAngular, norm_mul, Complex.norm_real, Real.norm_eq_abs] using
        hz.trans (show r ≤ 2 * r by linarith)
    · change ‖-((x : ℂ) + Complex.I * (y : ℂ))‖ ≤ 2 * r
      rw [norm_neg]
      exact (norm_add_le _ _).trans (by
        simpa [r, norm_mul, Complex.norm_real, Real.norm_eq_abs, two_mul] using add_le_add hx hy)
  have hB : ‖ckCurlAngular x y z j‖ ≤ 3 * r ^ 2 := by
    have hxy := mul_le_mul hx hy (abs_nonneg _) hr
    have hxz := mul_le_mul hx hz (abs_nonneg _) hr
    have hyz := mul_le_mul hy hz (abs_nonneg _) hr
    have hxx := pow_le_pow_left₀ (abs_nonneg x) hx 2
    have hyy := pow_le_pow_left₀ (abs_nonneg y) hy 2
    have hzz := pow_le_pow_left₀ (abs_nonneg z) hz 2
    have hquad (a b : ℝ) : ‖(a : ℂ) ^ 2 + (b : ℂ) ^ 2‖ ≤ |a| ^ 2 + |b| ^ 2 := by
      calc
        _ ≤ ‖(a : ℂ) ^ 2‖ + ‖(b : ℂ) ^ 2‖ := norm_add_le _ _
        _ = _ := by simp [pow_two, Complex.norm_real, Real.norm_eq_abs]
    fin_cases j
    · change ‖-((x : ℂ) * (y : ℂ)) - Complex.I * ((y : ℂ) ^ 2 + (z : ℂ) ^ 2)‖ ≤ _
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      refine (add_le_add_right (hquad y z) (|x| * |y|)).trans ?_
      linarith
    · change ‖(x : ℂ) ^ 2 + (z : ℂ) ^ 2 + Complex.I * ((x : ℂ) * (y : ℂ))‖ ≤ _
      refine (norm_add_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      refine (add_le_add_left (hquad x z) (|x| * |y|)).trans ?_
      linarith
    · change ‖Complex.I * ((x : ℂ) * (z : ℂ)) - (y : ℂ) * (z : ℂ)‖ ≤ _
      refine (norm_sub_le _ _).trans ?_
      simp only [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs]
      nlinarith [sq_nonneg r]
  have hC : ‖ckConstantCurl j‖ ≤ 2 := by
    fin_cases j <;> norm_num [ckConstantCurl, norm_mul]
  have hNorm (n : ℕ) (f : ℝ) (A : ℂ) :
      ‖((k ^ n * f : ℝ) : ℂ) * A‖ = k ^ n * |f| * ‖A‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (pow_nonneg hk.le n)]
  have h₃ := abs_mul_ckRadialThree_le u
  have h₅ := abs_sq_mul_ckRadialFive_le u
  rw [abs_of_nonneg hu] at h₃ h₅
  rw [hopfDipoleMode_eq_regular]
  change ‖((k ^ 4 * ckRadialThree u : ℝ) : ℂ) * ckAngular x y z j +
    ((k ^ 5 * ckRadialFive u : ℝ) : ℂ) * ckCurlAngular x y z j +
    ((k ^ 3 * ckRadialThree u : ℝ) : ℂ) * ckConstantCurl j‖ ≤ _
  refine (norm_add_le _ _).trans (le_trans (add_le_add (norm_add_le _ _) le_rfl) ?_)
  rw [hNorm, hNorm, hNorm]
  calc
    _ ≤ k ^ 4 * |ckRadialThree u| * (2 * r) + k ^ 5 * |ckRadialFive u| * (3 * r ^ 2) +
        k ^ 3 * |ckRadialThree u| * 2 := by gcongr
    _ = 2 * k ^ 3 * (u * |ckRadialThree u|) + 3 * k ^ 3 * (u ^ 2 * |ckRadialFive u|) +
        2 * k ^ 3 * |ckRadialThree u| := by dsimp only [u]; ring
    _ ≤ 2 * k ^ 3 * 2 + 3 * k ^ 3 * 7 + 2 * k ^ 3 * (1 / 3) := by
      gcongr
      exact abs_ckRadialThree_le u
    _ ≤ _ := by nlinarith [pow_nonneg hk.le 3]

/-- The actual positive-frequency potential is uniformly bounded on spacetime. -/
theorem exists_hopfPositivePotential_bound :
    ∃ C : ℝ, ∀ (x y z t : ℝ) (j : Fin 3), ‖hopfPositivePotential x y z t j‖ ≤ C := by
  let c := ‖Complex.I / (2 * (Real.pi : ℂ))‖
  let g := fun k : ℝ => (26 * c) * (Real.exp (-k) * k ^ 2)
  have hg : IntegrableOn g (Ioi 0) := by
    have h : IntegrableOn (fun k : ℝ => ‖(k : ℂ) ^ 2 * Complex.exp (-(1 : ℂ) * (k : ℂ))‖)
        (Ioi 0) := (integrableOn_hopf_laplace_moment (a := 1) (by norm_num) 2).norm
    have he : EqOn (fun k : ℝ => ‖(k : ℂ) ^ 2 * Complex.exp (-(1 : ℂ) * (k : ℂ))‖)
        (fun k : ℝ => Real.exp (-k) * k ^ 2) (Ioi 0) := by
      intro k hk
      simp [Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (show 0 < k from hk), mul_comm]
    exact (IntegrableOn.congr_fun h he measurableSet_Ioi).const_mul (26 * c)
  refine ⟨∫ k in Ioi (0 : ℝ), g k, fun x y z t j => ?_⟩
  unfold hopfPositivePotential
  refine (norm_integral_le_integral_norm _).trans
    (setIntegral_mono_on (integrableOn_hopfPotentialDensity x y z t j).norm hg
      measurableSet_Ioi fun k hk => ?_)
  have hk' : 0 < k := hk
  have hre : (-(1 + Complex.I * (t : ℂ)) * (k : ℂ)).re = -k := by
    simp [Complex.mul_re, Complex.add_re]
  rw [hopfPotentialDensity, norm_div, norm_mul, norm_mul, Complex.norm_exp, hre,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk']
  apply (div_le_iff₀ hk').2
  change c * (Real.exp (-k) * ‖hopfDipoleMode k x y z j‖) ≤ g k * k
  calc
    _ ≤ c * (Real.exp (-k) * (26 * k ^ 3)) := by
      gcongr
      exact norm_hopfDipoleMode_le_cubic hk' x y z j
    _ = _ := by dsimp only [g]; ring

end Qatlib.Papers.KnottedLight08.CurlEigenstate
