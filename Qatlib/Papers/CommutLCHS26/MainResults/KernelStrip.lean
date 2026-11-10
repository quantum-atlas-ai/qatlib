/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel
import Qatlib.Papers.CommutLCHS26.MainResults.StripSampling
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Matrix Complex Set Filter MeasureTheory
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder Topology
variable {ι : Type} [Fintype ι] [DecidableEq ι]

local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

def propagator (H L : Matrix ι ι ℂ) (T : ℝ) (z : ℂ) : Matrix ι ι ℂ :=
  NormedSpace.exp ((-T : ℂ) • (I • (H + z • L)))

omit [Fintype ι] in

theorem shifted_part (H L : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hL : L.IsHermitian) (z : ℂ) (γ : ℝ) :
    (I • (H + z • L) - γ • (1 : Matrix ι ι ℂ)) +
      (I • (H + z • L) - γ • (1 : Matrix ι ι ℂ))ᴴ =
      (-2 * z.im) • L - (2 * γ) • (1 : Matrix ι ι ℂ) := by
  simp only [conjTranspose_sub, conjTranspose_smul, conjTranspose_add,
    hH.eq, hL.eq, conjTranspose_one]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  simp [Complex.ext_iff, mul_re, mul_im]
  constructor <;> ring

theorem norm_gap_pos (L : Matrix ι ι ℂ) (hL : L.PosSemidef) :
    (‖L‖ • (1 : Matrix ι ι ℂ) - L).PosSemidef := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := {}
  have h := IsSelfAdjoint.le_algebraMap_norm_self (a := L)
    (ha := hL.isHermitian.isSelfAdjoint)
  simpa only [Algebra.algebraMap_eq_smul_one] using! h

theorem shifted_generator_pos (H L : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hL : L.PosSemidef) (z : ℂ) :
    ((I • (H + z • L) - (-max 0 z.im * ‖L‖) • (1 : Matrix ι ι ℂ)) +
      (I • (H + z • L) - (-max 0 z.im * ‖L‖) • (1 : Matrix ι ι ℂ))ᴴ).PosSemidef := by
  rw [shifted_part H L hH hL.isHermitian]
  rcases le_total z.im 0 with hz | hz
  · rw [max_eq_left hz]
    simpa using! hL.smul (show 0 ≤ -2 * z.im by linarith)
  · rw [max_eq_right hz]
    have he : (-2 * z.im) • L - (2 * (-z.im * ‖L‖)) • (1 : Matrix ι ι ℂ) =
        (2 * z.im) • (‖L‖ • (1 : Matrix ι ι ℂ) - L) := by module
    rw [he]
    exact (norm_gap_pos L hL).smul (mul_nonneg (by norm_num) hz)

theorem norm_propagator_le (H L : Matrix ι ι ℂ) (hH : H.IsHermitian)
    (hL : L.PosSemidef) {T : ℝ} (hT : 0 ≤ T) (z : ℂ) :
    ‖propagator H L T z‖ ≤ Real.exp (max 0 z.im * T * ‖L‖) := by
  have h := Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.norm_evolution_le_exp
    (I • (H + z • L)) (-max 0 z.im * ‖L‖) (shifted_generator_pos H L hH hL z) hT
  convert! h using 1
  · simp only [propagator,
      Qatlib.Concepts.TimeEvolution.DysonPropagator.ContractiveDuhamel.evolution]
    congr 2
    ext i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul, Complex.ofReal_neg]
  · congr 1
    ring

theorem propagator_analytic (H L : Matrix ι ι ℂ) (T : ℝ) (z : ℂ) :
    AnalyticAt ℂ (propagator H L T) z := by
  apply (NormedSpace.exp_analytic _).comp
  fun_prop

def coefficient (n : ℕ) (b c d : ℝ) (z : ℂ) : ℂ :=
  ((b + 1 : ℝ) ^ n / (2 * Real.pi) : ℝ) *
    exp ((d : ℂ) * (1 - I * z)) * exp (-(z ^ 2 + 1) / (4 * (c : ℂ) ^ 2)) /
      ((1 - I * z) * ((b : ℂ) + I * z) ^ n)

theorem lower_ne_zero {ρ : ℝ} (hρ : ρ < 1) {z : ℂ} (hz : |z.im| ≤ ρ) :
    1 - I * z ≠ 0 := by
  intro h
  have he := congrArg Complex.re h
  simp at he
  have := (abs_le.mp hz).1
  linarith

theorem upper_pow_ne_zero (n : ℕ) {b ρ : ℝ} (hb : n = 0 ∨ ρ < b)
    {z : ℂ} (hz : |z.im| ≤ ρ) : ((b : ℂ) + I * z) ^ n ≠ 0 := by
  rcases hb with rfl | hb
  · simp
  · apply pow_ne_zero
    intro h
    have he := congrArg Complex.re h
    simp at he
    have := (abs_le.mp hz).2
    linarith

theorem coefficient_analytic (n : ℕ) (b c d : ℝ) {ρ : ℝ} (hρ : ρ < 1)
    (hb : n = 0 ∨ ρ < b) :
    AnalyticOnNhd ℂ (coefficient n b c d) {z | |z.im| ≤ ρ} := by
  intro z hz
  unfold coefficient
  apply AnalyticAt.div
  · fun_prop
  · fun_prop
  · exact mul_ne_zero (lower_ne_zero hρ hz) (upper_pow_ne_zero n hb hz)

theorem exponent_re (c d : ℝ) (z : ℂ) :
    ((d : ℂ) * (1 - I * z)).re + (-(z ^ 2 + 1) / (4 * (c : ℂ) ^ 2)).re =
      d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2) - z.re ^ 2 / (4 * c ^ 2) := by
  rw [show (4 * (c : ℂ) ^ 2) = ((4 * c ^ 2 : ℝ) : ℂ) by push_cast; ring]
  simp only [div_ofReal_re, mul_re, sub_re, one_re, I_re, I_im, zero_mul, one_mul,
    zero_sub, sub_neg_eq_add, ofReal_re, ofReal_im, sub_im, one_im, mul_im,
    zero_add, neg_re, add_re, pow_two]
  ring

theorem linear_exponent_le {ρ K β d : ℝ} (hK : 0 ≤ K)
    (hβ : |β| ≤ ρ) : d * β + max 0 β * K ≤ ρ * max (-d) (d + K) := by
  have hq : 0 ≤ max (-d) (d + K) := by
    have h1 := le_max_left (-d) (d + K)
    have h2 := le_max_right (-d) (d + K)
    linarith
  rcases le_total β 0 with hb | hb
  · rw [max_eq_left hb]
    have hm := mul_le_mul_of_nonneg_right (le_max_left (-d) (d + K)) (neg_nonneg.mpr hb)
    have hr := mul_le_mul_of_nonneg_left (neg_le.mp (abs_le.mp hβ).1) hq
    nlinarith
  · rw [max_eq_right hb]
    have hm := mul_le_mul_of_nonneg_right (le_max_right (-d) (d + K)) hb
    have hr := mul_le_mul_of_nonneg_left (abs_le.mp hβ).2 hq
    nlinarith

theorem norm_coefficient (n : ℕ) (b c d : ℝ) (hb : 0 < b) (z : ℂ) :
    ‖coefficient n b c d z‖ =
      ((b + 1) ^ n / (2 * Real.pi)) *
        Real.exp (d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2)) *
        Real.exp (-z.re ^ 2 / (4 * c ^ 2)) /
        (‖1 - I * z‖ * ‖(b : ℂ) + I * z‖ ^ n) := by
  have hp : 0 ≤ (b + 1) ^ n / (2 * Real.pi) := by positivity
  have hn : ‖(((b + 1) ^ n / (2 * Real.pi) : ℝ) : ℂ)‖ =
      (b + 1) ^ n / (2 * Real.pi) := by
    rw [norm_real, Real.norm_of_nonneg hp]
  rw [coefficient, norm_div, norm_mul, norm_mul, hn, Complex.norm_exp,
    Complex.norm_exp, norm_mul, norm_pow]
  rw [mul_assoc, ← Real.exp_add, exponent_re]
  rw [sub_eq_add_neg, Real.exp_add]
  simp only [neg_div]
  ring

theorem denominator_lower {ρ b : ℝ} (hb : ρ < b)
    {z : ℂ} (hz : |z.im| ≤ ρ) (n : ℕ) :
    (1 - ρ) * (b - ρ) ^ n ≤ ‖1 - I * z‖ * ‖(b : ℂ) + I * z‖ ^ n := by
  have h1 : 1 - ρ ≤ ‖1 - I * z‖ := by
    have h := Complex.re_le_norm (1 - I * z)
    simp at h
    linarith [(abs_le.mp hz).1]
  have h2 : b - ρ ≤ ‖(b : ℂ) + I * z‖ := by
    have h := Complex.re_le_norm ((b : ℂ) + I * z)
    simp at h
    linarith [(abs_le.mp hz).2]
  exact mul_le_mul h1 (pow_le_pow_left₀ (sub_pos.mpr hb).le h2 n)
    (pow_nonneg (sub_pos.mpr hb).le n) (norm_nonneg _)

theorem full_exponent_le {ρ K β d c : ℝ} (hK : 0 ≤ K) (hβ : |β| ≤ ρ) :
    d * (1 + β) + (β ^ 2 - 1) / (4 * c ^ 2) + max 0 β * K ≤
      d + (ρ ^ 2 - 1) / (4 * c ^ 2) + ρ * max (-d) (d + K) := by
  have hl := linear_exponent_le (d := d) hK hβ
  have hs : β ^ 2 ≤ ρ ^ 2 := by
    simpa using! (sq_le_sq₀ (abs_nonneg β) (le_trans (abs_nonneg β) hβ)).mpr hβ
  have hd := div_le_div_of_nonneg_right (sub_le_sub_right hs 1)
    (show 0 ≤ 4 * c ^ 2 by positivity)
  linarith

def amplitude (n : ℕ) (b c d ρ K : ℝ) : ℝ :=
  (b + 1) ^ n / (2 * Real.pi * (1 - ρ) * (b - ρ) ^ n) *
    Real.exp (d + (ρ ^ 2 - 1) / (4 * c ^ 2) + ρ * max (-d) (d + K))

theorem denominator_lower_or (n : ℕ) {ρ b : ℝ} (hb : n = 0 ∨ ρ < b)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    (1 - ρ) * (b - ρ) ^ n ≤ ‖1 - I * z‖ * ‖(b : ℂ) + I * z‖ ^ n := by
  rcases hb with hn | hb
  · subst n
    simp only [pow_zero, mul_one]
    have h := Complex.re_le_norm (1 - I * z)
    simp at h
    linarith [(abs_le.mp hz).1]
  · exact denominator_lower hb hz n

theorem coefficient_growth_le (n : ℕ) (b c d : ℝ) (hb : 0 < b)
    {ρ K : ℝ} (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b) (hK : 0 ≤ K)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    ‖coefficient n b c d z‖ * Real.exp (max 0 z.im * K) ≤
      amplitude n b c d ρ K * Real.exp (-z.re ^ 2 / (4 * c ^ 2)) := by
  let P := (b + 1) ^ n / (2 * Real.pi)
  let D := ‖1 - I * z‖ * ‖(b : ℂ) + I * z‖ ^ n
  let D₀ := (1 - ρ) * (b - ρ) ^ n
  let q := d + (ρ ^ 2 - 1) / (4 * c ^ 2) + ρ * max (-d) (d + K)
  let g := Real.exp (-z.re ^ 2 / (4 * c ^ 2))
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hD : 0 < D₀ := by
    dsimp [D₀]
    rcases hbn with rfl | hbn
    · simpa using! sub_pos.mpr hρ
    · exact mul_pos (sub_pos.mpr hρ) (pow_pos (sub_pos.mpr hbn) _)
  have hDD : D₀ ≤ D := denominator_lower_or n hbn hz
  calc
    _ = P * Real.exp (d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2) +
        max 0 z.im * K) * g / D := by
      rw [norm_coefficient n b c d hb z]
      dsimp [P, D, g]
      simp only [Real.exp_add]
      ring
    _ ≤ P * Real.exp q * g / D := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (full_exponent_le hK hz)) hP)
          (Real.exp_pos _).le) (le_trans hD.le hDD)
    _ ≤ P * Real.exp q * g / D₀ :=
      div_le_div_of_nonneg_left (by positivity) hD hDD
    _ = amplitude n b c d ρ K * g := by
      dsimp [P, D₀, q, amplitude]
      simp only [div_eq_mul_inv, _root_.mul_inv_rev]
      ring

theorem gaussian_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun x : ℝ => Real.exp (-x ^ 2 / (4 * c ^ 2))) := by
  convert! integrable_exp_neg_mul_sq (show 0 < 1 / (4 * c ^ 2) by positivity) using 1
  ext x
  congr 1
  ring

theorem gaussian_integral {c : ℝ} (hc : 0 < c) :
    (∫ x : ℝ, Real.exp (-x ^ 2 / (4 * c ^ 2))) = 2 * c * Real.sqrt Real.pi := by
  have h := integral_gaussian (1 / (4 * c ^ 2))
  have he : (fun x : ℝ => Real.exp (-x ^ 2 / (4 * c ^ 2))) =
      (fun x : ℝ => Real.exp (-(1 / (4 * c ^ 2)) * x ^ 2)) := by
    funext x
    congr 1
    ring
  rw [he, h, one_div, div_inv_eq_mul, Real.sqrt_mul Real.pi_pos.le,
    show 4 * c ^ 2 = (2 * c) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  ring

def integrand (n : ℕ) (b c d T : ℝ) (H L : Matrix ι ι ℂ) (z : ℂ) : Matrix ι ι ℂ :=
  coefficient n b c d z • propagator H L T z

theorem integrand_analytic (n : ℕ) (b c d T : ℝ) (H L : Matrix ι ι ℂ)
    {ρ : ℝ} (hρ : ρ < 1) (hb : n = 0 ∨ ρ < b) :
    AnalyticOnNhd ℂ (integrand n b c d T H L) {z | |z.im| ≤ ρ} := by
  intro z hz
  exact (coefficient_analytic n b c d hρ hb z hz).smul (propagator_analytic H L T z)

theorem norm_integrand_le (n : ℕ) (b c d : ℝ) (hb : 0 < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T ρ : ℝ} (hT : 0 ≤ T) (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b)
    {z : ℂ} (hz : |z.im| ≤ ρ) :
    ‖integrand n b c d T H L z‖ ≤
      amplitude n b c d ρ (T * ‖L‖) * Real.exp (-z.re ^ 2 / (4 * c ^ 2)) := by
  rw [integrand, norm_smul]
  apply (mul_le_mul_of_nonneg_left (norm_propagator_le H L hH hL hT z)
    (norm_nonneg _)).trans
  simpa only [mul_assoc] using! coefficient_growth_le n b c d hb hρ hbn
    (mul_nonneg hT (norm_nonneg L)) hz

def mass (n : ℕ) (b c d ρ K : ℝ) : ℝ :=
  c / Real.sqrt Real.pi * ((b + 1) ^ n / ((1 - ρ) * (b - ρ) ^ n)) *
    Real.exp (d + (ρ ^ 2 - 1) / (4 * c ^ 2) + ρ * max (-d) (d + K))

theorem amplitude_mul_gaussian (n : ℕ) (b c d ρ K : ℝ) :
    amplitude n b c d ρ K * (2 * c * Real.sqrt Real.pi) = mass n b c d ρ K := by
  unfold amplitude mass
  have he : Real.sqrt Real.pi / Real.pi = 1 / Real.sqrt Real.pi := by
    rw [div_eq_div_iff (ne_of_gt Real.pi_pos) (Real.sqrt_pos.mpr Real.pi_pos).ne']
    simpa only [one_mul, pow_two] using! Real.sq_sqrt Real.pi_pos.le
  have hr : ∀ A D : ℝ, A / (2 * Real.pi * D) * (2 * c * Real.sqrt Real.pi) =
      c * A / D * (Real.sqrt Real.pi / Real.pi) := by
    intro A D
    simp only [div_eq_mul_inv, _root_.mul_inv_rev]
    ring
  rw [show 2 * Real.pi * (1 - ρ) * (b - ρ) ^ n =
      2 * Real.pi * ((1 - ρ) * (b - ρ) ^ n) by ring]
  rw [mul_right_comm _ (Real.exp _) (2 * c * Real.sqrt Real.pi), hr, he]
  simp only [div_eq_mul_inv]
  ring

theorem integrand_integrable (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T ρ y : ℝ} (hT : 0 ≤ T) (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b)
    (hy : |y| ≤ ρ) :
    Integrable (fun x : ℝ => integrand n b c d T H L ((x : ℂ) + y * I)) := by
  apply ((gaussian_integrable hc).const_mul
    (amplitude n b c d ρ (T * ‖L‖))).mono'
  · apply Continuous.aestronglyMeasurable
    exact continuous_iff_continuousAt.mpr fun x =>
      ((integrand_analytic n b c d T H L hρ hbn _ (by simpa using! hy)).continuousAt.comp
        (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + y * I) x))
  · filter_upwards [] with x
    simpa using! norm_integrand_le n b c d hb H L hH hL hT hρ hbn
      (z := (x : ℂ) + y * I) (by simpa using! hy)

theorem integral_norm_integrand_le (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T ρ y : ℝ} (hT : 0 ≤ T) (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b)
    (hy : |y| ≤ ρ) :
    (∫ x : ℝ, ‖integrand n b c d T H L ((x : ℂ) + y * I)‖) ≤
      mass n b c d ρ (T * ‖L‖) := by
  calc
    _ ≤ ∫ x : ℝ, amplitude n b c d ρ (T * ‖L‖) *
        Real.exp (-x ^ 2 / (4 * c ^ 2)) := by
      apply integral_mono (integrand_integrable n b c d hb hc H L hH hL hT hρ hbn hy).norm
        ((gaussian_integrable hc).const_mul _)
      intro x
      simpa using! norm_integrand_le n b c d hb H L hH hL hT hρ hbn
        (z := (x : ℂ) + y * I) (by simpa using! hy)
    _ = _ := by rw [integral_const_mul, gaussian_integral hc, amplitude_mul_gaussian]

theorem integrand_decay (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T ρ : ℝ} (hT : 0 ≤ T) (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b) :
    StripContour.UniformDecay (integrand n b c d T H L) (-ρ) ρ := by
  have ht : Tendsto (fun r : ℝ => amplitude n b c d ρ (T * ‖L‖) *
      Real.exp (-r ^ 2 / (4 * c ^ 2))) atTop (𝓝 0) := by
    have he := Real.tendsto_exp_atBot.comp
      ((tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop two_ne_zero)).atBot_div_const
        (show 0 < 4 * c ^ 2 by positivity))
    simpa using! he.const_mul (amplitude n b c d ρ (T * ‖L‖))
  intro ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.mp (ht (Iio_mem_nhds hε))
  refine ⟨R, fun x hx y hy => ?_⟩
  apply (norm_integrand_le n b c d hb H L hH hL hT hρ hbn
    (z := (x : ℂ) + y * I) (by simpa using! abs_le.mpr hy)).trans
  have he : amplitude n b c d ρ (T * ‖L‖) * Real.exp (-|x| ^ 2 / (4 * c ^ 2)) ≤ ε :=
    (hR |x| hx).le
  simpa only [sq_abs, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
    mul_zero, zero_mul, sub_zero, add_zero] using! he

theorem integrand_mesh_error (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T ρ h : ℝ} (hT : 0 ≤ T) (hρ₀ : 0 < ρ) (hρ : ρ < 1)
    (hbn : n = 0 ∨ ρ < b) (hh : 0 < h) :
    ‖(∫ x : ℝ, integrand n b c d T H L (x : ℂ)) -
        h • ∑' j : ℤ, integrand n b c d T H L ((h * (j : ℝ) : ℝ) : ℂ)‖ ≤
      2 * mass n b c d ρ (T * ‖L‖) / (Real.exp (2 * Real.pi * ρ / h) - 1) := by
  apply StripSampling.analytic_strip_mesh_error _ _ _ _ hρ₀ hh
    (integrand_analytic n b c d T H L hρ hbn)
    (integrand_decay n b c d hb hc H L hH hL hT hρ hbn)
  · intro y hy
    exact integrand_integrable n b c d hb hc H L hH hL hT hρ hbn
      (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
  · intro y hy
    exact integral_norm_integrand_le n b c d hb hc H L hH hL hT hρ hbn
      (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)

theorem integrand_strip_estimates (n : ℕ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T ρ : ℝ} (hT : 0 ≤ T) (hρ : ρ < 1) (hbn : n = 0 ∨ ρ < b) :
    AnalyticOnNhd ℂ (integrand n b c d T H L) {z | |z.im| ≤ ρ} ∧
      StripContour.UniformDecay (integrand n b c d T H L) (-ρ) ρ ∧
      ∀ y : ℝ, |y| ≤ ρ →
        Integrable (fun x : ℝ => integrand n b c d T H L ((x : ℂ) + y * I)) ∧
        (∫ x : ℝ, ‖integrand n b c d T H L ((x : ℂ) + y * I)‖) ≤
          mass n b c d ρ (T * ‖L‖) :=
  ⟨integrand_analytic n b c d T H L hρ hbn,
    integrand_decay n b c d hb hc H L hH hL hT hρ hbn,
    fun _ hy => ⟨integrand_integrable n b c d hb hc H L hH hL hT hρ hbn hy,
      integral_norm_integrand_le n b c d hb hc H L hH hL hT hρ hbn hy⟩⟩

end Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
