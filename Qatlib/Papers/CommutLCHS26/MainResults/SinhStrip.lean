/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Strip estimates for the sinh transform

This module proves pole separation, analyticity, and integrable envelopes for the
sinh-transformed matrix integrand in [AftabAnTrivisa2026]. The distances `poleDistance` and
`lowerDistance` control denominators, while `bellB` supplies an explicit Gaussian pullback
envelope.

The bounds `stripAmplitude` and `stripMass` yield uniform decay, horizontal integrability, and
an infinite-mesh quadrature estimate under explicit strip and pole-gap conditions.

## Main statements

* `transformed_strip_estimates`: analyticity, decay, and horizontal mass bounds.
* `transformed_mesh_error`: the exponential mesh error estimate.

## References

* [Aftab et al., 2026][AftabAnTrivisa2026]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
open Complex Set Filter MeasureTheory
open scoped Topology

/-- The complex hyperbolic sine at `x + y I` splits into its real hyperbolic and trigonometric
components. -/
theorem sinh_rect (x y : ℝ) :
    Complex.sinh ((x : ℂ) + y * I) =
      ((Real.sinh x * Real.cos y : ℝ) : ℂ) + ((Real.cosh x * Real.sin y : ℝ) : ℂ) * I := by
  rw [Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- The complex hyperbolic cosine at `x + y I` splits into its real hyperbolic and trigonometric
components. -/
theorem cosh_rect (x y : ℝ) :
    Complex.cosh ((x : ℂ) + y * I) =
      ((Real.cosh x * Real.cos y : ℝ) : ℂ) + ((Real.sinh x * Real.sin y : ℝ) : ℂ) * I := by
  rw [Complex.cosh_add, Complex.cosh_mul_I, Complex.sinh_mul_I,
    ← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  push_cast
  ring

/-- The real hyperbolic cosine is at most one plus the absolute value of the hyperbolic sine. -/
theorem cosh_le_one_add_abs_sinh (x : ℝ) : Real.cosh x ≤ 1 + |Real.sinh x| := by
  have hc := Real.cosh_sq_sub_sinh_sq x
  nlinarith [abs_nonneg (Real.sinh x), sq_abs (Real.sinh x), Real.cosh_pos x]

/-- On a symmetric interval of radius less than `π / 2`, cosine has a positive lower bound and
the absolute sine is bounded by the sine of the radius. -/
theorem trig_bounds {β y : ℝ} (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 2) (hy : |y| ≤ β) :
    0 < Real.cos β ∧ Real.cos β ≤ Real.cos y ∧ |Real.sin y| ≤ Real.sin β := by
  have hβπ : β ≤ Real.pi := by linarith [Real.pi_pos]
  refine ⟨Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩, ?_, ?_⟩
  · simpa only [Real.cos_abs] using! Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg y) hβπ hy
  · rw [Real.abs_sin_eq_sin_abs_of_abs_le_pi (hy.trans hβπ)]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [abs_nonneg y]) hβ.le hy

/-- The transformed pole factor `κ + I * (η * sinh z)`. -/
def pole (κ η : ℝ) (z : ℂ) : ℂ := (κ : ℂ) + I * ((η : ℂ) * Complex.sinh z)

/-- The real part of the transformed pole factor is `κ - η cosh x sin y`. -/
theorem pole_re (κ η x y : ℝ) : (pole κ η ((x : ℂ) + y * I)).re =
    κ - η * Real.cosh x * Real.sin y := by
  simp only [pole, sinh_rect, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- The imaginary part of the transformed pole factor is `η sinh x cos y`. -/
theorem pole_im (κ η x y : ℝ) : (pole κ η ((x : ℂ) + y * I)).im =
    η * Real.sinh x * Real.cos y := by
  simp only [pole, sinh_rect, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

/-- For positive `η` and `0 ≤ β < π / 2`, the pole-factor norm on the strip is at least `(κ - η
sin β) cos β / 2`. -/
theorem pole_uniform_lower {κ η β : ℝ} (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 2) (x y : ℝ) (hy : |y| ≤ β) :
    (κ - η * Real.sin β) * Real.cos β / 2 ≤ ‖pole κ η ((x : ℂ) + y * I)‖ := by
  obtain ⟨hc, hcos, hsin⟩ := trig_bounds hβ₀ hβ hy
  have hs : 0 ≤ Real.sin β := (abs_nonneg (Real.sin y)).trans hsin
  have hcy : 0 ≤ Real.cos y := hc.le.trans hcos
  have hRe := Complex.re_le_norm (pole κ η ((x : ℂ) + y * I))
  rw [pole_re] at hRe
  have hsin' : Real.sin y ≤ Real.sin β := (le_abs_self _).trans hsin
  have hR : κ - η * Real.sin β * (1 + |Real.sinh x|) ≤
      ‖pole κ η ((x : ℂ) + y * I)‖ := by
    have h1 := mul_le_mul_of_nonneg_left hsin' (show 0 ≤ η * Real.cosh x by positivity)
    have h2 := mul_le_mul_of_nonneg_left (cosh_le_one_add_abs_sinh x) (mul_nonneg hη.le hs)
    nlinarith
  have hI : η * |Real.sinh x| * Real.cos β ≤ ‖pole κ η ((x : ℂ) + y * I)‖ := by
    calc
      _ ≤ η * |Real.sinh x| * Real.cos y := mul_le_mul_of_nonneg_left hcos (by positivity)
      _ = |(pole κ η ((x : ℂ) + y * I)).im| := by
        rw [pole_im, abs_mul, abs_mul, abs_of_nonneg hη.le, abs_of_nonneg hcy]
      _ ≤ _ := Complex.abs_im_le_norm _
  have h1 := mul_le_mul_of_nonneg_right hR hc.le
  have h2 := mul_le_mul_of_nonneg_right hI hs
  have h3 :=
      mul_le_mul_of_nonneg_left (Real.cos_le_one β) (norm_nonneg (pole κ η ((x : ℂ) + y * I)))
  have h4 :=
      mul_le_mul_of_nonneg_left (Real.sin_le_one β) (norm_nonneg (pole κ η ((x : ℂ) + y * I)))
  nlinarith

/-- The infimum of the norms of the transformed pole factor over the closed strip of half-width
`β`. -/
def poleDistance (κ η β : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x y : ℝ, |y| ≤ β ∧ r = ‖pole κ η ((x : ℂ) + y * I)‖}

/-- The pole distance is bounded above by the pole-factor norm at any point in the strip. -/
theorem poleDistance_le (κ η β x y : ℝ) (hy : |y| ≤ β) :
    poleDistance κ η β ≤ ‖pole κ η ((x : ℂ) + y * I)‖ := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro r ⟨a, b, _, rfl⟩
    exact norm_nonneg _
  · exact ⟨x, y, hy, rfl⟩

/-- The pole distance is at least `(κ - η sin β) cos β / 2` for positive `η` and `0 ≤ β < π /
2`. -/
theorem poleDistance_lower {κ η β : ℝ} (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 2) :
    (κ - η * Real.sin β) * Real.cos β / 2 ≤ poleDistance κ η β := by
  apply le_csInf
  · exact ⟨‖pole κ η 0‖, 0, 0, by simpa using! hβ₀, by simp⟩
  · rintro r ⟨x, y, hy, rfl⟩
    exact pole_uniform_lower hη hβ₀ hβ x y hy

/-- The pole distance is positive when `η sin β < κ`, with positive `η` and `0 ≤ β < π / 2`. -/
theorem poleDistance_pos {κ η β : ℝ} (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 2) (hgap : η * Real.sin β < κ) : 0 < poleDistance κ η β := by
  have hc : 0 < Real.cos β := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hβ⟩
  exact (div_pos (mul_pos (sub_pos.mpr hgap) hc) (by norm_num)).trans_le
    (poleDistance_lower hη hβ₀ hβ)

/-- The transformed pole factor is nonzero throughout the strip when `η sin β < κ` under the
stated width conditions. -/
theorem pole_ne_zero {κ η β : ℝ} (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 2) (hgap : η * Real.sin β < κ) {z : ℂ} (hz : |z.im| ≤ β) :
    pole κ η z ≠ 0 := by
  have hl := (poleDistance_pos hη hβ₀ hβ hgap).trans_le (poleDistance_le κ η β z.re z.im hz)
  simpa only [Complex.re_add_im] using! norm_pos_iff.mp hl

/-- For positive `κ` and `η` and `0 ≤ β < π / 2`, the transformed pole factor is nonzero on the
closed strip exactly when `η sin β < κ`. -/
theorem pole_free_iff {κ η β : ℝ} (hκ : 0 < κ) (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 2) :
    (∀ z : ℂ, |z.im| ≤ β → pole κ η z ≠ 0) ↔ η * Real.sin β < κ := by
  constructor
  · intro hf
    by_contra! hbad
    have hκ₁ : κ / η ≤ 1 :=
        (div_le_one hη).mpr (hbad.trans (mul_le_of_le_one_right hη.le (Real.sin_le_one _)))
    have hκ₀ : -1 ≤ κ / η := by linarith [div_pos hκ hη]
    let y := Real.arcsin (κ / η)
    have hy₀ : 0 ≤ y := Real.arcsin_nonneg.mpr (by positivity)
    have hyβ : y ≤ β := (Real.arcsin_le_iff_le_sin ⟨hκ₀, hκ₁⟩ ⟨by linarith [Real.pi_pos], hβ.le⟩).mpr
      ((div_le_iff₀ hη).mpr (by nlinarith))
    have hz := hf ((y : ℂ) * I) (by simpa [abs_of_nonneg hy₀] using! hyβ)
    apply hz
    dsimp [pole, y]
    rw [Complex.sinh_mul_I, ← Complex.ofReal_sin, Real.sin_arcsin hκ₀ hκ₁]
    push_cast
    have hηc : (η : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hη.ne'
    field_simp
    simp [Complex.I_sq]
  · intro hgap z hz
    exact pole_ne_zero hη hβ₀ hβ hgap hz

/-- The norm of the lower pole factor equals the norm of `pole 1 η` at the reflected point. -/
theorem lower_reflection (η x y : ℝ) :
    ‖(1 : ℂ) - I * ((η : ℂ) * Complex.sinh ((x : ℂ) + y * I))‖ =
      ‖pole 1 η (((-x : ℝ) : ℂ) + (-y : ℝ) * I)‖ := by
  rw [show (((-x : ℝ) : ℂ) + (-y : ℝ) * I) = -((x : ℂ) + y * I) by push_cast; ring]
  simp only [pole, Complex.sinh_neg, Complex.ofReal_one]
  congr 1
  ring

/-- The infimum of the norms of `1 - I * (η * sinh z)` over the closed strip of half-width `β`. -/
def lowerDistance (η β : ℝ) : ℝ :=
  sInf {r : ℝ | ∃ x y : ℝ, |y| ≤ β ∧ r =
    ‖(1 : ℂ) - I * ((η : ℂ) * Complex.sinh ((x : ℂ) + y * I))‖}

/-- The lower pole distance equals `poleDistance 1 η β` by reflection. -/
theorem lowerDistance_eq (η β : ℝ) : lowerDistance η β = poleDistance 1 η β := by
  unfold lowerDistance poleDistance
  congr 1
  ext r
  constructor
  · rintro ⟨x, y, hy, rfl⟩
    exact ⟨-x, -y, by simpa using! hy, lower_reflection η x y⟩
  · rintro ⟨x, y, hy, rfl⟩
    refine ⟨-x, -y, by simpa using! hy, ?_⟩
    simpa only [neg_neg] using! (lower_reflection η (-x) (-y)).symm

/-- The squared norm of `cosh (x + y I)` is `cosh x` squared minus `sin y` squared. -/
theorem cosh_norm_sq (x y : ℝ) :
    Complex.normSq (Complex.cosh ((x : ℂ) + y * I)) = Real.cosh x ^ 2 - Real.sin y ^ 2 := by
  rw [cosh_rect, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, zero_add, add_zero, mul_one]
  calc
    _ = Real.cosh x ^ 2 * (Real.cos y ^ 2 + Real.sin y ^ 2) -
        (Real.cosh x ^ 2 - Real.sinh x ^ 2) * Real.sin y ^ 2 := by ring
    _ = _ := by rw [Real.cos_sq_add_sin_sq, Real.cosh_sq_sub_sinh_sq]; ring

/-- The norm of `cosh (x + y I)` is at most `cosh x`. -/
theorem norm_cosh_le (x y : ℝ) : ‖Complex.cosh ((x : ℂ) + y * I)‖ ≤ Real.cosh x := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.cosh_pos x).le).mp
  rw [Complex.sq_norm, cosh_norm_sq]
  exact sub_le_self _ (sq_nonneg _)

/-- The real part of `(sinh (x + y I))²` is `(sinh x)² * cos (2y) - (sin y)²`. -/
theorem sinh_sq_re (x y : ℝ) :
    (Complex.sinh ((x : ℂ) + y * I) ^ 2).re = Real.sinh x ^ 2 * Real.cos (2 * y) - Real.sin y ^ 2 := by
  rw [sinh_rect, pow_two]
  simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, zero_add, add_zero, mul_one]
  have hd : Real.cos (2 * y) = Real.cos y ^ 2 - Real.sin y ^ 2 := by
    rw [two_mul, Real.cos_add]
    ring
  calc
    _ = Real.sinh x ^ 2 * (Real.cos y ^ 2 - Real.sin y ^ 2) -
        (Real.cosh x ^ 2 - Real.sinh x ^ 2) * Real.sin y ^ 2 := by ring
    _ = _ := by rw [← hd, Real.cosh_sq_sub_sinh_sq]; ring

/-- For `|y| ≤ β < π / 4`, the real part of the squared complex hyperbolic sine is bounded below
using `cos (2β)` and `sin β`. -/
theorem sinh_sq_re_ge {β y : ℝ} (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4)
    (hy : |y| ≤ β) (x : ℝ) :
    Real.cos (2 * β) * Real.sinh x ^ 2 - Real.sin β ^ 2 ≤
      (Complex.sinh ((x : ℂ) + y * I) ^ 2).re := by
  have ht := trig_bounds hβ₀ (by linarith [Real.pi_pos] : β < Real.pi / 2) hy
  have hc := (trig_bounds (by linarith : 0 ≤ 2 * β) (by linarith : 2 * β < Real.pi / 2)
    (show |2 * y| ≤ 2 * β by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]; linarith)).2.1
  have hs : Real.sin y ^ 2 ≤ Real.sin β ^ 2 := by
    have hsβ : 0 ≤ Real.sin β := (abs_nonneg _).trans ht.2.2
    simpa only [sq_abs] using! (sq_le_sq₀ (abs_nonneg _) hsβ).mpr ht.2.2
  rw [sinh_sq_re]
  nlinarith [mul_le_mul_of_nonneg_right hc (sq_nonneg (Real.sinh x))]

open Qatlib.Papers.CommutLCHS26.MainResults.KernelStrip
open Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule (transformed)
open scoped Matrix.Norms.L2Operator ComplexOrder
set_option warningAsError false
variable {ι : Type} [Fintype ι] [DecidableEq ι]
local instance : ContinuousENorm (Matrix ι ι ℂ) :=
  SeminormedAddGroup.toESeminormedAddMonoid.toContinuousENorm

/-- The lower pole factor is nonzero on the strip when `η sin β < 1` under the stated width
conditions. -/
theorem lower_pole_ne_zero {η β : ℝ} (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 2) (hgap : η * Real.sin β < 1) {z : ℂ} (hz : |z.im| ≤ β) :
    1 - I * ((η : ℂ) * Complex.sinh z) ≠ 0 := by
  have hp := pole_ne_zero hη hβ₀ hβ hgap (z := -z) (by simpa using! hz)
  simpa only [pole, Complex.ofReal_one, Complex.sinh_neg, mul_neg, sub_eq_add_neg] using! hp

/-- The transformed matrix integrand is analytic on a neighborhood of the closed strip when the
lower pole gap and the applicable upper pole gap are positive. -/
theorem transformed_analytic (n : ℕ) (b c d T η β : ℝ) (hη : 0 < η)
    (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 2) (hgap : η * Real.sin β < 1)
    (hbn : n = 0 ∨ η * Real.sin β < b) (H L : Matrix ι ι ℂ) :
    AnalyticOnNhd ℂ (transformed n b c d T η H L) {z : ℂ | |z.im| ≤ β} := by
  intro z hz
  have hd : ((b : ℂ) + I * ((η : ℂ) * Complex.sinh z)) ^ n ≠ 0 := by
    rcases hbn with rfl | hb
    · simp
    · exact pow_ne_zero _ (pole_ne_zero hη hβ₀ hβ hb hz)
  have hc : AnalyticAt ℂ (fun w => coefficient n b c d ((η : ℂ) * Complex.sinh w)) z := by
    unfold coefficient
    apply AnalyticAt.div
    · fun_prop
    · fun_prop
    · exact mul_ne_zero (lower_pole_ne_zero hη hβ₀ hβ hgap hz) hd
  have hp : AnalyticAt ℂ (fun w => propagator H L T ((η : ℂ) * Complex.sinh w)) z :=
    (propagator_analytic H L T _).comp (by fun_prop)
  have hj : AnalyticAt ℂ (fun w : ℂ => (η : ℂ) * Complex.cosh w) z := by fun_prop
  exact hj.smul (hc.smul hp)

/-- The squared scale ratio `(η / (2c))²`. -/
def scaleSq (c η : ℝ) : ℝ := (η / (2 * c)) ^ 2

/-- The strip growth coefficient `η sin β (|d| + K)`. -/
def growth (η β d K : ℝ) : ℝ := η * Real.sin β * (|d| + K)

/-- The difference of the squared real and imaginary parts of the scaled hyperbolic sine equals
`η²` times the real part of the squared hyperbolic sine. -/
theorem transformed_square (η : ℝ) (z : ℂ) :
    (((η : ℂ) * Complex.sinh z).re ^ 2 - ((η : ℂ) * Complex.sinh z).im ^ 2) =
      η ^ 2 * (Complex.sinh z ^ 2).re := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, pow_two]
  ring

/-- On the strip, the absolute imaginary part of `η sinh (x + y I)` is at most `η sin β cosh x`. -/
theorem transformed_im_le {η β y : ℝ} (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 2) (hy : |y| ≤ β) (x : ℝ) :
    |((η : ℂ) * Complex.sinh ((x : ℂ) + y * I)).im| ≤ η * Real.sin β * Real.cosh x := by
  have hp := pole_re 0 η x y
  simp only [pole, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
    Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_sub, zero_add] at hp
  have he : ((η : ℂ) * Complex.sinh ((x : ℂ) + y * I)).im = η * Real.cosh x * Real.sin y :=
      neg_inj.mp hp
  rw [he, abs_mul, abs_mul, abs_of_pos hη, abs_of_pos (Real.cosh_pos x)]
  have hs := mul_le_mul_of_nonneg_left (trig_bounds hβ₀ hβ hy).2.2
    (show 0 ≤ η * Real.cosh x by positivity)
  simpa only [mul_assoc, mul_comm, mul_left_comm] using! hs

/-- For nonnegative `K`, the expression `d v + max 0 v * K` is at most `(|d| + K) |v|`. -/
theorem linear_growth {d K v : ℝ} (hK : 0 ≤ K) :
    d * v + max 0 v * K ≤ (|d| + K) * |v| := by
  have h1 : d * v ≤ |d| * |v| := by simpa only [abs_mul] using! le_abs_self (d * v)
  have h2 :=
      mul_le_mul_of_nonneg_right (show max 0 v ≤ |v| from max_le (abs_nonneg _) (le_abs_self _)) hK
  nlinarith

/-- The full transformed exponent is bounded by a constant, a negative `sinh x` squared term,
and a `cosh x` growth term under the stated strip conditions. -/
theorem full_exponent_bound {c η β K y : ℝ} (hc : 0 < c) (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 4) (hK : 0 ≤ K) (hy : |y| ≤ β) (d x : ℝ) :
    let z := (η : ℂ) * Complex.sinh ((x : ℂ) + y * I)
    d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2) - z.re ^ 2 / (4 * c ^ 2) + max 0 z.im * K ≤
      d - 1 / (4 * c ^ 2) + scaleSq c η * Real.sin β ^ 2 -
        scaleSq c η * Real.cos (2 * β) * Real.sinh x ^ 2 + growth η β d K * Real.cosh x := by
  (try dsimp only)
  let z := (η : ℂ) * Complex.sinh ((x : ℂ) + y * I)
  have hlin := (linear_growth (d := d) (v := z.im) hK).trans
    (mul_le_mul_of_nonneg_left (transformed_im_le hη hβ₀ (by linarith [Real.pi_pos]) hy x)
      (show 0 ≤ |d| + K by positivity))
  have hsq := mul_le_mul_of_nonneg_left (sinh_sq_re_ge hβ₀ hβ hy x) (sq_nonneg η)
  rw [← transformed_square] at hsq
  have hg := div_le_div_of_nonneg_right hsq (show 0 ≤ 4 * c ^ 2 by positivity)
  have he : scaleSq c η = η ^ 2 / (4 * c ^ 2) := by unfold scaleSq; field_simp; ring
  rw [he]
  unfold growth
  dsimp [z] at hlin
  linear_combination hlin + hg

/-- A nonnegative `cosh x` growth term can be absorbed into half of a negative `sinh x` squared
term at the cost of `A + A² / (2B)`. -/
theorem absorb_growth {B A : ℝ} (hB : 0 < B) (hA : 0 ≤ A) (x : ℝ) :
    -B * Real.sinh x ^ 2 + A * Real.cosh x ≤
      -(B / 2) * Real.sinh x ^ 2 + A + A ^ 2 / (2 * B) := by
  have hs : 0 ≤ B ^ 2 * Real.sinh x ^ 2 + A ^ 2 - 2 * B * A * |Real.sinh x| := by
    calc
      _ ≤ (B * |Real.sinh x| - A) ^ 2 := sq_nonneg _
      _ = _ := by rw [sub_sq, mul_pow, sq_abs]; ring
  have hY : A * |Real.sinh x| ≤ (B ^ 2 * Real.sinh x ^ 2 + A ^ 2) / (2 * B) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * B)).mpr
    nlinarith only [hs]
  have he : (B ^ 2 * Real.sinh x ^ 2 + A ^ 2) / (2 * B) =
      B / 2 * Real.sinh x ^ 2 + A ^ 2 / (2 * B) := by field_simp
  rw [he] at hY
  have hc := mul_le_mul_of_nonneg_left (cosh_le_one_add_abs_sinh x) hA
  linarith

/-- The envelope `cosh x * exp (-(B / 2) * (sinh x)²)`. -/
def bellB (B x : ℝ) : ℝ := Real.cosh x * Real.exp (-(B / 2) * Real.sinh x ^ 2)

/-- The envelope `bellB` is the unit-scale sinh pullback of a Gaussian. -/
theorem bellB_eq_pullback (B : ℝ) : bellB B =
    Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule.pullback 1
      (fun u : ℝ => Real.exp (-(B / 2) * u ^ 2)) := by
  funext x
  simp only [bellB, Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule.pullback,
    one_mul, smul_eq_mul]

/-- The envelope `bellB B` is integrable for positive `B`. -/
theorem bellB_integrable {B : ℝ} (hB : 0 < B) : Integrable (bellB B) := by
  have hf := integrable_exp_neg_mul_sq (show 0 < B / 2 by positivity)
  rw [bellB_eq_pullback]
  exact (Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule.integrable_pullback
    (η := 1) (by norm_num) (fun u : ℝ => Real.exp (-(B / 2) * u ^ 2))).mpr hf

/-- For positive `B`, the integral of `bellB B` is `sqrt (2π / B)`. -/
theorem bellB_integral {B : ℝ} (hB : 0 < B) :
    (∫ x : ℝ, bellB B x) = Real.sqrt (2 * Real.pi / B) := by
  have h := Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule.integral_pullback
    (η := 1) (by norm_num) (fun u : ℝ => Real.exp (-(B / 2) * u ^ 2))
  simp only [Qatlib.Papers.CommutLCHS26.QuadratureCmp.SinhRule.pullback,
    one_mul, smul_eq_mul] at h
  unfold bellB
  rw [h, integral_gaussian]
  congr 1
  field_simp

/-- A Gaussian multiplied by `D (1 + t)` tends to zero as `t` tends to positive infinity when
its decay rate is positive. -/
theorem bellB_decay {B : ℝ} (hB : 0 < B) (D : ℝ) :
    Tendsto (fun t : ℝ => D * (1 + t) * Real.exp (-(B / 2) * t ^ 2)) atTop (𝓝 0) := by
  have he : Tendsto (fun t : ℝ => Real.exp (-(B / 2) * t)) atTop (𝓝 0) :=
    by simpa only [Function.comp_apply, neg_mul, id_eq] using!
      Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop (by positivity : 0 < B / 2))
  have ht : Tendsto (fun t : ℝ => t * Real.exp (-(B / 2) * t)) atTop (𝓝 0) := by
    simpa only [Real.rpow_one] using!
        tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 (B / 2) (by positivity)
  have hlim : Tendsto (fun t : ℝ => |D| * (1 + t) * Real.exp (-(B / 2) * t)) atTop (𝓝 0) := by
    convert! (he.add ht).const_mul |D| using 1
    · funext t
      ring
    · simp
  have hlimneg : Tendsto (fun t : ℝ => -(|D| * (1 + t) * Real.exp (-(B / 2) * t))) atTop (𝓝 0) := by
    simpa only [neg_zero] using! hlim.neg
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimneg hlim
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht₁
    have ht₀ : 0 ≤ t := by linarith
    have heq : Real.exp (-(B / 2) * t ^ 2) ≤ Real.exp (-(B / 2) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (t - 1)]
    have hn : |D * (1 + t) * Real.exp (-(B / 2) * t ^ 2)| ≤
        |D| * (1 + t) * Real.exp (-(B / 2) * t) := by
      rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 + t), abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left heq (by positivity)
    exact (abs_le.mp hn).1
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with t ht₁
    have ht₀ : 0 ≤ t := by linarith
    have heq : Real.exp (-(B / 2) * t ^ 2) ≤ Real.exp (-(B / 2) * t) := by
      apply Real.exp_le_exp.mpr
      nlinarith [sq_nonneg (t - 1)]
    have hn := mul_le_mul_of_nonneg_left heq (show 0 ≤ |D| * (1 + t) by positivity)
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self D) (by positivity))
      (Real.exp_pos _).le).trans hn

/-- The pole distance is nonnegative when the strip half-width is nonnegative. -/
theorem poleDistance_nonneg (κ η β : ℝ) (hβ₀ : 0 ≤ β) : 0 ≤ poleDistance κ η β := by
  apply le_csInf
  · exact ⟨‖pole κ η 0‖, 0, 0, by simpa using! hβ₀, by simp⟩
  · rintro r ⟨_, _, _, rfl⟩
    exact norm_nonneg _

/-- The lower pole distance is at most the lower pole-factor norm at any point of the strip. -/
theorem lowerDistance_le (η β x y : ℝ) (hy : |y| ≤ β) :
    lowerDistance η β ≤ ‖(1 : ℂ) - I * ((η : ℂ) * Complex.sinh ((x : ℂ) + y * I))‖ := by
  rw [lowerDistance_eq]
  exact (poleDistance_le 1 η β (-x) (-y) (by simpa using! hy)).trans_eq
      (lower_reflection η x y).symm

/-- The product of the lower pole distance and the required power of the upper pole distance is
positive under the stated pole-gap conditions. -/
theorem distance_product_pos (n : ℕ) {b η β : ℝ} (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 2) (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b) :
    0 < lowerDistance η β * poleDistance b η β ^ n := by
  have hL : 0 < lowerDistance η β := by rw [lowerDistance_eq]; exact poleDistance_pos hη hβ₀ hβ hgap
  apply mul_pos hL
  rcases hbn with rfl | hb
  · simp
  · exact pow_pos (poleDistance_pos hη hβ₀ hβ hb) _

/-- The coefficient prefactor formed from `(b + 1)ⁿ`, `2π`, and the product of the strip pole
distances. -/
def kernelPrefactor (n : ℕ) (b η β : ℝ) : ℝ :=
  (b + 1) ^ n / (2 * Real.pi * lowerDistance η β * poleDistance b η β ^ n)

/-- The constant exponent remaining after absorbing the transformed linear growth into the
Gaussian decay. -/
def postExponent (c d η β K : ℝ) : ℝ :=
  d - 1 / (4 * c ^ 2) + scaleSq c η * Real.sin β ^ 2 + growth η β d K +
    growth η β d K ^ 2 / (2 * (scaleSq c η * Real.cos (2 * β)))

/-- The amplitude of the integrable strip envelope, including the sinh scale and the coefficient
prefactor. -/
def stripAmplitude (n : ℕ) (b c d η β K : ℝ) : ℝ :=
  η * kernelPrefactor n b η β * Real.exp (postExponent c d η β K)

/-- The integral bound obtained by multiplying `stripAmplitude` by the Gaussian mass factor. -/
def stripMass (n : ℕ) (b c d η β K : ℝ) : ℝ :=
  stripAmplitude n b c d η β K * Real.sqrt (2 * Real.pi / (scaleSq c η * Real.cos (2 * β)))

/-- The Gaussian decay rate `scaleSq c η * cos (2β)` is positive for positive scales and `0 ≤ β
< π / 4`. -/
theorem gaussian_rate_pos {c η β : ℝ} (hc : 0 < c) (hη : 0 < η) (hβ₀ : 0 ≤ β)
    (hβ : β < Real.pi / 4) : 0 < scaleSq c η * Real.cos (2 * β) := by
  apply mul_pos
  · unfold scaleSq
    exact sq_pos_of_pos (div_pos hη (by positivity))
  · exact Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], by linarith⟩

/-- The transformed scalar coefficient, including its exponential growth factor, is bounded by
the explicit Gaussian envelope under the stated pole-gap conditions. -/
theorem coefficient_envelope (n : ℕ) (b c d η β K : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4) (hK : 0 ≤ K)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (x y : ℝ) (hy : |y| ≤ β) :
    let z := (η : ℂ) * Complex.sinh ((x : ℂ) + y * I)
    ‖coefficient n b c d z‖ * Real.exp (max 0 z.im * K) ≤
      (kernelPrefactor n b η β * Real.exp (postExponent c d η β K)) *
        Real.exp (-(scaleSq c η * Real.cos (2 * β) / 2) * Real.sinh x ^ 2) := by
  (try dsimp only)
  let z := (η : ℂ) * Complex.sinh ((x : ℂ) + y * I)
  let P := (b + 1) ^ n / (2 * Real.pi)
  let D := ‖1 - I * z‖ * ‖(b : ℂ) + I * z‖ ^ n
  let D₀ := lowerDistance η β * poleDistance b η β ^ n
  let B := scaleSq c η * Real.cos (2 * β)
  let A := growth η β d K
  let q₀ := d - 1 / (4 * c ^ 2) + scaleSq c η * Real.sin β ^ 2
  have hB : 0 < B := gaussian_rate_pos hc hη hβ₀ hβ
  have hA : 0 ≤ A := by
    dsimp [A, growth]
    apply mul_nonneg
    · exact mul_nonneg hη.le (Real.sin_nonneg_of_nonneg_of_le_pi hβ₀ (by linarith [Real.pi_pos]))
    · positivity
  have hD₀ : 0 < D₀ := distance_product_pos n hη hβ₀ (by linarith [Real.pi_pos]) hgap hbn
  have hDD : D₀ ≤ D := mul_le_mul (lowerDistance_le η β x y hy)
    (pow_le_pow_left₀ (poleDistance_nonneg b η β hβ₀) (poleDistance_le b η β x y hy) n)
    (pow_nonneg (poleDistance_nonneg b η β hβ₀) _) (norm_nonneg _)
  have hF : d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2) - z.re ^ 2 / (4 * c ^ 2) +
      max 0 z.im * K ≤ postExponent c d η β K + (-(B / 2) * Real.sinh x ^ 2) := by
    have h1 : d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2) - z.re ^ 2 / (4 * c ^ 2) +
        max 0 z.im * K ≤ q₀ - B * Real.sinh x ^ 2 + A * Real.cosh x :=
      full_exponent_bound hc hη hβ₀ hβ hK hy d x
    have h2 := absorb_growth hB hA x
    change _ ≤ q₀ + A + A ^ 2 / (2 * B) + (-(B / 2) * Real.sinh x ^ 2)
    linear_combination h1 + h2
  have hP : 0 ≤ P := by dsimp [P]; positivity
  calc
    _ = P * Real.exp (d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2) -
        z.re ^ 2 / (4 * c ^ 2) + max 0 z.im * K) / D := by
      rw [norm_coefficient n b c d hb]
      simp only [neg_div]
      change P * Real.exp (d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2)) *
        Real.exp (-(z.re ^ 2 / (4 * c ^ 2))) / D * Real.exp (max 0 z.im * K) = _
      rw [show d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2) -
          z.re ^ 2 / (4 * c ^ 2) + max 0 z.im * K =
          (d * (1 + z.im) + (z.im ^ 2 - 1) / (4 * c ^ 2)) +
            (-(z.re ^ 2 / (4 * c ^ 2))) + max 0 z.im * K by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ P * Real.exp (postExponent c d η β K + (-(B / 2) * Real.sinh x ^ 2)) / D :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hF) hP) (hD₀.le.trans hDD)
    _ ≤ P * Real.exp (postExponent c d η β K + (-(B / 2) * Real.sinh x ^ 2)) / D₀ :=
      div_le_div_of_nonneg_left (by positivity) hD₀ hDD
    _ = _ := by
      rw [Real.exp_add]
      dsimp [P, D₀, B, kernelPrefactor]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- For Hermitian `H`, positive semidefinite `L`, and nonnegative time, the transformed
integrand is bounded by `stripAmplitude` times `bellB` under the stated strip conditions. -/
theorem norm_transformed_le_bell (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T : ℝ} (hT : 0 ≤ T)
    (x y : ℝ) (hy : |y| ≤ β) :
    ‖transformed n b c d T η H L ((x : ℂ) + y * I)‖ ≤
      stripAmplitude n b c d η β (T * ‖L‖) * bellB (scaleSq c η * Real.cos (2 * β)) x := by
  let z := (x : ℂ) + y * I
  let w := (η : ℂ) * Complex.sinh z
  let K := T * ‖L‖
  have hJac : ‖(η : ℂ) * Complex.cosh z‖ ≤ η * Real.cosh x := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hη.le]
    exact mul_le_mul_of_nonneg_left (norm_cosh_le x y) hη.le
  have hProp : ‖propagator H L T w‖ ≤ Real.exp (max 0 w.im * K) := by
    simpa only [K, mul_assoc] using! norm_propagator_le H L hH hL hT w
  have hcoef := coefficient_envelope n b c d η β K hb hc hη hβ₀ hβ
    (mul_nonneg hT (norm_nonneg _)) hgap hbn x y hy
  calc
    _ = ‖(η : ℂ) * Complex.cosh z‖ * (‖coefficient n b c d w‖ * ‖propagator H L T w‖) := by
      rw [transformed, integrand, norm_smul, norm_smul]
    _ ≤ (η * Real.cosh x) * (‖coefficient n b c d w‖ * Real.exp (max 0 w.im * K)) :=
      mul_le_mul hJac (mul_le_mul_of_nonneg_left hProp (norm_nonneg _)) (by positivity) (by positivity)
    _ ≤ (η * Real.cosh x) * ((kernelPrefactor n b η β * Real.exp (postExponent c d η β K)) *
        Real.exp (-(scaleSq c η * Real.cos (2 * β) / 2) * Real.sinh x ^ 2)) :=
      mul_le_mul_of_nonneg_left hcoef (by positivity)
    _ = _ := by dsimp [stripAmplitude, bellB, K]; ring

/-- Under the strip and pole-gap conditions, the transformed matrix integrand is integrable
along every horizontal line of the closed strip. -/
theorem transformed_integrable (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T : ℝ} (hT : 0 ≤ T)
    (y : ℝ) (hy : |y| ≤ β) :
    Integrable (fun x : ℝ => transformed n b c d T η H L ((x : ℂ) + y * I)) := by
  apply ((bellB_integrable (gaussian_rate_pos hc hη hβ₀ hβ)).const_mul
    (stripAmplitude n b c d η β (T * ‖L‖))).mono'
  · apply Continuous.aestronglyMeasurable
    exact continuous_iff_continuousAt.mpr fun x =>
      ((transformed_analytic n b c d T η β hη hβ₀ (by linarith [Real.pi_pos]) hgap hbn H L _
        (by simpa using! hy)).continuousAt.comp
          (by fun_prop : ContinuousAt (fun x : ℝ => (x : ℂ) + y * I) x))
  · filter_upwards [] with x
    exact norm_transformed_le_bell n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT x y hy

/-- The integral of the transformed integrand's norm along any horizontal line in the closed
strip is at most `stripMass` under the stated hypotheses. -/
theorem integral_norm_transformed_le (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T : ℝ} (hT : 0 ≤ T)
    (y : ℝ) (hy : |y| ≤ β) :
    (∫ x : ℝ, ‖transformed n b c d T η H L ((x : ℂ) + y * I)‖) ≤
      stripMass n b c d η β (T * ‖L‖) := by
  calc
    _ ≤ ∫ x : ℝ, stripAmplitude n b c d η β (T * ‖L‖) *
        bellB (scaleSq c η * Real.cos (2 * β)) x := by
      apply integral_mono
        (transformed_integrable n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT y hy).norm
        ((bellB_integrable (gaussian_rate_pos hc hη hβ₀ hβ)).const_mul _)
      intro x
      exact norm_transformed_le_bell n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT x y hy
    _ = _ := by rw [integral_const_mul, bellB_integral (gaussian_rate_pos hc hη hβ₀ hβ)]; rfl

/-- The envelope `bellB` is even. -/
theorem bellB_even (B x : ℝ) : bellB B (-x) = bellB B x := by
  simp only [bellB, Real.cosh_neg, Real.sinh_neg, neg_sq]

/-- Evaluating `bellB` at `|x|` gives its value at `x`. -/
theorem bellB_abs (B x : ℝ) : bellB B |x| = bellB B x := by
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
  · rw [abs_of_nonpos hx, bellB_even]

/-- The strip amplitude is nonnegative for positive `b` and `η` and nonnegative strip
half-width. -/
theorem amplitude_nonneg (n : ℕ) {b c d η β K : ℝ} (hb : 0 < b)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) : 0 ≤ stripAmplitude n b c d η β K := by
  dsimp [stripAmplitude, kernelPrefactor]
  rw [lowerDistance_eq]
  exact mul_nonneg (mul_nonneg hη.le (div_nonneg (by positivity)
    (mul_nonneg (mul_nonneg (by positivity) (poleDistance_nonneg _ _ _ hβ₀))
      (pow_nonneg (poleDistance_nonneg _ _ _ hβ₀) _)))) (Real.exp_pos _).le

/-- The transformed matrix integrand decays uniformly at both horizontal ends of the strip under
the stated pole-gap and positivity hypotheses. -/
theorem transformed_decay (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T : ℝ} (hT : 0 ≤ T) :
    Qatlib.Papers.CommutLCHS26.MainResults.StripContour.UniformDecay
      (transformed n b c d T η H L) (-β) β := by
  let B := scaleSq c η * Real.cos (2 * β)
  let D := stripAmplitude n b c d η β (T * ‖L‖)
  have hB : 0 < B := gaussian_rate_pos hc hη hβ₀ hβ
  have hD : 0 ≤ D := amplitude_nonneg n hb hη hβ₀
  have hs : Tendsto Real.sinh atTop atTop := by
    apply tendsto_atTop_mono' atTop _ tendsto_id
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact Real.self_le_sinh_iff.mpr hx
  have ht : Tendsto (fun x : ℝ => D * (1 + Real.sinh x) *
      Real.exp (-(B / 2) * Real.sinh x ^ 2)) atTop (𝓝 0) :=
    (bellB_decay hB D).comp hs
  intro ε hε
  obtain ⟨R, hR⟩ := eventually_atTop.mp (ht (Iio_mem_nhds hε))
  refine ⟨max R 0, fun x hx y hy => ?_⟩
  have hxR : R ≤ |x| := (le_max_left _ _).trans hx
  have he : D * (1 + Real.sinh |x|) * Real.exp (-(B / 2) * Real.sinh |x| ^ 2) ≤ ε :=
    le_of_lt (hR |x| hxR)
  have hcosh : Real.cosh |x| ≤ 1 + Real.sinh |x| := by
    simpa only [abs_of_nonneg (Real.sinh_nonneg_iff.mpr (abs_nonneg x))] using!
      cosh_le_one_add_abs_sinh |x|
  apply (norm_transformed_le_bell n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT x y
    (abs_le.mpr hy)).trans
  change D * bellB B x ≤ ε
  rw [← bellB_abs B x]
  exact (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcosh (Real.exp_pos _).le) hD).trans (by simpa only [mul_assoc] using! he)

/-- The infinite-mesh quadrature error for the transformed integrand is bounded by `2 *
stripMass / (exp (2πβ / h) - 1)` under the stated strip hypotheses, in the setting of [Aftab
et al., Lemma 4.16][AftabAnTrivisa2026]. -/
theorem transformed_mesh_error (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 < β) (hβ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef)
    {T h : ℝ} (hT : 0 ≤ T) (hh : 0 < h) :
    ‖(∫ x : ℝ, transformed n b c d T η H L (x : ℂ)) -
        h • ∑' j : ℤ, transformed n b c d T η H L ((h * (j : ℝ) : ℝ) : ℂ)‖ ≤
      2 * stripMass n b c d η β (T * ‖L‖) / (Real.exp (2 * Real.pi * β / h) - 1) := by
  apply Qatlib.Papers.CommutLCHS26.MainResults.StripSampling.analytic_strip_mesh_error
    _ _ _ _ hβ₀ hh
    (transformed_analytic n b c d T η β hη hβ₀.le (by linarith [Real.pi_pos]) hgap hbn H L)
    (transformed_decay n b c d η β hb hc hη hβ₀.le hβ hgap hbn H L hH hL hT)
  · intro y hy
    exact transformed_integrable n b c d η β hb hc hη hβ₀.le hβ hgap hbn H L hH hL hT y
      (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)
  · intro y hy
    exact integral_norm_transformed_le n b c d η β hb hc hη hβ₀.le hβ hgap hbn H L hH hL hT y
      (abs_le.mpr ⟨hy.1.le, hy.2.le⟩)

/-- The transformed integrand is analytic near the closed strip, decays uniformly, and has
integrable horizontal slices with norm integrals bounded by `stripMass`; see [Aftab et al.,
Lemma 4.16][AftabAnTrivisa2026]. -/
theorem transformed_strip_estimates (n : ℕ) (b c d η β : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hη : 0 < η) (hβ₀ : 0 ≤ β) (hβ : β < Real.pi / 4)
    (hgap : η * Real.sin β < 1) (hbn : n = 0 ∨ η * Real.sin β < b)
    (H L : Matrix ι ι ℂ) (hH : H.IsHermitian) (hL : L.PosSemidef) {T : ℝ} (hT : 0 ≤ T) :
    AnalyticOnNhd ℂ (transformed n b c d T η H L) {z : ℂ | |z.im| ≤ β} ∧
      Qatlib.Papers.CommutLCHS26.MainResults.StripContour.UniformDecay
        (transformed n b c d T η H L) (-β) β ∧
      ∀ y : ℝ, |y| ≤ β →
        Integrable (fun x : ℝ => transformed n b c d T η H L ((x : ℂ) + y * I)) ∧
        (∫ x : ℝ, ‖transformed n b c d T η H L ((x : ℂ) + y * I)‖) ≤
          stripMass n b c d η β (T * ‖L‖) := by
  exact ⟨transformed_analytic n b c d T η β hη hβ₀ (by linarith [Real.pi_pos]) hgap hbn H L,
    transformed_decay n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT,
    fun y hy => ⟨transformed_integrable n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT y hy,
      integral_norm_transformed_le n b c d η β hb hc hη hβ₀ hβ hgap hbn H L hH hL hT y hy⟩⟩

end Qatlib.Papers.CommutLCHS26.MainResults.SinhStrip
