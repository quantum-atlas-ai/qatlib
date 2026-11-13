/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

/-!
# Rational Cayley approximations to phase gates

`GaussianRat` stores rational real and imaginary parts. `cayleyRat` constructs an exact
unit-modulus rational point, and `countedCayleyPhase` repeatedly squares a scaled Cayley point
to approximate a complex exponential. The counters record the arithmetic operations explicitly
used by the construction.

The module derives an arctangent remainder bound, an explicit approximation error, and exact
preservation of unit modulus. `rationalPhaseGate` turns the resulting finite data into a
diagonal phase gate in the circuit setting of [NielsenChuang2010].

## Main statements

* `rational_cayley_unit_phase_and_angle`: the Cayley point has unit modulus and a known angle.
* `rational_cayley_actual_squaring_counts`: repeated squaring uses `4 * k` multiplications and
  `2 * k` additions or subtractions.
* `rational_cayley_explicit_precision`: the phase error satisfies cubic and geometric bounds.
* `rational_cayley_gate_unitarity_and_target_error`: the resulting gate is unitary and
  approximates `Rz`.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase

open Matrix
open scoped Matrix.Norms.L2Operator

/-- A pair of rational numbers representing the real and imaginary parts of a complex number. -/
abbrev GaussianRat := ℚ × ℚ

/-- Interprets a rational pair as the complex number `z.1 + z.2 * I`. -/
def gaussianRatComplex (z : GaussianRat) : ℂ := (z.1 : ℂ) + (z.2 : ℂ) * Complex.I

/-- The rational pair `((1 - x²) / (1 + x²), 2 * x / (1 + x²))` parametrizing a point on the
unit circle. -/
def cayleyRat (x : ℚ) : GaussianRat := ((1 - x ^ 2) / (1 + x ^ 2), 2 * x / (1 + x ^ 2))

/-- Squares a complex number represented by rational real and imaginary parts. -/
def squareGaussianRat (z : GaussianRat) : GaussianRat :=
  (z.1 * z.1 - z.2 * z.2, z.1 * z.2 + z.1 * z.2)

/-- Repeatedly squares a rational complex pair, recording four rational multiplications and two
additions or subtractions per iteration. -/
def squareLoop (z : GaussianRat) : ℕ → GaussianRat × ℕ × ℕ
  | 0 => (z, 0, 0)
  | k + 1 =>
    let previous := squareLoop z k
    (squareGaussianRat previous.1, previous.2.1 + 4, previous.2.2 + 2)

/-- Computes a power of two by repeated doubling and records the number of doubling steps. -/
def countedCayleyPowerTwo : ℕ → ℕ × ℕ
  | 0 => (1, 0)
  | k + 1 =>
    let previous := countedCayleyPowerTwo k
    (previous.1 * 2, previous.2 + 1)

/-- The repeated-doubling computation returns `2 ^ k` with counter `k`. -/
theorem countedCayleyPowerTwo_value_and_cost (k : ℕ) :
    countedCayleyPowerTwo k = (2 ^ k, k) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [countedCayleyPowerTwo, ih, pow_succ]

/-- Initializes the Cayley point at `x / (2 * 2 ^ k)` and records the doubling count together
with the fixed arithmetic counters. -/
def countedCayleyInit (x : ℚ) (k : ℕ) : GaussianRat × ℕ × ℕ × ℕ × ℕ :=
  let power := countedCayleyPowerTwo k
  let t := x / (2 * (power.1 : ℚ))
  let square := t * t
  let denominator := 1 + square
  (((1 - square) / denominator, (2 * t) / denominator), power.2, 3, 2, 3)

/-- The Cayley initializer returns `cayleyRat (x / (2 * 2 ^ k))` and the counter tuple `(k, 3,
2, 3)`. -/
theorem countedCayleyInit_value_and_cost (x : ℚ) (k : ℕ) :
    countedCayleyInit x k = (cayleyRat (x / (2 * (2 : ℚ) ^ k)), k, 3, 2, 3) := by
  simp [countedCayleyInit, countedCayleyPowerTwo_value_and_cost, cayleyRat, pow_two]

/-- Both denominators used by the scaled Cayley initialization are strictly positive. -/
theorem countedCayleyInit_denominators (x : ℚ) (k : ℕ) :
    (0 : ℚ) < 2 * (2 : ℚ) ^ k ∧
      (0 : ℚ) < 1 + (x / (2 * (2 : ℚ) ^ k)) ^ 2 := by
  constructor
  · positivity
  · linarith [sq_nonneg (x / (2 * (2 : ℚ) ^ k))]

/-- Approximates the phase at `x` by squaring the scaled Cayley initializer `k` times, retaining
the squaring-operation counters. -/
def countedCayleyPhase (x : ℚ) (k : ℕ) : GaussianRat × ℕ × ℕ :=
  squareLoop (countedCayleyInit x k).1 k

/-- The norm of `1 + x * I` is `sqrt (1 + x²)` for real `x`. -/
private theorem norm_one_add_mul_I (x : ℝ) : ‖(1:ℂ) + x * Complex.I‖ = Real.sqrt (1 + x ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  have hre : ((1:ℂ) + x * Complex.I).re = 1 := by
    simp [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
      mul_zero]
  have him : ((1:ℂ) + x * Complex.I).im = x := by
    simp [Complex.add_im, Complex.one_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im,
      mul_one]
  rw [hre, him]
  norm_num

/-- For rational `x`, the Cayley denominator `1 - x * I` is nonzero. -/
private theorem one_sub_mul_I_ne_zero (x : ℚ) : (1:ℂ) - (x:ℂ) * Complex.I ≠ 0 := by
  have hcast : (x:ℂ) = ((x:ℝ) : ℂ) := (Complex.ofReal_ratCast x).symm
  have hnorm : ‖(1:ℂ) - ((x:ℝ) : ℂ) * Complex.I‖ ≠ 0 := by
    have hform : (1:ℂ) - ((x:ℝ) : ℂ) * Complex.I
        = (1:ℂ) + (-(x:ℝ) : ℝ) * Complex.I := by
      push_cast
      ring
    rw [hform, norm_one_add_mul_I,
      show (-(x:ℝ)) ^ 2 = (x:ℝ) ^ 2 from by rw [pow_two, pow_two]; ring]
    positivity
  intro h
  rw [hcast] at h
  exact hnorm (by rw [h]; simp)

/-- The complex interpretation of the rational Cayley pair equals `(1 + x * I) / (1 - x * I)`. -/
theorem gaussianRatComplex_cayleyRat (x : ℚ) :
    gaussianRatComplex (cayleyRat x) = (1 + (x:ℂ) * Complex.I) / (1 - (x:ℂ) * Complex.I) := by
  have hq : ((1 + x ^ 2 : ℚ) : ℂ) ≠ 0 := by
    rw [← Complex.ofReal_ratCast]
    exact Complex.ofReal_ne_zero.mpr (by push_cast; intro h; linarith [sq_nonneg (x:ℝ)])
  have hmul : gaussianRatComplex (cayleyRat x) * ((1:ℂ) - (x:ℂ) * Complex.I)
      = (1:ℂ) + (x:ℂ) * Complex.I := by
    simp only [gaussianRatComplex, cayleyRat]
    push_cast
    push_cast at hq
    field_simp [hq]
    ring_nf
    simp only [pow_two, Complex.I_mul_I]
    ring
  rw [eq_div_iff (one_sub_mul_I_ne_zero x)]
  exact hmul

/-- The rational Cayley point has norm one and equals the complex exponential with angle `2 *
arctan x`. -/
theorem rational_cayley_unit_phase_and_angle (x : ℚ) :
    ‖gaussianRatComplex (cayleyRat x)‖ = 1 ∧
      gaussianRatComplex (cayleyRat x) = Complex.exp ((2 * Real.arctan (x:ℝ) : ℂ) * Complex.I) := by
  set t : ℝ := Real.arctan (x:ℝ) with htdef
  have hcos : 0 < Real.cos t := Real.cos_arctan_pos (x:ℝ)
  have hcosne : Real.cos t ≠ 0 := ne_of_gt hcos
  have htan : Real.sin t = (x:ℝ) * Real.cos t := by
    have h1 : Real.tan t = (x:ℝ) := Real.tan_arctan (x:ℝ)
    rw [Real.tan_eq_sin_div_cos] at h1
    exact (div_eq_iff hcosne).mp h1
  have hexp1 : Complex.exp ((t:ℂ) * Complex.I)
      = ((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I :=
    Complex.exp_ofReal_mul_I t
  have hexp2 : Complex.exp (((-t : ℝ) : ℂ) * Complex.I)
      = ((Real.cos t : ℝ) : ℂ) - ((Real.sin t : ℝ) : ℂ) * Complex.I := by
    rw [Complex.exp_ofReal_mul_I, Real.cos_neg, Real.sin_neg]
    push_cast
    ring

  have hcross : (1 + (x:ℂ) * Complex.I)
        * (((Real.cos t : ℝ) : ℂ) - ((Real.sin t : ℝ) : ℂ) * Complex.I)
      = (((Real.cos t : ℝ) : ℂ) + ((Real.sin t : ℝ) : ℂ) * Complex.I)
        * (1 - (x:ℂ) * Complex.I) := by
    rw [htan]
    push_cast
    ring
  have hden2 : ((Real.cos t : ℝ) : ℂ) - ((Real.sin t : ℝ) : ℂ) * Complex.I ≠ 0 := by
    intro h
    have h0 := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, sub_zero, Complex.zero_re] at h0
    exact absurd h0 hcosne
  have hexpquad : Complex.exp ((2 * t : ℂ) * Complex.I)
      = Complex.exp ((t:ℂ) * Complex.I) / Complex.exp (((-t : ℝ) : ℂ) * Complex.I) := by
    rw [div_eq_mul_inv, ← Complex.exp_neg, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hexpne : Complex.exp (((-t : ℝ) : ℂ) * Complex.I) ≠ 0 := by
    have hn := Complex.norm_exp_ofReal_mul_I (-t)
    exact fun h => by rw [h] at hn; simp at hn
  have hcross2 : (1 + (x:ℂ) * Complex.I) * Complex.exp (((-t : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((t:ℂ) * Complex.I) * (1 - (x:ℂ) * Complex.I) := by
    rw [hexp2, hexp1]
    exact hcross

  have hnorm : ‖gaussianRatComplex (cayleyRat x)‖ = 1 := by
    rw [gaussianRatComplex_cayleyRat, Complex.norm_div, (Complex.ofReal_ratCast x).symm]
    have h1 : ‖(1:ℂ) + ((x:ℝ) : ℂ) * Complex.I‖ = Real.sqrt (1 + (x:ℝ) ^ 2) :=
      norm_one_add_mul_I _
    have h2 : ‖(1:ℂ) - ((x:ℝ) : ℂ) * Complex.I‖ = Real.sqrt (1 + (x:ℝ) ^ 2) := by
      have hform : (1:ℂ) - ((x:ℝ) : ℂ) * Complex.I
          = (1:ℂ) + (-(x:ℝ) : ℝ) * Complex.I := by
        push_cast
        ring
      rw [hform, norm_one_add_mul_I, show (-(x:ℝ)) ^ 2 = (x:ℝ) ^ 2 from by ring]
    rw [h1, h2]
    exact div_self (ne_of_gt (Real.sqrt_pos_of_pos (by nlinarith : (0:ℝ) < 1 + (x:ℝ) ^ 2)))
  refine ⟨hnorm, ?_⟩
  rw [gaussianRatComplex_cayleyRat, hexpquad,
    div_eq_div_iff (one_sub_mul_I_ne_zero x) hexpne, hcross2]

/-- The distance between complex unit phases at real angles `a` and `b` is at most `|a - b|`. -/
theorem norm_exp_mul_I_sub_le (a b : ℝ) :
    ‖Complex.exp ((a:ℂ) * Complex.I) - Complex.exp ((b:ℂ) * Complex.I)‖ ≤ |a - b| := by
  have hsplit : Complex.exp ((a:ℂ) * Complex.I) - Complex.exp ((b:ℂ) * Complex.I)
      = Complex.exp ((b:ℂ) * Complex.I)
        * (Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1) := by
    rw [mul_sub, ← Complex.exp_add]
    congr 1
    · rw [← add_mul]
      push_cast
      ring
    · exact (mul_one _).symm
  calc ‖Complex.exp ((a:ℂ) * Complex.I) - Complex.exp ((b:ℂ) * Complex.I)‖
      = ‖Complex.exp ((b:ℂ) * Complex.I)‖
          * ‖Complex.exp (((a - b : ℝ) : ℂ) * Complex.I) - 1‖ := by
        rw [hsplit, norm_mul]
    _ ≤ 1 * ‖a - b‖ := by
        rw [Complex.norm_exp_ofReal_mul_I,
          show ((a - b : ℝ) : ℂ) * Complex.I = Complex.I * (a - b : ℂ) from by push_cast; ring]
        have h1 : ‖Complex.exp (Complex.I * ((a - b : ℝ) : ℂ)) - 1‖ ≤ ‖a - b‖ :=
          Real.norm_exp_I_mul_ofReal_sub_one_le
        have h2 : ((a - b : ℝ) : ℂ) = (↑a - ↑b : ℂ) := by push_cast; ring
        rw [h2] at h1
        linarith
    _ = |a - b| := by rw [Real.norm_eq_abs, one_mul]

/-- The rational-pair interpretation, explicit Cayley coordinates, and complex Cayley quotient
agree. -/
theorem rational_cayley_actual_finite_data :
    (∀ z : GaussianRat, gaussianRatComplex z = (z.1:ℂ) + (z.2:ℂ) * Complex.I) ∧
      (∀ x : ℚ, cayleyRat x = ((1 - x ^ 2) / (1 + x ^ 2), 2 * x / (1 + x ^ 2))) ∧
      (∀ x : ℚ, gaussianRatComplex (cayleyRat x) = (1 + (x:ℂ) * Complex.I) / (1 - (x:ℂ) * Complex.I)) :=
  ⟨fun _ => rfl, fun _ => rfl, gaussianRatComplex_cayleyRat⟩

/-- The function `t - arctan t` is monotone on the nonnegative real numbers. -/
private theorem monotoneOn_sub_arctan :
    MonotoneOn (fun t : ℝ => t - Real.arctan t) (Set.Ici 0) := by
  have hdiff : Differentiable ℝ (fun t : ℝ => t - Real.arctan t) := by
    intro u
    exact ((hasDerivAt_id u).sub (Real.hasDerivAt_arctan u)).differentiableAt
  refine monotoneOn_of_deriv_nonneg (convex_Ici (0:ℝ)) hdiff.continuous.continuousOn
    (hdiff.differentiableOn.mono interior_subset) ?_
  rw [interior_Ici]
  intro u hu
  have hd : deriv (fun t : ℝ => t - Real.arctan t) u = 1 - 1 / (1 + u ^ 2) :=
    ((hasDerivAt_id u).sub (Real.hasDerivAt_arctan u)).deriv
  rw [hd]
  refine sub_nonneg.mpr ?_
  exact (div_le_one (by linarith [sq_nonneg u] : (0:ℝ) < 1 + u ^ 2)).mpr
    (by linarith [sq_nonneg u])

/-- The function `t³ / 3 - (t - arctan t)` is monotone on the nonnegative real numbers. -/
private theorem monotoneOn_cubic_arctan :
    MonotoneOn (fun t : ℝ => t ^ 3 / 3 - (t - Real.arctan t)) (Set.Ici 0) := by
  have hdiff : Differentiable ℝ (fun t : ℝ => t ^ 3 / 3 - (t - Real.arctan t)) := by
    intro u
    exact ((((hasDerivAt_id u).pow 3).div_const 3).sub
      ((hasDerivAt_id u).sub (Real.hasDerivAt_arctan u))).differentiableAt
  refine monotoneOn_of_deriv_nonneg (convex_Ici (0:ℝ)) hdiff.continuous.continuousOn
    (hdiff.differentiableOn.mono interior_subset) ?_
  rw [interior_Ici]
  intro u hu
  have hd : deriv (fun t : ℝ => t ^ 3 / 3 - (t - Real.arctan t)) u
      = (3:ℝ) * u ^ 2 / 3 - (1 - 1 / (1 + u ^ 2)) := by
    have h := ((((hasDerivAt_id u).pow 3).div_const 3).sub
      ((hasDerivAt_id u).sub (Real.hasDerivAt_arctan u))).deriv
    simpa using! h
  rw [hd]
  have hform : (3:ℝ) * u ^ 2 / 3 - (1 - 1 / (1 + u ^ 2)) = u ^ 4 / (1 + u ^ 2) := by
    field_simp
    ring
  rw [hform]
  exact div_nonneg (by positivity) (by positivity)

/-- For every real `x`, the arctangent approximation error is bounded by `|x|³ / 3`. -/
theorem rational_cayley_derived_arctan_remainder (x : ℝ) :
    |Real.arctan x - x| ≤ |x| ^ 3 / 3 := by
  rcases le_or_gt 0 x with hx | hx
  · have h1 : 0 ≤ x - Real.arctan x := by
      simpa using monotoneOn_sub_arctan (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx)
        hx
    have h2 : x - Real.arctan x ≤ x ^ 3 / 3 := by
      simpa using monotoneOn_cubic_arctan (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx)
        hx
    rw [abs_sub_comm, abs_of_nonneg h1, show |x| = x from abs_of_nonneg hx]
    exact h2
  · have hx' : 0 ≤ -x := by linarith
    have h1 : 0 ≤ (-x) - Real.arctan (-x) := by
      simpa using monotoneOn_sub_arctan (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx') hx'
    have h2 : (-x) - Real.arctan (-x) ≤ (-x) ^ 3 / 3 := by
      simpa using monotoneOn_cubic_arctan (Set.mem_Ici.mpr (le_refl 0)) (Set.mem_Ici.mpr hx') hx'
    rw [Real.arctan_neg] at h1 h2
    have h2' : x - Real.arctan x ≤ (-x) ^ 3 / 3 := by linarith
    have habseq : |x - Real.arctan x| = (-x) - (-Real.arctan x) := by
      rw [abs_of_nonpos (show x - Real.arctan x ≤ 0 from by linarith)]
      ring
    rw [abs_sub_comm, habseq, show |x| = -x from abs_of_neg hx]
    exact h2

/-- Interpreting a squared rational pair in the complex numbers gives the square of its
interpretation. -/
theorem gaussianRatComplex_squareGaussianRat (z : GaussianRat) :
    gaussianRatComplex (squareGaussianRat z) = gaussianRatComplex z ^ 2 := by
  simp only [squareGaussianRat, gaussianRatComplex, pow_two]
  push_cast
  ring_nf
  simp only [pow_two, Complex.I_mul_I]
  ring

/-- After `k` squarings, the interpreted value is the original value to the power `2 ^ k`, with
counters `4 * k` and `2 * k`. -/
theorem squareLoop_value_and_counts (z : GaussianRat) : ∀ k : ℕ,
    gaussianRatComplex (squareLoop z k).1 = gaussianRatComplex z ^ (2 ^ k) ∧
    (squareLoop z k).2.1 = 4 * k ∧ (squareLoop z k).2.2 = 2 * k := by
  intro k
  induction k with
  | zero =>
    refine ⟨?_, rfl, rfl⟩
    show gaussianRatComplex (squareLoop z 0).1 = _
    simp [squareLoop]
  | succ k ih =>
    obtain ⟨hval, hm, ha⟩ := ih
    refine ⟨?_, ?_, ?_⟩
    · show gaussianRatComplex (squareGaussianRat (squareLoop z k).1) = _
      rw [gaussianRatComplex_squareGaussianRat, hval, Nat.pow_succ, pow_mul]
    · show (squareLoop z k).2.1 + 4 = 4 * (k + 1)
      rw [hm]
      omega
    · show (squareLoop z k).2.2 + 2 = 2 * (k + 1)
      rw [ha]
      omega

/-- The counted Cayley phase is the scaled Cayley point raised to `2 ^ k`, using counters `4 *
k` and `2 * k` for the squaring loop. -/
theorem rational_cayley_actual_squaring_counts (x : ℚ) (k : ℕ) :
    gaussianRatComplex (countedCayleyPhase x k).1 =
      (gaussianRatComplex (cayleyRat (x / (2 * (2:ℚ) ^ k)))) ^ (2 ^ k) ∧
    (countedCayleyPhase x k).2.1 = 4 * k ∧ (countedCayleyPhase x k).2.2 = 2 * k := by
  unfold countedCayleyPhase
  rw [countedCayleyInit_value_and_cost]
  exact squareLoop_value_and_counts (cayleyRat (x / (2 * (2:ℚ) ^ k))) k

/-- The real angle `2 * 2 ^ k * arctan (x / (2 * 2 ^ k))` of the repeated-squaring Cayley
construction. -/
noncomputable def rationalCayleyAngle (x : ℝ) (k : ℕ) : ℝ :=
  2 * (2 ^ k : ℝ) * Real.arctan (x / (2 * (2 ^ k : ℝ)))

/-- The counted rational Cayley phase equals the complex exponential at `rationalCayleyAngle`. -/
theorem gaussianRatComplex_countedCayleyPhase_eq_exp (x : ℚ) (k : ℕ) :
    gaussianRatComplex (countedCayleyPhase x k).1
      = Complex.exp ((rationalCayleyAngle (x:ℝ) k : ℂ) * Complex.I) := by
  have h3 := (rational_cayley_actual_squaring_counts x k).1
  have h2 := (rational_cayley_unit_phase_and_angle (x / (2 * (2:ℚ) ^ k))).2
  have harg : ((x / (2 * (2:ℚ) ^ k) : ℚ) : ℝ) = (x:ℝ) / (2 * ((2 ^ k : ℕ) : ℝ)) := by
    push_cast
    field_simp
  rw [h3, h2, harg, ← Complex.exp_nat_mul]
  congr 1
  have hscal : ((rationalCayleyAngle (x:ℝ) k : ℝ) : ℂ)
      = ((2 ^ k : ℕ) : ℂ) * ((2:ℂ) * (Real.arctan ((x:ℝ) / (2 * ((2 ^ k : ℕ) : ℝ))) : ℂ)) := by
    simp only [rationalCayleyAngle]
    push_cast
    ring
  rw [hscal, ← mul_assoc]

/-- For rational `x` with `|x| ≤ 1`, the phase error is at most `|x|³ / (12 * (2 ^ k)²)` and at
most `(1 / 2) ^ k`. -/
theorem rational_cayley_explicit_precision (x : ℚ) (k : ℕ) (hx : |(x:ℝ)| ≤ 1) :
    ‖gaussianRatComplex (countedCayleyPhase x k).1 - Complex.exp ((x:ℂ) * Complex.I)‖ ≤
      |(x:ℝ)| ^ 3 / (12 * ((2 ^ k : ℕ) : ℝ) ^ 2) ∧
    ‖gaussianRatComplex (countedCayleyPhase x k).1 - Complex.exp ((x:ℂ) * Complex.I)‖ ≤
      ((2:ℝ) ⁻¹) ^ k := by
  have hNpos : (0:ℝ) < 2 * ((2 ^ k : ℕ) : ℝ) := by positivity
  have hcast : ((2 ^ k : ℕ) : ℝ) = (2:ℝ) ^ k := by push_cast; ring
  have h2N : (2:ℝ) ^ k ≠ 0 := by
    have h : (0:ℝ) < 2 ^ k := by positivity
    exact ne_of_gt h

  have hfactor : rationalCayleyAngle (x:ℝ) k - (x:ℝ)
      = 2 * ((2 ^ k : ℕ) : ℝ)
        * (Real.arctan (x / (2 * ((2 ^ k : ℕ) : ℝ))) - x / (2 * ((2 ^ k : ℕ) : ℝ))) := by
    rw [rationalCayleyAngle, hcast]
    field_simp

  have habsdiv : |x / (2 * ((2 ^ k : ℕ) : ℝ))| = |(x:ℝ)| / (2 * ((2 ^ k : ℕ) : ℝ)) := by
    rw [abs_div, abs_of_pos hNpos]
  have hdivpow : |x / (2 * ((2 ^ k : ℕ) : ℝ))| ^ 3
      = |(x:ℝ)| ^ 3 / (2 * ((2 ^ k : ℕ) : ℝ)) ^ 3 := by
    rw [habsdiv, div_pow]
  have hbound : 2 * ((2 ^ k : ℕ) : ℝ)
        * |Real.arctan (x / (2 * ((2 ^ k : ℕ) : ℝ))) - x / (2 * ((2 ^ k : ℕ) : ℝ))|
      ≤ |(x:ℝ)| ^ 3 / (12 * ((2 ^ k : ℕ) : ℝ) ^ 2) := by
    have hstep := rational_cayley_derived_arctan_remainder (x / (2 * ((2 ^ k : ℕ) : ℝ)))
    rw [hdivpow] at hstep
    calc 2 * ((2 ^ k : ℕ) : ℝ)
          * |Real.arctan (x / (2 * ((2 ^ k : ℕ) : ℝ))) - x / (2 * ((2 ^ k : ℕ) : ℝ))|
        ≤ 2 * ((2 ^ k : ℕ) : ℝ)
            * (|(x:ℝ)| ^ 3 / (2 * ((2 ^ k : ℕ) : ℝ)) ^ 3 / 3) :=
          mul_le_mul_of_nonneg_left hstep (le_of_lt hNpos)
      _ = |(x:ℝ)| ^ 3 / (12 * ((2 ^ k : ℕ) : ℝ) ^ 2) := by
          field_simp
          ring
  have hv := gaussianRatComplex_countedCayleyPhase_eq_exp x k
  have hchain : ‖gaussianRatComplex (countedCayleyPhase x k).1
        - Complex.exp ((x:ℂ) * Complex.I)‖
      ≤ |(x:ℝ)| ^ 3 / (12 * ((2 ^ k : ℕ) : ℝ) ^ 2) := by
    calc ‖gaussianRatComplex (countedCayleyPhase x k).1
          - Complex.exp ((x:ℂ) * Complex.I)‖
        ≤ |rationalCayleyAngle (x:ℝ) k - (x:ℝ)| := by
          rw [hv]; exact norm_exp_mul_I_sub_le _ _
      _ = 2 * ((2 ^ k : ℕ) : ℝ)
          * |Real.arctan (x / (2 * ((2 ^ k : ℕ) : ℝ))) - x / (2 * ((2 ^ k : ℕ) : ℝ))| := by
          rw [hfactor, abs_mul, abs_of_pos hNpos]
      _ ≤ |(x:ℝ)| ^ 3 / (12 * ((2 ^ k : ℕ) : ℝ) ^ 2) := hbound
  refine ⟨hchain, ?_⟩

  have hcubic : |(x:ℝ)| ^ 3 ≤ 1 := by
    have h2 : |(x:ℝ)| ^ 3 = |(x:ℝ)| * |(x:ℝ)| * |(x:ℝ)| := by
      rw [pow_succ']
      ring
    nlinarith [h2, hx, abs_nonneg (x:ℝ)]
  have hN1 : (1:ℝ) ≤ ((2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_pow' k 1
  have hinv : ((2:ℝ) ⁻¹) ^ k = 1 / ((2 ^ k : ℕ) : ℝ) := by
    rw [hcast, inv_pow, inv_eq_one_div]
  calc ‖gaussianRatComplex (countedCayleyPhase x k).1
        - Complex.exp ((x:ℂ) * Complex.I)‖
      ≤ |(x:ℝ)| ^ 3 / (12 * ((2 ^ k : ℕ) : ℝ) ^ 2) := hchain
    _ ≤ 1 / (12 * ((2 ^ k : ℕ) : ℝ) ^ 2) := by
        have hpos : (0:ℝ) < 12 * ((2 ^ k : ℕ) : ℝ) ^ 2 := by nlinarith [hN1]
        rw [div_eq_mul_inv, div_eq_mul_inv]
        exact mul_le_mul_of_nonneg_right hcubic (inv_nonneg.mpr (le_of_lt hpos))
    _ ≤ 1 / ((2 ^ k : ℕ) : ℝ) :=
        one_div_le_one_div_of_le
          (by nlinarith [hNpos] : (0:ℝ) < ((2 ^ k : ℕ) : ℝ))
          (show ((2 ^ k : ℕ) : ℝ) ≤ 12 * ((2 ^ k : ℕ) : ℝ) ^ 2 by
            nlinarith [hN1, sq_nonneg ((2 ^ k : ℕ) : ℝ)])
    _ = ((2:ℝ) ⁻¹) ^ k := hinv.symm

/-- The counted rational Cayley phase has complex norm exactly one for every input and iteration
count. -/
theorem gaussianRatComplex_countedCayleyPhase_norm (x : ℚ) (k : ℕ) :
    ‖gaussianRatComplex (countedCayleyPhase x k).1‖ = 1 := by
  rw [(rational_cayley_actual_squaring_counts x k).1, norm_pow,
    (rational_cayley_unit_phase_and_angle _).1, one_pow]

/-- The diagonal Boolean-register gate with entries one and the complex interpretation of the
rational phase pair. -/
def rationalPhaseGate (z : GaussianRat) : Matrix Bool Bool ℂ :=
  Matrix.diagonal fun a => if a then gaussianRatComplex z else 1

/-- A rational phase pair of complex norm one determines a unitary diagonal phase gate. -/
theorem rationalPhaseGate_mem_unitaryGroup {z : GaussianRat}
    (hz : ‖gaussianRatComplex z‖ = 1) : rationalPhaseGate z ∈ Matrix.unitaryGroup Bool ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold rationalPhaseGate
  rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  show star (if a then gaussianRatComplex z else 1)
      * (if a then gaussianRatComplex z else 1) = 1
  split_ifs with ha
  · rw [RCLike.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hz]
    norm_num
  · simp

/-- The counted rational phase gate is unitary; when `|x| ≤ 1`, its matrix-norm distance from
`Rz x` is at most `(1 / 2) ^ k`. -/
theorem rational_cayley_gate_unitarity_and_target_error (x : ℚ) (k : ℕ) :
    rationalPhaseGate (countedCayleyPhase x k).1 ∈ Matrix.unitaryGroup Bool ℂ ∧
      (|(x:ℝ)| ≤ 1 → ‖rationalPhaseGate (countedCayleyPhase x k).1 - Rz (x:ℝ)‖
        ≤ ((2:ℝ) ⁻¹) ^ k) := by
  refine ⟨rationalPhaseGate_mem_unitaryGroup
    (gaussianRatComplex_countedCayleyPhase_norm x k), fun hx => ?_⟩
  have hsub : rationalPhaseGate (countedCayleyPhase x k).1 - Rz (x:ℝ)
      = Matrix.diagonal fun a =>
        if a then (gaussianRatComplex (countedCayleyPhase x k).1
          - Complex.exp ((x:ℂ) * Complex.I)) else 0 := by
    unfold rationalPhaseGate Rz
    rw [Matrix.diagonal_sub]
    congr 1
    funext a
    by_cases h : a
    · simp [h]
    · simp [h]
  rw [hsub, Matrix.l2_opNorm_diagonal]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 ?_
  intro b
  by_cases h : b
  · simpa [h] using (rational_cayley_explicit_precision x k hx).2
  · simp [h]

end Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase
