/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Hadamard basis dynamics and runtime bounds

Defines the real Walsh signs and `hadBasisDriver`, a diagonal matrix with a rank-one Walsh
correction, and derives the evolution of the zero-string probability. Finite-dimensional inner
product estimates, a two-vector probability bound, and norm conservation give bounds on the
final Hadamard-transformed amplitude and on the required runtime. See [IoannouMosca2008].

## Main statements

* `twoAmplitudeBound`: Bounds two squared overlaps using the overlap of the two unit vectors.
* `eq30_success_bound_normalized`: Bounds success probability for evolution starting at the
  zero-string basis vector.
* `runtime_lower_bound_normalized`: Converts the success estimate into a runtime lower bound.

## References

* [Ioannou and Mosca, 2008][IoannouMosca2008]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
noncomputable section

namespace Qatlib.Papers.AdiabLimit07.MainResults

open Matrix
open scoped BigOperators
open Qatlib.Foundations.PureStateMath

variable {n : ℕ}

/-- The real Walsh sign given by the product of `-1` over coordinates where both strings are
true. -/
def hadWalshChar (w x : Reg n) : ℝ := ∏ i, if w i && x i then (-1 : ℝ) else 1

/-- The Walsh sign against the zero string is one. -/
@[simp] theorem hadWalshChar_zeroStr (w : Reg n) : hadWalshChar w (ZeroStr n) = 1 := by
  simp [hadWalshChar, ZeroStr]

/-- The square of every real Walsh sign is one. -/
theorem hadWalshChar_sq (w x : Reg n) : hadWalshChar w x ^ 2 = 1 := by
  unfold hadWalshChar
  rw [← Finset.prod_pow]
  apply Finset.prod_eq_one
  intro i _
  split_ifs <;> norm_num

/-- The Hadamard basis driver with diagonal energies `(1 - s) * F x + s * E1` and the rank-one
Walsh correction scaled by `s * E1 / 2 ^ n`. -/
def hadBasisDriver (F : Reg n → ℝ) (E1 s : ℝ) (w : Reg n) :
    Matrix (Reg n) (Reg n) ℂ :=
  Matrix.of fun x y =>
    (((1 - s) * F x + s * E1 : ℝ) : ℂ) * (if x = y then (1 : ℂ) else 0)
      - (((s * E1 / (2 : ℝ) ^ n) * (hadWalshChar w x * hadWalshChar w y) : ℝ) : ℂ)

/-- The action of `hadBasisDriver` on the time-dependent state at time `t`. -/
def hadBasisAction (F : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ → ℝ)
    (β : ℝ → QState (Reg n)) (t : ℝ) : QState (Reg n) :=
  (hadBasisDriver F E1 (s t) w).mulVec (β t)

/-- The zero-string row of the driver consists of its diagonal term minus the scaled Walsh sign. -/
theorem hadBasisDriver_zeroStr_apply (F : Reg n → ℝ) (E1 s : ℝ) (w y : Reg n) :
    hadBasisDriver F E1 s w (ZeroStr n) y =
      (((1 - s) * F (ZeroStr n) + s * E1 : ℝ) : ℂ) *
          (if ZeroStr n = y then (1 : ℂ) else 0)
        - (((s * E1 / (2 : ℝ) ^ n) * hadWalshChar w y : ℝ) : ℂ) := by
  unfold hadBasisDriver
  simp only [Matrix.of_apply, hadWalshChar_zeroStr, one_mul]

/-- The zero-string component of the driver action is its diagonal contribution minus a scaled
Walsh-weighted amplitude sum. -/
theorem hadBasisAction_zeroStr (F : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ → ℝ)
    (β : ℝ → QState (Reg n)) (t : ℝ) :
    hadBasisAction F E1 w s β t (ZeroStr n) =
      (((1 - s t) * F (ZeroStr n) + s t * E1 : ℝ) : ℂ) * β t (ZeroStr n)
        - (((s t * E1 / (2 : ℝ) ^ n) : ℝ) : ℂ) *
            ∑ y, ((hadWalshChar w y : ℝ) : ℂ) * β t y := by
  unfold hadBasisAction
  rw [Matrix.mulVec, dotProduct]
  simp only [hadBasisDriver_zeroStr_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single (ZeroStr n)]
    · simp
    · intro y _ hy
      rw [if_neg (Ne.symm hy)]
      simp
    · intro h
      exact absurd (Finset.mem_univ (ZeroStr n)) h
  · simp only [Complex.ofReal_mul, mul_assoc]
    rw [← Finset.mul_sum]

/-- The real inner product expression for the derivative of a squared amplitude equals `-(2 * B)
* im (conj a * S)`. -/
theorem inner_val (a S : ℂ) (A B : ℝ) :
    2 * inner ℝ a ((-Complex.I) * ((A : ℂ) * a - (B : ℂ) * S)) =
      -(2 * B) * (star a * S).im := by
  rw [Complex.inner]
  have h : ((-Complex.I) * ((A : ℂ) * a - (B : ℂ) * S)) * (starRingEnd ℂ) a
      = -((A : ℝ) : ℂ) * (Complex.I * (a * (starRingEnd ℂ) a))
        + ((B : ℝ) : ℂ) * (Complex.I * (S * (starRingEnd ℂ) a)) := by
    ring
  rw [h]
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.I_re, Complex.I_im, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.star_def]
  ring

/-- The imaginary part of a conjugated amplitude times a real-weighted sum equals the
corresponding sum of imaginary parts. -/
theorem im_star_mul_sum (a : ℂ) (χ : Reg n → ℝ) (b : Reg n → ℂ) :
    (star a * ∑ y, ((χ y : ℝ) : ℂ) * b y).im =
      ∑ y, χ y * (star a * b y).im := by
  rw [Finset.mul_sum, Complex.im_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [← mul_assoc]
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The squared zero-string amplitude has derivative given by the scaled Walsh-weighted
imaginary coupling sum under the stated vector differential equation [IoannouMosca2008]. -/
theorem hadBasis_zero_deriv (F : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ → ℝ)
    (β : ℝ → QState (Reg n))
    (hode : ∀ t, HasDerivAt β (fun x => (-Complex.I) * hadBasisAction F E1 w s β t x) t)
    (t : ℝ) :
    HasDerivAt (fun u => ‖β u (ZeroStr n)‖ ^ 2)
      (-(2 * s t * E1 / (2 : ℝ) ^ n) *
        ∑ y, hadWalshChar w y * ((star (β t (ZeroStr n))) * β t y).im) t := by
  have hg : HasDerivAt (fun u => β u (ZeroStr n))
      ((-Complex.I) * hadBasisAction F E1 w s β t (ZeroStr n)) t := by
    simpa only [Function.comp, ContinuousLinearMap.proj_apply] using!
      (ContinuousLinearMap.proj (ZeroStr n)).hasFDerivAt.comp_hasDerivAt t (hode t)
  have h1 := hg.norm_sq
  rw [hadBasisAction_zeroStr] at h1
  convert! h1 using 1
  rw [inner_val, im_star_mul_sum]
  ring

/-- If the squared norm of `b` is at most one, the absolute Walsh-weighted imaginary coupling
sum is at most `sqrt (2 ^ n)`. -/
theorem flow_sum_abs_le (w : Reg n) (b : QState (Reg n))
    (hb : ∑ y, ‖b y‖ ^ 2 ≤ 1) :
    |∑ y, hadWalshChar w y * ((star (b (ZeroStr n))) * b y).im| ≤
      Real.sqrt ((2 : ℝ) ^ n) := by
  rw [← im_star_mul_sum (b (ZeroStr n)) (hadWalshChar w) b]
  set S : ℂ := ∑ y, ((hadWalshChar w y : ℝ) : ℂ) * b y with hS
  have hs0 : 0 ≤ ∑ y, ‖b y‖ ^ 2 := by positivity
  have hNpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have ha : ‖b (ZeroStr n)‖ ≤ Real.sqrt (∑ y, ‖b y‖ ^ 2) := by
    have hterm : ‖b (ZeroStr n)‖ ^ 2 ≤ ∑ y, ‖b y‖ ^ 2 :=
      Finset.single_le_sum (f := fun y => ‖b y‖ ^ 2) (fun i _ => by positivity)
        (Finset.mem_univ (ZeroStr n))
    calc ‖b (ZeroStr n)‖ = Real.sqrt (‖b (ZeroStr n)‖ ^ 2) :=
          (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (∑ y, ‖b y‖ ^ 2) := Real.sqrt_le_sqrt hterm
  have ha1 : ‖b (ZeroStr n)‖ ≤ 1 :=
    ha.trans (Real.sqrt_le_one.mpr hb)
  have hSle : ‖S‖ ≤ Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt (∑ y, ‖b y‖ ^ 2) := by
    have h1 : ‖S‖ ≤ ∑ y, ‖b y‖ := by
      calc ‖S‖ = ‖∑ y, ((hadWalshChar w y : ℝ) : ℂ) * b y‖ := by rw [hS]
        _ ≤ ∑ y, ‖((hadWalshChar w y : ℝ) : ℂ) * b y‖ := norm_sum_le _ _
        _ = ∑ y, ‖b y‖ := by
            apply Finset.sum_congr rfl
            intro y _
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            have habs : |hadWalshChar w y| = 1 := by
              rw [← Real.sqrt_sq_eq_abs, hadWalshChar_sq, Real.sqrt_one]
            rw [habs, one_mul]
    calc ‖S‖ ≤ ∑ y, ‖b y‖ := h1
      _ = ∑ y, (1 : ℝ) * ‖b y‖ := by simp
      _ ≤ Real.sqrt (∑ y, (1 : ℝ) ^ 2) * Real.sqrt (∑ y, ‖b y‖ ^ 2) :=
            Real.sum_mul_le_sqrt_mul_sqrt _ _ _
      _ = Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt (∑ y, ‖b y‖ ^ 2) := by
            rw [Finset.sum_const, Finset.card_univ, card_reg, nsmul_eq_mul]
            norm_num
  calc |(star (b (ZeroStr n)) * S).im| ≤ ‖star (b (ZeroStr n)) * S‖ :=
        Complex.abs_im_le_norm _
    _ = ‖b (ZeroStr n)‖ * ‖S‖ := by rw [norm_mul, norm_star]
    _ ≤ Real.sqrt (∑ y, ‖b y‖ ^ 2) *
          (Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt (∑ y, ‖b y‖ ^ 2)) := by
          exact mul_le_mul ha hSle (by positivity) (by positivity)
    _ = Real.sqrt ((2 : ℝ) ^ n) * (∑ y, ‖b y‖ ^ 2) := by
          rw [show Real.sqrt (∑ y, ‖b y‖ ^ 2) *
                (Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt (∑ y, ‖b y‖ ^ 2))
              = Real.sqrt ((2 : ℝ) ^ n) *
                (Real.sqrt (∑ y, ‖b y‖ ^ 2) * Real.sqrt (∑ y, ‖b y‖ ^ 2)) by ring,
            Real.mul_self_sqrt hs0]
    _ ≤ Real.sqrt ((2 : ℝ) ^ n) * 1 :=
          mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Real.sqrt ((2 : ℝ) ^ n) := by ring

/-- Under the evolution, schedule, and norm bounds, an initial zero-string amplitude of one
yields final squared amplitude at least `1 - 2 * E1 * T / sqrt (2 ^ n)` [IoannouMosca2008]. -/
theorem hadBasis_start_lower (F : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ → ℝ)
    (β : ℝ → QState (Reg n)) (T : ℝ) (hT : 0 ≤ T)
    (hE1 : 0 ≤ E1) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hode : ∀ t, HasDerivAt β (fun x => (-Complex.I) * hadBasisAction F E1 w s β t x) t)
    (hnorm : ∀ t ∈ Set.Icc 0 T, ∑ y, ‖β t y‖ ^ 2 ≤ 1)
    (hstart : β 0 (ZeroStr n) = 1) :
    ‖β T (ZeroStr n)‖ ^ 2 ≥ 1 - 2 * E1 * T / Real.sqrt ((2 : ℝ) ^ n) := by
  set f : ℝ → ℝ := fun u => ‖β u (ZeroStr n)‖ ^ 2 with hf
  set g : ℝ → ℝ := fun u =>
    -(2 * s u * E1 / (2 : ℝ) ^ n) *
      ∑ y, hadWalshChar w y * ((star (β u (ZeroStr n))) * β u y).im with hg
  have hderiv : ∀ u, HasDerivAt f (g u) u := by
    intro u
    rw [hf, hg]
    exact hadBasis_zero_deriv F E1 w s β hode u
  have hNpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hsqrtN : 0 < Real.sqrt ((2 : ℝ) ^ n) := Real.sqrt_pos_of_pos hNpos
  have hNsq : Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ n :=
    Real.mul_self_sqrt (le_of_lt hNpos)
  have hbound : ∀ u ∈ Set.Icc 0 T, ‖g u‖ ≤ 2 * E1 / Real.sqrt ((2 : ℝ) ^ n) := by
    intro u hu
    have hcoef : 0 ≤ 2 * s u * E1 / (2 : ℝ) ^ n :=
      div_nonneg (by nlinarith [hs0 u, hE1]) (by positivity)
    have hsum := flow_sum_abs_le w (β u) (hnorm u hu)
    rw [hg]
    rw [norm_mul, norm_neg, Real.norm_of_nonneg hcoef, Real.norm_eq_abs]
    calc 2 * s u * E1 / (2 : ℝ) ^ n *
          |∑ y, hadWalshChar w y * ((star (β u (ZeroStr n))) * β u y).im|
        ≤ 2 * s u * E1 / (2 : ℝ) ^ n * Real.sqrt ((2 : ℝ) ^ n) :=
          mul_le_mul_of_nonneg_left hsum hcoef
      _ = 2 * s u * E1 / Real.sqrt ((2 : ℝ) ^ n) := by
          rw [← hNsq]
          field_simp
          rw [Real.sqrt_sq (Real.sqrt_nonneg ((2 : ℝ) ^ n))]
      _ ≤ 2 * E1 / Real.sqrt ((2 : ℝ) ^ n) := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hsqrtN)
          nlinarith [hs1 u, hE1]
  have hmvt : ‖f T - f 0‖ ≤
      (2 * E1 / Real.sqrt ((2 : ℝ) ^ n)) * ‖T - 0‖ :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (f := f) (f' := g) (s := Set.Icc 0 T) (x := 0) (y := T)
      (C := 2 * E1 / Real.sqrt ((2 : ℝ) ^ n))
      (fun u hu => (hderiv u).hasDerivWithinAt) hbound
      (convex_Icc 0 T) (Set.left_mem_Icc.mpr hT) (Set.right_mem_Icc.mpr hT)
  have hf0 : f 0 = 1 := by rw [hf]; simp [hstart]
  rw [hf0, Real.norm_eq_abs, sub_zero, Real.norm_of_nonneg hT] at hmvt
  have hge : f T ≥ 1 - (2 * E1 / Real.sqrt ((2 : ℝ) ^ n)) * T := by
    have := (abs_le.mp hmvt).1
    linarith
  have harith : (2 * E1 / Real.sqrt ((2 : ℝ) ^ n)) * T =
      2 * E1 * T / Real.sqrt ((2 : ℝ) ^ n) := by ring
  rw [harith] at hge
  rw [hf] at hge
  exact hge

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The complex coordinate inner product `PureStateMath.Inner` on finite quantum states. -/
abbrev QInner (ψ φ : QState I) : ℂ :=
  Qatlib.Foundations.PureStateMath.Inner ψ φ

/-- The sum of squared complex norms of the coordinates of a state. -/
def nrmSq (ψ : QState I) : ℝ := ∑ i, ‖ψ i‖ ^ 2

/-- The coordinate inner product is additive in its second argument. -/
theorem inner_add_right (ψ φ χ : QState I) :
    QInner ψ (φ + χ) = QInner ψ φ + QInner ψ χ := by
  simp only [QInner, Qatlib.Foundations.PureStateMath.Inner,
    Pi.add_apply, mul_add, Finset.sum_add_distrib, dotProduct]

/-- The coordinate inner product is complex linear in its second argument. -/
theorem inner_smul_right (ψ φ : QState I) (a : ℂ) :
    QInner ψ (a • φ) = a * QInner ψ φ := by
  simp only [QInner, Qatlib.Foundations.PureStateMath.Inner,
    Pi.smul_apply, smul_eq_mul, Finset.mul_sum, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The coordinate inner product is conjugate symmetric. -/
theorem inner_conj_symm (ψ φ : QState I) : QInner ψ φ = star (QInner φ ψ) := by
  simp only [QInner, Qatlib.Foundations.PureStateMath.Inner, dotProduct]
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [mul_comm, star_mul]

/-- The coordinate inner product is additive in its first argument. -/
theorem inner_add_left (ψ φ χ : QState I) :
    QInner (ψ + φ) χ = QInner ψ χ + QInner φ χ := by
  rw [inner_conj_symm, inner_add_right, star_add, ← inner_conj_symm, ← inner_conj_symm]

/-- Scaling the first argument multiplies the inner product by the conjugate scalar. -/
theorem inner_smul_left (ψ φ : QState I) (a : ℂ) :
    QInner (a • ψ) φ = (star a) * QInner ψ φ := by
  rw [inner_conj_symm, inner_smul_right, star_mul, ← inner_conj_symm, mul_comm]

/-- The inner product of a state with itself is the complex coercion of its squared norm. -/
theorem inner_self_nrmSq (ψ : QState I) : QInner ψ ψ = (nrmSq ψ : ℂ) := by
  rw [QInner, Qatlib.Foundations.PureStateMath.inner_self,
    nrmSq, Complex.ofReal_sum]

/-- The norm of the inner product is at most the product of the square roots of the two squared
norms. -/
theorem inner_norm_le (ψ φ : QState I) :
    ‖QInner ψ φ‖ ≤ Real.sqrt (nrmSq ψ) * Real.sqrt (nrmSq φ) := by
  rw [QInner, Qatlib.Foundations.PureStateMath.Inner, dotProduct]
  calc ‖∑ i, (starRingEnd ℂ) (ψ i) * φ i‖
      ≤ ∑ i, ‖(starRingEnd ℂ) (ψ i) * φ i‖ := norm_sum_le _ _
    _ = ∑ i, ‖ψ i‖ * ‖φ i‖ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [norm_mul, Complex.norm_conj]
    _ ≤ Real.sqrt (∑ i, ‖ψ i‖ ^ 2) * Real.sqrt (∑ i, ‖φ i‖ ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (nrmSq ψ) * Real.sqrt (nrmSq φ) := by rw [nrmSq, nrmSq]

/-- The coordinate inner product preserves subtraction in its second argument. -/
theorem inner_sub_right (ψ φ χ : QState I) :
    QInner ψ (φ - χ) = QInner ψ φ - QInner ψ χ := by
  rw [sub_eq_add_neg, inner_add_right, ← neg_one_smul ℂ χ, inner_smul_right]
  ring

/-- The coordinate inner product preserves subtraction in its first argument. -/
theorem inner_sub_left (ψ φ χ : QState I) :
    QInner (ψ - φ) χ = QInner ψ χ - QInner φ χ := by
  rw [sub_eq_add_neg, inner_add_left, ← neg_one_smul ℂ φ, inner_smul_left]
  simp
  rw [sub_eq_add_neg]

/-- For two orthonormal vectors, the sum of squared overlaps with any vector is at most its
squared norm. -/
theorem bessel2 (e f z : QState I)
    (he : QInner e e = 1) (hf : QInner f f = 1) (hef : QInner e f = 0) :
    ‖QInner e z‖ ^ 2 + ‖QInner f z‖ ^ 2 ≤ nrmSq z := by
  have hef' : QInner f e = 0 := by rw [inner_conj_symm, hef, star_zero]
  set u := QInner e z with hu
  set v := QInner f z with hv
  set w : QState I := z - u • e - v • f with hw
  have hew : QInner e w = 0 := by
    simp only [hw, inner_sub_right, inner_smul_right, he, hef, mul_one, mul_zero,
      hu, sub_self]
  have hfw : QInner f w = 0 := by
    simp only [hw, inner_sub_right, inner_smul_right, hf, hef', mul_one, mul_zero,
      sub_zero, hv, sub_self]
  have hwe : QInner w e = 0 := by rw [inner_conj_symm, hew, star_zero]
  have hwf : QInner w f = 0 := by rw [inner_conj_symm, hfw, star_zero]
  have hz : z = u • e + v • f + w := by
    simp only [hw]
    abel
  have hzz : QInner z z = (star u * u + star v * v) + QInner w w := by
    conv_lhs => rw [hz]
    simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
      he, hf, hef, hef', hew, hfw, hwe, hwf, mul_one, mul_zero, add_zero, zero_add]
    ring
  have hwu : (star u * u).re = ‖u‖ ^ 2 := by
    have h := Complex.normSq_eq_conj_mul_self (z := u)
    rw [Complex.star_def, ← h, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hwv : (star v * v).re = ‖v‖ ^ 2 := by
    have h := Complex.normSq_eq_conj_mul_self (z := v)
    rw [Complex.star_def, ← h, Complex.normSq_eq_norm_sq, Complex.ofReal_re]
  have hre := congrArg Complex.re hzz
  rw [inner_self_nrmSq, Complex.ofReal_re, Complex.add_re, Complex.add_re, hwu, hwv,
    inner_self_nrmSq, Complex.ofReal_re] at hre
  have hw0 : 0 ≤ nrmSq w := by unfold nrmSq; positivity
  have : ‖u‖ ^ 2 + ‖v‖ ^ 2 ≤ nrmSq z := by rw [hre]; linarith
  simpa [hu, hv] using this

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The squared coordinate norm is nonnegative. -/
theorem nrmSq_nonneg (ψ : QState I) : 0 ≤ nrmSq ψ := by
  unfold nrmSq; positivity

/-- Scaling a state by a real number multiplies its squared norm by the square of that number. -/
theorem nrmSq_real_smul (c : ℝ) (ψ : QState I) :
    nrmSq ((c : ℂ) • ψ) = c ^ 2 * nrmSq ψ := by
  unfold nrmSq
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

example (M : ℂ) : ‖star M‖ = ‖M‖ := by simp

example (a b : ℝ) (h : (a : ℂ) = (b : ℂ)) : a = b := Complex.ofReal_inj.mp h

/-- For unit vectors `x` and `y`, their squared overlaps with `z` sum to at most `(1 + ‖QInner x
y‖) * nrmSq z` [IoannouMosca2008]. -/
theorem twoAmplitudeBound (x y z : QState I)
    (hx : nrmSq x = 1) (hy : nrmSq y = 1) :
    ‖QInner x z‖ ^ 2 + ‖QInner y z‖ ^ 2 ≤ (1 + ‖QInner x y‖) * nrmSq z := by
  have he : QInner x x = 1 := by rw [inner_self_nrmSq, hx]; norm_num
  have hyy : QInner y y = 1 := by rw [inner_self_nrmSq, hy]; norm_num
  set p : ℂ := QInner x y with hp
  set ρ : ℝ := ‖p‖ with hρ
  set a : ℂ := QInner x z with ha
  set b : ℂ := QInner y z with hb
  set f : QState I := y - p • x with hfdef
  set B : ℂ := QInner f z with hBdef
  have hyx : QInner y x = star p := by rw [inner_conj_symm, ← hp]
  have hxf : QInner x f = 0 := by
    rw [hfdef, inner_sub_right, inner_smul_right, he, ← hp, mul_one, sub_self]
  have h1 : QInner y (y - p • x) = 1 - p * star p := by
    rw [inner_sub_right, inner_smul_right, hyy, hyx]
  have h2 : QInner (p • x) (y - p • x) = 0 := by
    rw [inner_smul_left, hxf, mul_zero]
  have hps : p * star p = ((ρ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, ← hρ]
  have hff0 : QInner (y - p • x) (y - p • x) = ((1 - ρ ^ 2 : ℝ) : ℂ) := by
    rw [inner_sub_left, h1, h2, sub_zero, hps]
    push_cast
    ring
  have hff : QInner f f = ((1 - ρ ^ 2 : ℝ) : ℂ) := hff0
  have hnrmf : nrmSq f = 1 - ρ ^ 2 := by
    have h := hff
    rw [inner_self_nrmSq] at h
    exact Complex.ofReal_inj.mp h
  have hρle : ρ ≤ 1 := by
    have h := inner_norm_le x y
    simp only [hx, hy, Real.sqrt_one, mul_one] at h
    rw [hρ, hp]
    exact h
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hBrel : B = b - star p * a := by
    rw [hBdef, hfdef, inner_sub_left, inner_smul_left, ← ha, ← hb]
  have hbrel : b = B + star p * a := by rw [hBrel]; ring
  by_cases hρ1 : ρ = 1
  · have hB0 : ‖B‖ = 0 := by
      have h := inner_norm_le f z
      rw [hnrmf, hρ1, show (1 : ℝ) - 1 ^ 2 = 0 by norm_num, Real.sqrt_zero, zero_mul] at h
      exact le_antisymm h (norm_nonneg _)
    have hBz : B = 0 := norm_eq_zero.mp hB0
    have hbnorm : ‖b‖ = ‖a‖ := by
      rw [hbrel, hBz, zero_add, norm_mul, norm_star, ← hρ, hρ1, one_mul]
    have hAle : ‖a‖ ^ 2 ≤ nrmSq z := by
      have h := inner_norm_le x z
      simp only [hx, Real.sqrt_one] at h
      have h' : ‖a‖ ≤ Real.sqrt (nrmSq z) := by simpa [← ha] using h
      calc ‖a‖ ^ 2 ≤ (Real.sqrt (nrmSq z)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) h' 2
        _ = nrmSq z := Real.sq_sqrt (nrmSq_nonneg z)
    have hfin : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ (1 + ρ) * nrmSq z := by
      rw [hbnorm]
      have : ‖a‖ ^ 2 + ‖a‖ ^ 2 = 2 * ‖a‖ ^ 2 := by ring
      rw [this, hρ1]
      linarith
    simpa [ha, hb, hρ, hp] using hfin
  · have hlt : ρ < 1 := lt_of_le_of_ne hρle hρ1
    have h1ρpos : 0 < 1 - ρ := by linarith
    have h1ρ2pos : 0 < 1 - ρ ^ 2 := by nlinarith
    set q : ℝ := Real.sqrt (1 - ρ ^ 2) with hqdef
    have hq2 : q ^ 2 = 1 - ρ ^ 2 := by
      rw [hqdef]; exact Real.sq_sqrt (le_of_lt h1ρ2pos)
    have hqpos : 0 < q := by rw [hqdef]; exact Real.sqrt_pos.mpr h1ρ2pos
    set c : ℝ := q⁻¹ with hcdef
    have hc2 : c ^ 2 = (1 - ρ ^ 2)⁻¹ := by
      rw [hcdef, inv_pow, hq2]
    have hcpos : 0 < c := by rw [hcdef]; exact inv_pos.mpr hqpos
    have he2 : nrmSq ((c : ℂ) • f) = 1 := by
      rw [nrmSq_real_smul, hnrmf, hc2]
      exact inv_mul_cancel₀ (ne_of_gt h1ρ2pos)
    have he2' : QInner ((c : ℂ) • f) ((c : ℂ) • f) = 1 := by
      rw [inner_self_nrmSq, he2]; norm_num
    have hxe2 : QInner x ((c : ℂ) • f) = 0 := by
      rw [inner_smul_right, hxf, mul_zero]
    have hb := bessel2 x ((c : ℂ) • f) z he he2' hxe2
    have hQe2z : QInner ((c : ℂ) • f) z = (c : ℂ) * B := by
      rw [inner_smul_left, show star (c : ℂ) = (c : ℂ) from by simp, ← hBdef]
    have hb' : ‖a‖ ^ 2 + c ^ 2 * ‖B‖ ^ 2 ≤ nrmSq z := by
      have h := hb
      rw [hQe2z, norm_mul] at h
      have hcn : ‖(c : ℂ)‖ = c := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos]
      rw [hcn, mul_pow, ← ha] at h
      exact h
    have hcprod : (1 - ρ ^ 2) * c ^ 2 = 1 := by
      rw [hc2]
      exact mul_inv_cancel₀ (ne_of_gt h1ρ2pos)
    have heq : (1 - ρ) * ((1 + ρ) * (‖a‖ ^ 2 + c ^ 2 * ‖B‖ ^ 2))
        = (1 - ρ ^ 2) * ‖a‖ ^ 2 + ‖B‖ ^ 2 := by
      calc (1 - ρ) * ((1 + ρ) * (‖a‖ ^ 2 + c ^ 2 * ‖B‖ ^ 2))
          = ((1 - ρ) * (1 + ρ)) * ‖a‖ ^ 2
              + ((1 - ρ ^ 2) * c ^ 2) * ‖B‖ ^ 2 := by ring
        _ = (1 - ρ ^ 2) * ‖a‖ ^ 2 + ‖B‖ ^ 2 := by
            rw [show (1 - ρ) * (1 + ρ) = 1 - ρ ^ 2 by ring, hcprod, one_mul]
    have hpoly : (1 - ρ) * (‖a‖ ^ 2 + (ρ * ‖a‖ + ‖B‖) ^ 2)
        ≤ (1 - ρ ^ 2) * ‖a‖ ^ 2 + ‖B‖ ^ 2 := by
      nlinarith [sq_nonneg ((1 - ρ) * ‖a‖ - ‖B‖), hρ0, h1ρpos, norm_nonneg a, norm_nonneg B]
    have hkey : ‖a‖ ^ 2 + (ρ * ‖a‖ + ‖B‖) ^ 2
        ≤ (1 + ρ) * (‖a‖ ^ 2 + c ^ 2 * ‖B‖ ^ 2) := by
      have hL : (1 - ρ) * (‖a‖ ^ 2 + (ρ * ‖a‖ + ‖B‖) ^ 2)
          ≤ (1 - ρ) * ((1 + ρ) * (‖a‖ ^ 2 + c ^ 2 * ‖B‖ ^ 2)) := by
        rw [heq]; exact hpoly
      exact le_of_mul_le_mul_left hL h1ρpos
    have hb_ub : ‖b‖ ≤ ρ * ‖a‖ + ‖B‖ := by
      rw [hbrel]
      calc ‖B + star p * a‖ ≤ ‖B‖ + ‖star p * a‖ := norm_add_le _ _
        _ = ‖B‖ + ρ * ‖a‖ := by
            rw [norm_mul, norm_star, ← hρ]
        _ = ρ * ‖a‖ + ‖B‖ := by ring
    have hfin : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ (1 + ρ) * nrmSq z := by
      have hs := pow_le_pow_left₀ (norm_nonneg b) hb_ub 2
      calc ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖a‖ ^ 2 + (ρ * ‖a‖ + ‖B‖) ^ 2 := by linarith
        _ ≤ (1 + ρ) * (‖a‖ ^ 2 + c ^ 2 * ‖B‖ ^ 2) := hkey
        _ ≤ (1 + ρ) * nrmSq z := by
            apply mul_le_mul_of_nonneg_left hb'
            linarith
    simpa [ha, hb, hρ, hp] using hfin

/-- If `x` and `y` are unit vectors and `nrmSq z ≤ 1`, their squared overlaps with `z` sum to at
most `1 + ‖QInner x y‖` [IoannouMosca2008]. -/
theorem eq29_twoState (x y z : QState I)
    (hx : nrmSq x = 1) (hy : nrmSq y = 1) (hz : nrmSq z ≤ 1) :
    ‖QInner x z‖ ^ 2 + ‖QInner y z‖ ^ 2 ≤ 1 + ‖QInner x y‖ := by
  have h := twoAmplitudeBound x y z hx hy
  have h1 : (1 + ‖QInner x y‖) * nrmSq z ≤ (1 + ‖QInner x y‖) * 1 := by
    apply mul_le_mul_of_nonneg_left hz
    positivity
  linarith

variable {n : ℕ}

/-- The column of the register Hadamard matrix indexed by `w`, viewed as a state. -/
def hadamardColumn (w : Reg n) : QState (Reg n) := fun z => HadamardN n z w

/-- The register Hadamard matrix is symmetric in its two indices. -/
theorem hadamardN_symm (y z : Reg n) : HadamardN n y z = HadamardN n z y := by
  rw [hadamardN_apply, hadamardN_apply]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [Bool.and_comm]

/-- The zero-string basis state has squared coordinate norm one. -/
theorem nrmSq_ket_zeroStr : nrmSq (Ket (ZeroStr n) : QState (Reg n)) = 1 := by
  unfold nrmSq
  rw [Finset.sum_eq_single (ZeroStr n)]
  · simp
  · intro b _ hb
    simp [Ket, hb]
  · intro h
    exact absurd (Finset.mem_univ (ZeroStr n)) h

/-- Every column of the register Hadamard matrix has squared coordinate norm one. -/
theorem nrmSq_hadamardColumn (w : Reg n) : nrmSq (hadamardColumn (n := n) w) = 1 := by
  unfold nrmSq hadamardColumn
  have hU := sum_normSq_mulVec_of_mem_unitaryGroup (I := Reg n) (U := HadamardN n)
    (hadamardN_unitary n) (Ket w)
  have hR : (∑ j, Complex.normSq ((Ket w) j)) = 1 := by
    rw [Finset.sum_eq_single w]
    · simp
    · intro b _ hb
      simp [Ket, hb]
    · intro h
      exact absurd (Finset.mem_univ w) h
  have hL : ∀ i, Complex.normSq ((HadamardN n *ᵥ Ket w) i) = Complex.normSq (HadamardN n i w) := by
    intro i
    congr 1
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single w]
    · simp [Ket]
    · intro b _ hb
      simp [Ket, hb]
    · intro h
      exact absurd (Finset.mem_univ w) h
  rw [hR] at hU
  calc (∑ z, ‖HadamardN n z w‖ ^ 2)
      = ∑ z, Complex.normSq (HadamardN n z w) := by
        apply Finset.sum_congr rfl
        intro z _
        rw [Complex.normSq_eq_norm_sq]
    _ = ∑ i, Complex.normSq ((HadamardN n *ᵥ Ket w) i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hL i]
    _ = 1 := hU

/-- Taking the inner product with the zero-string basis state extracts the zero-string
amplitude. -/
theorem QInner_ket_zeroStr (β : QState (Reg n)) :
    QInner (Ket (ZeroStr n) : QState (Reg n)) β = β (ZeroStr n) := by
  unfold QInner Qatlib.Foundations.PureStateMath.Inner
  simp [dotProduct, Ket]

/-- The inner product with Hadamard column `w` equals coordinate `w` of the Hadamard-transformed
state. -/
theorem QInner_hadamardColumn (w : Reg n) (β : QState (Reg n)) :
    QInner (hadamardColumn w) β = (HadamardN n).mulVec β w := by
  unfold QInner Qatlib.Foundations.PureStateMath.Inner hadamardColumn
  rw [Matrix.mulVec, dotProduct]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Pi.star_apply]
  rw [Complex.star_def, hadamardN_conj, hadamardN_symm z w]

/-- The norm of the `n`th power of the complex inverse square root of two is `1 / sqrt (2 ^ n)`. -/
theorem norm_inv_sqrt2_pow (n : ℕ) :
    ‖((Real.sqrt 2 : ℂ)⁻¹) ^ n‖ = 1 / Real.sqrt ((2 : ℝ) ^ n) := by
  have h2 : ‖((Real.sqrt 2 : ℂ)⁻¹)‖ = (Real.sqrt 2)⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2)]
  rw [norm_pow, h2, inv_pow]
  rw [show Real.sqrt ((2 : ℝ) ^ n) = (Real.sqrt 2) ^ n from by
    induction n with
    | zero => simp
    | succ k ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]]
  rw [one_div]

/-- The norm of every entry in the zero-string row of the register Hadamard matrix is `1 / sqrt
(2 ^ n)`. -/
theorem norm_hadamardN_zero_left (w : Reg n) :
    ‖HadamardN n (ZeroStr n) w‖ = 1 / Real.sqrt ((2 : ℝ) ^ n) := by
  rw [hadamardN_apply_zero_left, norm_inv_sqrt2_pow]

/-- The overlap norm between the zero-string basis vector and a Hadamard column is `1 / sqrt (2
^ n)`. -/
theorem norm_inner_ket_column (w : Reg n) :
    ‖QInner (Ket (ZeroStr n) : QState (Reg n)) (hadamardColumn w)‖ =
      1 / Real.sqrt ((2 : ℝ) ^ n) := by
  rw [QInner_ket_zeroStr, hadamardColumn, norm_hadamardN_zero_left]

/-- Under the stated differential equation, schedule bounds, norm bound, and initial amplitude,
the final transformed probability at `w` is at most `(2 * E1 * T + 1) / sqrt (2 ^ n)`. -/
theorem eq30_success_bound (F : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ → ℝ)
    (β : ℝ → QState (Reg n)) (T : ℝ) (hT : 0 ≤ T)
    (hE1 : 0 ≤ E1) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hode : ∀ t, HasDerivAt β (fun x => (-Complex.I) * hadBasisAction F E1 w s β t x) t)
    (hnorm : ∀ t ∈ Set.Icc 0 T, nrmSq (β t) ≤ 1)
    (hstart : β 0 (ZeroStr n) = 1) :
    ‖(HadamardN n).mulVec (β T) w‖ ^ 2 ≤
      2 * E1 * T / Real.sqrt ((2 : ℝ) ^ n) + 1 / Real.sqrt ((2 : ℝ) ^ n) := by
  have hlow := hadBasis_start_lower F E1 w s β T hT hE1 hs0 hs1 hode
    (fun t ht => hnorm t ht) hstart
  have hb := eq29_twoState (Ket (ZeroStr n) : QState (Reg n)) (hadamardColumn w) (β T)
    (nrmSq_ket_zeroStr) (nrmSq_hadamardColumn w) (hnorm T ⟨hT, le_rfl⟩)
  rw [QInner_ket_zeroStr, QInner_hadamardColumn, norm_inner_ket_column] at hb
  linarith

/-- For positive `E1`, achieving transformed probability at least `c` under the stated evolution
hypotheses requires `(c * sqrt (2 ^ n) - 1) / (2 * E1) ≤ T`. -/
theorem runtime_lower_bound_eq30 (F : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ → ℝ)
    (β : ℝ → QState (Reg n)) (T c : ℝ) (hT : 0 ≤ T)
    (hE1 : 0 < E1) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hode : ∀ t, HasDerivAt β (fun x => (-Complex.I) * hadBasisAction F E1 w s β t x) t)
    (hnorm : ∀ t ∈ Set.Icc 0 T, nrmSq (β t) ≤ 1)
    (hstart : β 0 (ZeroStr n) = 1)
    (hsucc : c ≤ ‖(HadamardN n).mulVec (β T) w‖ ^ 2) :
    (c * Real.sqrt ((2 : ℝ) ^ n) - 1) / (2 * E1) ≤ T := by
  have h30 := eq30_success_bound F E1 w s β T hT (le_of_lt hE1) hs0 hs1 hode hnorm hstart
  have hc := le_trans hsucc h30
  have hNpos : 0 < Real.sqrt ((2 : ℝ) ^ n) := Real.sqrt_pos_of_pos (by positivity)
  have hmul := mul_le_mul_of_nonneg_right hc (le_of_lt hNpos)
  have hEq : (2 * E1 * T / Real.sqrt ((2 : ℝ) ^ n) + 1 / Real.sqrt ((2 : ℝ) ^ n))
      * Real.sqrt ((2 : ℝ) ^ n) = 2 * E1 * T + 1 := by
    field_simp [ne_of_gt hNpos]
  rw [hEq] at hmul
  have hE1pos : 0 < 2 * E1 := by linarith
  rw [div_le_iff₀ hE1pos]
  linarith

/-- A probability upper bound of the form in equation (30), together with success probability at
least `c`, gives `(c - 1 / sqrt N) * sqrt N / (2 * E1) ≤ T`. -/
theorem runtime_ge_from_eq30 {E1 T c N : ℝ} (ψ : QState (Reg n)) (w : Reg n)
    (hN : 0 < N) (hE1 : 0 < E1)
    (h30 : BornProb ψ w ≤ 2 * E1 * T / Real.sqrt N + 1 / Real.sqrt N)
    (hc : c ≤ BornProb ψ w) :
    (c - 1 / Real.sqrt N) * Real.sqrt N / (2 * E1) ≤ T := by
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN
  have hstep : c - 1 / Real.sqrt N ≤ 2 * E1 * T / Real.sqrt N := by
    linarith [h30, hc]
  have hmul : (c - 1 / Real.sqrt N) * Real.sqrt N ≤ 2 * E1 * T := by
    have := mul_le_mul_of_nonneg_right hstep (le_of_lt hsN)
    rwa [div_mul_cancel₀ _ (ne_of_gt hsN)] at this
  rw [div_le_iff₀ (by positivity : 0 < 2 * E1)]
  nlinarith [hmul]

/-- The Hadamard basis driver equals its conjugate transpose entrywise. -/
theorem hadBasisDriver_star (F : Reg n → ℝ) (E1 s : ℝ) (w x y : Reg n) :
    star (hadBasisDriver F E1 s w y x) = hadBasisDriver F E1 s w x y := by
  unfold hadBasisDriver
  simp only [Matrix.of_apply]
  by_cases h : x = y
  · subst h; simp
  · have hyx : ¬ y = x := fun hyx => h hyx.symm
    simp [h, hyx, mul_comm]

/-- The quadratic form of a matrix equal to its conjugate transpose has zero imaginary part. -/
theorem quadForm_im_zero (H : Matrix (Reg n) (Reg n) ℂ)
    (hsym : ∀ x y, star (H y x) = H x y) (b : QState (Reg n)) :
    (∑ i, star (b i) * (H.mulVec b) i).im = 0 := by
  set z : ℂ := ∑ i, star (b i) * (H.mulVec b) i with hz
  have hexp : z = ∑ i, ∑ j, star (b i) * H i j * b j := by
    rw [hz]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hconj : star z = z := by
    calc star z = ∑ i, ∑ j, star (star (b i) * H i j * b j) := by
          rw [hexp, star_sum]
          simp only [star_sum]
      _ = ∑ i, ∑ j, b i * star (H i j) * star (b j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          simp [mul_comm, mul_left_comm]
      _ = ∑ i, ∑ j, b i * H j i * star (b j) := by
          apply Finset.sum_congr rfl
          intro i _
          apply Finset.sum_congr rfl
          intro j _
          rw [hsym j i]
      _ = ∑ j, ∑ i, b i * H j i * star (b j) := Finset.sum_comm
      _ = ∑ j, ∑ i, star (b j) * H j i * b i := by
          apply Finset.sum_congr rfl
          intro j _
          apply Finset.sum_congr rfl
          intro i _
          ring
      _ = z := by rw [← hexp]
  rw [Complex.star_def] at hconj
  exact Complex.conj_eq_iff_im.mp hconj

/-- A state satisfying the Schrödinger derivative equation for a Hermitian matrix has squared
norm derivative zero at that time. -/
theorem nrmSq_hasDeriv_zero_at (Ht : Matrix (Reg n) (Reg n) ℂ)
    (hsym : ∀ x y, star (Ht y x) = Ht x y)
    (b : ℝ → QState (Reg n)) (t : ℝ)
    (hode : HasDerivAt b (fun x => (-Complex.I) * (Ht.mulVec (b t)) x) t) :
    HasDerivAt (fun u => nrmSq (b u)) 0 t := by
  have hcoord : ∀ i, HasDerivAt (fun u => b u i)
      ((-Complex.I) * (Ht.mulVec (b t)) i) t := by
    intro i
    simpa only [Function.comp, ContinuousLinearMap.proj_apply] using!
      (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt t hode
  have hterm : ∀ i, HasDerivAt (fun u => ‖b u i‖ ^ 2)
      (2 * ((-Complex.I * (Ht.mulVec (b t)) i) * star (b t i)).re) t := by
    intro i
    have h := (hcoord i).norm_sq
    simpa only [Complex.inner] using! h
  have hsum : HasDerivAt (fun u => ∑ i, ‖b u i‖ ^ 2)
      (∑ i, 2 * ((-Complex.I * (Ht.mulVec (b t)) i) * star (b t i)).re) t := by
    have hsum' := HasDerivAt.sum (u := Finset.univ) (fun i _ => hterm i)
    convert! hsum' using 1
    ext u
    simp only [Finset.sum_apply]
  have hval : (∑ i, 2 * ((-Complex.I * (Ht.mulVec (b t)) i) * star (b t i)).re) = 0 := by
    have hsplit : (∑ i, 2 * ((-Complex.I * (Ht.mulVec (b t)) i) * star (b t i)).re)
        = 2 * (∑ i, (-Complex.I * (Ht.mulVec (b t)) i) * star (b t i)).re := by
      rw [Complex.re_sum, Finset.mul_sum]
    have hlin : (∑ i, (-Complex.I * (Ht.mulVec (b t)) i) * star (b t i))
        = -Complex.I * (∑ i, star (b t i) * (Ht.mulVec (b t)) i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have him : (-Complex.I * (∑ i, star (b t i) * (Ht.mulVec (b t)) i)).re
        = (∑ i, star (b t i) * (Ht.mulVec (b t)) i).im := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.I_re,
        Complex.I_im]
      ring
    have hzero := quadForm_im_zero Ht hsym (b t)
    rw [hsplit, hlin, him, hzero]
    ring
  rw [hval] at hsum
  simpa [nrmSq] using hsum

/-- Evolution by the Hadamard basis driver from the zero-string basis vector preserves squared
norm one throughout `[0,T]` [IoannouMosca2008]. -/
theorem nrmSq_eq_one_of_hode (F : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ → ℝ)
    (β : ℝ → QState (Reg n)) (T : ℝ) (hT : 0 ≤ T)
    (hode : ∀ t, HasDerivAt β (fun x => (-Complex.I) * hadBasisAction F E1 w s β t x) t)
    (hβ0 : β 0 = Ket (ZeroStr n)) :
    ∀ t ∈ Set.Icc 0 T, nrmSq (β t) = 1 := by
  intro t ht
  have hf : ∀ u, HasDerivAt (fun u => nrmSq (β u)) 0 u := by
    intro u
    exact nrmSq_hasDeriv_zero_at (hadBasisDriver F E1 (s u) w)
      (hadBasisDriver_star F E1 (s u) w) β u (by simpa [hadBasisAction] using hode u)
  have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := fun u => nrmSq (β u)) (f' := fun _ => (0 : ℝ)) (s := Set.Icc (0 : ℝ) T)
    (x := 0) (y := t) (C := 0)
    (fun u _ => (hf u).hasDerivWithinAt) (fun u _ => by simp)
    (convex_Icc 0 T) (Set.left_mem_Icc.mpr hT) ht
  have hmvt' : ‖nrmSq (β t) - nrmSq (β 0)‖ ≤ 0 := by simpa using hmvt
  have hzero : ‖nrmSq (β t) - nrmSq (β 0)‖ = 0 := le_antisymm hmvt' (norm_nonneg _)
  have heq : nrmSq (β t) = nrmSq (β 0) := by
    exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
  rw [heq, hβ0, nrmSq_ket_zeroStr]

/-- Evolution starting at the zero-string basis vector satisfies the equation (30) success
bound, with normalization supplied by norm conservation [IoannouMosca2008]. -/
theorem eq30_success_bound_normalized (F : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ → ℝ)
    (β : ℝ → QState (Reg n)) (T : ℝ) (hT : 0 ≤ T)
    (hE1 : 0 ≤ E1) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hode : ∀ t, HasDerivAt β (fun x => (-Complex.I) * hadBasisAction F E1 w s β t x) t)
    (hβ0 : β 0 = Ket (ZeroStr n)) :
    ‖(HadamardN n).mulVec (β T) w‖ ^ 2 ≤
      2 * E1 * T / Real.sqrt ((2 : ℝ) ^ n) + 1 / Real.sqrt ((2 : ℝ) ^ n) := by
  have hnorm : ∀ t ∈ Set.Icc 0 T, nrmSq (β t) ≤ 1 := by
    intro t ht
    rw [nrmSq_eq_one_of_hode F E1 w s β T hT hode hβ0 t ht]
  have hstart : β 0 (ZeroStr n) = 1 := by
    rw [hβ0]
    simp [Ket]
  exact eq30_success_bound F E1 w s β T hT hE1 hs0 hs1 hode hnorm hstart

/-- For positive `E1`, normalized evolution from the zero-string basis vector with final
transformed probability at least `c` requires `(c * sqrt (2 ^ n) - 1) / (2 * E1) ≤ T`
[IoannouMosca2008]. -/
theorem runtime_lower_bound_normalized (F : Reg n → ℝ) (E1 : ℝ) (w : Reg n) (s : ℝ → ℝ)
    (β : ℝ → QState (Reg n)) (T c : ℝ) (hT : 0 ≤ T)
    (hE1 : 0 < E1) (hs0 : ∀ t, 0 ≤ s t) (hs1 : ∀ t, s t ≤ 1)
    (hode : ∀ t, HasDerivAt β (fun x => (-Complex.I) * hadBasisAction F E1 w s β t x) t)
    (hβ0 : β 0 = Ket (ZeroStr n))
    (hsucc : c ≤ ‖(HadamardN n).mulVec (β T) w‖ ^ 2) :
    (c * Real.sqrt ((2 : ℝ) ^ n) - 1) / (2 * E1) ≤ T := by
  have hnorm : ∀ t ∈ Set.Icc 0 T, nrmSq (β t) ≤ 1 := by
    intro t ht
    rw [nrmSq_eq_one_of_hode F E1 w s β T hT hode hβ0 t ht]
  have hstart : β 0 (ZeroStr n) = 1 := by
    rw [hβ0]
    simp [Ket]
  exact runtime_lower_bound_eq30 F E1 w s β T c hT hE1 hs0 hs1 hode hnorm hstart hsucc

end Qatlib.Papers.AdiabLimit07.MainResults
