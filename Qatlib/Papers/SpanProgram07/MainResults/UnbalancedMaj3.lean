/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgram07.MainResults.WitnessSize
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Unbalanced three-input majority witnesses

This module constructs `maj3UnbalProgram` with column weights `[1, 1, β]` and derives the
parameter identities needed for its witnesses. For nonnegative `β`, it proves an exact positive
witness size on `{0, 1}` and upper bounds on the other input sets, including the common
nonnegative rescaling used in [ReichardtSpalek2008].

## Main statements

* `maj3_unbalanced_witness_size`: For nonnegative `β`, collect the exact positive witness size
  `uM β` on `{0, 1}` and witness upper bounds `uM β` on every other listed availability pattern.
* `maj3_unbalanced_witness_size_scaled`: Scaling all column weights by nonnegative `B` gives
  exact positive witness size `B * uM β` on `{0, 1}` and the same upper bound on every other
  listed pattern, for nonnegative `β`.

## References

* [Reichardt and Spalek, 2008][ReichardtSpalek2008]
-/

set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Qatlib.Papers.SpanProgram07.MainResults

open Finset
open SpanProgram
open scoped BigOperators

namespace Maj3Unbalanced

/-- The parameter `sqrt (8 + β²)` for the unbalanced majority construction. -/
def uS (β : ℝ) : ℝ := Real.sqrt (8 + β ^ 2)

/-- The witness-size parameter `(uS β + β) / 2`. -/
def uM (β : ℝ) : ℝ := (uS β + β) / 2

/-- The parameter `sqrt (uS β - β) / (2 * sqrt 2)` for the first two output coordinates. -/
def uA (β : ℝ) : ℝ := Real.sqrt (uS β - β) / (2 * Real.sqrt 2)

/-- The parameter `sqrt (1/2 + β * (uA β)²)` for the third output coordinate. -/
def uC (β : ℝ) : ℝ := Real.sqrt (1 / 2 + β * (uA β) ^ 2)

/-- The parameter `uS β` is nonnegative. -/
lemma uS_nonneg (β : ℝ) : 0 ≤ uS β := Real.sqrt_nonneg _

/-- The square of `uS β` is `8 + β²`. -/
lemma uS_sq (β : ℝ) : uS β ^ 2 = 8 + β ^ 2 := by
  rw [uS, Real.sq_sqrt]; positivity

/-- Every real `β` is at most `uS β`. -/
lemma le_uS (β : ℝ) : β ≤ uS β := by
  have h1 : β ≤ Real.sqrt (β ^ 2) := by
    rw [Real.sqrt_sq_eq_abs]; exact le_abs_self β
  have h2 : Real.sqrt (β ^ 2) ≤ Real.sqrt (8 + β ^ 2) :=
    Real.sqrt_le_sqrt (by linarith [sq_nonneg β])
  exact h1.trans h2

/-- The square of `uA β` equals `(uS β - β) / 8`. -/
lemma uA_sq (β : ℝ) : (uA β) ^ 2 = (uS β - β) / 8 := by
  unfold uA
  rw [div_pow, Real.sq_sqrt (by linarith [le_uS β]), mul_pow,
    Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)]
  norm_num

/-- The parameter `uA β` is positive for every real `β`. -/
lemma uA_pos (β : ℝ) : 0 < uA β := by
  have hpos : 0 < uS β - β := by
    have hs := uS_sq β
    have h1 : β < uS β := by nlinarith [hs, uS_nonneg β]
    linarith
  unfold uA
  exact div_pos (Real.sqrt_pos.2 hpos) (by positivity)

/-- For nonnegative `β`, the square of `uC β` equals `1/2 + β * (uA β)²`. -/
lemma uC_sq (β : ℝ) (hβ : 0 ≤ β) : (uC β) ^ 2 = 1 / 2 + β * (uA β) ^ 2 := by
  unfold uC
  rw [Real.sq_sqrt]
  have : 0 ≤ β * (uA β) ^ 2 := mul_nonneg hβ (sq_nonneg _)
  positivity

/-- For nonnegative `β`, the parameters satisfy `(uC β)² + 4 * (uA β)⁴ = 1`. -/
lemma uC_sq_add (β : ℝ) (hβ : 0 ≤ β) : (uC β) ^ 2 + 4 * (uA β) ^ 4 = 1 := by
  have hc := uC_sq β hβ
  have ha := uA_sq β
  have hs := uS_sq β
  have h4 : (uA β) ^ 4 = ((uA β) ^ 2) ^ 2 := by ring
  rw [h4, hc, ha]
  have hkey : uS β ^ 2 - β ^ 2 = 8 := by rw [hs]; ring
  nlinarith [hkey, sq_nonneg (uS β - β)]

/-- The quantity `4 * (uA β)² + β` equals `uM β`. -/
lemma four_uA_add (β : ℝ) : 4 * (uA β) ^ 2 + β = uM β := by
  have ha := uA_sq β
  rw [uM]
  linarith [ha]

/-- The reciprocal of `2 * (uA β)²` equals `uM β`. -/
lemma inv_two_uA (β : ℝ) : 1 / (2 * (uA β) ^ 2) = uM β := by
  have ha := uA_sq β
  have hs := uS_sq β
  have hpos : 0 < uS β - β := by
    have hs := uS_sq β
    have h1 : β < uS β := by nlinarith [hs, uS_nonneg β]
    linarith
  rw [uM, ha]
  field_simp
  nlinarith [hs, sq_nonneg (uS β - β)]

/-- For nonnegative `β`, the sum `2 * (uA β)² + (uC β)² / (2 * (uA β)²)` equals `uM β`. -/
lemma two_uA_add (β : ℝ) (hβ : 0 ≤ β) :
    2 * (uA β) ^ 2 + (uC β) ^ 2 / (2 * (uA β) ^ 2) = uM β := by
  have ha := uA_sq β
  have hc := uC_sq β hβ
  have hs := uS_sq β
  have hpos : 0 < uS β - β := by
    have hs := uS_sq β
    have h1 : β < uS β := by nlinarith [hs, uS_nonneg β]
    linarith
  rw [uM, ha, hc]
  have hne : uS β - β ≠ 0 := hpos.ne'
  field_simp
  nlinarith [hs, sq_nonneg (uS β - β)]

end Maj3Unbalanced

open Maj3Unbalanced

/-- The complex output-coordinate vector with entries `uA β`, `uA β`, and `uC β`. -/
def ubOut (β : ℝ) : Fin 3 → ℂ := ![((uA β : ℝ) : ℂ), ((uA β : ℝ) : ℂ), ((uC β : ℝ) : ℂ)]

/-- The complex auxiliary-coordinate vector with entries `I`, `-I`, and `2 * uA β`. -/
def ubCon (β : ℝ) : Fin 3 → ℂ := ![Complex.I, -Complex.I, ((2 * uA β : ℝ) : ℂ)]

/-- The column-weight vector `[1, 1, β]`. -/
def ubz (β : ℝ) : Fin 3 → ℝ := ![1, 1, β]

/-- The three-input positive-literal span program with output coordinates `ubOut β` and
auxiliary coordinates `ubCon β`. -/
def maj3UnbalProgram (β : ℝ) : SpanProgram 3 (Fin 3) Unit (Fin 3) where
  grp j := j
  lit j := Lit.pos j
  v j k := match k with
    | none => ubOut β j
    | some _ => ubCon β j

namespace Unbalanced

/-- The target coordinate of unbalanced-majority column `j` is `ubOut β j`. -/
@[simp] theorem v_none (β : ℝ) (j : Fin 3) :
    (maj3UnbalProgram β).v j none = ubOut β j := rfl

/-- The auxiliary coordinate of unbalanced-majority column `j` is `ubCon β j`. -/
@[simp] theorem v_some (β : ℝ) (j : Fin 3) (u : Unit) :
    (maj3UnbalProgram β).v j (some u) = ubCon β j := rfl

/-- Expand an unbalanced-majority column pairing into the conjugate output and auxiliary
coordinate contributions. -/
theorem pair_eq (β : ℝ) (b : Option Unit → ℂ) (j : Fin 3) :
    (maj3UnbalProgram β).pair b j
      = (starRingEnd ℂ) (ubOut β j) * b none
        + (starRingEnd ℂ) (ubCon β j) * b (some ()) := by
  unfold SpanProgram.pair
  rw [Fintype.sum_option]
  simp

/-- Output coordinate zero is the complex embedding of `uA β`. -/
@[simp] theorem out_zero (β : ℝ) : ubOut β 0 = ((uA β : ℝ) : ℂ) := rfl

/-- Output coordinate one is the complex embedding of `uA β`. -/
@[simp] theorem out_one (β : ℝ) : ubOut β 1 = ((uA β : ℝ) : ℂ) := rfl

/-- Output coordinate two is the complex embedding of `uC β`. -/
@[simp] theorem out_two (β : ℝ) : ubOut β 2 = ((uC β : ℝ) : ℂ) := rfl

/-- Auxiliary coordinate zero is the imaginary unit. -/
@[simp] theorem con_zero (β : ℝ) : ubCon β 0 = Complex.I := rfl

/-- Auxiliary coordinate one is minus the imaginary unit. -/
@[simp] theorem con_one (β : ℝ) : ubCon β 1 = -Complex.I := rfl

/-- Auxiliary coordinate two is the complex embedding of `2 * uA β`. -/
@[simp] theorem con_two (β : ℝ) : ubCon β 2 = ((2 * uA β : ℝ) : ℂ) := rfl

/-- Column weight zero is one. -/
@[simp] theorem z_zero (β : ℝ) : ubz β 0 = 1 := rfl

/-- Column weight one is one. -/
@[simp] theorem z_one (β : ℝ) : ubz β 1 = 1 := rfl

/-- Column weight two is `β`. -/
@[simp] theorem z_two (β : ℝ) : ubz β 2 = β := rfl

/-- The complex embedding of `uA β` is nonzero. -/
theorem uA_complex_ne (β : ℝ) : ((uA β : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (uA_pos β).ne'

/-- The squared norm of the complex inverse of `2 * uA β` is `1 / (4 * (uA β)²)`. -/
theorem normSq_two_uA_inv (β : ℝ) :
    ‖(((2 * uA β : ℝ) : ℂ))⁻¹‖ ^ 2 = 1 / (4 * (uA β) ^ 2) := by
  have hpos : 0 < uA β := uA_pos β
  rw [← Complex.normSq_eq_norm_sq, map_inv₀, Complex.normSq_ofReal]
  have hq : (uA β) ^ 2 ≠ 0 := pow_ne_zero 2 (uA_pos β).ne'
  field_simp
  ring

/-- The complex number with real part `x` and imaginary part `y` has squared norm `x² + y²`. -/
theorem normSq_ofReal_add_mul_I (x y : ℝ) :
    Complex.normSq ((x : ℂ) + (y : ℂ) * Complex.I) = x ^ 2 + y ^ 2 := by
  rw [Complex.normSq_apply]
  simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
  ring

/-- For nonnegative `β`, the complex number with real part `uC β` and imaginary part `-2 * (uA
β)²` has squared norm one. -/
theorem normSq_uC_sub (β : ℝ) (hβ : 0 ≤ β) :
    Complex.normSq (((uC β : ℝ) : ℂ) - 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2) = 1 := by
  have heq : ((uC β : ℝ) : ℂ) - 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2
      = ((uC β : ℝ) : ℂ) + ((-(2 * (uA β) ^ 2) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [heq, normSq_ofReal_add_mul_I]
  have h := uC_sq_add β hβ
  nlinarith [h]

/-- For nonnegative `β`, the complex number with real part `uC β` and imaginary part `2 * (uA
β)²` has squared norm one. -/
theorem normSq_uC_add (β : ℝ) (hβ : 0 ≤ β) :
    Complex.normSq (((uC β : ℝ) : ℂ) + 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2) = 1 := by
  have heq : ((uC β : ℝ) : ℂ) + 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2
      = ((uC β : ℝ) : ℂ) + ((2 * (uA β) ^ 2 : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [heq, normSq_ofReal_add_mul_I]
  have h := uC_sq_add β hβ
  nlinarith [h]

/-- Twice the squared norm of the complex inverse of `2 * uA β` equals `uM β`. -/
theorem two_norm_sq (β : ℝ) :
    2 * ‖(((2 * uA β : ℝ) : ℂ))⁻¹‖ ^ 2 = uM β := by
  rw [normSq_two_uA_inv]
  have hq : (uA β) ^ 2 ≠ 0 := pow_ne_zero 2 (uA_pos β).ne'
  rw [show 2 * (1 / (4 * (uA β) ^ 2)) = 1 / (2 * (uA β) ^ 2) by
    field_simp
    ring]
  exact inv_two_uA β

/-- Multiplication of `z` by `2 * I * uA β` multiplies its squared norm by `4 * (uA β)²`. -/
theorem norm_two_I_uA_mul (β : ℝ) (z : ℂ) :
    ‖2 * Complex.I * ((uA β : ℝ) : ℂ) * z‖ ^ 2 = 4 * (uA β) ^ 2 * ‖z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  rw [show 2 * Complex.I * ((uA β : ℝ) : ℂ) * z
      = (((2 * uA β : ℝ)) : ℂ) * Complex.I * z by push_cast; ring]
  rw [Complex.normSq_mul, Complex.normSq_mul, Complex.normSq_I, Complex.normSq_ofReal]
  ring

/-- The complex embedding of `2 * uA β` has squared norm `4 * (uA β)²`. -/
theorem norm_two_uA_sq (β : ℝ) :
    ‖(2 * ((uA β : ℝ) : ℂ))‖ ^ 2 = 4 * (uA β) ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq]
  rw [show 2 * ((uA β : ℝ) : ℂ) = (((2 * uA β : ℝ)) : ℂ) by push_cast; ring]
  rw [Complex.normSq_ofReal]
  ring

/-- For nonnegative `β`, the inverse of the complex number with real part `uC β` and imaginary
part `2 * (uA β)²` has squared norm one. -/
theorem normSq_inv_uC_add (β : ℝ) (hβ : 0 ≤ β) :
    ‖(((uC β : ℝ) : ℂ) + 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2)⁻¹‖ ^ 2 = 1 := by
  rw [← Complex.normSq_eq_norm_sq, map_inv₀, normSq_uC_add β hβ]
  norm_num

/-- For nonnegative `β`, the inverse of the complex number with real part `uC β` and imaginary
part `-2 * (uA β)²` has squared norm one. -/
theorem normSq_inv_uC_sub (β : ℝ) (hβ : 0 ≤ β) :
    ‖(((uC β : ℝ) : ℂ) - 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2)⁻¹‖ ^ 2 = 1 := by
  rw [← Complex.normSq_eq_norm_sq, map_inv₀, normSq_uC_sub β hβ]
  norm_num

/-- Multiplying a real complex number twice by the imaginary unit gives its negative. -/
theorem I_mul_I_mul (r : ℝ) :
    Complex.I * (Complex.I * (r : ℂ)) = -(r : ℂ) := by
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-- Multiplication first by minus the imaginary unit and then by the imaginary unit fixes a real
complex number. -/
theorem I_mul_neg_I_mul (r : ℝ) :
    Complex.I * (-Complex.I * (r : ℂ)) = (r : ℂ) := by
  rw [← mul_assoc, mul_neg, Complex.I_mul_I, neg_neg, one_mul]

/-- Multiplying a real complex number twice by minus the imaginary unit gives its negative. -/
theorem neg_I_mul_neg_I_mul (r : ℝ) :
    (-Complex.I) * (-Complex.I * (r : ℂ)) = -(r : ℂ) := by
  rw [← mul_assoc, neg_mul_neg, Complex.I_mul_I, neg_one_mul]

/-- Multiplication first by the imaginary unit and then by minus the imaginary unit fixes a real
complex number. -/
theorem neg_I_mul_I_mul (r : ℝ) :
    (-Complex.I) * (Complex.I * (r : ℂ)) = (r : ℂ) := by
  rw [← mul_assoc, neg_mul, Complex.I_mul_I]
  ring

/-- A linear combination of unbalanced-majority columns equal to the target has
output-coordinate sum one and auxiliary-coordinate sum zero. -/
theorem true_coords (β : ℝ) {S : Finset (Fin 3)} {w : Fin 3 → ℂ}
    (hsum : ∑ j ∈ S, w j • (maj3UnbalProgram β).v j = target Unit) :
    (∑ j ∈ S, w j * ubOut β j) = 1 ∧ (∑ j ∈ S, w j * ubCon β j) = 0 := by
  constructor
  · have h := congr_fun hsum none
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h
  · have h := congr_fun hsum (some ())
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

/-- The squared norm of complex zero is zero. -/
theorem norm_zero_sq : ‖(0 : ℂ)‖ ^ 2 = 0 := by simp

/-- The two-coordinate vector with distinguished coordinate one and auxiliary coordinate `t`. -/
def falsB (t : ℂ) : Option Unit → ℂ
  | none => 1
  | some _ => t

/-- The distinguished coordinate of `falsB t` is one. -/
@[simp] theorem falsB_none (t : ℂ) : falsB t none = 1 := rfl

/-- The auxiliary coordinate of `falsB t` is `t`. -/
@[simp] theorem falsB_some (t : ℂ) (u : Unit) : falsB t (some u) = t := rfl

/-- Pairing `falsB t` with column zero gives `uA β - I*t`. -/
theorem pair_falsB_zero (β : ℝ) (t : ℂ) :
    (maj3UnbalProgram β).pair (falsB t) 0 = ((uA β : ℝ) : ℂ) - Complex.I * t := by
  rw [pair_eq β (falsB t) 0]
  simp only [falsB_none, falsB_some, out_zero, con_zero, mul_one]
  rw [Complex.conj_ofReal, Complex.conj_I]
  ring

/-- Pairing `falsB t` with column one gives `uA β + I*t`. -/
theorem pair_falsB_one (β : ℝ) (t : ℂ) :
    (maj3UnbalProgram β).pair (falsB t) 1 = ((uA β : ℝ) : ℂ) + Complex.I * t := by
  rw [pair_eq β (falsB t) 1]
  simp only [falsB_none, falsB_some, out_one, con_one, mul_one]
  rw [Complex.conj_ofReal, Complex.conj_neg_I]

/-- Pairing `falsB t` with column two gives `uC β + (2 * uA β)*t`. -/
theorem pair_falsB_two (β : ℝ) (t : ℂ) :
    (maj3UnbalProgram β).pair (falsB t) 2
      = ((uC β : ℝ) : ℂ) + ((2 * uA β : ℝ) : ℂ) * t := by
  rw [pair_eq β (falsB t) 2]
  simp only [falsB_none, falsB_some, out_two, con_two, mul_one]
  rw [Complex.conj_ofReal, Complex.conj_ofReal]

/-- With weights `ubz β`, the exact positive witness size on columns `{0, 1}` is `uM β`. See
[ReichardtSpalek2008]. -/
theorem wsize_true_01 (β : ℝ) :
    (maj3UnbalProgram β).WsizeTrueAt (ubz β) ({0, 1} : Finset (Fin 3)) (uM β) := by
  classical
  have hjk : (0 : Fin 3) ≠ 1 := by decide
  have h2 : (2 * uA β : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (uA_pos β).ne'
  have hne : (((2 * uA β : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2
  set X : ℂ := (((2 * uA β : ℝ)) : ℂ)⁻¹ with hX
  set w : Fin 3 → ℂ := (Pi.single 0 X + Pi.single 1 X : Fin 3 → ℂ) with hw
  have hw0 : w 0 = X := by simp [hw]
  have hw1 : w 1 = X := by simp [hw]
  have hw2 : w 2 = 0 := by simp [hw]
  have hXmul : X * (((2 * uA β : ℝ)) : ℂ) = 1 := by
    rw [hX]; exact inv_mul_cancel₀ hne
  have hcast : (((2 * uA β : ℝ)) : ℂ) = 2 * ((uA β : ℝ) : ℂ) := by push_cast; ring
  have hmul : X * (2 * ((uA β : ℝ) : ℂ)) = 1 := by rw [← hcast]; exact hXmul
  refine SpanProgram.WsizeTrueAt.ofLE ?_ ?_
  · refine ⟨w, ?_, ?_, ?_⟩
    · intro j hj
      have hj0 : j ≠ 0 := by rintro rfl; exact hj (by simp)
      have hj1 : j ≠ 1 := by rintro rfl; exact hj (by simp)
      simp [hw, Pi.single_eq_of_ne, hj0, hj1]
    · funext k
      cases k with
      | none =>
          simp only [target_none, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, v_none, out_zero, out_one]
          rw [hw0, hw1]
          linear_combination hmul
      | some u =>
          have hu : u = () := Subsingleton.elim u ()
          subst hu
          simp only [target_some, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
            smul_eq_mul, v_some, con_zero, con_one]
          rw [hw0, hw1]
          ring
    · have hwt : SpanProgram.wt (ubz β) w = uM β := by
        rw [SpanProgram.wt, Fin.sum_univ_three, z_zero, z_one, z_two, hw0, hw1, hw2]
        rw [norm_zero_sq]
        simp only [mul_zero, one_mul]
        rw [hX, ← two_norm_sq β]
        ring
      exact le_of_eq hwt
  · intro a hsupp hsum
    obtain ⟨hn, hs⟩ := true_coords β hsum
    rw [Finset.sum_pair hjk] at hn hs
    simp only [out_zero, out_one, con_zero, con_one] at hn hs
    have ha01 : a 0 = a 1 := by
      have h2 : (a 0 - a 1) * Complex.I = 0 := by linear_combination hs
      rcases mul_eq_zero.mp h2 with h | h
      · linear_combination h
      · exact absurd h Complex.I_ne_zero
    have h2α : (((2 * uA β : ℝ)) : ℂ) * a 0 = 1 := by
      rw [← ha01] at hn
      push_cast
      linear_combination hn
    have ha0 : a 0 = (((2 * uA β : ℝ)) : ℂ)⁻¹ := eq_inv_of_mul_eq_one_right h2α
    have ha1 : a 1 = (((2 * uA β : ℝ)) : ℂ)⁻¹ := by rw [← ha01]; exact ha0
    have ha2 : a 2 = 0 := hsupp 2 (by simp)
    have hwt : SpanProgram.wt (ubz β) a = uM β := by
      rw [SpanProgram.wt, Fin.sum_univ_three, z_zero, z_one, z_two, ha0, ha1, ha2]
      rw [norm_zero_sq]
      simp only [mul_zero, one_mul]
      rw [← two_norm_sq β]
      ring
    exact le_of_eq hwt.symm

/-- For nonnegative `β`, there is a positive witness supported on `{0, 2}` of weighted cost at
most `uM β`. See [ReichardtSpalek2008]. -/
theorem wsize_true_02 (β : ℝ) (hβ : 0 ≤ β) :
    (maj3UnbalProgram β).WsizeTrueLE (ubz β) ({0, 2} : Finset (Fin 3)) (uM β) := by
  classical
  have hjk : (0 : Fin 3) ≠ 2 := by decide
  set E : ℂ := ((uC β : ℝ) : ℂ) + 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2 with hE
  have hEne : E ≠ 0 := by
    intro h
    have h1 : Complex.normSq E = 1 := by rw [hE]; exact normSq_uC_add β hβ
    rw [h] at h1
    simp at h1
  set d : ℂ := E⁻¹ with hd
  have hd2 : ‖d‖ ^ 2 = 1 := by rw [hd, hE]; exact normSq_inv_uC_add β hβ
  have hdE : d * E = 1 := by rw [hd]; exact inv_mul_cancel₀ hEne
  set w : Fin 3 → ℂ :=
    (Pi.single 0 (2 * Complex.I * ((uA β : ℝ) : ℂ) * d) + Pi.single 2 d : Fin 3 → ℂ) with hw
  have hw0 : w 0 = 2 * Complex.I * ((uA β : ℝ) : ℂ) * d := by simp [hw]
  have hw1 : w 1 = 0 := by simp [hw]
  have hw2 : w 2 = d := by simp [hw]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j hj
    have hj0 : j ≠ 0 := by rintro rfl; exact hj (by simp)
    have hj2 : j ≠ 2 := by rintro rfl; exact hj (by simp)
    simp [hw, Pi.single_eq_of_ne, hj0, hj2]
  · funext k
    cases k with
    | none =>
        simp only [target_none, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, v_none, out_zero, out_two]
        rw [hw0, hw2]
        rw [hE] at hdE
        linear_combination hdE
    | some u =>
        have hu : u = () := Subsingleton.elim u ()
        subst hu
        simp only [target_some, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, v_some, con_zero, con_two]
        rw [hw0, hw2]
        push_cast
        linear_combination (2 * ((uA β : ℝ) : ℂ) * d) * Complex.I_mul_I
  · have hwt : SpanProgram.wt (ubz β) w = uM β := by
      rw [SpanProgram.wt, Fin.sum_univ_three, z_zero, z_one, z_two, hw0, hw1, hw2]
      rw [norm_zero_sq]
      rw [norm_two_I_uA_mul β d, hd2]
      simp only [mul_zero, mul_one, one_mul, add_zero, zero_add]
      rw [four_uA_add β]
    exact le_of_eq hwt

/-- For nonnegative `β`, there is a positive witness supported on `{1, 2}` of weighted cost at
most `uM β`. See [ReichardtSpalek2008]. -/
theorem wsize_true_12 (β : ℝ) (hβ : 0 ≤ β) :
    (maj3UnbalProgram β).WsizeTrueLE (ubz β) ({1, 2} : Finset (Fin 3)) (uM β) := by
  classical
  have hjk : (1 : Fin 3) ≠ 2 := by decide
  set E : ℂ := ((uC β : ℝ) : ℂ) - 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2 with hE
  have hEne : E ≠ 0 := by
    intro h
    have h1 : Complex.normSq E = 1 := by rw [hE]; exact normSq_uC_sub β hβ
    rw [h] at h1
    simp at h1
  set d : ℂ := E⁻¹ with hd
  have hd2 : ‖d‖ ^ 2 = 1 := by rw [hd, hE]; exact normSq_inv_uC_sub β hβ
  have hdE : d * E = 1 := by rw [hd]; exact inv_mul_cancel₀ hEne
  set w : Fin 3 → ℂ :=
    (Pi.single 1 (-(2 * Complex.I * ((uA β : ℝ) : ℂ) * d)) + Pi.single 2 d : Fin 3 → ℂ) with hw
  have hw0 : w 0 = 0 := by simp [hw]
  have hw1 : w 1 = -(2 * Complex.I * ((uA β : ℝ) : ℂ) * d) := by simp [hw]
  have hw2 : w 2 = d := by simp [hw]
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j hj
    have hj1 : j ≠ 1 := by rintro rfl; exact hj (by simp)
    have hj2 : j ≠ 2 := by rintro rfl; exact hj (by simp)
    simp [hw, Pi.single_eq_of_ne, hj1, hj2]
  · funext k
    cases k with
    | none =>
        simp only [target_none, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, v_none, out_one, out_two]
        rw [hw1, hw2]
        rw [hE] at hdE
        linear_combination hdE
    | some u =>
        have hu : u = () := Subsingleton.elim u ()
        subst hu
        simp only [target_some, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, v_some, con_one, con_two]
        rw [hw1, hw2]
        push_cast
        linear_combination (2 * ((uA β : ℝ) : ℂ) * d) * Complex.I_mul_I
  · have hwt : SpanProgram.wt (ubz β) w = uM β := by
      rw [SpanProgram.wt, Fin.sum_univ_three, z_zero, z_one, z_two, hw0, hw1, hw2]
      rw [norm_zero_sq]
      rw [show ‖-(2 * Complex.I * ((uA β : ℝ) : ℂ) * d)‖ ^ 2
          = ‖2 * Complex.I * ((uA β : ℝ) : ℂ) * d‖ ^ 2 by rw [norm_neg]]
      rw [norm_two_I_uA_mul β d, hd2]
      simp only [mul_zero, mul_one, one_mul, add_zero, zero_add]
      rw [four_uA_add β]
    exact le_of_eq hwt

/-- There is a positive witness using all three columns of weighted cost at most `uM β`. See
[ReichardtSpalek2008]. -/
theorem wsize_true_three (β : ℝ) :
    (maj3UnbalProgram β).WsizeTrueLE (ubz β) (univ : Finset (Fin 3)) (uM β) := by
  classical
  have hjk : (0 : Fin 3) ≠ 1 := by decide
  have h2 : (2 * uA β : ℝ) ≠ 0 := mul_ne_zero (by norm_num) (uA_pos β).ne'
  have hne : (((2 * uA β : ℝ)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h2
  set X : ℂ := (((2 * uA β : ℝ)) : ℂ)⁻¹ with hX
  set w : Fin 3 → ℂ := (Pi.single 0 X + Pi.single 1 X : Fin 3 → ℂ) with hw
  have hw0 : w 0 = X := by simp [hw]
  have hw1 : w 1 = X := by simp [hw]
  have hw2 : w 2 = 0 := by simp [hw]
  have hXmul : X * (((2 * uA β : ℝ)) : ℂ) = 1 := by
    rw [hX]; exact inv_mul_cancel₀ hne
  have hcast : (((2 * uA β : ℝ)) : ℂ) = 2 * ((uA β : ℝ) : ℂ) := by push_cast; ring
  have hmul : X * (2 * ((uA β : ℝ) : ℂ)) = 1 := by rw [← hcast]; exact hXmul
  refine ⟨w, ?_, ?_, ?_⟩
  · intro j hj
    exact absurd (Finset.mem_univ j) hj
  · have hzero : ∀ j ∈ (univ : Finset (Fin 3)), j ∉ ({0, 1} : Finset (Fin 3)) →
        w j • (maj3UnbalProgram β).v j = 0 := by
      intro j _ hj
      have hj0 : j ≠ 0 := by rintro rfl; exact hj (by simp)
      have hj1 : j ≠ 1 := by rintro rfl; exact hj (by simp)
      rw [show w j = 0 by simp [hw, Pi.single_eq_of_ne, hj0, hj1]]
      simp
    rw [← Finset.sum_subset (Finset.subset_univ ({0, 1} : Finset (Fin 3))) hzero]
    funext k
    cases k with
    | none =>
        simp only [target_none, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, v_none, out_zero, out_one]
        rw [hw0, hw1]
        linear_combination hmul
    | some u =>
        have hu : u = () := Subsingleton.elim u ()
        subst hu
        simp only [target_some, Finset.sum_pair hjk, Finset.sum_apply, Pi.smul_apply,
          smul_eq_mul, v_some, con_zero, con_one]
        rw [hw0, hw1]
        ring
  · have hwt : SpanProgram.wt (ubz β) w = uM β := by
      rw [SpanProgram.wt, Fin.sum_univ_three, z_zero, z_one, z_two, hw0, hw1, hw2]
      rw [norm_zero_sq]
      simp only [mul_zero, one_mul]
      rw [hX, ← two_norm_sq β]
      ring
    exact le_of_eq hwt

/-- For nonnegative `β`, there is a normalized negative witness orthogonal to column zero of
weighted cost at most `uM β`. See [ReichardtSpalek2008]. -/
theorem wsize_false_zero (β : ℝ) (hβ : 0 ≤ β) :
    (maj3UnbalProgram β).WsizeFalseLE (ubz β) ({0} : Finset (Fin 3)) (uM β) := by
  classical
  refine ⟨falsB (-Complex.I * ((uA β : ℝ) : ℂ)), rfl, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    rw [pair_falsB_zero]
    have e0 : ((uA β : ℝ) : ℂ) - Complex.I * (-Complex.I * ((uA β : ℝ) : ℂ)) = 0 := by
      linear_combination ((uA β : ℝ) : ℂ) * Complex.I_mul_I
    rw [e0]
  · rw [Fin.sum_univ_three, z_zero, z_one, z_two,
      pair_falsB_zero, pair_falsB_one, pair_falsB_two]
    have h0n : ‖((uA β : ℝ) : ℂ) - Complex.I * (-Complex.I * ((uA β : ℝ) : ℂ))‖ ^ 2 = 0 := by
      have e0 : ((uA β : ℝ) : ℂ) - Complex.I * (-Complex.I * ((uA β : ℝ) : ℂ)) = 0 := by
        linear_combination ((uA β : ℝ) : ℂ) * Complex.I_mul_I
      rw [e0]; simp
    have e1 : ((uA β : ℝ) : ℂ) + Complex.I * (-Complex.I * ((uA β : ℝ) : ℂ))
        = 2 * ((uA β : ℝ) : ℂ) := by
      linear_combination (-((uA β : ℝ) : ℂ)) * Complex.I_mul_I
    have e2 : ((uC β : ℝ) : ℂ) + ((2 * uA β : ℝ) : ℂ) * (-Complex.I * ((uA β : ℝ) : ℂ))
        = ((uC β : ℝ) : ℂ) - 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2 := by
      push_cast; ring
    rw [h0n, e1, norm_two_uA_sq β, e2, ← Complex.normSq_eq_norm_sq, normSq_uC_sub β hβ]
    simp only [mul_zero, mul_one, one_mul, zero_add]
    linarith [four_uA_add β]

/-- For nonnegative `β`, there is a normalized negative witness orthogonal to column one of
weighted cost at most `uM β`. See [ReichardtSpalek2008]. -/
theorem wsize_false_one (β : ℝ) (hβ : 0 ≤ β) :
    (maj3UnbalProgram β).WsizeFalseLE (ubz β) ({1} : Finset (Fin 3)) (uM β) := by
  classical
  refine ⟨falsB (Complex.I * ((uA β : ℝ) : ℂ)), rfl, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    rw [pair_falsB_one]
    have e1 : ((uA β : ℝ) : ℂ) + Complex.I * (Complex.I * ((uA β : ℝ) : ℂ)) = 0 := by
      linear_combination ((uA β : ℝ) : ℂ) * Complex.I_mul_I
    rw [e1]
  · rw [Fin.sum_univ_three, z_zero, z_one, z_two,
      pair_falsB_zero, pair_falsB_one, pair_falsB_two]
    have e0 : ((uA β : ℝ) : ℂ) - Complex.I * (Complex.I * ((uA β : ℝ) : ℂ))
        = 2 * ((uA β : ℝ) : ℂ) := by
      linear_combination (-((uA β : ℝ) : ℂ)) * Complex.I_mul_I
    have h1n : ‖((uA β : ℝ) : ℂ) + Complex.I * (Complex.I * ((uA β : ℝ) : ℂ))‖ ^ 2 = 0 := by
      have e1 : ((uA β : ℝ) : ℂ) + Complex.I * (Complex.I * ((uA β : ℝ) : ℂ)) = 0 := by
        linear_combination ((uA β : ℝ) : ℂ) * Complex.I_mul_I
      rw [e1]; simp
    have e2 : ((uC β : ℝ) : ℂ) + ((2 * uA β : ℝ) : ℂ) * (Complex.I * ((uA β : ℝ) : ℂ))
        = ((uC β : ℝ) : ℂ) + 2 * Complex.I * (((uA β : ℝ) : ℂ)) ^ 2 := by
      push_cast; ring
    rw [e0, norm_two_uA_sq β, h1n, e2, ← Complex.normSq_eq_norm_sq, normSq_uC_add β hβ]
    simp only [mul_zero, mul_one, one_mul, zero_add]
    linarith [four_uA_add β]

/-- For nonnegative `β`, there is a normalized negative witness orthogonal to column two of
weighted cost at most `uM β`. See [ReichardtSpalek2008]. -/
theorem wsize_false_two (β : ℝ) (hβ : 0 ≤ β) :
    (maj3UnbalProgram β).WsizeFalseLE (ubz β) ({2} : Finset (Fin 3)) (uM β) := by
  classical
  have ha : uA β ≠ 0 := (uA_pos β).ne'
  set r : ℝ := uC β / (2 * uA β) with hr
  have hr2 : r ^ 2 = (uC β) ^ 2 / (4 * (uA β) ^ 2) := by
    rw [hr]; field_simp; ring
  have hr2' : 2 * r ^ 2 = (uC β) ^ 2 / (2 * (uA β) ^ 2) := by
    rw [hr2]; field_simp; ring
  refine ⟨falsB (-((r : ℝ) : ℂ)), rfl, ?_, ?_⟩
  · intro j hj
    rw [Finset.mem_singleton] at hj
    subst hj
    rw [pair_falsB_two]
    have e2 : ((uC β : ℝ) : ℂ) + ((2 * uA β : ℝ) : ℂ) * (-((r : ℝ) : ℂ)) = 0 := by
      rw [hr]; push_cast; have hα : ((uA β : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha; field_simp; ring
    rw [e2]
  · rw [Fin.sum_univ_three, z_zero, z_one, z_two,
      pair_falsB_zero, pair_falsB_one, pair_falsB_two]
    have hp0 : ‖((uA β : ℝ) : ℂ) - Complex.I * (-((r : ℝ) : ℂ))‖ ^ 2
        = (uA β) ^ 2 + r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq,
        show ((uA β : ℝ) : ℂ) - Complex.I * (-((r : ℝ) : ℂ))
          = ((uA β : ℝ) : ℂ) + ((r : ℝ) : ℂ) * Complex.I by ring]
      rw [normSq_ofReal_add_mul_I]
    have hp1 : ‖((uA β : ℝ) : ℂ) + Complex.I * (-((r : ℝ) : ℂ))‖ ^ 2
        = (uA β) ^ 2 + r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq,
        show ((uA β : ℝ) : ℂ) + Complex.I * (-((r : ℝ) : ℂ))
          = ((uA β : ℝ) : ℂ) + (((-r) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [normSq_ofReal_add_mul_I]; ring
    have hp2 : ‖((uC β : ℝ) : ℂ) + ((2 * uA β : ℝ) : ℂ) * (-((r : ℝ) : ℂ))‖ ^ 2 = 0 := by
      have e2 : ((uC β : ℝ) : ℂ) + ((2 * uA β : ℝ) : ℂ) * (-((r : ℝ) : ℂ)) = 0 := by
        rw [hr]; push_cast; have hα : ((uA β : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha; field_simp; ring
      rw [e2]; simp
    rw [hp0, hp1, hp2]
    simp only [mul_zero, mul_one, one_mul, zero_add, add_zero]
    linarith [two_uA_add β hβ, hr2']

/-- For nonnegative `β`, there is a normalized negative witness for the empty available set of
weighted cost at most `uM β`. See [ReichardtSpalek2008]. -/
theorem wsize_false_none (β : ℝ) (hβ : 0 ≤ β) :
    (maj3UnbalProgram β).WsizeFalseLE (ubz β) (∅ : Finset (Fin 3)) (uM β) := by
  classical
  have ha : uA β ≠ 0 := (uA_pos β).ne'
  set r : ℝ := uC β / (2 * uA β) with hr
  have hr2 : r ^ 2 = (uC β) ^ 2 / (4 * (uA β) ^ 2) := by
    rw [hr]; field_simp; ring
  have hr2' : 2 * r ^ 2 = (uC β) ^ 2 / (2 * (uA β) ^ 2) := by
    rw [hr2]; field_simp; ring
  refine ⟨falsB (-((r : ℝ) : ℂ)), rfl, ?_, ?_⟩
  · intro j hj
    simp at hj
  · rw [Fin.sum_univ_three, z_zero, z_one, z_two,
      pair_falsB_zero, pair_falsB_one, pair_falsB_two]
    have hp0 : ‖((uA β : ℝ) : ℂ) - Complex.I * (-((r : ℝ) : ℂ))‖ ^ 2
        = (uA β) ^ 2 + r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq,
        show ((uA β : ℝ) : ℂ) - Complex.I * (-((r : ℝ) : ℂ))
          = ((uA β : ℝ) : ℂ) + ((r : ℝ) : ℂ) * Complex.I by ring]
      rw [normSq_ofReal_add_mul_I]
    have hp1 : ‖((uA β : ℝ) : ℂ) + Complex.I * (-((r : ℝ) : ℂ))‖ ^ 2
        = (uA β) ^ 2 + r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq,
        show ((uA β : ℝ) : ℂ) + Complex.I * (-((r : ℝ) : ℂ))
          = ((uA β : ℝ) : ℂ) + (((-r) : ℝ) : ℂ) * Complex.I by push_cast; ring]
      rw [normSq_ofReal_add_mul_I]; ring
    have hp2 : ‖((uC β : ℝ) : ℂ) + ((2 * uA β : ℝ) : ℂ) * (-((r : ℝ) : ℂ))‖ ^ 2 = 0 := by
      have e2 : ((uC β : ℝ) : ℂ) + ((2 * uA β : ℝ) : ℂ) * (-((r : ℝ) : ℂ)) = 0 := by
        rw [hr]; push_cast; have hα : ((uA β : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ha; field_simp; ring
      rw [e2]; simp
    rw [hp0, hp1, hp2]
    simp only [mul_zero, mul_one, one_mul, zero_add, add_zero]
    linarith [two_uA_add β hβ, hr2']

/-- For nonnegative `β`, collect the exact positive witness size `uM β` on `{0, 1}` and witness
upper bounds `uM β` on every other listed availability pattern. See [ReichardtSpalek2008]. -/
theorem maj3_unbalanced_witness_size (β : ℝ) (hβ : 0 ≤ β) :
    ((maj3UnbalProgram β).WsizeTrueAt (ubz β) ({0, 1} : Finset (Fin 3)) (uM β)) ∧
    ((maj3UnbalProgram β).WsizeTrueLE (ubz β) ({0, 2} : Finset (Fin 3)) (uM β)) ∧
    ((maj3UnbalProgram β).WsizeTrueLE (ubz β) ({1, 2} : Finset (Fin 3)) (uM β)) ∧
    ((maj3UnbalProgram β).WsizeTrueLE (ubz β) (univ : Finset (Fin 3)) (uM β)) ∧
    ((maj3UnbalProgram β).WsizeFalseLE (ubz β) ({0} : Finset (Fin 3)) (uM β)) ∧
    ((maj3UnbalProgram β).WsizeFalseLE (ubz β) ({1} : Finset (Fin 3)) (uM β)) ∧
    ((maj3UnbalProgram β).WsizeFalseLE (ubz β) ({2} : Finset (Fin 3)) (uM β)) ∧
    ((maj3UnbalProgram β).WsizeFalseLE (ubz β) (∅ : Finset (Fin 3)) (uM β)) :=
  ⟨wsize_true_01 β, wsize_true_02 β hβ, wsize_true_12 β hβ, wsize_true_three β,
    wsize_false_zero β hβ, wsize_false_one β hβ, wsize_false_two β hβ,
    wsize_false_none β hβ⟩

/-- Scaling all column weights by nonnegative `B` gives exact positive witness size `B * uM β`
on `{0, 1}` and the same upper bound on every other listed pattern, for nonnegative `β`. See
[ReichardtSpalek2008]. -/
theorem maj3_unbalanced_witness_size_scaled (β : ℝ) (hβ : 0 ≤ β) (B : ℝ) (hB : 0 ≤ B) :
    ((maj3UnbalProgram β).WsizeTrueAt (fun j => B * ubz β j) ({0, 1} : Finset (Fin 3))
        (B * uM β)) ∧
    ((maj3UnbalProgram β).WsizeTrueLE (fun j => B * ubz β j) ({0, 2} : Finset (Fin 3))
        (B * uM β)) ∧
    ((maj3UnbalProgram β).WsizeTrueLE (fun j => B * ubz β j) ({1, 2} : Finset (Fin 3))
        (B * uM β)) ∧
    ((maj3UnbalProgram β).WsizeTrueLE (fun j => B * ubz β j) (univ : Finset (Fin 3))
        (B * uM β)) ∧
    ((maj3UnbalProgram β).WsizeFalseLE (fun j => B * ubz β j) ({0} : Finset (Fin 3))
        (B * uM β)) ∧
    ((maj3UnbalProgram β).WsizeFalseLE (fun j => B * ubz β j) ({1} : Finset (Fin 3))
        (B * uM β)) ∧
    ((maj3UnbalProgram β).WsizeFalseLE (fun j => B * ubz β j) ({2} : Finset (Fin 3))
        (B * uM β)) ∧
    ((maj3UnbalProgram β).WsizeFalseLE (fun j => B * ubz β j) (∅ : Finset (Fin 3))
        (B * uM β)) :=
  ⟨(wsize_true_01 β).smul B hB, (wsize_true_02 β hβ).smul B hB,
    (wsize_true_12 β hβ).smul B hB, (wsize_true_three β).smul B hB,
    (wsize_false_zero β hβ).smul B hB, (wsize_false_one β hβ).smul B hB,
    (wsize_false_two β hβ).smul B hB, (wsize_false_none β hβ).smul B hB⟩

end Unbalanced

end Qatlib.Papers.SpanProgram07.MainResults
