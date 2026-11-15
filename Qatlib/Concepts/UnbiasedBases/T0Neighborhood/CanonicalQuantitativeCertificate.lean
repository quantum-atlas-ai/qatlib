/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

@[expose] public section

namespace Qatlib.Concepts.UnbiasedBases.T0Neighborhood

/-- Bounds the norm of a sum of complex numbers by the sum of their given norm bounds. -/
private theorem nb_add {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖a + b‖ ≤ A + B := (norm_add_le a b).trans (add_le_add ha hb)

/-- Bounds the norm of a difference of complex numbers by the sum of their given norm bounds. -/
private theorem nb_sub {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖a - b‖ ≤ A + B := (norm_sub_le a b).trans (add_le_add ha hb)

/-- Negating a complex number preserves its given norm bound. -/
private theorem nb_neg {a : ℂ} {A : ℝ} (ha : ‖a‖ ≤ A) : ‖-a‖ ≤ A := by
  simpa only [norm_neg] using ha

/-- Bounds the norm of a product of complex numbers by the product of their given norm bounds. -/
private theorem nb_mul {a b : ℂ} {A B : ℝ} (ha : ‖a‖ ≤ A) (hb : ‖b‖ ≤ B) :
    ‖a * b‖ ≤ A * B := by
  rw [norm_mul]
  exact mul_le_mul ha hb (norm_nonneg b) ((norm_nonneg a).trans ha)

/-- Dividing a complex number by a natural number divides its given norm bound by that number. -/
private theorem nb_div {a : ℂ} {A : ℝ} (ha : ‖a‖ ≤ A) (n : ℕ) :
    ‖a / (n : ℂ)‖ ≤ A / n := by
  rw [norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right ha (Nat.cast_nonneg n)

/-- Raising a complex number to a natural power raises its given norm bound to the same power. -/
private theorem nb_pow {a : ℂ} {A : ℝ} (ha : ‖a‖ ≤ A) (n : ℕ) :
    ‖a ^ n‖ ≤ A ^ n := by
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg a) ha n

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 5 by 6 times `η` under the stated
assumptions. -/
private theorem step5 (x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (ph5 : ‖((x1 + x2 + x3 + x4 + x5 + 1) * (y1 + y2 + y3 + y4 + y5 + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η := by
  let target : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let h5 : ℂ := (x1 + x2 + x3 + x4 + x5 + 1) * (y1 + y2 + y3 + y4 + y5 + 1) - 6
  have eid : target = ((((((1 * h5) + ((-1) * g0)) + ((-1) * g1)) + ((-1) * g2)) + ((-1) * g3)) + ((-1) * g4)) := by
    dsimp only [target, g0, g1, g2, g3, g4, h5]
    ring_nf
  have c0 : ‖(1 : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(1 : ℂ)‖ ≤ 1 := (by norm_num)
      _ ≤ 1 := by norm_num
  have c1 : ‖((-1) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((-1) : ℂ)‖ ≤ 1 := (nb_neg (by norm_num))
      _ ≤ 1 := by norm_num
  have c2 : ‖((-1) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((-1) : ℂ)‖ ≤ 1 := (nb_neg (by norm_num))
      _ ≤ 1 := by norm_num
  have c3 : ‖((-1) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((-1) : ℂ)‖ ≤ 1 := (nb_neg (by norm_num))
      _ ≤ 1 := by norm_num
  have c4 : ‖((-1) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((-1) : ℂ)‖ ≤ 1 := (nb_neg (by norm_num))
      _ ≤ 1 := by norm_num
  have c5 : ‖((-1) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((-1) : ℂ)‖ ≤ 1 := (nb_neg (by norm_num))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 6 * η
  rw [eid]
  calc
    _ ≤ ((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph5) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4))
    _ = 6 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 6 by 12 times `η` under the stated
assumptions. -/
private theorem step6 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (ph6 : ‖((x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 + r*Complex.I/2) + x3 + x4*(-1/2 - r*Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 - r*Complex.I/2) + y3 + y4*(-1/2 + r*Complex.I/2) + y5*(-1/2 - r*Complex.I/2) + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let h6 : ℂ :=
      (x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 + r*Complex.I/2) + x3 + x4*(-1/2 - r*Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 - r*Complex.I/2) + y3 + y4*(-1/2 + r*Complex.I/2) + y5*(-1/2 - r*Complex.I/2) + 1) - 6
  have eid : target = ((((((((((-r) * Complex.I) / 3) * h6) + (((r * Complex.I) / 3) * g0)) + (((r * Complex.I) / 3) * g1)) + (((r * Complex.I) / 3) * g2)) + (((r * Complex.I) / 3) * g3)) + (((r * Complex.I) / 3) * g4)) + (((1 / 2) - ((r * Complex.I) / 6)) * g5)) := by
    dsimp only [target, g0, g1, g2, g3, g4, g5, h6]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-r) * Complex.I) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) * Complex.I) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul (nb_neg hrN) (by simp)) 3)
      _ ≤ 1 := by norm_num
  have c1 : ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul hrN (by simp)) 3)
      _ ≤ 1 := by norm_num
  have c2 : ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul hrN (by simp)) 3)
      _ ≤ 1 := by norm_num
  have c3 : ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul hrN (by simp)) 3)
      _ ≤ 1 := by norm_num
  have c4 : ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul hrN (by simp)) 3)
      _ ≤ 1 := by norm_num
  have c5 : ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul hrN (by simp)) 3)
      _ ≤ 1 := by norm_num
  have c6 : ‖(((1 / 2) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 2) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((1/2)+((2*1)/6)) := (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 12 * η
  rw [eid]
  calc
    _ ≤ (((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (6 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph6) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4)) (nb_mul c6 pg5))
    _ = 12 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 7 by 24 times `η` under the stated
assumptions. -/
private theorem step7 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (ph7 : ‖((x1*(-1/2 + r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) + x3 + x4*(-1/2 + r*Complex.I/2) + x5*(-1/2 - r*Complex.I/2) + 1) * (y1*(-1/2 - r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) + y3 + y4*(-1/2 - r*Complex.I/2) + y5*(-1/2 + r*Complex.I/2) + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let h7 : ℂ :=
      (x1*(-1/2 + r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) + x3 + x4*(-1/2 + r*Complex.I/2) + x5*(-1/2 - r*Complex.I/2) + 1) * (y1*(-1/2 - r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) + y3 + y4*(-1/2 - r*Complex.I/2) + y5*(-1/2 + r*Complex.I/2) + 1) - 6
  have eid : target = (((((((((1 / 3) * h7) + (((-1) / 3) * g0)) + (((-1) / 3) * g1)) + (((-1) / 3) * g2)) + (((-1) / 3) * g3)) + (((-1) / 3) * g4)) + (((1 / 6) - ((r * Complex.I) / 6)) * g5)) + (((r * Complex.I) / 3) * g6)) := by
    dsimp only [target, g0, g1, g2, g3, g4, g5, g6, h7]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((1 / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 3) : ℂ)‖ ≤ (1/3) := (nb_div (by norm_num) 3)
      _ ≤ 1 := by norm_num
  have c1 : ‖(((-1) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-1) / 3) : ℂ)‖ ≤ (1/3) := (nb_div (nb_neg (by norm_num)) 3)
      _ ≤ 1 := by norm_num
  have c2 : ‖(((-1) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-1) / 3) : ℂ)‖ ≤ (1/3) := (nb_div (nb_neg (by norm_num)) 3)
      _ ≤ 1 := by norm_num
  have c3 : ‖(((-1) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-1) / 3) : ℂ)‖ ≤ (1/3) := (nb_div (nb_neg (by norm_num)) 3)
      _ ≤ 1 := by norm_num
  have c4 : ‖(((-1) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-1) / 3) : ℂ)‖ ≤ (1/3) := (nb_div (nb_neg (by norm_num)) 3)
      _ ≤ 1 := by norm_num
  have c5 : ‖(((-1) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-1) / 3) : ℂ)‖ ≤ (1/3) := (nb_div (nb_neg (by norm_num)) 3)
      _ ≤ 1 := by norm_num
  have c6 : ‖(((1 / 6) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 6) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((1/6)+((2*1)/6)) := (nb_sub (nb_div (by norm_num) 6) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 1 := by norm_num
  have c7 : ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul hrN (by simp)) 3)
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 24 * η
  rw [eid]
  calc
    _ ≤ ((((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (6 * η))) + (1 * (12 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph7) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4)) (nb_mul c6 pg5)) (nb_mul c7 pg6))
    _ = 24 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 8 by 72 times `η` under the stated
assumptions. -/
private theorem step8 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hrN : ‖r‖ ≤ 2)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (ph8 : ‖((x1 + x2 - x3 - x4 - x5 + 1) * (y1 + y2 - y3 - y4 - y5 + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η := by
  let target : ℂ :=
      -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let h8 : ℂ := (x1 + x2 - x3 - x4 - x5 + 1) * (y1 + y2 - y3 - y4 - y5 + 1) - 6
  have eid : target = (((((((((((-1) / 2) * h8) + ((1 / 2) * g0)) + ((1 / 2) * g1)) + ((1 / 2) * g2)) + ((1 / 2) * g3)) + ((1 / 2) * g4)) + ((1 / 2) * g5)) + ((-1) * g6)) + ((((-1) / 2) - ((r * Complex.I) / 2)) * g7)) := by
    dsimp only [target, g0, g1, g2, g3, g4, g5, g6, g7, h8]
    ring_nf
  have c0 : ‖(((-1) / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-1) / 2) : ℂ)‖ ≤ (1/2) := (nb_div (nb_neg (by norm_num)) 2)
      _ ≤ 1 := by norm_num
  have c1 : ‖((1 / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 2) : ℂ)‖ ≤ (1/2) := (nb_div (by norm_num) 2)
      _ ≤ 1 := by norm_num
  have c2 : ‖((1 / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 2) : ℂ)‖ ≤ (1/2) := (nb_div (by norm_num) 2)
      _ ≤ 1 := by norm_num
  have c3 : ‖((1 / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 2) : ℂ)‖ ≤ (1/2) := (nb_div (by norm_num) 2)
      _ ≤ 1 := by norm_num
  have c4 : ‖((1 / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 2) : ℂ)‖ ≤ (1/2) := (nb_div (by norm_num) 2)
      _ ≤ 1 := by norm_num
  have c5 : ‖((1 / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 2) : ℂ)‖ ≤ (1/2) := (nb_div (by norm_num) 2)
      _ ≤ 1 := by norm_num
  have c6 : ‖((1 / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 2) : ℂ)‖ ≤ (1/2) := (nb_div (by norm_num) 2)
      _ ≤ 1 := by norm_num
  have c7 : ‖((-1) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((-1) : ℂ)‖ ≤ 1 := (nb_neg (by norm_num))
      _ ≤ 1 := by norm_num
  have c8 : ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 72 * η
  rw [eid]
  calc
    _ ≤ (((((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (6 * η))) + (1 * (12 * η))) + (2 * (24 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph8) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4)) (nb_mul c6 pg5)) (nb_mul c7 pg6)) (nb_mul c8 pg7))
    _ = 72 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 9 by 120 times `η` under the stated
assumptions. -/
private theorem step9 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (ph9 : ‖((x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 + r*Complex.I/2) - x3 + x4*(1/2 + r*Complex.I/2) + x5*(1/2 - r*Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 - r*Complex.I/2) - y3 + y4*(1/2 - r*Complex.I/2) + y5*(1/2 + r*Complex.I/2) + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let h9 : ℂ :=
      (x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 + r*Complex.I/2) - x3 + x4*(1/2 + r*Complex.I/2) + x5*(1/2 - r*Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 - r*Complex.I/2) - y3 + y4*(1/2 - r*Complex.I/2) + y5*(1/2 + r*Complex.I/2) + 1) - 6
  have eid : target = (((((((((((((-r) * Complex.I) / 6) * h9) + (((r * Complex.I) / 6) * g0)) + (((r * Complex.I) / 6) * g1)) + (((r * Complex.I) / 6) * g2)) + (((r * Complex.I) / 6) * g3)) + (((r * Complex.I) / 6) * g4)) + (((1 / 4) - ((r * Complex.I) / 12)) * g5)) + (((r * Complex.I) / 6) * g6)) + ((((-1) / 2) - ((r * Complex.I) / 6)) * g7)) + ((((-1) / 2) + ((r * Complex.I) / 6)) * g8)) := by
    dsimp only [target, g0, g1, g2, g3, g4, g5, g6, g7, g8, h9]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-r) * Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) * Complex.I) / 6) : ℂ)‖ ≤ ((2*1)/6) := (nb_div (nb_mul (nb_neg hrN) (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c1 : ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ ((2*1)/6) := (nb_div (nb_mul hrN (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c2 : ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ ((2*1)/6) := (nb_div (nb_mul hrN (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c3 : ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ ((2*1)/6) := (nb_div (nb_mul hrN (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c4 : ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ ((2*1)/6) := (nb_div (nb_mul hrN (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c5 : ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ ((2*1)/6) := (nb_div (nb_mul hrN (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c6 : ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c7 : ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ ((2*1)/6) := (nb_div (nb_mul hrN (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c8 : ‖((((-1) / 2) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((1/2)+((2*1)/6)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 1 := by norm_num
  have c9 : ‖((((-1) / 2) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 2) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((1/2)+((2*1)/6)) := (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 120 * η
  rw [eid]
  calc
    _ ≤ ((((((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (6 * η))) + (1 * (12 * η))) + (1 * (24 * η))) + (1 * (72 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph9) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4)) (nb_mul c6 pg5)) (nb_mul c7 pg6)) (nb_mul c8 pg7)) (nb_mul c9 pg8))
    _ = 120 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 10 by 348 times `η` under the stated
assumptions. -/
private theorem step10 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (ph10 : ‖((x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) - Complex.I*x3 + x4*(-r/2 + Complex.I/2) + x5*(-r/2 + Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) + Complex.I*y3 + y4*(-r/2 - Complex.I/2) + y5*(-r/2 - Complex.I/2) + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let h10 : ℂ :=
      (x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) - Complex.I*x3 + x4*(-r/2 + Complex.I/2) + x5*(-r/2 + Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) + Complex.I*y3 + y4*(-r/2 - Complex.I/2) + y5*(-r/2 - Complex.I/2) + 1) - 6
  have eid : target = (((((((((((((r / 6) - (Complex.I / 2)) * h10) + ((((-r) / 6) + (Complex.I / 2)) * g0)) + ((((-r) / 6) + (Complex.I / 2)) * g1)) + ((((-r) / 6) + (Complex.I / 2)) * g2)) + ((((-r) / 6) + (Complex.I / 2)) * g3)) + ((((-r) / 6) + (Complex.I / 2)) * g4)) + ((((-r) / 6) + (Complex.I / 2)) * g5)) + ((((((-1) / 2) + (r / 6)) - (Complex.I / 2)) + ((r * Complex.I) / 6)) * g6)) + ((((1 / 2) + (r / 3)) - ((r * Complex.I) / 6)) * g7)) + (((((r / 6) + (1 / 2)) - (Complex.I / 2)) + ((r * Complex.I) / 6)) * g8)) + (1 * g9)) := by
    dsimp only [target, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, h10]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((r / 6) - (Complex.I / 2)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r / 6) - (Complex.I / 2)) : ℂ)‖ ≤ ((2/6)+(1/2)) := (nb_sub (nb_div hrN 6) (nb_div (by simp) 2))
      _ ≤ 1 := by norm_num
  have c1 : ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ ((2/6)+(1/2)) := (nb_add (nb_div (nb_neg hrN) 6) (nb_div (by simp) 2))
      _ ≤ 1 := by norm_num
  have c2 : ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ ((2/6)+(1/2)) := (nb_add (nb_div (nb_neg hrN) 6) (nb_div (by simp) 2))
      _ ≤ 1 := by norm_num
  have c3 : ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ ((2/6)+(1/2)) := (nb_add (nb_div (nb_neg hrN) 6) (nb_div (by simp) 2))
      _ ≤ 1 := by norm_num
  have c4 : ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ ((2/6)+(1/2)) := (nb_add (nb_div (nb_neg hrN) 6) (nb_div (by simp) 2))
      _ ≤ 1 := by norm_num
  have c5 : ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ ((2/6)+(1/2)) := (nb_add (nb_div (nb_neg hrN) 6) (nb_div (by simp) 2))
      _ ≤ 1 := by norm_num
  have c6 : ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) + (Complex.I / 2)) : ℂ)‖ ≤ ((2/6)+(1/2)) := (nb_add (nb_div (nb_neg hrN) 6) (nb_div (by simp) 2))
      _ ≤ 1 := by norm_num
  have c7 : ‖((((((-1) / 2) + (r / 6)) - (Complex.I / 2)) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((((-1) / 2) + (r / 6)) - (Complex.I / 2)) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((((1/2)+(2/6))+(1/2))+((2*1)/6)) := (nb_add (nb_sub (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div hrN 6)) (nb_div (by simp) 2)) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 2 := by norm_num
  have c8 : ‖((((1 / 2) + (r / 3)) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((1 / 2) + (r / 3)) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (((1/2)+(2/3))+((2*1)/6)) := (nb_sub (nb_add (nb_div (by norm_num) 2) (nb_div hrN 3)) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 2 := by norm_num
  have c9 : ‖(((((r / 6) + (1 / 2)) - (Complex.I / 2)) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((((r / 6) + (1 / 2)) - (Complex.I / 2)) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((((2/6)+(1/2))+(1/2))+((2*1)/6)) := (nb_add (nb_sub (nb_add (nb_div hrN 6) (nb_div (by norm_num) 2)) (nb_div (by simp) 2)) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 2 := by norm_num
  have c10 : ‖(1 : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(1 : ℂ)‖ ≤ 1 := (by norm_num)
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 348 * η
  rw [eid]
  calc
    _ ≤ (((((((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (6 * η))) + (2 * (12 * η))) + (2 * (24 * η))) + (2 * (72 * η))) + (1 * (120 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph10) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4)) (nb_mul c6 pg5)) (nb_mul c7 pg6)) (nb_mul c8 pg7)) (nb_mul c9 pg8)) (nb_mul c10 pg9))
    _ = 348 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 11 by 612 times `η` under the stated
assumptions. -/
private theorem step11 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (ph11 : ‖((x1*(-1/2 + r*Complex.I/2) + x2 - Complex.I*x3 + x4*(r/2 + Complex.I/2) - Complex.I*x5 + 1) * (y1*(-1/2 - r*Complex.I/2) + y2 + Complex.I*y3 + y4*(r/2 - Complex.I/2) + Complex.I*y5 + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let h11 : ℂ :=
      (x1*(-1/2 + r*Complex.I/2) + x2 - Complex.I*x3 + x4*(r/2 + Complex.I/2) - Complex.I*x5 + 1) *
      (y1*(-1/2 - r*Complex.I/2) + y2 + Complex.I*y3 + y4*(r/2 - Complex.I/2) + Complex.I*y5 + 1) - 6
  have eid : target = ((((((((((((((r / 6) + (Complex.I / 6)) * h11) + ((((-r) / 6) - (Complex.I / 6)) * g0)) + ((((-r) / 6) - (Complex.I / 6)) * g1)) + ((((-r) / 6) - (Complex.I / 6)) * g2)) + ((((-r) / 6) - (Complex.I / 6)) * g3)) + ((((-r) / 6) - (Complex.I / 6)) * g4)) + ((Complex.I / 3) * g5)) + (((1 / 3) - (Complex.I / 3)) * g6)) + ((((((-1) / 3) + (r / 6)) - (Complex.I / 6)) + ((r * Complex.I) / 3)) * g7)) + (((1 / 3) - (Complex.I / 3)) * g8)) + (((r / 6) - (Complex.I / 2)) * g9)) + ((((-1) / 2) + ((r * Complex.I) / 6)) * thresholdGoal)) := by
    dsimp only [target, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, thresholdGoal, h11]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((r / 6) + (Complex.I / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r / 6) + (Complex.I / 6)) : ℂ)‖ ≤ ((2/6)+(1/6)) := (nb_add (nb_div hrN 6) (nb_div (by simp) 6))
      _ ≤ 1 := by norm_num
  have c1 : ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ ((2/6)+(1/6)) := (nb_sub (nb_div (nb_neg hrN) 6) (nb_div (by simp) 6))
      _ ≤ 1 := by norm_num
  have c2 : ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ ((2/6)+(1/6)) := (nb_sub (nb_div (nb_neg hrN) 6) (nb_div (by simp) 6))
      _ ≤ 1 := by norm_num
  have c3 : ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ ((2/6)+(1/6)) := (nb_sub (nb_div (nb_neg hrN) 6) (nb_div (by simp) 6))
      _ ≤ 1 := by norm_num
  have c4 : ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ ((2/6)+(1/6)) := (nb_sub (nb_div (nb_neg hrN) 6) (nb_div (by simp) 6))
      _ ≤ 1 := by norm_num
  have c5 : ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 6) - (Complex.I / 6)) : ℂ)‖ ≤ ((2/6)+(1/6)) := (nb_sub (nb_div (nb_neg hrN) 6) (nb_div (by simp) 6))
      _ ≤ 1 := by norm_num
  have c6 : ‖((Complex.I / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((Complex.I / 3) : ℂ)‖ ≤ (1/3) := (nb_div (by simp) 3)
      _ ≤ 1 := by norm_num
  have c7 : ‖(((1 / 3) - (Complex.I / 3)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 3) - (Complex.I / 3)) : ℂ)‖ ≤ ((1/3)+(1/3)) := (nb_sub (nb_div (by norm_num) 3) (nb_div (by simp) 3))
      _ ≤ 1 := by norm_num
  have c8 : ‖((((((-1) / 3) + (r / 6)) - (Complex.I / 6)) + ((r * Complex.I) / 3)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((((-1) / 3) + (r / 6)) - (Complex.I / 6)) + ((r * Complex.I) / 3)) : ℂ)‖ ≤ ((((1/3)+(2/6))+(1/6))+((2*1)/3)) := (nb_add (nb_sub (nb_add (nb_div (nb_neg (by norm_num)) 3) (nb_div hrN 6)) (nb_div (by simp) 6)) (nb_div (nb_mul hrN (by simp)) 3))
      _ ≤ 2 := by norm_num
  have c9 : ‖(((1 / 3) - (Complex.I / 3)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 3) - (Complex.I / 3)) : ℂ)‖ ≤ ((1/3)+(1/3)) := (nb_sub (nb_div (by norm_num) 3) (nb_div (by simp) 3))
      _ ≤ 1 := by norm_num
  have c10 : ‖(((r / 6) - (Complex.I / 2)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r / 6) - (Complex.I / 2)) : ℂ)‖ ≤ ((2/6)+(1/2)) := (nb_sub (nb_div hrN 6) (nb_div (by simp) 2))
      _ ≤ 1 := by norm_num
  have c11 : ‖((((-1) / 2) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 2) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((1/2)+((2*1)/6)) := (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 612 * η
  rw [eid]
  calc
    _ ≤ ((((((((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (6 * η))) + (1 * (12 * η))) + (2 * (24 * η))) + (1 * (72 * η))) + (1 * (120 * η))) + (1 * (348 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph11) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4)) (nb_mul c6 pg5)) (nb_mul c7 pg6)) (nb_mul c8 pg7)) (nb_mul c9 pg8)) (nb_mul c10 pg9)) (nb_mul c11 pg10))
    _ = 612 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 12 by 1200 times `η` under the
stated assumptions. -/
private theorem step12 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (ph12 : ‖((x1 + x2*(-1/2 + r*Complex.I/2) - Complex.I*x3 - Complex.I*x4 + x5*(r/2 + Complex.I/2) + 1) * (y1 + y2*(-1/2 - r*Complex.I/2) + Complex.I*y3 + Complex.I*y4 + y5*(r/2 - Complex.I/2) + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x1*y4 + x2*y5 + y3
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let h12 : ℂ :=
      (x1 + x2*(-1/2 + r*Complex.I/2) - Complex.I*x3 - Complex.I*x4 + x5*(r/2 + Complex.I/2) + 1) *
      (y1 + y2*(-1/2 - r*Complex.I/2) + Complex.I*y3 + Complex.I*y4 + y5*(r/2 - Complex.I/2) + 1) - 6
  have eid : target = (((((((((((((((-Complex.I) / 6) * h12) + ((Complex.I / 6) * g0)) + ((Complex.I / 6) * g1)) + ((Complex.I / 6) * g2)) + ((Complex.I / 6) * g3)) + ((Complex.I / 6) * g4)) + ((((-r) / 12) - (Complex.I / 12)) * g5)) + ((((r / 12) + (1 / 6)) + (Complex.I / 12)) * g6)) + ((((1 / 12) + ((r * Complex.I) / 12)) + (Complex.I / 6)) * g7)) + ((((((-1) / 12) + (r / 12)) + (Complex.I / 12)) + ((r * Complex.I) / 12)) * g8)) + (((((-1) / 4) + (r / 6)) + ((r * Complex.I) / 12)) * g9)) + ((((-r) * Complex.I) / 6) * thresholdGoal)) + ((((-1) / 4) - ((r * Complex.I) / 4)) * clause11)) := by
    dsimp only [target, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, thresholdGoal, clause11, h12]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((-Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-Complex.I) / 6) : ℂ)‖ ≤ (1/6) := (nb_div (nb_neg (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c1 : ‖((Complex.I / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((Complex.I / 6) : ℂ)‖ ≤ (1/6) := (nb_div (by simp) 6)
      _ ≤ 1 := by norm_num
  have c2 : ‖((Complex.I / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((Complex.I / 6) : ℂ)‖ ≤ (1/6) := (nb_div (by simp) 6)
      _ ≤ 1 := by norm_num
  have c3 : ‖((Complex.I / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((Complex.I / 6) : ℂ)‖ ≤ (1/6) := (nb_div (by simp) 6)
      _ ≤ 1 := by norm_num
  have c4 : ‖((Complex.I / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((Complex.I / 6) : ℂ)‖ ≤ (1/6) := (nb_div (by simp) 6)
      _ ≤ 1 := by norm_num
  have c5 : ‖((Complex.I / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((Complex.I / 6) : ℂ)‖ ≤ (1/6) := (nb_div (by simp) 6)
      _ ≤ 1 := by norm_num
  have c6 : ‖((((-r) / 12) - (Complex.I / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 12) - (Complex.I / 12)) : ℂ)‖ ≤ ((2/12)+(1/12)) := (nb_sub (nb_div (nb_neg hrN) 12) (nb_div (by simp) 12))
      _ ≤ 1 := by norm_num
  have c7 : ‖((((r / 12) + (1 / 6)) + (Complex.I / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((r / 12) + (1 / 6)) + (Complex.I / 12)) : ℂ)‖ ≤ (((2/12)+(1/6))+(1/12)) := (nb_add (nb_add (nb_div hrN 12) (nb_div (by norm_num) 6)) (nb_div (by simp) 12))
      _ ≤ 1 := by norm_num
  have c8 : ‖((((1 / 12) + ((r * Complex.I) / 12)) + (Complex.I / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((1 / 12) + ((r * Complex.I) / 12)) + (Complex.I / 6)) : ℂ)‖ ≤ (((1/12)+((2*1)/12))+(1/6)) := (nb_add (nb_add (nb_div (by norm_num) 12) (nb_div (nb_mul hrN (by simp)) 12)) (nb_div (by simp) 6))
      _ ≤ 1 := by norm_num
  have c9 : ‖((((((-1) / 12) + (r / 12)) + (Complex.I / 12)) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((((-1) / 12) + (r / 12)) + (Complex.I / 12)) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((((1/12)+(2/12))+(1/12))+((2*1)/12)) := (nb_add (nb_add (nb_add (nb_div (nb_neg (by norm_num)) 12) (nb_div hrN 12)) (nb_div (by simp) 12)) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c10 : ‖(((((-1) / 4) + (r / 6)) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((-1) / 4) + (r / 6)) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (((1/4)+(2/6))+((2*1)/12)) := (nb_add (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div hrN 6)) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c11 : ‖((((-r) * Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) * Complex.I) / 6) : ℂ)‖ ≤ ((2*1)/6) := (nb_div (nb_mul (nb_neg hrN) (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c12 : ‖((((-1) / 4) - ((r * Complex.I) / 4)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 4) - ((r * Complex.I) / 4)) : ℂ)‖ ≤ ((1/4)+((2*1)/4)) := (nb_sub (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 4))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 1200 * η
  rw [eid]
  calc
    _ ≤ (((((((((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (6 * η))) + (1 * (12 * η))) + (1 * (24 * η))) + (1 * (72 * η))) + (1 * (120 * η))) + (1 * (348 * η))) + (1 * (612 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph12) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4)) (nb_mul c6 pg5)) (nb_mul c7 pg6)) (nb_mul c8 pg7)) (nb_mul c9 pg8)) (nb_mul c10 pg9)) (nb_mul c11 pg10)) (nb_mul c12 pg11))
    _ = 1200 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 13 by 588 times `η` under the stated
assumptions. -/
private theorem step13 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (ph13 : ‖((x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) + Complex.I*x3 + x4*(r/2 - Complex.I/2) + x5*(r/2 - Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) - Complex.I*y3 + y4*(r/2 + Complex.I/2) + y5*(r/2 + Complex.I/2) + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let h13 : ℂ :=
      (x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) + Complex.I*x3 + x4*(r/2 - Complex.I/2) + x5*(r/2 - Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) - Complex.I*y3 + y4*(r/2 + Complex.I/2) + y5*(r/2 + Complex.I/2) + 1) - 6
  have eid : target = (((((((((((((((-1) / 4) + ((r * Complex.I) / 12)) * h13) + (((1 / 4) - ((r * Complex.I) / 12)) * g0)) + (((1 / 4) - ((r * Complex.I) / 12)) * g1)) + (((1 / 4) - ((r * Complex.I) / 12)) * g2)) + (((1 / 4) - ((r * Complex.I) / 12)) * g3)) + (((1 / 4) - ((r * Complex.I) / 12)) * g4)) + (((1 / 4) - ((r * Complex.I) / 12)) * g5)) + (((((-r) / 6) - (1 / 4)) + ((r * Complex.I) / 12)) * g6)) + (((((-1) / 4) + (r / 6)) - ((r * Complex.I) / 12)) * g7)) + ((((((-1) / 4) + (r / 12)) + ((r * Complex.I) / 12)) + (Complex.I / 4)) * g8)) + (((r / 4) + (Complex.I / 4)) * g9)) + ((((-r) / 4) - (Complex.I / 4)) * thresholdGoal)) := by
    dsimp only [target, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, thresholdGoal, h13]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-1) / 4) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 4) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c1 : ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c2 : ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c3 : ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c4 : ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c5 : ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c6 : ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c7 : ‖(((((-r) / 6) - (1 / 4)) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((-r) / 6) - (1 / 4)) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (((2/6)+(1/4))+((2*1)/12)) := (nb_add (nb_sub (nb_div (nb_neg hrN) 6) (nb_div (by norm_num) 4)) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c8 : ‖(((((-1) / 4) + (r / 6)) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((-1) / 4) + (r / 6)) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (((1/4)+(2/6))+((2*1)/12)) := (nb_sub (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div hrN 6)) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c9 : ‖((((((-1) / 4) + (r / 12)) + ((r * Complex.I) / 12)) + (Complex.I / 4)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((((-1) / 4) + (r / 12)) + ((r * Complex.I) / 12)) + (Complex.I / 4)) : ℂ)‖ ≤ ((((1/4)+(2/12))+((2*1)/12))+(1/4)) := (nb_add (nb_add (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div hrN 12)) (nb_div (nb_mul hrN (by simp)) 12)) (nb_div (by simp) 4))
      _ ≤ 1 := by norm_num
  have c10 : ‖(((r / 4) + (Complex.I / 4)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r / 4) + (Complex.I / 4)) : ℂ)‖ ≤ ((2/4)+(1/4)) := (nb_add (nb_div hrN 4) (nb_div (by simp) 4))
      _ ≤ 1 := by norm_num
  have c11 : ‖((((-r) / 4) - (Complex.I / 4)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 4) - (Complex.I / 4)) : ℂ)‖ ≤ ((2/4)+(1/4)) := (nb_sub (nb_div (nb_neg hrN) 4) (nb_div (by simp) 4))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 588 * η
  rw [eid]
  calc
    _ ≤ ((((((((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (6 * η))) + (1 * (12 * η))) + (1 * (24 * η))) + (1 * (72 * η))) + (1 * (120 * η))) + (1 * (348 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph13) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4)) (nb_mul c6 pg5)) (nb_mul c7 pg6)) (nb_mul c8 pg7)) (nb_mul c9 pg8)) (nb_mul c10 pg9)) (nb_mul c11 pg10))
    _ = 588 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 14 by 1788 times `η` under the
stated assumptions. -/
private theorem step14 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (pg0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (ph14 : ‖((x1*(-1/2 + r*Complex.I/2) + x2 + Complex.I*x3 + x4*(-r/2 - Complex.I/2) + Complex.I*x5 + 1) * (y1*(-1/2 - r*Complex.I/2) + y2 - Complex.I*y3 + y4*(-r/2 + Complex.I/2) - Complex.I*y5 + 1) - 6 : ℂ)‖ ≤ (1 : ℝ) * η)
    : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let g0 : ℂ := x1*y1 - 1
  let g1 : ℂ := x2*y2 - 1
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let h14 : ℂ :=
      (x1*(-1/2 + r*Complex.I/2) + x2 + Complex.I*x3 + x4*(-r/2 - Complex.I/2) + Complex.I*x5 + 1) * (y1*(-1/2 - r*Complex.I/2) + y2 - Complex.I*y3 + y4*(-r/2 + Complex.I/2) - Complex.I*y5 + 1) - 6
  have eid : target = ((((((((((((((((1 / 12) + ((r * Complex.I) / 12)) * h14) + ((((-1) / 12) - ((r * Complex.I) / 12)) * g0)) + ((((-1) / 12) - ((r * Complex.I) / 12)) * g1)) + ((((-1) / 12) - ((r * Complex.I) / 12)) * g2)) + ((((-1) / 12) - ((r * Complex.I) / 12)) * g3)) + ((((-1) / 12) - ((r * Complex.I) / 12)) * g4)) + ((((-1) / 12) + ((r * Complex.I) / 12)) * g5)) + ((((((-r) / 12) + (1 / 12)) - ((r * Complex.I) / 12)) - (Complex.I / 12)) * g6)) + ((((1 / 6) + (r / 6)) - (Complex.I / 6)) * g7)) + ((((((-r) / 12) + (1 / 12)) - ((r * Complex.I) / 12)) - (Complex.I / 12)) * g8)) + (((1 / 4) - ((r * Complex.I) / 12)) * g9)) + ((r / 6) * thresholdGoal)) + (((r / 4) + (Complex.I / 4)) * clause11)) + (((1 / 2) - ((r * Complex.I) / 6)) * clause13)) := by
    dsimp only [target, g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, thresholdGoal, clause11, clause13,
        h14]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((1 / 12) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 12) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/12)+((2*1)/12)) := (nb_add (nb_div (by norm_num) 12) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c1 : ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/12)+((2*1)/12)) := (nb_sub (nb_div (nb_neg (by norm_num)) 12) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c2 : ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/12)+((2*1)/12)) := (nb_sub (nb_div (nb_neg (by norm_num)) 12) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c3 : ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/12)+((2*1)/12)) := (nb_sub (nb_div (nb_neg (by norm_num)) 12) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c4 : ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/12)+((2*1)/12)) := (nb_sub (nb_div (nb_neg (by norm_num)) 12) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c5 : ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 12) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/12)+((2*1)/12)) := (nb_sub (nb_div (nb_neg (by norm_num)) 12) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c6 : ‖((((-1) / 12) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 12) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/12)+((2*1)/12)) := (nb_add (nb_div (nb_neg (by norm_num)) 12) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c7 : ‖((((((-r) / 12) + (1 / 12)) - ((r * Complex.I) / 12)) - (Complex.I / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((((-r) / 12) + (1 / 12)) - ((r * Complex.I) / 12)) - (Complex.I / 12)) : ℂ)‖ ≤ ((((2/12)+(1/12))+((2*1)/12))+(1/12)) := (nb_sub (nb_sub (nb_add (nb_div (nb_neg hrN) 12) (nb_div (by norm_num) 12)) (nb_div (nb_mul hrN (by simp)) 12)) (nb_div (by simp) 12))
      _ ≤ 1 := by norm_num
  have c8 : ‖((((1 / 6) + (r / 6)) - (Complex.I / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((1 / 6) + (r / 6)) - (Complex.I / 6)) : ℂ)‖ ≤ (((1/6)+(2/6))+(1/6)) := (nb_sub (nb_add (nb_div (by norm_num) 6) (nb_div hrN 6)) (nb_div (by simp) 6))
      _ ≤ 1 := by norm_num
  have c9 : ‖((((((-r) / 12) + (1 / 12)) - ((r * Complex.I) / 12)) - (Complex.I / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((((-r) / 12) + (1 / 12)) - ((r * Complex.I) / 12)) - (Complex.I / 12)) : ℂ)‖ ≤ ((((2/12)+(1/12))+((2*1)/12))+(1/12)) := (nb_sub (nb_sub (nb_add (nb_div (nb_neg hrN) 12) (nb_div (by norm_num) 12)) (nb_div (nb_mul hrN (by simp)) 12)) (nb_div (by simp) 12))
      _ ≤ 1 := by norm_num
  have c10 : ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c11 : ‖((r / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((r / 6) : ℂ)‖ ≤ (2/6) := (nb_div hrN 6)
      _ ≤ 1 := by norm_num
  have c12 : ‖(((r / 4) + (Complex.I / 4)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r / 4) + (Complex.I / 4)) : ℂ)‖ ≤ ((2/4)+(1/4)) := (nb_add (nb_div hrN 4) (nb_div (by simp) 4))
      _ ≤ 1 := by norm_num
  have c13 : ‖(((1 / 2) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 2) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((1/2)+((2*1)/6)) := (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 1788 * η
  rw [eid]
  calc
    _ ≤ ((((((((((((((1 * (1 * η)) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (1 * (6 * η))) + (1 * (12 * η))) + (1 * (24 * η))) + (1 * (72 * η))) + (1 * (120 * η))) + (1 * (348 * η))) + (1 * (612 * η))) + (1 * (588 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 ph14) (nb_mul c1 pg0)) (nb_mul c2 pg1)) (nb_mul c3 pg2)) (nb_mul c4 pg3)) (nb_mul c5 pg4)) (nb_mul c6 pg5)) (nb_mul c7 pg6)) (nb_mul c8 pg7)) (nb_mul c9 pg8)) (nb_mul c10 pg9)) (nb_mul c11 pg10)) (nb_mul c12 pg11)) (nb_mul c13 pg13))
    _ = 1788 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 15 by 3578 times `η` under the
stated assumptions. -/
private theorem step15 (r x2 x3 x5 y1 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let g4 : ℂ := x5*y5 - 1
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  have eid : target = (((y3 * (((-1) / 2) - ((r * Complex.I) / 2))) * g4) + ((y5 * ((1 / 2) + ((r * Complex.I) / 2))) * clause14)) := by
    dsimp only [target, g4, clause14]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y3 * (((-1) / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y3 * (((-1) / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy3 (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y5 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y5 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 3578 * η
  rw [eid]
  calc
    _ ≤ ((2 * (1 * η)) + (2 * (1788 * η))) := (nb_add (nb_mul c0 pg4) (nb_mul c1 pg14))
    _ = 3578 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 16 by 19559 times `η` under the
stated assumptions. -/
private theorem step16 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    : ‖(x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I) : ℂ)‖ ≤ (19559 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I)
  let g4 : ℂ := x5*y5 - 1
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  have eid : target = ((((((((((y1 * (((-3) / 2) + ((r * Complex.I) / 2))) + (y3 * ((r / 2) - ((3 * Complex.I) / 2)))) * g4) + ((y5 * ((3 / 2) - ((r * Complex.I) / 2))) * g8)) + ((y5 * ((3 / 2) - ((r * Complex.I) / 2))) * g9)) + ((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) * thresholdGoal)) + ((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) * clause11)) + ((y5 * (1 + (r * Complex.I))) * clause12)) + ((y5 * (((-r) / 2) + ((3 * Complex.I) / 2))) * clause13)) + ((((-r) / 2) - ((3 * Complex.I) / 2)) * walkGoal)) := by
    dsimp only [target, g4, g8, g9, thresholdGoal, clause11, clause12, clause13, walkGoal]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((y1 * (((-3) / 2) + ((r * Complex.I) / 2))) + (y3 * ((r / 2) - ((3 * Complex.I) / 2)))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖(((y1 * (((-3) / 2) + ((r * Complex.I) / 2))) + (y3 * ((r / 2) - ((3 * Complex.I) / 2)))) : ℂ)‖ ≤ ((1*((3/2)+((2*1)/2)))+(1*((2/2)+((3*1)/2)))) := (nb_add (nb_mul hNy1 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))) (nb_mul hNy3 (nb_sub (nb_div hrN 2) (nb_div (nb_mul (by norm_num) (by simp)) 2))))
      _ ≤ 5 := by norm_num
  have c1 : ‖((y5 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c2 : ‖((y5 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c3 : ‖((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c4 : ‖((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c5 : ‖((y5 * (1 + (r * Complex.I))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (1 + (r * Complex.I))) : ℂ)‖ ≤ (1*(1+(2*1))) := (nb_mul hNy5 (nb_add (by norm_num) (nb_mul hrN (by simp))))
      _ ≤ 3 := by norm_num
  have c6 : ‖((y5 * (((-r) / 2) + ((3 * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (((-r) / 2) + ((3 * Complex.I) / 2))) : ℂ)‖ ≤ (1*((2/2)+((3*1)/2))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg hrN) 2) (nb_div (nb_mul (by norm_num) (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c7 : ‖((((-r) / 2) - ((3 * Complex.I) / 2)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((-r) / 2) - ((3 * Complex.I) / 2)) : ℂ)‖ ≤ ((2/2)+((3*1)/2)) := (nb_sub (nb_div (nb_neg hrN) 2) (nb_div (nb_mul (by norm_num) (by simp)) 2))
      _ ≤ 3 := by norm_num
  change ‖target‖ ≤ 19559 * η
  rw [eid]
  calc
    _ ≤ ((((((((5 * (1 * η)) + (3 * (72 * η))) + (3 * (120 * η))) + (3 * (348 * η))) + (3 * (612 * η))) + (3 * (1200 * η))) + (3 * (588 * η))) + (3 * (3578 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg4) (nb_mul c1 pg8)) (nb_mul c2 pg9)) (nb_mul c3 pg10)) (nb_mul c4 pg11)) (nb_mul c5 pg12)) (nb_mul c6 pg13)) (nb_mul c7 pg15))
    _ = 19559 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 17 by 10732 times `η` under the
stated assumptions. -/
private theorem step17 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  let g3 : ℂ := x4*y4 - 1
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  have eid : target = ((((((y3 * (((-1) / 2) - ((r * Complex.I) / 2))) * g3) + ((y4 * ((1 / 2) + ((r * Complex.I) / 2))) * clause13)) + ((((-1) / 2) - ((r * Complex.I) / 2)) * clause12)) + ((y4 * (((-1) / 2) - ((r * Complex.I) / 2))) * clause14)) + ((-1) * walkGoal)) := by
    dsimp only [target, g3, clause12, clause13, clause14, walkGoal]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y3 * (((-1) / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y3 * (((-1) / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy3 (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y4 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy4 (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c2 : ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c3 : ‖((y4 * (((-1) / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * (((-1) / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy4 (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c4 : ‖((-1) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((-1) : ℂ)‖ ≤ 1 := (nb_neg (by norm_num))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 10732 * η
  rw [eid]
  calc
    _ ≤ (((((2 * (1 * η)) + (2 * (588 * η))) + (2 * (1200 * η))) + (2 * (1788 * η))) + (1 * (3578 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg3) (nb_mul c1 pg13)) (nb_mul c2 pg12)) (nb_mul c3 pg14)) (nb_mul c4 pg15))
    _ = 10732 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 18 by 13203 times `η` under the
stated assumptions. -/
private theorem step18 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    : ‖(x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) : ℂ)‖ ≤ (13203 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I)
  let g3 : ℂ := x4*y4 - 1
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  have eid : target = (((((y2 * (((-3) / 2) + ((r * Complex.I) / 2))) * g3) + ((y4 * ((3 / 2) - ((r * Complex.I) / 2))) * clause11)) + (((y4 * (1 - (r * Complex.I))) + (y5 * ((1 / 2) + ((r * Complex.I) / 2)))) * clause12)) + ((y4 * (((-r) / 2) + ((3 * Complex.I) / 2))) * clause14)) := by
    dsimp only [target, g3, clause11, clause12, clause14]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y2 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y2 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy2 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c1 : ‖((y4 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y4 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy4 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c2 : ‖(((y4 * (1 - (r * Complex.I))) + (y5 * ((1 / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖(((y4 * (1 - (r * Complex.I))) + (y5 * ((1 / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ ((1*(1+(2*1)))+(1*((1/2)+((2*1)/2)))) := (nb_add (nb_mul hNy4 (nb_sub (by norm_num) (nb_mul hrN (by simp)))) (nb_mul hNy5 (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))))
      _ ≤ 5 := by norm_num
  have c3 : ‖((y4 * (((-r) / 2) + ((3 * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y4 * (((-r) / 2) + ((3 * Complex.I) / 2))) : ℂ)‖ ≤ (1*((2/2)+((3*1)/2))) := (nb_mul hNy4 (nb_add (nb_div (nb_neg hrN) 2) (nb_div (nb_mul (by norm_num) (by simp)) 2)))
      _ ≤ 3 := by norm_num
  change ‖target‖ ≤ 13203 * η
  rw [eid]
  calc
    _ ≤ ((((3 * (1 * η)) + (3 * (612 * η))) + (5 * (1200 * η))) + (3 * (1788 * η))) := (nb_add (nb_add (nb_add (nb_mul c0 pg3) (nb_mul c1 pg11)) (nb_mul c2 pg12)) (nb_mul c3 pg14))
    _ = 13203 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 19 by 14334 times `η` under the
stated assumptions. -/
private theorem step19 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx4 : ‖x4‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg17 : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η)
    : ‖(-x1/2 + x2*x4*y5 + x3*y5*(-1/2 + r*Complex.I/2) + y2*(-3/4 + 3*r*Complex.I/4) : ℂ)‖ ≤ (14334 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := -x1/2 + x2*x4*y5 + x3*y5*(-1/2 + r*Complex.I/2) + y2*(-3/4 + 3*r*Complex.I/4)
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause17 : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  have eid : target = ((((((((y2 * ((1 / 4) - ((r * Complex.I) / 4))) * g3) + ((x4 * (((-1) / 4) + ((r * Complex.I) / 4))) * clause17)) + ((y2 * ((1 / 4) - ((r * Complex.I) / 4))) * g4)) + ((y5 * (((-1) / 4) + ((r * Complex.I) / 4))) * g7)) + ((y5 * ((1 / 4) - ((r * Complex.I) / 4))) * clause12)) + (((-1) / 2) * clause13)) + ((1 / 2) * clause14)) := by
    dsimp only [target, g3, g4, g7, clause12, clause13, clause14, clause17]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y2 * ((1 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y2 * ((1 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/4))) := (nb_mul hNy2 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 1 := by norm_num
  have c1 : ‖((x4 * (((-1) / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((x4 * (((-1) / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/4))) := (nb_mul hNx4 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 1 := by norm_num
  have c2 : ‖((y2 * ((1 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y2 * ((1 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/4))) := (nb_mul hNy2 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 1 := by norm_num
  have c3 : ‖((y5 * (((-1) / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * (((-1) / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/4))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 1 := by norm_num
  have c4 : ‖((y5 * ((1 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((1 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/4))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 1 := by norm_num
  have c5 : ‖(((-1) / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-1) / 2) : ℂ)‖ ≤ (1/2) := (nb_div (nb_neg (by norm_num)) 2)
      _ ≤ 1 := by norm_num
  have c6 : ‖((1 / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 2) : ℂ)‖ ≤ (1/2) := (nb_div (by norm_num) 2)
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 14334 * η
  rw [eid]
  calc
    _ ≤ (((((((1 * (1 * η)) + (1 * (10732 * η))) + (1 * (1 * η))) + (1 * (24 * η))) + (1 * (1200 * η))) + (1 * (588 * η))) + (1 * (1788 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg3) (nb_mul c1 pg17)) (nb_mul c2 pg4)) (nb_mul c3 pg7)) (nb_mul c4 pg12)) (nb_mul c5 pg13)) (nb_mul c6 pg14))
    _ = 14334 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 20 by 57192 times `η` under the
stated assumptions. -/
private theorem step20 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx3 : ‖x3‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg17 : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η)
    (pg18 : ‖(x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) : ℂ)‖ ≤ (13203 : ℝ) * η)
    : ‖(-x1*y5^2 + x2*x3*y5*(3/2 + r*Complex.I/2) + x2*y3*y5*(-1/2 + r*Complex.I/2) + x2*y4^2 + y3^2*(-1/4 + r*Complex.I/4) + 3/4 + r*Complex.I/4 : ℂ)‖ ≤ (57192 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      -x1*y5^2 + x2*x3*y5*(3/2 + r*Complex.I/2) + x2*y3*y5*(-1/2 + r*Complex.I/2) + x2*y4^2 + y3^2*(-1/4 + r*Complex.I/4) + 3/4 + r*Complex.I/4
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause17 : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  let clause18 : ℂ :=
      x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I)
  have eid : target = (((((((((((((y4 * ((3 / 4) - ((r * Complex.I) / 4))) * thresholdGoal) + ((((x3 * (((-3) / 4) + ((r * Complex.I) / 4))) - (r / 4)) - ((3 * Complex.I) / 4)) * clause17)) + ((((-3) / 4) - ((r * Complex.I) / 4)) * g2)) + (((((y2 * ((3 / 4) - ((r * Complex.I) / 4))) + (y3 * ((r / 4) - ((3 * Complex.I) / 4)))) - (3 / 4)) - ((r * Complex.I) / 4)) * g3)) + ((((y3 * (((-r) / 4) + ((3 * Complex.I) / 4))) + (3 / 4)) + ((r * Complex.I) / 4)) * g4)) + ((y5 * (((-3) / 4) + ((r * Complex.I) / 4))) * g6)) + (((((-r) * Complex.I) * y5) / 2) * g7)) + ((y5 * ((3 / 4) - ((r * Complex.I) / 4))) * g9)) + ((y5 * ((3 / 4) - ((r * Complex.I) / 4))) * clause11)) + ((((((y3 * (((-1) / 4) + ((r * Complex.I) / 4))) - y4) + (y5 * ((1 / 4) - (((3 * r) * Complex.I) / 4)))) + (r / 4)) - ((3 * Complex.I) / 4)) * clause12)) + ((y4 * ((r / 4) - ((3 * Complex.I) / 4))) * clause14)) + ((1 / 2) * clause18)) := by
    dsimp only [target, g2, g3, g4, g6, g7, g9, thresholdGoal, clause11, clause12, clause14,
        clause17, clause18]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y4 * ((3 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * ((3 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((3/4)+((2*1)/4))) := (nb_mul hNy4 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 2 := by norm_num
  have c1 : ‖((((x3 * (((-3) / 4) + ((r * Complex.I) / 4))) - (r / 4)) - ((3 * Complex.I) / 4)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((x3 * (((-3) / 4) + ((r * Complex.I) / 4))) - (r / 4)) - ((3 * Complex.I) / 4)) : ℂ)‖ ≤ (((1*((3/4)+((2*1)/4)))+(2/4))+((3*1)/4)) := (nb_sub (nb_sub (nb_mul hNx3 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 4))) (nb_div hrN 4)) (nb_div (nb_mul (by norm_num) (by simp)) 4))
      _ ≤ 3 := by norm_num
  have c2 : ‖((((-3) / 4) - ((r * Complex.I) / 4)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-3) / 4) - ((r * Complex.I) / 4)) : ℂ)‖ ≤ ((3/4)+((2*1)/4)) := (nb_sub (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 4))
      _ ≤ 2 := by norm_num
  have c3 : ‖(((((y2 * ((3 / 4) - ((r * Complex.I) / 4))) + (y3 * ((r / 4) - ((3 * Complex.I) / 4)))) - (3 / 4)) - ((r * Complex.I) / 4)) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖(((((y2 * ((3 / 4) - ((r * Complex.I) / 4))) + (y3 * ((r / 4) - ((3 * Complex.I) / 4)))) - (3 / 4)) - ((r * Complex.I) / 4)) : ℂ)‖ ≤ ((((1*((3/4)+((2*1)/4)))+(1*((2/4)+((3*1)/4))))+(3/4))+((2*1)/4)) := (nb_sub (nb_sub (nb_add (nb_mul hNy2 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4))) (nb_mul hNy3 (nb_sub (nb_div hrN 4) (nb_div (nb_mul (by norm_num) (by simp)) 4)))) (nb_div (by norm_num) 4)) (nb_div (nb_mul hrN (by simp)) 4))
      _ ≤ 4 := by norm_num
  have c4 : ‖((((y3 * (((-r) / 4) + ((3 * Complex.I) / 4))) + (3 / 4)) + ((r * Complex.I) / 4)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((y3 * (((-r) / 4) + ((3 * Complex.I) / 4))) + (3 / 4)) + ((r * Complex.I) / 4)) : ℂ)‖ ≤ (((1*((2/4)+((3*1)/4)))+(3/4))+((2*1)/4)) := (nb_add (nb_add (nb_mul hNy3 (nb_add (nb_div (nb_neg hrN) 4) (nb_div (nb_mul (by norm_num) (by simp)) 4))) (nb_div (by norm_num) 4)) (nb_div (nb_mul hrN (by simp)) 4))
      _ ≤ 3 := by norm_num
  have c5 : ‖((y5 * (((-3) / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y5 * (((-3) / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((3/4)+((2*1)/4))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 2 := by norm_num
  have c6 : ‖(((((-r) * Complex.I) * y5) / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((-r) * Complex.I) * y5) / 2) : ℂ)‖ ≤ (((2*1)*1)/2) := (nb_div (nb_mul (nb_mul (nb_neg hrN) (by simp)) hNy5) 2)
      _ ≤ 1 := by norm_num
  have c7 : ‖((y5 * ((3 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y5 * ((3 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((3/4)+((2*1)/4))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 2 := by norm_num
  have c8 : ‖((y5 * ((3 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y5 * ((3 / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((3/4)+((2*1)/4))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 2 := by norm_num
  have c9 : ‖((((((y3 * (((-1) / 4) + ((r * Complex.I) / 4))) - y4) + (y5 * ((1 / 4) - (((3 * r) * Complex.I) / 4)))) + (r / 4)) - ((3 * Complex.I) / 4)) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((((((y3 * (((-1) / 4) + ((r * Complex.I) / 4))) - y4) + (y5 * ((1 / 4) - (((3 * r) * Complex.I) / 4)))) + (r / 4)) - ((3 * Complex.I) / 4)) : ℂ)‖ ≤ (((((1*((1/4)+((2*1)/4)))+1)+(1*((1/4)+(((3*2)*1)/4))))+(2/4))+((3*1)/4)) := (nb_sub (nb_add (nb_add (nb_sub (nb_mul hNy3 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 4))) hNy4) (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 4)))) (nb_div hrN 4)) (nb_div (nb_mul (by norm_num) (by simp)) 4))
      _ ≤ 5 := by norm_num
  have c10 : ‖((y4 * ((r / 4) - ((3 * Complex.I) / 4))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * ((r / 4) - ((3 * Complex.I) / 4))) : ℂ)‖ ≤ (1*((2/4)+((3*1)/4))) := (nb_mul hNy4 (nb_sub (nb_div hrN 4) (nb_div (nb_mul (by norm_num) (by simp)) 4)))
      _ ≤ 2 := by norm_num
  have c11 : ‖((1 / 2) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 2) : ℂ)‖ ≤ (1/2) := (nb_div (by norm_num) 2)
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 57192 * η
  rw [eid]
  calc
    _ ≤ ((((((((((((2 * (348 * η)) + (3 * (10732 * η))) + (2 * (1 * η))) + (4 * (1 * η))) + (3 * (1 * η))) + (2 * (12 * η))) + (1 * (24 * η))) + (2 * (120 * η))) + (2 * (612 * η))) + (5 * (1200 * η))) + (2 * (1788 * η))) + (1 * (13203 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg10) (nb_mul c1 pg17)) (nb_mul c2 pg2)) (nb_mul c3 pg3)) (nb_mul c4 pg4)) (nb_mul c5 pg6)) (nb_mul c6 pg7)) (nb_mul c7 pg9)) (nb_mul c8 pg11)) (nb_mul c9 pg12)) (nb_mul c10 pg14)) (nb_mul c11 pg18))
    _ = 57192 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 22 by 6220 times `η` under the
stated assumptions. -/
private theorem step22 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    : ‖(x3*y4^2 + y1*y4 + y2*y3*(-1/2 + r*Complex.I/2) : ℂ)‖ ≤ (6220 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x3*y4^2 + y1*y4 + y2*y3*(-1/2 + r*Complex.I/2)
  let g1 : ℂ := x2*y2 - 1
  let g3 : ℂ := x4*y4 - 1
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  have eid : target = ((((((y4 * ((1 / 2) - ((r * Complex.I) / 2))) * g9) + ((y2 * (((-1) / 2) + ((r * Complex.I) / 2))) * clause12)) + ((y5 * ((1 / 2) - ((r * Complex.I) / 2))) * g1)) + ((y5 * (((-1) / 2) + ((r * Complex.I) / 2))) * g3)) + ((y4 * (((-1) / 2) + ((r * Complex.I) / 2))) * clause14)) := by
    dsimp only [target, g1, g3, g9, clause12, clause14]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y4 * ((1 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * ((1 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy4 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y2 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y2 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy2 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c2 : ‖((y5 * ((1 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y5 * ((1 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c3 : ‖((y5 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y5 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c4 : ‖((y4 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy4 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 6220 * η
  rw [eid]
  calc
    _ ≤ (((((2 * (120 * η)) + (2 * (1200 * η))) + (2 * (1 * η))) + (2 * (1 * η))) + (2 * (1788 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg9) (nb_mul c1 pg12)) (nb_mul c2 pg1)) (nb_mul c3 pg3)) (nb_mul c4 pg14))
    _ = 6220 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 24 by 25706 times `η` under the
stated assumptions. -/
private theorem step24 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx2 : ‖x2‖ ≤ 1)
    (hNx5 : ‖x5‖ ≤ 1)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg17 : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η)
    : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause17 : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  have eid : target = (((((((y1 * (((-1) / 2) + ((r * Complex.I) / 2))) * g3) + ((y4 * ((1 / 2) - ((r * Complex.I) / 2))) * g7)) + ((((-2) * x2) + (y1 * (((-1) / 2) + ((r * Complex.I) / 2)))) * g4)) + ((y4 * (((-1) / 2) + ((r * Complex.I) / 2))) * clause12)) + ((-1) * clause14)) + ((x5 * (((-1) / 2) + ((r * Complex.I) / 2))) * clause17)) := by
    dsimp only [target, g3, g4, g7, clause12, clause14, clause17]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y1 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y1 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy1 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y4 * ((1 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * ((1 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy4 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c2 : ‖((((-2) * x2) + (y1 * (((-1) / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((((-2) * x2) + (y1 * (((-1) / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ ((2*1)+(1*((1/2)+((2*1)/2)))) := (nb_add (nb_mul (nb_neg (by norm_num)) hNx2) (nb_mul hNy1 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))))
      _ ≤ 4 := by norm_num
  have c3 : ‖((y4 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy4 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c4 : ‖((-1) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((-1) : ℂ)‖ ≤ 1 := (nb_neg (by norm_num))
      _ ≤ 1 := by norm_num
  have c5 : ‖((x5 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((x5 * (((-1) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNx5 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 25706 * η
  rw [eid]
  calc
    _ ≤ ((((((2 * (1 * η)) + (2 * (24 * η))) + (4 * (1 * η))) + (2 * (1200 * η))) + (1 * (1788 * η))) + (2 * (10732 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg3) (nb_mul c1 pg7)) (nb_mul c2 pg4)) (nb_mul c3 pg12)) (nb_mul c4 pg14)) (nb_mul c5 pg17))
    _ = 25706 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 25 by 51414 times `η` under the
stated assumptions. -/
private theorem step25 (r x2 y1 y2 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy2 : ‖y2‖ ≤ 1)
    (pg1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    : ‖(y1*y2 + 1/2 + r*Complex.I/2 : ℂ)‖ ≤ (51414 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y1*y2 + 1/2 + r*Complex.I/2
  let g1 : ℂ := x2*y2 - 1
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  have eid : target = (((((-1) / 2) - ((r * Complex.I) / 2)) * g1) + ((y2 * ((1 / 2) + ((r * Complex.I) / 2))) * clause24)) := by
    dsimp only [target, g1, clause24]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y2 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y2 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy2 (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 51414 * η
  rw [eid]
  calc
    _ ≤ ((2 * (1 * η)) + (2 * (25706 * η))) := (nb_add (nb_mul c0 pg1) (nb_mul c1 pg24))
    _ = 51414 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 26 by 56632 times `η` under the
stated assumptions. -/
private theorem step26 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy1 : ‖y1‖ ≤ 1)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    : ‖(x3*y5*(1/2 - r*Complex.I/2) + x5*y4*(-1/2 - r*Complex.I/2) + y1^2 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (56632 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x3*y5*(1/2 - r*Complex.I/2) + x5*y4*(-1/2 - r*Complex.I/2) + y1^2 + y2*(1/2 - r*Complex.I/2)
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  have eid : target = (((((((((((-1) / 2) - ((r * Complex.I) / 2)) * g5) + ((y1 * ((1 / 2) + ((r * Complex.I) / 2))) * clause24)) + (((1 / 2) + ((r * Complex.I) / 2)) * g6)) + ((((-1) / 2) + ((r * Complex.I) / 2)) * g7)) + (((1 / 2) + ((r * Complex.I) / 2)) * g8)) + (((1 / 2) + ((r * Complex.I) / 2)) * g9)) + (((1 / 2) + ((r * Complex.I) / 2)) * clause13)) + ((((-1) / 2) - ((r * Complex.I) / 2)) * clause14)) := by
    dsimp only [target, g5, g6, g7, g8, g9, clause13, clause14, clause24]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y1 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y1 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy1 (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c2 : ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c3 : ‖((((-1) / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c4 : ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c5 : ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c6 : ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c7 : ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 56632 * η
  rw [eid]
  calc
    _ ≤ ((((((((2 * (6 * η)) + (2 * (25706 * η))) + (2 * (12 * η))) + (2 * (24 * η))) + (2 * (72 * η))) + (2 * (120 * η))) + (2 * (588 * η))) + (2 * (1788 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg5) (nb_mul c1 pg24)) (nb_mul c2 pg6)) (nb_mul c3 pg7)) (nb_mul c4 pg8)) (nb_mul c5 pg9)) (nb_mul c6 pg13)) (nb_mul c7 pg14))
    _ = 56632 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 27 by 83755 times `η` under the
stated assumptions. -/
private theorem step27 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hrN : ‖r‖ ≤ 2)
    (hNx4 : ‖x4‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg19 : ‖(-x1/2 + x2*x4*y5 + x3*y5*(-1/2 + r*Complex.I/2) + y2*(-3/4 + 3*r*Complex.I/4) : ℂ)‖ ≤ (14334 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    : ‖(x1 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (83755 : ℝ) * η := by
  let target : ℂ := x1 + y2*(1/2 - r*Complex.I/2)
  let g4 : ℂ := x5*y5 - 1
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause19 : ℂ := -x1/2 + x2*x4*y5 + x3*y5*(-1/2 + r*Complex.I/2) + y2*(-3/4 + 3*r*Complex.I/4)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  have eid : target = ((((((-2) * clause19) + (((2 * x4) * y5) * clause24)) + ((y2 * (1 - (r * Complex.I))) * g4)) + ((y5 * ((-1) + (r * Complex.I))) * g7)) + ((y5 * (1 - (r * Complex.I))) * clause12)) := by
    dsimp only [target, g4, g7, clause12, clause19, clause24]
    ring_nf
  have c0 : ‖((-2) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((-2) : ℂ)‖ ≤ 2 := (nb_neg (by norm_num))
      _ ≤ 2 := by norm_num
  have c1 : ‖(((2 * x4) * y5) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((2 * x4) * y5) : ℂ)‖ ≤ ((2*1)*1) := (nb_mul (nb_mul (by norm_num) hNx4) hNy5)
      _ ≤ 2 := by norm_num
  have c2 : ‖((y2 * (1 - (r * Complex.I))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y2 * (1 - (r * Complex.I))) : ℂ)‖ ≤ (1*(1+(2*1))) := (nb_mul hNy2 (nb_sub (by norm_num) (nb_mul hrN (by simp))))
      _ ≤ 3 := by norm_num
  have c3 : ‖((y5 * ((-1) + (r * Complex.I))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * ((-1) + (r * Complex.I))) : ℂ)‖ ≤ (1*(1+(2*1))) := (nb_mul hNy5 (nb_add (nb_neg (by norm_num)) (nb_mul hrN (by simp))))
      _ ≤ 3 := by norm_num
  have c4 : ‖((y5 * (1 - (r * Complex.I))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (1 - (r * Complex.I))) : ℂ)‖ ≤ (1*(1+(2*1))) := (nb_mul hNy5 (nb_sub (by norm_num) (nb_mul hrN (by simp))))
      _ ≤ 3 := by norm_num
  change ‖target‖ ≤ 83755 * η
  rw [eid]
  calc
    _ ≤ (((((2 * (14334 * η)) + (2 * (25706 * η))) + (3 * (1 * η))) + (3 * (24 * η))) + (3 * (1200 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg19) (nb_mul c1 pg24)) (nb_mul c2 pg4)) (nb_mul c3 pg7)) (nb_mul c4 pg12))
    _ = 83755 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 28 by 171326 times `η` under the
stated assumptions. -/
private theorem step28 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy2 : ‖y2‖ ≤ 1)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg27 : ‖(x1 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (83755 : ℝ) * η)
    : ‖(x3*y4*(1/2 - r*Complex.I/2) + x4*y5*(-1/2 - r*Complex.I/2) + y1*(1/2 - r*Complex.I/2) + y2^2 : ℂ)‖ ≤ (171326 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x3*y4*(1/2 - r*Complex.I/2) + x4*y5*(-1/2 - r*Complex.I/2) + y1*(1/2 - r*Complex.I/2) + y2^2
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause27 : ℂ := x1 + y2*(1/2 - r*Complex.I/2)
  have eid : target = ((((((-1) / 2) - ((r * Complex.I) / 2)) * g9) + ((y2 * ((1 / 2) + ((r * Complex.I) / 2))) * clause27)) + (((1 / 2) + ((r * Complex.I) / 2)) * clause14)) := by
    dsimp only [target, g9, clause14, clause27]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y2 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y2 * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/2))) := (nb_mul hNy2 (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c2 : ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 171326 * η
  rw [eid]
  calc
    _ ≤ (((2 * (120 * η)) + (2 * (83755 * η))) + (2 * (1788 * η))) := (nb_add (nb_add (nb_mul c0 pg9) (nb_mul c1 pg27)) (nb_mul c2 pg14))
    _ = 171326 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 29 by 258040 times `η` under the
stated assumptions. -/
private theorem step29 (r x1 x2 x4 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg16 : ‖(x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I) : ℂ)‖ ≤ (19559 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg27 : ‖(x1 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (83755 : ℝ) * η)
    : ‖(x4*y5*(-3/2 + r*Complex.I/2) + y1*y4*y5*(-1/2 - r*Complex.I/2) + y1*(-3/2 - r*Complex.I/2) + y2*y3*y5 - 2*y5^2 : ℂ)‖ ≤ (258040 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x4*y5*(-3/2 + r*Complex.I/2) + y1*y4*y5*(-1/2 - r*Complex.I/2) + y1*(-3/2 - r*Complex.I/2) + y2*y3*y5 - 2*y5^2
  let clause16 : ℂ :=
      x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause27 : ℂ := x1 + y2*(1/2 - r*Complex.I/2)
  have eid : target = ((((((-1) / 2) - ((r * Complex.I) / 2)) * clause16) + (((y3 * y5) * ((1 / 2) + ((r * Complex.I) / 2))) * clause27)) + (((y4 * y5) * ((1 / 2) - ((r * Complex.I) / 2))) * clause24)) := by
    dsimp only [target, clause16, clause24, clause27]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c1 : ‖(((y3 * y5) * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((y3 * y5) * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ ((1*1)*((1/2)+((2*1)/2))) := (nb_mul (nb_mul hNy3 hNy5) (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  have c2 : ‖(((y4 * y5) * ((1 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((y4 * y5) * ((1 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ ((1*1)*((1/2)+((2*1)/2))) := (nb_mul (nb_mul hNy4 hNy5) (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 258040 * η
  rw [eid]
  calc
    _ ≤ (((2 * (19559 * η)) + (2 * (83755 * η))) + (2 * (25706 * η))) := (nb_add (nb_add (nb_mul c0 pg16) (nb_mul c1 pg27)) (nb_mul c2 pg24))
    _ = 258040 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 31 by 400160 times `η` under the
stated assumptions. -/
private theorem step31 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx3 : ‖x3‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    (pg20 : ‖(-x1*y5^2 + x2*x3*y5*(3/2 + r*Complex.I/2) + x2*y3*y5*(-1/2 + r*Complex.I/2) + x2*y4^2 + y3^2*(-1/4 + r*Complex.I/4) + 3/4 + r*Complex.I/4 : ℂ)‖ ≤ (57192 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg27 : ‖(x1 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (83755 : ℝ) * η)
    : ‖(y1*y4^2 + y2*y5^2 + y3^2/2 + y4*y5*(1/2 - r*Complex.I/2) - 3*r*Complex.I/2 : ℂ)‖ ≤ (400160 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y1*y4^2 + y2*y5^2 + y3^2/2 + y4*y5*(1/2 - r*Complex.I/2) - 3*r*Complex.I/2
  let g4 : ℂ := x5*y5 - 1
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let clause20 : ℂ :=
      -x1*y5^2 + x2*x3*y5*(3/2 + r*Complex.I/2) + x2*y3*y5*(-1/2 + r*Complex.I/2) + x2*y4^2 + y3^2*(-1/4 + r*Complex.I/4) + 3/4 + r*Complex.I/4
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause27 : ℂ := x1 + y2*(1/2 - r*Complex.I/2)
  have eid : target = (((((((((((((-1) / 2) - ((r * Complex.I) / 2)) * clause20) + (((((r * Complex.I) * x3) * y5) + ((y4 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2)))) * clause24)) + ((((-r) * y3) + (r * Complex.I)) * g4)) + ((y5 * (((-3) / 2) - ((r * Complex.I) / 2))) * g6)) + ((y5 * ((3 / 2) - ((r * Complex.I) / 2))) * g7)) + ((y5 * ((3 / 2) + ((r * Complex.I) / 2))) * g9)) + ((y5 * ((3 / 2) + ((r * Complex.I) / 2))) * clause11)) + ((2 * y5) * clause12)) + ((((-r) / 2) + ((3 * Complex.I) / 2)) * walkGoal)) + (((y5 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2))) * clause27)) := by
    dsimp only [target, g4, g6, g7, g9, clause11, clause12, walkGoal, clause20, clause24, clause27]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c1 : ‖(((((r * Complex.I) * x3) * y5) + ((y4 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖(((((r * Complex.I) * x3) * y5) + ((y4 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ ((((2*1)*1)*1)+((1^2)*((1/2)+((2*1)/2)))) := (nb_add (nb_mul (nb_mul (nb_mul hrN (by simp)) hNx3) hNy5) (nb_mul (nb_pow hNy4 2) (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))))
      _ ≤ 4 := by norm_num
  have c2 : ‖((((-r) * y3) + (r * Complex.I)) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((((-r) * y3) + (r * Complex.I)) : ℂ)‖ ≤ ((2*1)+(2*1)) := (nb_add (nb_mul (nb_neg hrN) hNy3) (nb_mul hrN (by simp)))
      _ ≤ 4 := by norm_num
  have c3 : ‖((y5 * (((-3) / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (((-3) / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c4 : ‖((y5 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c5 : ‖((y5 * ((3 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * ((3 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c6 : ‖((y5 * ((3 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * ((3 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c7 : ‖((2 * y5) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((2 * y5) : ℂ)‖ ≤ (2*1) := (nb_mul (by norm_num) hNy5)
      _ ≤ 2 := by norm_num
  have c8 : ‖((((-r) / 2) + ((3 * Complex.I) / 2)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((-r) / 2) + ((3 * Complex.I) / 2)) : ℂ)‖ ≤ ((2/2)+((3*1)/2)) := (nb_add (nb_div (nb_neg hrN) 2) (nb_div (nb_mul (by norm_num) (by simp)) 2))
      _ ≤ 3 := by norm_num
  have c9 : ‖(((y5 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((y5 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ ((1^2)*((1/2)+((2*1)/2))) := (nb_mul (nb_pow hNy5 2) (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 400160 * η
  rw [eid]
  calc
    _ ≤ ((((((((((2 * (57192 * η)) + (4 * (25706 * η))) + (4 * (1 * η))) + (3 * (12 * η))) + (3 * (24 * η))) + (3 * (120 * η))) + (3 * (612 * η))) + (2 * (1200 * η))) + (3 * (3578 * η))) + (2 * (83755 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg20) (nb_mul c1 pg24)) (nb_mul c2 pg4)) (nb_mul c3 pg6)) (nb_mul c4 pg7)) (nb_mul c5 pg9)) (nb_mul c6 pg11)) (nb_mul c7 pg12)) (nb_mul c8 pg15)) (nb_mul c9 pg27))
    _ = 400160 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 32 by 103524 times `η` under the
stated assumptions. -/
private theorem step32 (r x2 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg18 : ‖(x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) : ℂ)‖ ≤ (13203 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    : ‖(x5*y4*(-3/2 + r*Complex.I/2) + y1*y3*y4 + y1*y5^2*(1/2 + r*Complex.I/2) + y2*(-3/2 - r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/2) - 2*y4^2 : ℂ)‖ ≤ (103524 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x5*y4*(-3/2 + r*Complex.I/2) + y1*y3*y4 + y1*y5^2*(1/2 + r*Complex.I/2) + y2*(-3/2 - r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/2) - 2*y4^2
  let clause18 : ℂ :=
      x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  have eid : target = (((((-1) / 2) - ((r * Complex.I) / 2)) * clause18) + ((((y3 * y4) * ((1 / 2) + ((r * Complex.I) / 2))) + ((y5 ^ 2) * (((-1) / 2) + ((r * Complex.I) / 2)))) * clause24)) := by
    dsimp only [target, clause18, clause24]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-1) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  have c1 : ‖((((y3 * y4) * ((1 / 2) + ((r * Complex.I) / 2))) + ((y5 ^ 2) * (((-1) / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((y3 * y4) * ((1 / 2) + ((r * Complex.I) / 2))) + ((y5 ^ 2) * (((-1) / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ (((1*1)*((1/2)+((2*1)/2)))+((1^2)*((1/2)+((2*1)/2)))) := (nb_add (nb_mul (nb_mul hNy3 hNy4) (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))) (nb_mul (nb_pow hNy5 2) (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))))
      _ ≤ 3 := by norm_num
  change ‖target‖ ≤ 103524 * η
  rw [eid]
  calc
    _ ≤ ((2 * (13203 * η)) + (3 * (25706 * η))) := (nb_add (nb_mul c0 pg18) (nb_mul c1 pg24))
    _ = 103524 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 33 by 816748 times `η` under the
stated assumptions. -/
private theorem step33 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    (pg16 : ‖(x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I) : ℂ)‖ ≤ (19559 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg28 : ‖(x3*y4*(1/2 - r*Complex.I/2) + x4*y5*(-1/2 - r*Complex.I/2) + y1*(1/2 - r*Complex.I/2) + y2^2 : ℂ)‖ ≤ (171326 : ℝ) * η)
    : ‖(-r*Complex.I*x3*y4 + x4*y5*(-9/2 - 3*r*Complex.I/2) + y1*y3^2 + y1*y4*y5*(2 - 2*r*Complex.I) - 2*r*Complex.I*y1 - 2*y3*y4 + y5^2*(-5/2 - 5*r*Complex.I/2) : ℂ)‖ ≤ (816748 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      -r*Complex.I*x3*y4 + x4*y5*(-9/2 - 3*r*Complex.I/2) + y1*y3^2 + y1*y4*y5*(2 - 2*r*Complex.I) - 2*r*Complex.I*y1 - 2*y3*y4 + y5^2*(-5/2 - 5*r*Complex.I/2)
  let g4 : ℂ := x5*y5 - 1
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let clause16 : ℂ :=
      x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause28 : ℂ :=
      x3*y4*(1/2 - r*Complex.I/2) + x4*y5*(-1/2 - r*Complex.I/2) + y1*(1/2 - r*Complex.I/2) + y2^2
  have eid : target = (((((((((((((y3 * (((-3) / 2) - ((r * Complex.I) / 2))) + (y5 * (((-3) / 2) + ((r * Complex.I) / 2)))) * clause11) + (((y2 * ((3 / 2) + ((r * Complex.I) / 2))) + (y5 * (((-r) / 2) + ((3 * Complex.I) / 2)))) * clause13)) + ((y3 * ((r / 2) - ((3 * Complex.I) / 2))) * g4)) + ((((-3) / 2) - ((r * Complex.I) / 2)) * g9)) + ((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) * thresholdGoal)) + ((((-2) * y3) + (y5 * (1 + (r * Complex.I)))) * clause12)) + ((((y2 * (((-3) / 2) - ((r * Complex.I) / 2))) + (r * y3)) + 3) * clause14)) + ((((-r) / 2) - ((3 * Complex.I) / 2)) * walkGoal)) + ((1 - (r * Complex.I)) * clause16)) + ((((((y3 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2))) + ((4 * y4) * y5)) - (3 / 2)) + ((r * Complex.I) / 2)) * clause24)) + ((((-3) / 2) + ((r * Complex.I) / 2)) * clause28)) := by
    dsimp only [target, g4, g9, thresholdGoal, clause11, clause12, clause13, clause14, walkGoal,
        clause16, clause24, clause28]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((y3 * (((-3) / 2) - ((r * Complex.I) / 2))) + (y5 * (((-3) / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖(((y3 * (((-3) / 2) - ((r * Complex.I) / 2))) + (y5 * (((-3) / 2) + ((r * Complex.I) / 2)))) : ℂ)‖ ≤ ((1*((3/2)+((2*1)/2)))+(1*((3/2)+((2*1)/2)))) := (nb_add (nb_mul hNy3 (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))) (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))))
      _ ≤ 5 := by norm_num
  have c1 : ‖(((y2 * ((3 / 2) + ((r * Complex.I) / 2))) + (y5 * (((-r) / 2) + ((3 * Complex.I) / 2)))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖(((y2 * ((3 / 2) + ((r * Complex.I) / 2))) + (y5 * (((-r) / 2) + ((3 * Complex.I) / 2)))) : ℂ)‖ ≤ ((1*((3/2)+((2*1)/2)))+(1*((2/2)+((3*1)/2)))) := (nb_add (nb_mul hNy2 (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))) (nb_mul hNy5 (nb_add (nb_div (nb_neg hrN) 2) (nb_div (nb_mul (by norm_num) (by simp)) 2))))
      _ ≤ 5 := by norm_num
  have c2 : ‖((y3 * ((r / 2) - ((3 * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y3 * ((r / 2) - ((3 * Complex.I) / 2))) : ℂ)‖ ≤ (1*((2/2)+((3*1)/2))) := (nb_mul hNy3 (nb_sub (nb_div hrN 2) (nb_div (nb_mul (by norm_num) (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c3 : ‖((((-3) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((-3) / 2) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((3/2)+((2*1)/2)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 3 := by norm_num
  have c4 : ‖((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c5 : ‖((((-2) * y3) + (y5 * (1 + (r * Complex.I)))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((((-2) * y3) + (y5 * (1 + (r * Complex.I)))) : ℂ)‖ ≤ ((2*1)+(1*(1+(2*1)))) := (nb_add (nb_mul (nb_neg (by norm_num)) hNy3) (nb_mul hNy5 (nb_add (by norm_num) (nb_mul hrN (by simp)))))
      _ ≤ 5 := by norm_num
  have c6 : ‖((((y2 * (((-3) / 2) - ((r * Complex.I) / 2))) + (r * y3)) + 3) : ℂ)‖ ≤ (8 : ℝ) := by
    calc
      ‖((((y2 * (((-3) / 2) - ((r * Complex.I) / 2))) + (r * y3)) + 3) : ℂ)‖ ≤ (((1*((3/2)+((2*1)/2)))+(2*1))+3) := (nb_add (nb_add (nb_mul hNy2 (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))) (nb_mul hrN hNy3)) (by norm_num))
      _ ≤ 8 := by norm_num
  have c7 : ‖((((-r) / 2) - ((3 * Complex.I) / 2)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((-r) / 2) - ((3 * Complex.I) / 2)) : ℂ)‖ ≤ ((2/2)+((3*1)/2)) := (nb_sub (nb_div (nb_neg hrN) 2) (nb_div (nb_mul (by norm_num) (by simp)) 2))
      _ ≤ 3 := by norm_num
  have c8 : ‖((1 - (r * Complex.I)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((1 - (r * Complex.I)) : ℂ)‖ ≤ (1+(2*1)) := (nb_sub (by norm_num) (nb_mul hrN (by simp)))
      _ ≤ 3 := by norm_num
  have c9 : ‖((((((y3 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2))) + ((4 * y4) * y5)) - (3 / 2)) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (8 : ℝ) := by
    calc
      ‖((((((y3 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2))) + ((4 * y4) * y5)) - (3 / 2)) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (((((1^2)*((1/2)+((2*1)/2)))+((4*1)*1))+(3/2))+((2*1)/2)) := (nb_add (nb_sub (nb_add (nb_mul (nb_pow hNy3 2) (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))) (nb_mul (nb_mul (by norm_num) hNy4) hNy5)) (nb_div (by norm_num) 2)) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 8 := by norm_num
  have c10 : ‖((((-3) / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((-3) / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((3/2)+((2*1)/2)) := (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 3 := by norm_num
  change ‖target‖ ≤ 816748 * η
  rw [eid]
  calc
    _ ≤ (((((((((((5 * (612 * η)) + (5 * (588 * η))) + (3 * (1 * η))) + (3 * (120 * η))) + (3 * (348 * η))) + (5 * (1200 * η))) + (8 * (1788 * η))) + (3 * (3578 * η))) + (3 * (19559 * η))) + (8 * (25706 * η))) + (3 * (171326 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg11) (nb_mul c1 pg13)) (nb_mul c2 pg4)) (nb_mul c3 pg9)) (nb_mul c4 pg10)) (nb_mul c5 pg12)) (nb_mul c6 pg14)) (nb_mul c7 pg15)) (nb_mul c8 pg16)) (nb_mul c9 pg24)) (nb_mul c10 pg28))
    _ = 816748 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 34 by 442243 times `η` under the
stated assumptions. -/
private theorem step34 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg18 : ‖(x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) : ℂ)‖ ≤ (13203 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg27 : ‖(x1 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (83755 : ℝ) * η)
    : ‖(r*Complex.I*x3*y5 + x5*y4*(3 + r*Complex.I) + y1*y5^2*(1 - r*Complex.I) + y2*y3^2 + r*Complex.I*y2 - y3*y5 + y4^2*(2 + 2*r*Complex.I) : ℂ)‖ ≤ (442243 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      r*Complex.I*x3*y5 + x5*y4*(3 + r*Complex.I) + y1*y5^2*(1 - r*Complex.I) + y2*y3^2 + r*Complex.I*y2 - y3*y5 + y4^2*(2 + 2*r*Complex.I)
  let g2 : ℂ := x3*y3 - 1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause18 : ℂ :=
      x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause27 : ℂ := x1 + y2*(1/2 - r*Complex.I/2)
  have eid : target = (((((((((((r * Complex.I) * y2) * g2) + ((((-r) * Complex.I) * y3) * thresholdGoal)) + ((((-r) * Complex.I) * y3) * clause11)) + (((-2) * y3) * clause12)) + ((((y3 * (((-r) / 2) - ((3 * Complex.I) / 2))) - (3 / 2)) + ((r * Complex.I) / 2)) * clause13)) + ((((y3 * ((r / 2) + ((3 * Complex.I) / 2))) + (3 / 2)) - ((r * Complex.I) / 2)) * clause14)) + (((-1) + (r * Complex.I)) * clause18)) + ((2 * (y5 ^ 2)) * clause24)) + (((((y3 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2))) + (3 / 2)) - ((r * Complex.I) / 2)) * clause27)) := by
    dsimp only [target, g2, thresholdGoal, clause11, clause12, clause13, clause14, clause18,
        clause24, clause27]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((r * Complex.I) * y2) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((r * Complex.I) * y2) : ℂ)‖ ≤ ((2*1)*1) := (nb_mul (nb_mul hrN (by simp)) hNy2)
      _ ≤ 2 := by norm_num
  have c1 : ‖((((-r) * Complex.I) * y3) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-r) * Complex.I) * y3) : ℂ)‖ ≤ ((2*1)*1) := (nb_mul (nb_mul (nb_neg hrN) (by simp)) hNy3)
      _ ≤ 2 := by norm_num
  have c2 : ‖((((-r) * Complex.I) * y3) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-r) * Complex.I) * y3) : ℂ)‖ ≤ ((2*1)*1) := (nb_mul (nb_mul (nb_neg hrN) (by simp)) hNy3)
      _ ≤ 2 := by norm_num
  have c3 : ‖(((-2) * y3) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((-2) * y3) : ℂ)‖ ≤ (2*1) := (nb_mul (nb_neg (by norm_num)) hNy3)
      _ ≤ 2 := by norm_num
  have c4 : ‖((((y3 * (((-r) / 2) - ((3 * Complex.I) / 2))) - (3 / 2)) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((((y3 * (((-r) / 2) - ((3 * Complex.I) / 2))) - (3 / 2)) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (((1*((2/2)+((3*1)/2)))+(3/2))+((2*1)/2)) := (nb_add (nb_sub (nb_mul hNy3 (nb_sub (nb_div (nb_neg hrN) 2) (nb_div (nb_mul (by norm_num) (by simp)) 2))) (nb_div (by norm_num) 2)) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 5 := by norm_num
  have c5 : ‖((((y3 * ((r / 2) + ((3 * Complex.I) / 2))) + (3 / 2)) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((((y3 * ((r / 2) + ((3 * Complex.I) / 2))) + (3 / 2)) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (((1*((2/2)+((3*1)/2)))+(3/2))+((2*1)/2)) := (nb_sub (nb_add (nb_mul hNy3 (nb_add (nb_div hrN 2) (nb_div (nb_mul (by norm_num) (by simp)) 2))) (nb_div (by norm_num) 2)) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 5 := by norm_num
  have c6 : ‖(((-1) + (r * Complex.I)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖(((-1) + (r * Complex.I)) : ℂ)‖ ≤ (1+(2*1)) := (nb_add (nb_neg (by norm_num)) (nb_mul hrN (by simp)))
      _ ≤ 3 := by norm_num
  have c7 : ‖((2 * (y5 ^ 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((2 * (y5 ^ 2)) : ℂ)‖ ≤ (2*(1^2)) := (nb_mul (by norm_num) (nb_pow hNy5 2))
      _ ≤ 2 := by norm_num
  have c8 : ‖(((((y3 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2))) + (3 / 2)) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖(((((y3 ^ 2) * ((1 / 2) + ((r * Complex.I) / 2))) + (3 / 2)) - ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((((1^2)*((1/2)+((2*1)/2)))+(3/2))+((2*1)/2)) := (nb_sub (nb_add (nb_mul (nb_pow hNy3 2) (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))) (nb_div (by norm_num) 2)) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 4 := by norm_num
  change ‖target‖ ≤ 442243 * η
  rw [eid]
  calc
    _ ≤ (((((((((2 * (1 * η)) + (2 * (348 * η))) + (2 * (612 * η))) + (2 * (1200 * η))) + (5 * (588 * η))) + (5 * (1788 * η))) + (3 * (13203 * η))) + (2 * (25706 * η))) + (4 * (83755 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg2) (nb_mul c1 pg10)) (nb_mul c2 pg11)) (nb_mul c3 pg12)) (nb_mul c4 pg13)) (nb_mul c5 pg14)) (nb_mul c6 pg18)) (nb_mul c7 pg24)) (nb_mul c8 pg27))
    _ = 442243 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 35 by 663699 times `η` under the
stated assumptions. -/
private theorem step35 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx2 : ‖x2‖ ≤ 1)
    (hNx5 : ‖x5‖ ≤ 1)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg5 : ‖(x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5 : ℂ)‖ ≤ (6 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg17 : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η)
    (pg18 : ‖(x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) : ℂ)‖ ≤ (13203 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg26 : ‖(x3*y5*(1/2 - r*Complex.I/2) + x5*y4*(-1/2 - r*Complex.I/2) + y1^2 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (56632 : ℝ) * η)
    (pg27 : ‖(x1 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (83755 : ℝ) * η)
    (pg34 : ‖(r*Complex.I*x3*y5 + x5*y4*(3 + r*Complex.I) + y1*y5^2*(1 - r*Complex.I) + y2*y3^2 + r*Complex.I*y2 - y3*y5 + y4^2*(2 + 2*r*Complex.I) : ℂ)‖ ≤ (442243 : ℝ) * η)
    : ‖(x3*y5*(-1/2 + r*Complex.I/6) + 5*r*Complex.I*x5*y4/6 + y1*y5^2 + y2*(-3/4 + r*Complex.I/4) + y3*y5*(-1/4 - r*Complex.I/4) + y4^2*(-3/4 + 3*r*Complex.I/4) : ℂ)‖ ≤ (663699 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x3*y5*(-1/2 + r*Complex.I/6) + 5*r*Complex.I*x5*y4/6 + y1*y5^2 + y2*(-3/4 + r*Complex.I/4) + y3*y5*(-1/4 - r*Complex.I/4) + y4^2*(-3/4 + 3*r*Complex.I/4)
  let g2 : ℂ := x3*y3 - 1
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g5 : ℂ :=
      x1*y2 + x1*y3 + x1*y4 + x1*y5 + x1 + x2*y1 + x2*y3 + x2*y4 + x2*y5 + x2 + x3*y1 + x3*y2 + x3*y4 + x3*y5 + x3 + x4*y1 + x4*y2 + x4*y3 + x4*y5 + x4 + x5*y1 + x5*y2 + x5*y3 + x5*y4 + x5 + y1 + y2 + y3 + y4 + y5
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause17 : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  let clause18 : ℂ :=
      x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause26 : ℂ :=
      x3*y5*(1/2 - r*Complex.I/2) + x5*y4*(-1/2 - r*Complex.I/2) + y1^2 + y2*(1/2 - r*Complex.I/2)
  let clause27 : ℂ := x1 + y2*(1/2 - r*Complex.I/2)
  let tunableGoal : ℂ :=
      r*Complex.I*x3*y5 + x5*y4*(3 + r*Complex.I) + y1*y5^2*(1 - r*Complex.I) + y2*y3^2 + r*Complex.I*y2 - y3*y5 + y4^2*(2 + 2*r*Complex.I)
  have eid : target = (((((((((((((((((((((r * Complex.I) * y3) / 6) - ((r * Complex.I) / 6)) * g8) + (((((((-r) * Complex.I) * y1) / 6) - (1 / 4)) + ((r * Complex.I) / 4)) * clause14)) + (((((-r) * Complex.I) * y2) / 6) * g2)) + (((y1 * (((-1) / 4) + ((r * Complex.I) / 12))) + (y2 * (((-1) / 4) - ((r * Complex.I) / 12)))) * g3)) + (((x2 * (((-1) / 2) - ((r * Complex.I) / 6))) + (y1 * (((-1) / 4) + ((r * Complex.I) / 12)))) * g4)) + (((r * Complex.I) / 6) * g5)) + (((y4 * ((1 / 4) + ((r * Complex.I) / 12))) - ((r * Complex.I) / 6)) * g6)) + (((1 / 4) - ((r * Complex.I) / 12)) * g7)) + ((((((r * Complex.I) * y3) / 6) + (y4 * (((-1) / 4) - ((r * Complex.I) / 12)))) - ((r * Complex.I) / 6)) * g9)) + (((y4 * (((-1) / 4) + ((r * Complex.I) / 12))) + (y5 * (((-1) / 4) - ((r * Complex.I) / 12)))) * clause12)) + ((((-r) * Complex.I) / 3) * clause13)) + ((x5 * (((-1) / 4) + ((r * Complex.I) / 12))) * clause17)) + ((((-1) / 4) - ((r * Complex.I) / 4)) * clause18)) + ((((((r * Complex.I) * (y5 ^ 2)) / 3) - (1 / 4)) - ((r * Complex.I) / 12)) * clause24)) + (((1 / 4) + ((r * Complex.I) / 12)) * clause26)) + ((((((-r) * Complex.I) * (y3 ^ 2)) / 6) + ((r * Complex.I) / 6)) * clause27)) + (((1 / 4) + ((r * Complex.I) / 12)) * tunableGoal)) := by
    dsimp only [target, g2, g3, g4, g5, g6, g7, g8, g9, clause12, clause13, clause14, clause17,
        clause18, clause24, clause26, clause27, tunableGoal]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((((r * Complex.I) * y3) / 6) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((r * Complex.I) * y3) / 6) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((((2*1)*1)/6)+((2*1)/6)) := (nb_sub (nb_div (nb_mul (nb_mul hrN (by simp)) hNy3) 6) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 1 := by norm_num
  have c1 : ‖(((((((-r) * Complex.I) * y1) / 6) - (1 / 4)) + ((r * Complex.I) / 4)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((((((-r) * Complex.I) * y1) / 6) - (1 / 4)) + ((r * Complex.I) / 4)) : ℂ)‖ ≤ (((((2*1)*1)/6)+(1/4))+((2*1)/4)) := (nb_add (nb_sub (nb_div (nb_mul (nb_mul (nb_neg hrN) (by simp)) hNy1) 6) (nb_div (by norm_num) 4)) (nb_div (nb_mul hrN (by simp)) 4))
      _ ≤ 2 := by norm_num
  have c2 : ‖(((((-r) * Complex.I) * y2) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((-r) * Complex.I) * y2) / 6) : ℂ)‖ ≤ (((2*1)*1)/6) := (nb_div (nb_mul (nb_mul (nb_neg hrN) (by simp)) hNy2) 6)
      _ ≤ 1 := by norm_num
  have c3 : ‖(((y1 * (((-1) / 4) + ((r * Complex.I) / 12))) + (y2 * (((-1) / 4) - ((r * Complex.I) / 12)))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((y1 * (((-1) / 4) + ((r * Complex.I) / 12))) + (y2 * (((-1) / 4) - ((r * Complex.I) / 12)))) : ℂ)‖ ≤ ((1*((1/4)+((2*1)/12)))+(1*((1/4)+((2*1)/12)))) := (nb_add (nb_mul hNy1 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12))) (nb_mul hNy2 (nb_sub (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12))))
      _ ≤ 1 := by norm_num
  have c4 : ‖(((x2 * (((-1) / 2) - ((r * Complex.I) / 6))) + (y1 * (((-1) / 4) + ((r * Complex.I) / 12)))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((x2 * (((-1) / 2) - ((r * Complex.I) / 6))) + (y1 * (((-1) / 4) + ((r * Complex.I) / 12)))) : ℂ)‖ ≤ ((1*((1/2)+((2*1)/6)))+(1*((1/4)+((2*1)/12)))) := (nb_add (nb_mul hNx2 (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 6))) (nb_mul hNy1 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12))))
      _ ≤ 2 := by norm_num
  have c5 : ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((r * Complex.I) / 6) : ℂ)‖ ≤ ((2*1)/6) := (nb_div (nb_mul hrN (by simp)) 6)
      _ ≤ 1 := by norm_num
  have c6 : ‖(((y4 * ((1 / 4) + ((r * Complex.I) / 12))) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((y4 * ((1 / 4) + ((r * Complex.I) / 12))) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((1*((1/4)+((2*1)/12)))+((2*1)/6)) := (nb_sub (nb_mul hNy4 (nb_add (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 1 := by norm_num
  have c7 : ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c8 : ‖((((((r * Complex.I) * y3) / 6) + (y4 * (((-1) / 4) - ((r * Complex.I) / 12)))) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((((r * Complex.I) * y3) / 6) + (y4 * (((-1) / 4) - ((r * Complex.I) / 12)))) - ((r * Complex.I) / 6)) : ℂ)‖ ≤ (((((2*1)*1)/6)+(1*((1/4)+((2*1)/12))))+((2*1)/6)) := (nb_sub (nb_add (nb_div (nb_mul (nb_mul hrN (by simp)) hNy3) 6) (nb_mul hNy4 (nb_sub (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12)))) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 2 := by norm_num
  have c9 : ‖(((y4 * (((-1) / 4) + ((r * Complex.I) / 12))) + (y5 * (((-1) / 4) - ((r * Complex.I) / 12)))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((y4 * (((-1) / 4) + ((r * Complex.I) / 12))) + (y5 * (((-1) / 4) - ((r * Complex.I) / 12)))) : ℂ)‖ ≤ ((1*((1/4)+((2*1)/12)))+(1*((1/4)+((2*1)/12)))) := (nb_add (nb_mul hNy4 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12))) (nb_mul hNy5 (nb_sub (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12))))
      _ ≤ 1 := by norm_num
  have c10 : ‖((((-r) * Complex.I) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) * Complex.I) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul (nb_neg hrN) (by simp)) 3)
      _ ≤ 1 := by norm_num
  have c11 : ‖((x5 * (((-1) / 4) + ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((x5 * (((-1) / 4) + ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/12))) := (nb_mul hNx5 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12)))
      _ ≤ 1 := by norm_num
  have c12 : ‖((((-1) / 4) - ((r * Complex.I) / 4)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 4) - ((r * Complex.I) / 4)) : ℂ)‖ ≤ ((1/4)+((2*1)/4)) := (nb_sub (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 4))
      _ ≤ 1 := by norm_num
  have c13 : ‖((((((r * Complex.I) * (y5 ^ 2)) / 3) - (1 / 4)) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((((r * Complex.I) * (y5 ^ 2)) / 3) - (1 / 4)) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (((((2*1)*(1^2))/3)+(1/4))+((2*1)/12)) := (nb_sub (nb_sub (nb_div (nb_mul (nb_mul hrN (by simp)) (nb_pow hNy5 2)) 3) (nb_div (by norm_num) 4)) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 2 := by norm_num
  have c14 : ‖(((1 / 4) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_add (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c15 : ‖((((((-r) * Complex.I) * (y3 ^ 2)) / 6) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((((-r) * Complex.I) * (y3 ^ 2)) / 6) + ((r * Complex.I) / 6)) : ℂ)‖ ≤ ((((2*1)*(1^2))/6)+((2*1)/6)) := (nb_add (nb_div (nb_mul (nb_mul (nb_neg hrN) (by simp)) (nb_pow hNy3 2)) 6) (nb_div (nb_mul hrN (by simp)) 6))
      _ ≤ 1 := by norm_num
  have c16 : ‖(((1 / 4) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 4) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_add (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 663699 * η
  rw [eid]
  calc
    _ ≤ (((((((((((((((((1 * (72 * η)) + (2 * (1788 * η))) + (1 * (1 * η))) + (1 * (1 * η))) + (2 * (1 * η))) + (1 * (6 * η))) + (1 * (12 * η))) + (1 * (24 * η))) + (2 * (120 * η))) + (1 * (1200 * η))) + (1 * (588 * η))) + (1 * (10732 * η))) + (1 * (13203 * η))) + (2 * (25706 * η))) + (1 * (56632 * η))) + (1 * (83755 * η))) + (1 * (442243 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg8) (nb_mul c1 pg14)) (nb_mul c2 pg2)) (nb_mul c3 pg3)) (nb_mul c4 pg4)) (nb_mul c5 pg5)) (nb_mul c6 pg6)) (nb_mul c7 pg7)) (nb_mul c8 pg9)) (nb_mul c9 pg12)) (nb_mul c10 pg13)) (nb_mul c11 pg17)) (nb_mul c12 pg18)) (nb_mul c13 pg24)) (nb_mul c14 pg26)) (nb_mul c15 pg27)) (nb_mul c16 pg34))
    _ = 663699 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 36 by 891476 times `η` under the
stated assumptions. -/
private theorem step36 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg16 : ‖(x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I) : ℂ)‖ ≤ (19559 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg33 : ‖(-r*Complex.I*x3*y4 + x4*y5*(-9/2 - 3*r*Complex.I/2) + y1*y3^2 + y1*y4*y5*(2 - 2*r*Complex.I) - 2*r*Complex.I*y1 - 2*y3*y4 + y5^2*(-5/2 - 5*r*Complex.I/2) : ℂ)‖ ≤ (816748 : ℝ) * η)
    : ‖(x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4) : ℂ)‖ ≤ (891476 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4)
  let g2 : ℂ := x3*y3 - 1
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause16 : ℂ :=
      x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause33 : ℂ :=
      -r*Complex.I*x3*y4 + x4*y5*(-9/2 - 3*r*Complex.I/2) + y1*y3^2 + y1*y4*y5*(2 - 2*r*Complex.I) - 2*r*Complex.I*y1 - 2*y3*y4 + y5^2*(-5/2 - 5*r*Complex.I/2)
  have eid : target = (((((((((((y1 * ((1 / 4) - ((r * Complex.I) / 12))) * g2) + ((y3 * (((-1) / 4) + ((r * Complex.I) / 12))) * g6)) + (((((-r) * Complex.I) * y3) / 6) * g7)) + ((y3 * ((1 / 4) - ((r * Complex.I) / 12))) * g9)) + ((y3 * ((1 / 4) - ((r * Complex.I) / 12))) * clause11)) + ((y3 * ((1 / 6) - ((r * Complex.I) / 6))) * clause12)) + ((((y3 * (((-r) / 12) + (Complex.I / 4))) + (1 / 4)) + ((r * Complex.I) / 12)) * clause14)) + ((1 / 3) * clause16)) + ((((((y3 ^ 2) * ((1 / 12) - ((r * Complex.I) / 12))) + ((y4 * y5) * ((1 / 6) + ((r * Complex.I) / 6)))) - (1 / 4)) - ((r * Complex.I) / 12)) * clause24)) + (((1 / 12) + ((r * Complex.I) / 12)) * clause33)) := by
    dsimp only [target, g2, g6, g7, g9, clause11, clause12, clause14, clause16, clause24, clause33]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y1 * ((1 / 4) - ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y1 * ((1 / 4) - ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/12))) := (nb_mul hNy1 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12)))
      _ ≤ 1 := by norm_num
  have c1 : ‖((y3 * (((-1) / 4) + ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y3 * (((-1) / 4) + ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/12))) := (nb_mul hNy3 (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12)))
      _ ≤ 1 := by norm_num
  have c2 : ‖(((((-r) * Complex.I) * y3) / 6) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((-r) * Complex.I) * y3) / 6) : ℂ)‖ ≤ (((2*1)*1)/6) := (nb_div (nb_mul (nb_mul (nb_neg hrN) (by simp)) hNy3) 6)
      _ ≤ 1 := by norm_num
  have c3 : ‖((y3 * ((1 / 4) - ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y3 * ((1 / 4) - ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/12))) := (nb_mul hNy3 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12)))
      _ ≤ 1 := by norm_num
  have c4 : ‖((y3 * ((1 / 4) - ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y3 * ((1 / 4) - ((r * Complex.I) / 12))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/12))) := (nb_mul hNy3 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 12)))
      _ ≤ 1 := by norm_num
  have c5 : ‖((y3 * ((1 / 6) - ((r * Complex.I) / 6))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y3 * ((1 / 6) - ((r * Complex.I) / 6))) : ℂ)‖ ≤ (1*((1/6)+((2*1)/6))) := (nb_mul hNy3 (nb_sub (nb_div (by norm_num) 6) (nb_div (nb_mul hrN (by simp)) 6)))
      _ ≤ 1 := by norm_num
  have c6 : ‖((((y3 * (((-r) / 12) + (Complex.I / 4))) + (1 / 4)) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((y3 * (((-r) / 12) + (Complex.I / 4))) + (1 / 4)) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (((1*((2/12)+(1/4)))+(1/4))+((2*1)/12)) := (nb_add (nb_add (nb_mul hNy3 (nb_add (nb_div (nb_neg hrN) 12) (nb_div (by simp) 4))) (nb_div (by norm_num) 4)) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c7 : ‖((1 / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((1 / 3) : ℂ)‖ ≤ (1/3) := (nb_div (by norm_num) 3)
      _ ≤ 1 := by norm_num
  have c8 : ‖((((((y3 ^ 2) * ((1 / 12) - ((r * Complex.I) / 12))) + ((y4 * y5) * ((1 / 6) + ((r * Complex.I) / 6)))) - (1 / 4)) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((((y3 ^ 2) * ((1 / 12) - ((r * Complex.I) / 12))) + ((y4 * y5) * ((1 / 6) + ((r * Complex.I) / 6)))) - (1 / 4)) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (((((1^2)*((1/12)+((2*1)/12)))+((1*1)*((1/6)+((2*1)/6))))+(1/4))+((2*1)/12)) := (nb_sub (nb_sub (nb_add (nb_mul (nb_pow hNy3 2) (nb_sub (nb_div (by norm_num) 12) (nb_div (nb_mul hrN (by simp)) 12))) (nb_mul (nb_mul hNy4 hNy5) (nb_add (nb_div (by norm_num) 6) (nb_div (nb_mul hrN (by simp)) 6)))) (nb_div (by norm_num) 4)) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 2 := by norm_num
  have c9 : ‖(((1 / 12) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 12) + ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/12)+((2*1)/12)) := (nb_add (nb_div (by norm_num) 12) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 891476 * η
  rw [eid]
  calc
    _ ≤ ((((((((((1 * (1 * η)) + (1 * (12 * η))) + (1 * (24 * η))) + (1 * (120 * η))) + (1 * (612 * η))) + (1 * (1200 * η))) + (1 * (1788 * η))) + (1 * (19559 * η))) + (2 * (25706 * η))) + (1 * (816748 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg2) (nb_mul c1 pg6)) (nb_mul c2 pg7)) (nb_mul c3 pg9)) (nb_mul c4 pg11)) (nb_mul c5 pg12)) (nb_mul c6 pg14)) (nb_mul c7 pg16)) (nb_mul c8 pg24)) (nb_mul c9 pg33))
    _ = 891476 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 39 by 1713373 times `η` under the
stated assumptions. -/
private theorem step39 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx2 : ‖x2‖ ≤ 1)
    (hNx5 : ‖x5‖ ≤ 1)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg17 : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η)
    (pg18 : ‖(x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) : ℂ)‖ ≤ (13203 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg25 : ‖(y1*y2 + 1/2 + r*Complex.I/2 : ℂ)‖ ≤ (51414 : ℝ) * η)
    (pg26 : ‖(x3*y5*(1/2 - r*Complex.I/2) + x5*y4*(-1/2 - r*Complex.I/2) + y1^2 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (56632 : ℝ) * η)
    (pg28 : ‖(x3*y4*(1/2 - r*Complex.I/2) + x4*y5*(-1/2 - r*Complex.I/2) + y1*(1/2 - r*Complex.I/2) + y2^2 : ℂ)‖ ≤ (171326 : ℝ) * η)
    (pg35 : ‖(x3*y5*(-1/2 + r*Complex.I/6) + 5*r*Complex.I*x5*y4/6 + y1*y5^2 + y2*(-3/4 + r*Complex.I/4) + y3*y5*(-1/4 - r*Complex.I/4) + y4^2*(-3/4 + 3*r*Complex.I/4) : ℂ)‖ ≤ (663699 : ℝ) * η)
    : ‖(x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6) : ℂ)‖ ≤ (1713373 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6)
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause17 : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  let clause18 : ℂ :=
      x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause25 : ℂ := y1*y2 + 1/2 + r*Complex.I/2
  let clause26 : ℂ :=
      x3*y5*(1/2 - r*Complex.I/2) + x5*y4*(-1/2 - r*Complex.I/2) + y1^2 + y2*(1/2 - r*Complex.I/2)
  let clause28 : ℂ :=
      x3*y4*(1/2 - r*Complex.I/2) + x4*y5*(-1/2 - r*Complex.I/2) + y1*(1/2 - r*Complex.I/2) + y2^2
  let optGoal : ℂ :=
      x3*y5*(-1/2 + r*Complex.I/6) + 5*r*Complex.I*x5*y4/6 + y1*y5^2 + y2*(-3/4 + r*Complex.I/4) + y3*y5*(-1/4 - r*Complex.I/4) + y4^2*(-3/4 + 3*r*Complex.I/4)
  have eid : target = (((((((((((((((((-2) * y2) / 3) * clause25) + (((2 * y1) / 3) * clause28)) + (((y1 * (((-1) / 3) - ((r * Complex.I) / 3))) + (y2 * ((1 / 3) - ((r * Complex.I) / 3)))) * g3)) + ((((x2 * ((2 / 3) - (((2 * r) * Complex.I) / 3))) + (y1 * (((-1) / 3) - ((r * Complex.I) / 3)))) + (y2 * (((-1) / 3) - ((r * Complex.I) / 3)))) * g4)) + ((y4 * (((-1) / 3) + ((r * Complex.I) / 3))) * g6)) + ((y5 * ((1 / 3) + ((r * Complex.I) / 3))) * g7)) + ((y4 * ((1 / 3) - ((r * Complex.I) / 3))) * g9)) + (((y4 * (((-1) / 3) - ((r * Complex.I) / 3))) - ((((2 * r) * Complex.I) * y5) / 3)) * clause12)) + (((1 / 3) - ((r * Complex.I) / 3)) * clause14)) + ((x5 * (((-1) / 3) - ((r * Complex.I) / 3))) * clause17)) + (((1 / 3) - ((r * Complex.I) / 3)) * clause18)) + (((((y5 ^ 2) * ((-1) + ((r * Complex.I) / 3))) + (1 / 3)) - ((r * Complex.I) / 3)) * clause24)) + ((((-1) / 3) + ((r * Complex.I) / 3)) * clause26)) + (((((-2) * r) * Complex.I) / 3) * optGoal)) := by
    dsimp only [target, g3, g4, g6, g7, g9, clause12, clause14, clause17, clause18, clause24,
        clause25, clause26, clause28, optGoal]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-2) * y2) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-2) * y2) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul (nb_neg (by norm_num)) hNy2) 3)
      _ ≤ 1 := by norm_num
  have c1 : ‖(((2 * y1) / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((2 * y1) / 3) : ℂ)‖ ≤ ((2*1)/3) := (nb_div (nb_mul (by norm_num) hNy1) 3)
      _ ≤ 1 := by norm_num
  have c2 : ‖(((y1 * (((-1) / 3) - ((r * Complex.I) / 3))) + (y2 * ((1 / 3) - ((r * Complex.I) / 3)))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((y1 * (((-1) / 3) - ((r * Complex.I) / 3))) + (y2 * ((1 / 3) - ((r * Complex.I) / 3)))) : ℂ)‖ ≤ ((1*((1/3)+((2*1)/3)))+(1*((1/3)+((2*1)/3)))) := (nb_add (nb_mul hNy1 (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul hrN (by simp)) 3))) (nb_mul hNy2 (nb_sub (nb_div (by norm_num) 3) (nb_div (nb_mul hrN (by simp)) 3))))
      _ ≤ 2 := by norm_num
  have c3 : ‖((((x2 * ((2 / 3) - (((2 * r) * Complex.I) / 3))) + (y1 * (((-1) / 3) - ((r * Complex.I) / 3)))) + (y2 * (((-1) / 3) - ((r * Complex.I) / 3)))) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((((x2 * ((2 / 3) - (((2 * r) * Complex.I) / 3))) + (y1 * (((-1) / 3) - ((r * Complex.I) / 3)))) + (y2 * (((-1) / 3) - ((r * Complex.I) / 3)))) : ℂ)‖ ≤ (((1*((2/3)+(((2*2)*1)/3)))+(1*((1/3)+((2*1)/3))))+(1*((1/3)+((2*1)/3)))) := (nb_add (nb_add (nb_mul hNx2 (nb_sub (nb_div (by norm_num) 3) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3))) (nb_mul hNy1 (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul hrN (by simp)) 3)))) (nb_mul hNy2 (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul hrN (by simp)) 3))))
      _ ≤ 4 := by norm_num
  have c4 : ‖((y4 * (((-1) / 3) + ((r * Complex.I) / 3))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y4 * (((-1) / 3) + ((r * Complex.I) / 3))) : ℂ)‖ ≤ (1*((1/3)+((2*1)/3))) := (nb_mul hNy4 (nb_add (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul hrN (by simp)) 3)))
      _ ≤ 1 := by norm_num
  have c5 : ‖((y5 * ((1 / 3) + ((r * Complex.I) / 3))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((1 / 3) + ((r * Complex.I) / 3))) : ℂ)‖ ≤ (1*((1/3)+((2*1)/3))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 3) (nb_div (nb_mul hrN (by simp)) 3)))
      _ ≤ 1 := by norm_num
  have c6 : ‖((y4 * ((1 / 3) - ((r * Complex.I) / 3))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y4 * ((1 / 3) - ((r * Complex.I) / 3))) : ℂ)‖ ≤ (1*((1/3)+((2*1)/3))) := (nb_mul hNy4 (nb_sub (nb_div (by norm_num) 3) (nb_div (nb_mul hrN (by simp)) 3)))
      _ ≤ 1 := by norm_num
  have c7 : ‖(((y4 * (((-1) / 3) - ((r * Complex.I) / 3))) - ((((2 * r) * Complex.I) * y5) / 3)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖(((y4 * (((-1) / 3) - ((r * Complex.I) / 3))) - ((((2 * r) * Complex.I) * y5) / 3)) : ℂ)‖ ≤ ((1*((1/3)+((2*1)/3)))+((((2*2)*1)*1)/3)) := (nb_sub (nb_mul hNy4 (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul hrN (by simp)) 3))) (nb_div (nb_mul (nb_mul (nb_mul (by norm_num) hrN) (by simp)) hNy5) 3))
      _ ≤ 3 := by norm_num
  have c8 : ‖(((1 / 3) - ((r * Complex.I) / 3)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 3) - ((r * Complex.I) / 3)) : ℂ)‖ ≤ ((1/3)+((2*1)/3)) := (nb_sub (nb_div (by norm_num) 3) (nb_div (nb_mul hrN (by simp)) 3))
      _ ≤ 1 := by norm_num
  have c9 : ‖((x5 * (((-1) / 3) - ((r * Complex.I) / 3))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((x5 * (((-1) / 3) - ((r * Complex.I) / 3))) : ℂ)‖ ≤ (1*((1/3)+((2*1)/3))) := (nb_mul hNx5 (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul hrN (by simp)) 3)))
      _ ≤ 1 := by norm_num
  have c10 : ‖(((1 / 3) - ((r * Complex.I) / 3)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 3) - ((r * Complex.I) / 3)) : ℂ)‖ ≤ ((1/3)+((2*1)/3)) := (nb_sub (nb_div (by norm_num) 3) (nb_div (nb_mul hrN (by simp)) 3))
      _ ≤ 1 := by norm_num
  have c11 : ‖(((((y5 ^ 2) * ((-1) + ((r * Complex.I) / 3))) + (1 / 3)) - ((r * Complex.I) / 3)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖(((((y5 ^ 2) * ((-1) + ((r * Complex.I) / 3))) + (1 / 3)) - ((r * Complex.I) / 3)) : ℂ)‖ ≤ ((((1^2)*(1+((2*1)/3)))+(1/3))+((2*1)/3)) := (nb_sub (nb_add (nb_mul (nb_pow hNy5 2) (nb_add (nb_neg (by norm_num)) (nb_div (nb_mul hrN (by simp)) 3))) (nb_div (by norm_num) 3)) (nb_div (nb_mul hrN (by simp)) 3))
      _ ≤ 3 := by norm_num
  have c12 : ‖((((-1) / 3) + ((r * Complex.I) / 3)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 3) + ((r * Complex.I) / 3)) : ℂ)‖ ≤ ((1/3)+((2*1)/3)) := (nb_add (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul hrN (by simp)) 3))
      _ ≤ 1 := by norm_num
  have c13 : ‖(((((-2) * r) * Complex.I) / 3) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((((-2) * r) * Complex.I) / 3) : ℂ)‖ ≤ (((2*2)*1)/3) := (nb_div (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) (by simp)) 3)
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 1713373 * η
  rw [eid]
  calc
    _ ≤ ((((((((((((((1 * (51414 * η)) + (1 * (171326 * η))) + (2 * (1 * η))) + (4 * (1 * η))) + (1 * (12 * η))) + (1 * (24 * η))) + (1 * (120 * η))) + (3 * (1200 * η))) + (1 * (1788 * η))) + (1 * (10732 * η))) + (1 * (13203 * η))) + (3 * (25706 * η))) + (1 * (56632 * η))) + (2 * (663699 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg25) (nb_mul c1 pg28)) (nb_mul c2 pg3)) (nb_mul c3 pg4)) (nb_mul c4 pg6)) (nb_mul c5 pg7)) (nb_mul c6 pg9)) (nb_mul c7 pg12)) (nb_mul c8 pg14)) (nb_mul c9 pg17)) (nb_mul c10 pg18)) (nb_mul c11 pg24)) (nb_mul c12 pg26)) (nb_mul c13 pg35))
    _ = 1713373 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 41 by 5235046 times `η` under the
stated assumptions. -/
private theorem step41 (r x2 x3 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg22 : ‖(x3*y4^2 + y1*y4 + y2*y3*(-1/2 + r*Complex.I/2) : ℂ)‖ ≤ (6220 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg39 : ‖(x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6) : ℂ)‖ ≤ (1713373 : ℝ) * η)
    : ‖(-r*Complex.I*y1*y4 + y2*y3*(3 + r*Complex.I) + y3^2*y5*(1/2 - r*Complex.I/2) + y3*y4^2 + y5*(3 + r*Complex.I) : ℂ)‖ ≤ (5235046 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      -r*Complex.I*y1*y4 + y2*y3*(3 + r*Complex.I) + y3^2*y5*(1/2 - r*Complex.I/2) + y3*y4^2 + y5*(3 + r*Complex.I)
  let g2 : ℂ := x3*y3 - 1
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause22 : ℂ := x3*y4^2 + y1*y4 + y2*y3*(-1/2 + r*Complex.I/2)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause39 : ℂ :=
      x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6)
  have eid : target = ((((((y4 * (((-3) / 2) + ((r * Complex.I) / 2))) * clause14) + ((y3 * ((3 / 2) - ((r * Complex.I) / 2))) * clause39)) + ((y5 * ((-3) - (r * Complex.I))) * g2)) + (((-r) * Complex.I) * clause22)) + ((y4 * ((3 / 2) - ((r * Complex.I) / 2))) * clause24)) := by
    dsimp only [target, g2, clause14, clause22, clause24, clause39]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y4 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y4 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy4 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c1 : ‖((y3 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y3 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy3 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c2 : ‖((y5 * ((-3) - (r * Complex.I))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((y5 * ((-3) - (r * Complex.I))) : ℂ)‖ ≤ (1*(3+(2*1))) := (nb_mul hNy5 (nb_sub (nb_neg (by norm_num)) (nb_mul hrN (by simp))))
      _ ≤ 5 := by norm_num
  have c3 : ‖(((-r) * Complex.I) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((-r) * Complex.I) : ℂ)‖ ≤ (2*1) := (nb_mul (nb_neg hrN) (by simp))
      _ ≤ 2 := by norm_num
  have c4 : ‖((y4 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y4 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy4 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  change ‖target‖ ≤ 5235046 * η
  rw [eid]
  calc
    _ ≤ (((((3 * (1788 * η)) + (3 * (1713373 * η))) + (5 * (1 * η))) + (2 * (6220 * η))) + (3 * (25706 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg14) (nb_mul c1 pg39)) (nb_mul c2 pg2)) (nb_mul c3 pg22)) (nb_mul c4 pg24))
    _ = 5235046 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 42 by 4015510 times `η` under the
stated assumptions. -/
private theorem step42 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx2 : ‖x2‖ ≤ 1)
    (hNx5 : ‖x5‖ ≤ 1)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    (pg16 : ‖(x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I) : ℂ)‖ ≤ (19559 : ℝ) * η)
    (pg17 : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg28 : ‖(x3*y4*(1/2 - r*Complex.I/2) + x4*y5*(-1/2 - r*Complex.I/2) + y1*(1/2 - r*Complex.I/2) + y2^2 : ℂ)‖ ≤ (171326 : ℝ) * η)
    (pg29 : ‖(x4*y5*(-3/2 + r*Complex.I/2) + y1*y4*y5*(-1/2 - r*Complex.I/2) + y1*(-3/2 - r*Complex.I/2) + y2*y3*y5 - 2*y5^2 : ℂ)‖ ≤ (258040 : ℝ) * η)
    (pg36 : ‖(x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4) : ℂ)‖ ≤ (891476 : ℝ) * η)
    (pg39 : ‖(x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6) : ℂ)‖ ≤ (1713373 : ℝ) * η)
    : ‖(x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24) : ℂ)‖ ≤ (4015510 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24)
  let g4 : ℂ := x5*y5 - 1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let clause16 : ℂ :=
      x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I)
  let clause17 : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause28 : ℂ :=
      x3*y4*(1/2 - r*Complex.I/2) + x4*y5*(-1/2 - r*Complex.I/2) + y1*(1/2 - r*Complex.I/2) + y2^2
  let clause29 : ℂ :=
      x4*y5*(-3/2 + r*Complex.I/2) + y1*y4*y5*(-1/2 - r*Complex.I/2) + y1*(-3/2 - r*Complex.I/2) + y2*y3*y5 - 2*y5^2
  let clause36 : ℂ :=
      x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4)
  let clause39 : ℂ :=
      x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6)
  have eid : target = ((((((((((((((((x5 / 4) + (y4 * ((1 / 8) + ((r * Complex.I) / 24)))) * clause17) + (((-y2) / 4) * clause39)) + ((((x2 * ((1 / 4) + ((r * Complex.I) / 4))) + (y1 / 4)) + (y3 * (((-r) / 4) - (Complex.I / 4)))) * g4)) + ((y5 * ((1 / 4) + ((r * Complex.I) / 4))) * thresholdGoal)) + ((y5 * ((1 / 4) + ((r * Complex.I) / 4))) * clause11)) + ((y5 * ((1 / 2) - ((r * Complex.I) / 6))) * clause12)) + ((y5 * ((r / 4) + (Complex.I / 4))) * clause13)) + (((1 / 8) + ((r * Complex.I) / 8)) * clause14)) + ((((-r) / 4) + (Complex.I / 4)) * walkGoal)) + ((((-1) / 4) - ((r * Complex.I) / 12)) * clause16)) + ((((((((-r) * Complex.I) * y4) * y5) / 3) + (1 / 8)) + ((r * Complex.I) / 8)) * clause24)) + (((1 / 8) + ((r * Complex.I) / 8)) * clause28)) + (((1 / 8) - ((r * Complex.I) / 24)) * clause29)) + (((3 / 4) + ((r * Complex.I) / 4)) * clause36)) := by
    dsimp only [target, g4, thresholdGoal, clause11, clause12, clause13, clause14, walkGoal,
        clause16, clause17, clause24, clause28, clause29, clause36, clause39]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((x5 / 4) + (y4 * ((1 / 8) + ((r * Complex.I) / 24)))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((x5 / 4) + (y4 * ((1 / 8) + ((r * Complex.I) / 24)))) : ℂ)‖ ≤ ((1/4)+(1*((1/8)+((2*1)/24)))) := (nb_add (nb_div hNx5 4) (nb_mul hNy4 (nb_add (nb_div (by norm_num) 8) (nb_div (nb_mul hrN (by simp)) 24))))
      _ ≤ 1 := by norm_num
  have c1 : ‖(((-y2) / 4) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-y2) / 4) : ℂ)‖ ≤ (1/4) := (nb_div (nb_neg hNy2) 4)
      _ ≤ 1 := by norm_num
  have c2 : ‖((((x2 * ((1 / 4) + ((r * Complex.I) / 4))) + (y1 / 4)) + (y3 * (((-r) / 4) - (Complex.I / 4)))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((x2 * ((1 / 4) + ((r * Complex.I) / 4))) + (y1 / 4)) + (y3 * (((-r) / 4) - (Complex.I / 4)))) : ℂ)‖ ≤ (((1*((1/4)+((2*1)/4)))+(1/4))+(1*((2/4)+(1/4)))) := (nb_add (nb_add (nb_mul hNx2 (nb_add (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4))) (nb_div hNy1 4)) (nb_mul hNy3 (nb_sub (nb_div (nb_neg hrN) 4) (nb_div (by simp) 4))))
      _ ≤ 2 := by norm_num
  have c3 : ‖((y5 * ((1 / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((1 / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/4))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 1 := by norm_num
  have c4 : ‖((y5 * ((1 / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((1 / 4) + ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((1/4)+((2*1)/4))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 1 := by norm_num
  have c5 : ‖((y5 * ((1 / 2) - ((r * Complex.I) / 6))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((1 / 2) - ((r * Complex.I) / 6))) : ℂ)‖ ≤ (1*((1/2)+((2*1)/6))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 6)))
      _ ≤ 1 := by norm_num
  have c6 : ‖((y5 * ((r / 4) + (Complex.I / 4))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((r / 4) + (Complex.I / 4))) : ℂ)‖ ≤ (1*((2/4)+(1/4))) := (nb_mul hNy5 (nb_add (nb_div hrN 4) (nb_div (by simp) 4)))
      _ ≤ 1 := by norm_num
  have c7 : ‖(((1 / 8) + ((r * Complex.I) / 8)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 8) + ((r * Complex.I) / 8)) : ℂ)‖ ≤ ((1/8)+((2*1)/8)) := (nb_add (nb_div (by norm_num) 8) (nb_div (nb_mul hrN (by simp)) 8))
      _ ≤ 1 := by norm_num
  have c8 : ‖((((-r) / 4) + (Complex.I / 4)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 4) + (Complex.I / 4)) : ℂ)‖ ≤ ((2/4)+(1/4)) := (nb_add (nb_div (nb_neg hrN) 4) (nb_div (by simp) 4))
      _ ≤ 1 := by norm_num
  have c9 : ‖((((-1) / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-1) / 4) - ((r * Complex.I) / 12)) : ℂ)‖ ≤ ((1/4)+((2*1)/12)) := (nb_sub (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 12))
      _ ≤ 1 := by norm_num
  have c10 : ‖((((((((-r) * Complex.I) * y4) * y5) / 3) + (1 / 8)) + ((r * Complex.I) / 8)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((((((-r) * Complex.I) * y4) * y5) / 3) + (1 / 8)) + ((r * Complex.I) / 8)) : ℂ)‖ ≤ ((((((2*1)*1)*1)/3)+(1/8))+((2*1)/8)) := (nb_add (nb_add (nb_div (nb_mul (nb_mul (nb_mul (nb_neg hrN) (by simp)) hNy4) hNy5) 3) (nb_div (by norm_num) 8)) (nb_div (nb_mul hrN (by simp)) 8))
      _ ≤ 2 := by norm_num
  have c11 : ‖(((1 / 8) + ((r * Complex.I) / 8)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 8) + ((r * Complex.I) / 8)) : ℂ)‖ ≤ ((1/8)+((2*1)/8)) := (nb_add (nb_div (by norm_num) 8) (nb_div (nb_mul hrN (by simp)) 8))
      _ ≤ 1 := by norm_num
  have c12 : ‖(((1 / 8) - ((r * Complex.I) / 24)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 8) - ((r * Complex.I) / 24)) : ℂ)‖ ≤ ((1/8)+((2*1)/24)) := (nb_sub (nb_div (by norm_num) 8) (nb_div (nb_mul hrN (by simp)) 24))
      _ ≤ 1 := by norm_num
  have c13 : ‖(((3 / 4) + ((r * Complex.I) / 4)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((3 / 4) + ((r * Complex.I) / 4)) : ℂ)‖ ≤ ((3/4)+((2*1)/4)) := (nb_add (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 4015510 * η
  rw [eid]
  calc
    _ ≤ ((((((((((((((1 * (10732 * η)) + (1 * (1713373 * η))) + (2 * (1 * η))) + (1 * (348 * η))) + (1 * (612 * η))) + (1 * (1200 * η))) + (1 * (588 * η))) + (1 * (1788 * η))) + (1 * (3578 * η))) + (1 * (19559 * η))) + (2 * (25706 * η))) + (1 * (171326 * η))) + (1 * (258040 * η))) + (2 * (891476 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg17) (nb_mul c1 pg39)) (nb_mul c2 pg4)) (nb_mul c3 pg10)) (nb_mul c4 pg11)) (nb_mul c5 pg12)) (nb_mul c6 pg13)) (nb_mul c7 pg14)) (nb_mul c8 pg15)) (nb_mul c9 pg16)) (nb_mul c10 pg24)) (nb_mul c11 pg28)) (nb_mul c12 pg29)) (nb_mul c13 pg36))
    _ = 4015510 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 43 by 8115294 times `η` under the
stated assumptions. -/
private theorem step43 (r x2 x3 x4 y1 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg42 : ‖(x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24) : ℂ)‖ ≤ (4015510 : ℝ) * η)
    : ‖(x4*y5^2*(3/8 + r*Complex.I/8) + r*Complex.I*y1*y5/2 + y3*y4*y5 + y3*(3/2 - r*Complex.I/2) + y5^3*(1/8 + r*Complex.I/8) : ℂ)‖ ≤ (8115294 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x4*y5^2*(3/8 + r*Complex.I/8) + r*Complex.I*y1*y5/2 + y3*y4*y5 + y3*(3/2 - r*Complex.I/2) + y5^3*(1/8 + r*Complex.I/8)
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause42 : ℂ :=
      x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24)
  have eid : target = (((((-r) * Complex.I) * walkGoal) + (((r * Complex.I) * y5) * clause42)) + ((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) * clause24)) := by
    dsimp only [target, walkGoal, clause24, clause42]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((-r) * Complex.I) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((-r) * Complex.I) : ℂ)‖ ≤ (2*1) := (nb_mul (nb_neg hrN) (by simp))
      _ ≤ 2 := by norm_num
  have c1 : ‖(((r * Complex.I) * y5) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((r * Complex.I) * y5) : ℂ)‖ ≤ ((2*1)*1) := (nb_mul (nb_mul hrN (by simp)) hNy5)
      _ ≤ 2 := by norm_num
  have c2 : ‖((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (((-3) / 2) + ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  change ‖target‖ ≤ 8115294 * η
  rw [eid]
  calc
    _ ≤ (((2 * (3578 * η)) + (2 * (4015510 * η))) + (3 * (25706 * η))) := (nb_add (nb_add (nb_mul c0 pg15) (nb_mul c1 pg42)) (nb_mul c2 pg24))
    _ = 8115294 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 44 by 22535283 times `η` under the
stated assumptions. -/
private theorem step44 (r x3 x4 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg22 : ‖(x3*y4^2 + y1*y4 + y2*y3*(-1/2 + r*Complex.I/2) : ℂ)‖ ≤ (6220 : ℝ) * η)
    (pg41 : ‖(-r*Complex.I*y1*y4 + y2*y3*(3 + r*Complex.I) + y3^2*y5*(1/2 - r*Complex.I/2) + y3*y4^2 + y5*(3 + r*Complex.I) : ℂ)‖ ≤ (5235046 : ℝ) * η)
    (pg42 : ‖(x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24) : ℂ)‖ ≤ (4015510 : ℝ) * η)
    : ‖(y1*y4*(3/4 - r*Complex.I/4) + r*Complex.I*y2*y3 + y3^2*y5 + y4*y5^2*(1/8 - r*Complex.I/8) + 7*r*Complex.I*y5/4 : ℂ)‖ ≤ (22535283 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      y1*y4*(3/4 - r*Complex.I/4) + r*Complex.I*y2*y3 + y3^2*y5 + y4*y5^2*(1/8 - r*Complex.I/8) + 7*r*Complex.I*y5/4
  let g3 : ℂ := x4*y4 - 1
  let clause22 : ℂ := x3*y4^2 + y1*y4 + y2*y3*(-1/2 + r*Complex.I/2)
  let clause41 : ℂ :=
      -r*Complex.I*y1*y4 + y2*y3*(3 + r*Complex.I) + y3^2*y5*(1/2 - r*Complex.I/2) + y3*y4^2 + y5*(3 + r*Complex.I)
  let clause42 : ℂ :=
      x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24)
  have eid : target = (((((((-3) / 2) + ((r * Complex.I) / 2)) * clause22) + ((y4 * ((3 / 2) - ((r * Complex.I) / 2))) * clause42)) + ((((r * Complex.I) * y5) / 4) * g3)) + (((1 / 2) + ((r * Complex.I) / 2)) * clause41)) := by
    dsimp only [target, g3, clause22, clause41, clause42]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-3) / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((-3) / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((3/2)+((2*1)/2)) := (nb_add (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 3 := by norm_num
  have c1 : ‖((y4 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y4 * ((3 / 2) - ((r * Complex.I) / 2))) : ℂ)‖ ≤ (1*((3/2)+((2*1)/2))) := (nb_mul hNy4 (nb_sub (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2)))
      _ ≤ 3 := by norm_num
  have c2 : ‖((((r * Complex.I) * y5) / 4) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((r * Complex.I) * y5) / 4) : ℂ)‖ ≤ (((2*1)*1)/4) := (nb_div (nb_mul (nb_mul hrN (by simp)) hNy5) 4)
      _ ≤ 1 := by norm_num
  have c3 : ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((1 / 2) + ((r * Complex.I) / 2)) : ℂ)‖ ≤ ((1/2)+((2*1)/2)) := (nb_add (nb_div (by norm_num) 2) (nb_div (nb_mul hrN (by simp)) 2))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 22535283 * η
  rw [eid]
  calc
    _ ≤ ((((3 * (6220 * η)) + (3 * (4015510 * η))) + (1 * (1 * η))) + (2 * (5235046 * η))) := (nb_add (nb_add (nb_add (nb_mul c0 pg22) (nb_mul c1 pg42)) (nb_mul c2 pg3)) (nb_mul c3 pg41))
    _ = 22535283 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 46 by 8577774 times `η` under the
stated assumptions. -/
private theorem step46 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx3 : ‖x3‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    (pg17 : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η)
    (pg18 : ‖(x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) : ℂ)‖ ≤ (13203 : ℝ) * η)
    (pg20 : ‖(-x1*y5^2 + x2*x3*y5*(3/2 + r*Complex.I/2) + x2*y3*y5*(-1/2 + r*Complex.I/2) + x2*y4^2 + y3^2*(-1/4 + r*Complex.I/4) + 3/4 + r*Complex.I/4 : ℂ)‖ ≤ (57192 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg25 : ‖(y1*y2 + 1/2 + r*Complex.I/2 : ℂ)‖ ≤ (51414 : ℝ) * η)
    (pg27 : ‖(x1 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (83755 : ℝ) * η)
    (pg42 : ‖(x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24) : ℂ)‖ ≤ (4015510 : ℝ) * η)
    : ‖(y1*y3*y5 + y2*y5^2*(4/7 + 4*r*Complex.I/7) + y3^2*(-2/7 - 2*r*Complex.I/7) + 6*y4*y5/7 + 3/2 - r*Complex.I/2 : ℂ)‖ ≤ (8577774 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      y1*y3*y5 + y2*y5^2*(4/7 + 4*r*Complex.I/7) + y3^2*(-2/7 - 2*r*Complex.I/7) + 6*y4*y5/7 + 3/2 - r*Complex.I/2
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let clause17 : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  let clause18 : ℂ :=
      x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I)
  let clause20 : ℂ :=
      -x1*y5^2 + x2*x3*y5*(3/2 + r*Complex.I/2) + x2*y3*y5*(-1/2 + r*Complex.I/2) + x2*y4^2 + y3^2*(-1/4 + r*Complex.I/4) + 3/4 + r*Complex.I/4
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause25 : ℂ := y1*y2 + 1/2 + r*Complex.I/2
  let clause27 : ℂ := x1 + y2*(1/2 - r*Complex.I/2)
  let clause42 : ℂ :=
      x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24)
  have eid : target = (((((((((((((((((((((4 * r) * Complex.I) * y4) / 7) * thresholdGoal) + ((((((-4) * r) * Complex.I) * y2) / 7) * clause42)) + ((((((((4 * r) * Complex.I) * y2) / 7) + (y3 * (((2 * r) / 7) + ((6 * Complex.I) / 7)))) + (6 / 7)) - (((2 * r) * Complex.I) / 7)) * g3)) + ((((y3 * ((((-5) * r) / 7) - ((12 * Complex.I) / 7))) - (27 / 14)) + (((9 * r) * Complex.I) / 14)) * g4)) + ((((((-8) * r) * Complex.I) * y5) / 7) * g6)) + ((y5 * ((12 / 7) + (((4 * r) * Complex.I) / 7))) * g7)) + (((((8 * r) * Complex.I) * y5) / 7) * g9)) + ((y5 * ((3 / 14) + (((17 * r) * Complex.I) / 14))) * clause11)) + ((((((y3 * (((-2) / 7) - (((2 * r) * Complex.I) / 7))) + (y4 * ((4 / 7) - (((4 * r) * Complex.I) / 7)))) + (y5 * (2 + (((8 * r) * Complex.I) / 7)))) + ((2 * r) / 7)) + ((6 * Complex.I) / 7)) * clause12)) + ((y4 * (((2 * r) / 7) + ((6 * Complex.I) / 7))) * clause14)) + (((((-9) * r) / 14) + ((3 * Complex.I) / 14)) * walkGoal)) + ((((4 * y3) / 7) + ((4 * r) / 7)) * clause17)) + ((((-2) / 7) + (((2 * r) * Complex.I) / 7)) * clause18)) + (((4 / 7) - (((4 * r) * Complex.I) / 7)) * clause20)) + ((((x3 * y5) * (((-12) / 7) + (((4 * r) * Complex.I) / 7))) + ((y3 * y5) * ((11 / 14) + (((11 * r) * Complex.I) / 14)))) * clause24)) + ((((2 * r) * Complex.I) / 7) * clause25)) + (((y5 ^ 2) * (((-9) / 14) + (((9 * r) * Complex.I) / 14))) * clause27)) := by
    dsimp only [target, g3, g4, g6, g7, g9, thresholdGoal, clause11, clause12, clause14, walkGoal,
        clause17, clause18, clause20, clause24, clause25, clause27, clause42]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((((4 * r) * Complex.I) * y4) / 7) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((((4 * r) * Complex.I) * y4) / 7) : ℂ)‖ ≤ ((((4*2)*1)*1)/7) := (nb_div (nb_mul (nb_mul (nb_mul (by norm_num) hrN) (by simp)) hNy4) 7)
      _ ≤ 2 := by norm_num
  have c1 : ‖((((((-4) * r) * Complex.I) * y2) / 7) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((((-4) * r) * Complex.I) * y2) / 7) : ℂ)‖ ≤ ((((4*2)*1)*1)/7) := (nb_div (nb_mul (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) (by simp)) hNy2) 7)
      _ ≤ 2 := by norm_num
  have c2 : ‖((((((((4 * r) * Complex.I) * y2) / 7) + (y3 * (((2 * r) / 7) + ((6 * Complex.I) / 7)))) + (6 / 7)) - (((2 * r) * Complex.I) / 7)) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((((((((4 * r) * Complex.I) * y2) / 7) + (y3 * (((2 * r) / 7) + ((6 * Complex.I) / 7)))) + (6 / 7)) - (((2 * r) * Complex.I) / 7)) : ℂ)‖ ≤ (((((((4*2)*1)*1)/7)+(1*(((2*2)/7)+((6*1)/7))))+(6/7))+(((2*2)*1)/7)) := (nb_sub (nb_add (nb_add (nb_div (nb_mul (nb_mul (nb_mul (by norm_num) hrN) (by simp)) hNy2) 7) (nb_mul hNy3 (nb_add (nb_div (nb_mul (by norm_num) hrN) 7) (nb_div (nb_mul (by norm_num) (by simp)) 7)))) (nb_div (by norm_num) 7)) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7))
      _ ≤ 4 := by norm_num
  have c3 : ‖((((y3 * ((((-5) * r) / 7) - ((12 * Complex.I) / 7))) - (27 / 14)) + (((9 * r) * Complex.I) / 14)) : ℂ)‖ ≤ (7 : ℝ) := by
    calc
      ‖((((y3 * ((((-5) * r) / 7) - ((12 * Complex.I) / 7))) - (27 / 14)) + (((9 * r) * Complex.I) / 14)) : ℂ)‖ ≤ (((1*(((5*2)/7)+((12*1)/7)))+(27/14))+(((9*2)*1)/14)) := (nb_add (nb_sub (nb_mul hNy3 (nb_sub (nb_div (nb_mul (nb_neg (by norm_num)) hrN) 7) (nb_div (nb_mul (by norm_num) (by simp)) 7))) (nb_div (by norm_num) 14)) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 14))
      _ ≤ 7 := by norm_num
  have c4 : ‖((((((-8) * r) * Complex.I) * y5) / 7) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((((((-8) * r) * Complex.I) * y5) / 7) : ℂ)‖ ≤ ((((8*2)*1)*1)/7) := (nb_div (nb_mul (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) (by simp)) hNy5) 7)
      _ ≤ 3 := by norm_num
  have c5 : ‖((y5 * ((12 / 7) + (((4 * r) * Complex.I) / 7))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * ((12 / 7) + (((4 * r) * Complex.I) / 7))) : ℂ)‖ ≤ (1*((12/7)+(((4*2)*1)/7))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 7) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7)))
      _ ≤ 3 := by norm_num
  have c6 : ‖(((((8 * r) * Complex.I) * y5) / 7) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖(((((8 * r) * Complex.I) * y5) / 7) : ℂ)‖ ≤ ((((8*2)*1)*1)/7) := (nb_div (nb_mul (nb_mul (nb_mul (by norm_num) hrN) (by simp)) hNy5) 7)
      _ ≤ 3 := by norm_num
  have c7 : ‖((y5 * ((3 / 14) + (((17 * r) * Complex.I) / 14))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * ((3 / 14) + (((17 * r) * Complex.I) / 14))) : ℂ)‖ ≤ (1*((3/14)+(((17*2)*1)/14))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 14) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 14)))
      _ ≤ 3 := by norm_num
  have c8 : ‖((((((y3 * (((-2) / 7) - (((2 * r) * Complex.I) / 7))) + (y4 * ((4 / 7) - (((4 * r) * Complex.I) / 7)))) + (y5 * (2 + (((8 * r) * Complex.I) / 7)))) + ((2 * r) / 7)) + ((6 * Complex.I) / 7)) : ℂ)‖ ≤ (9 : ℝ) := by
    calc
      ‖((((((y3 * (((-2) / 7) - (((2 * r) * Complex.I) / 7))) + (y4 * ((4 / 7) - (((4 * r) * Complex.I) / 7)))) + (y5 * (2 + (((8 * r) * Complex.I) / 7)))) + ((2 * r) / 7)) + ((6 * Complex.I) / 7)) : ℂ)‖ ≤ (((((1*((2/7)+(((2*2)*1)/7)))+(1*((4/7)+(((4*2)*1)/7))))+(1*(2+(((8*2)*1)/7))))+((2*2)/7))+((6*1)/7)) := (nb_add (nb_add (nb_add (nb_add (nb_mul hNy3 (nb_sub (nb_div (nb_neg (by norm_num)) 7) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7))) (nb_mul hNy4 (nb_sub (nb_div (by norm_num) 7) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7)))) (nb_mul hNy5 (nb_add (by norm_num) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7)))) (nb_div (nb_mul (by norm_num) hrN) 7)) (nb_div (nb_mul (by norm_num) (by simp)) 7))
      _ ≤ 9 := by norm_num
  have c9 : ‖((y4 * (((2 * r) / 7) + ((6 * Complex.I) / 7))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * (((2 * r) / 7) + ((6 * Complex.I) / 7))) : ℂ)‖ ≤ (1*(((2*2)/7)+((6*1)/7))) := (nb_mul hNy4 (nb_add (nb_div (nb_mul (by norm_num) hrN) 7) (nb_div (nb_mul (by norm_num) (by simp)) 7)))
      _ ≤ 2 := by norm_num
  have c10 : ‖(((((-9) * r) / 14) + ((3 * Complex.I) / 14)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((((-9) * r) / 14) + ((3 * Complex.I) / 14)) : ℂ)‖ ≤ (((9*2)/14)+((3*1)/14)) := (nb_add (nb_div (nb_mul (nb_neg (by norm_num)) hrN) 14) (nb_div (nb_mul (by norm_num) (by simp)) 14))
      _ ≤ 2 := by norm_num
  have c11 : ‖((((4 * y3) / 7) + ((4 * r) / 7)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((4 * y3) / 7) + ((4 * r) / 7)) : ℂ)‖ ≤ (((4*1)/7)+((4*2)/7)) := (nb_add (nb_div (nb_mul (by norm_num) hNy3) 7) (nb_div (nb_mul (by norm_num) hrN) 7))
      _ ≤ 2 := by norm_num
  have c12 : ‖((((-2) / 7) + (((2 * r) * Complex.I) / 7)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-2) / 7) + (((2 * r) * Complex.I) / 7)) : ℂ)‖ ≤ ((2/7)+(((2*2)*1)/7)) := (nb_add (nb_div (nb_neg (by norm_num)) 7) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7))
      _ ≤ 1 := by norm_num
  have c13 : ‖(((4 / 7) - (((4 * r) * Complex.I) / 7)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((4 / 7) - (((4 * r) * Complex.I) / 7)) : ℂ)‖ ≤ ((4/7)+(((4*2)*1)/7)) := (nb_sub (nb_div (by norm_num) 7) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7))
      _ ≤ 2 := by norm_num
  have c14 : ‖((((x3 * y5) * (((-12) / 7) + (((4 * r) * Complex.I) / 7))) + ((y3 * y5) * ((11 / 14) + (((11 * r) * Complex.I) / 14)))) : ℂ)‖ ≤ (6 : ℝ) := by
    calc
      ‖((((x3 * y5) * (((-12) / 7) + (((4 * r) * Complex.I) / 7))) + ((y3 * y5) * ((11 / 14) + (((11 * r) * Complex.I) / 14)))) : ℂ)‖ ≤ (((1*1)*((12/7)+(((4*2)*1)/7)))+((1*1)*((11/14)+(((11*2)*1)/14)))) := (nb_add (nb_mul (nb_mul hNx3 hNy5) (nb_add (nb_div (nb_neg (by norm_num)) 7) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7))) (nb_mul (nb_mul hNy3 hNy5) (nb_add (nb_div (by norm_num) 14) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 14))))
      _ ≤ 6 := by norm_num
  have c15 : ‖((((2 * r) * Complex.I) / 7) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((2 * r) * Complex.I) / 7) : ℂ)‖ ≤ (((2*2)*1)/7) := (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7)
      _ ≤ 1 := by norm_num
  have c16 : ‖(((y5 ^ 2) * (((-9) / 14) + (((9 * r) * Complex.I) / 14))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((y5 ^ 2) * (((-9) / 14) + (((9 * r) * Complex.I) / 14))) : ℂ)‖ ≤ ((1^2)*((9/14)+(((9*2)*1)/14))) := (nb_mul (nb_pow hNy5 2) (nb_add (nb_div (nb_neg (by norm_num)) 14) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 14)))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 8577774 * η
  rw [eid]
  calc
    _ ≤ (((((((((((((((((2 * (348 * η)) + (2 * (4015510 * η))) + (4 * (1 * η))) + (7 * (1 * η))) + (3 * (12 * η))) + (3 * (24 * η))) + (3 * (120 * η))) + (3 * (612 * η))) + (9 * (1200 * η))) + (2 * (1788 * η))) + (2 * (3578 * η))) + (2 * (10732 * η))) + (1 * (13203 * η))) + (2 * (57192 * η))) + (6 * (25706 * η))) + (1 * (51414 * η))) + (2 * (83755 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg10) (nb_mul c1 pg42)) (nb_mul c2 pg3)) (nb_mul c3 pg4)) (nb_mul c4 pg6)) (nb_mul c5 pg7)) (nb_mul c6 pg9)) (nb_mul c7 pg11)) (nb_mul c8 pg12)) (nb_mul c9 pg14)) (nb_mul c10 pg15)) (nb_mul c11 pg17)) (nb_mul c12 pg18)) (nb_mul c13 pg20)) (nb_mul c14 pg24)) (nb_mul c15 pg25)) (nb_mul c16 pg27))
    _ = 8577774 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 47 by 21682006 times `η` under the
stated assumptions. -/
private theorem step47 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx3 : ‖x3‖ ≤ 1)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg8 : ‖(-x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5 : ℂ)‖ ≤ (72 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    (pg17 : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η)
    (pg18 : ‖(x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) : ℂ)‖ ≤ (13203 : ℝ) * η)
    (pg20 : ‖(-x1*y5^2 + x2*x3*y5*(3/2 + r*Complex.I/2) + x2*y3*y5*(-1/2 + r*Complex.I/2) + x2*y4^2 + y3^2*(-1/4 + r*Complex.I/4) + 3/4 + r*Complex.I/4 : ℂ)‖ ≤ (57192 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg25 : ‖(y1*y2 + 1/2 + r*Complex.I/2 : ℂ)‖ ≤ (51414 : ℝ) * η)
    (pg27 : ‖(x1 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (83755 : ℝ) * η)
    (pg31 : ‖(y1*y4^2 + y2*y5^2 + y3^2/2 + y4*y5*(1/2 - r*Complex.I/2) - 3*r*Complex.I/2 : ℂ)‖ ≤ (400160 : ℝ) * η)
    (pg39 : ‖(x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6) : ℂ)‖ ≤ (1713373 : ℝ) * η)
    (pg46 : ‖(y1*y3*y5 + y2*y5^2*(4/7 + 4*r*Complex.I/7) + y3^2*(-2/7 - 2*r*Complex.I/7) + 6*y4*y5/7 + 3/2 - r*Complex.I/2 : ℂ)‖ ≤ (8577774 : ℝ) * η)
    : ‖(y2*y5^2 + 5*y3^2/4 + y4*y5*(-1/2 + r*Complex.I/2) : ℂ)‖ ≤ (21682006 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y2*y5^2 + 5*y3^2/4 + y4*y5*(-1/2 + r*Complex.I/2)
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g8 : ℂ := -x1*y2 + x1*y3 + x2*y4 - x2 + x3*y2 - x3*y4 - x4*y5 + x4 + x5*y1 - x5*y3 - y1 + y5
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let clause17 : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  let clause18 : ℂ :=
      x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I)
  let clause20 : ℂ :=
      -x1*y5^2 + x2*x3*y5*(3/2 + r*Complex.I/2) + x2*y3*y5*(-1/2 + r*Complex.I/2) + x2*y4^2 + y3^2*(-1/4 + r*Complex.I/4) + 3/4 + r*Complex.I/4
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause25 : ℂ := y1*y2 + 1/2 + r*Complex.I/2
  let clause27 : ℂ := x1 + y2*(1/2 - r*Complex.I/2)
  let clause31 : ℂ := y1*y4^2 + y2*y5^2 + y3^2/2 + y4*y5*(1/2 - r*Complex.I/2) - 3*r*Complex.I/2
  let clause39 : ℂ :=
      x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6)
  let clause46 : ℂ :=
      y1*y3*y5 + y2*y5^2*(4/7 + 4*r*Complex.I/7) + y3^2*(-2/7 - 2*r*Complex.I/7) + 6*y4*y5/7 + 3/2 - r*Complex.I/2
  have eid : target = (((((((((((((((((((((y4 * (((-7) / 8) + (((7 * r) * Complex.I) / 24))) * g8) + ((y1 * ((7 / 8) - (((7 * r) * Complex.I) / 24))) * clause39)) + ((((y2 * ((7 / 8) - (((7 * r) * Complex.I) / 24))) + (y3 * (((7 * r) / 24) - ((7 * Complex.I) / 8)))) - (((7 * r) * Complex.I) / 12)) * g3)) + ((((((-7) * r) * y3) / 4) + (((7 * r) * Complex.I) / 4)) * g4)) + ((y5 * (((-21) / 8) - (((7 * r) * Complex.I) / 8))) * g6)) + ((y5 * ((21 / 8) - (((7 * r) * Complex.I) / 8))) * g7)) + (((y4 * (((-7) / 8) + (((7 * r) * Complex.I) / 24))) + (y5 * ((21 / 8) + (((7 * r) * Complex.I) / 8)))) * g9)) + ((y4 * ((7 / 8) - (((7 * r) * Complex.I) / 24))) * thresholdGoal)) + ((y5 * ((21 / 8) + (((7 * r) * Complex.I) / 8))) * clause11)) + (((((((7 * y3) / 12) - ((7 * y4) / 6)) + (y5 * ((77 / 24) - (((7 * r) * Complex.I) / 24)))) + ((7 * r) / 24)) - ((7 * Complex.I) / 8)) * clause12)) + ((y4 * (((7 * r) / 24) - ((7 * Complex.I) / 8))) * clause14)) + (((((-7) * r) / 6) + ((7 * Complex.I) / 4)) * walkGoal)) + (((((-7) * r) / 24) - ((7 * Complex.I) / 8)) * clause17)) + ((7 / 12) * clause18)) + ((((-7) / 24) - (((7 * r) * Complex.I) / 24)) * clause20)) + (((((((7 * r) * Complex.I) * x3) * y5) / 12) + (((7 * y3) * y5) / 12)) * clause24)) + ((((-7) / 8) - (((7 * r) * Complex.I) / 24)) * clause25)) + (((y5 ^ 2) * ((35 / 24) + (((35 * r) * Complex.I) / 24))) * clause27)) + (((-7) / 12) * clause31)) + ((((-7) / 12) + (((7 * r) * Complex.I) / 12)) * clause46)) := by
    dsimp only [target, g3, g4, g6, g7, g8, g9, thresholdGoal, clause11, clause12, clause14,
        walkGoal, clause17, clause18, clause20, clause24, clause25, clause27, clause31, clause39, clause46]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y4 * (((-7) / 8) + (((7 * r) * Complex.I) / 24))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * (((-7) / 8) + (((7 * r) * Complex.I) / 24))) : ℂ)‖ ≤ (1*((7/8)+(((7*2)*1)/24))) := (nb_mul hNy4 (nb_add (nb_div (nb_neg (by norm_num)) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 24)))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y1 * ((7 / 8) - (((7 * r) * Complex.I) / 24))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y1 * ((7 / 8) - (((7 * r) * Complex.I) / 24))) : ℂ)‖ ≤ (1*((7/8)+(((7*2)*1)/24))) := (nb_mul hNy1 (nb_sub (nb_div (by norm_num) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 24)))
      _ ≤ 2 := by norm_num
  have c2 : ‖((((y2 * ((7 / 8) - (((7 * r) * Complex.I) / 24))) + (y3 * (((7 * r) / 24) - ((7 * Complex.I) / 8)))) - (((7 * r) * Complex.I) / 12)) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((((y2 * ((7 / 8) - (((7 * r) * Complex.I) / 24))) + (y3 * (((7 * r) / 24) - ((7 * Complex.I) / 8)))) - (((7 * r) * Complex.I) / 12)) : ℂ)‖ ≤ (((1*((7/8)+(((7*2)*1)/24)))+(1*(((7*2)/24)+((7*1)/8))))+(((7*2)*1)/12)) := (nb_sub (nb_add (nb_mul hNy2 (nb_sub (nb_div (by norm_num) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 24))) (nb_mul hNy3 (nb_sub (nb_div (nb_mul (by norm_num) hrN) 24) (nb_div (nb_mul (by norm_num) (by simp)) 8)))) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 12))
      _ ≤ 5 := by norm_num
  have c3 : ‖((((((-7) * r) * y3) / 4) + (((7 * r) * Complex.I) / 4)) : ℂ)‖ ≤ (7 : ℝ) := by
    calc
      ‖((((((-7) * r) * y3) / 4) + (((7 * r) * Complex.I) / 4)) : ℂ)‖ ≤ ((((7*2)*1)/4)+(((7*2)*1)/4)) := (nb_add (nb_div (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) hNy3) 4) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 4))
      _ ≤ 7 := by norm_num
  have c4 : ‖((y5 * (((-21) / 8) - (((7 * r) * Complex.I) / 8))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((y5 * (((-21) / 8) - (((7 * r) * Complex.I) / 8))) : ℂ)‖ ≤ (1*((21/8)+(((7*2)*1)/8))) := (nb_mul hNy5 (nb_sub (nb_div (nb_neg (by norm_num)) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 8)))
      _ ≤ 5 := by norm_num
  have c5 : ‖((y5 * ((21 / 8) - (((7 * r) * Complex.I) / 8))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((y5 * ((21 / 8) - (((7 * r) * Complex.I) / 8))) : ℂ)‖ ≤ (1*((21/8)+(((7*2)*1)/8))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 8)))
      _ ≤ 5 := by norm_num
  have c6 : ‖(((y4 * (((-7) / 8) + (((7 * r) * Complex.I) / 24))) + (y5 * ((21 / 8) + (((7 * r) * Complex.I) / 8)))) : ℂ)‖ ≤ (6 : ℝ) := by
    calc
      ‖(((y4 * (((-7) / 8) + (((7 * r) * Complex.I) / 24))) + (y5 * ((21 / 8) + (((7 * r) * Complex.I) / 8)))) : ℂ)‖ ≤ ((1*((7/8)+(((7*2)*1)/24)))+(1*((21/8)+(((7*2)*1)/8)))) := (nb_add (nb_mul hNy4 (nb_add (nb_div (nb_neg (by norm_num)) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 24))) (nb_mul hNy5 (nb_add (nb_div (by norm_num) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 8))))
      _ ≤ 6 := by norm_num
  have c7 : ‖((y4 * ((7 / 8) - (((7 * r) * Complex.I) / 24))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * ((7 / 8) - (((7 * r) * Complex.I) / 24))) : ℂ)‖ ≤ (1*((7/8)+(((7*2)*1)/24))) := (nb_mul hNy4 (nb_sub (nb_div (by norm_num) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 24)))
      _ ≤ 2 := by norm_num
  have c8 : ‖((y5 * ((21 / 8) + (((7 * r) * Complex.I) / 8))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((y5 * ((21 / 8) + (((7 * r) * Complex.I) / 8))) : ℂ)‖ ≤ (1*((21/8)+(((7*2)*1)/8))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 8)))
      _ ≤ 5 := by norm_num
  have c9 : ‖(((((((7 * y3) / 12) - ((7 * y4) / 6)) + (y5 * ((77 / 24) - (((7 * r) * Complex.I) / 24)))) + ((7 * r) / 24)) - ((7 * Complex.I) / 8)) : ℂ)‖ ≤ (7 : ℝ) := by
    calc
      ‖(((((((7 * y3) / 12) - ((7 * y4) / 6)) + (y5 * ((77 / 24) - (((7 * r) * Complex.I) / 24)))) + ((7 * r) / 24)) - ((7 * Complex.I) / 8)) : ℂ)‖ ≤ ((((((7*1)/12)+((7*1)/6))+(1*((77/24)+(((7*2)*1)/24))))+((7*2)/24))+((7*1)/8)) := (nb_sub (nb_add (nb_add (nb_sub (nb_div (nb_mul (by norm_num) hNy3) 12) (nb_div (nb_mul (by norm_num) hNy4) 6)) (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 24) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 24)))) (nb_div (nb_mul (by norm_num) hrN) 24)) (nb_div (nb_mul (by norm_num) (by simp)) 8))
      _ ≤ 7 := by norm_num
  have c10 : ‖((y4 * (((7 * r) / 24) - ((7 * Complex.I) / 8))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * (((7 * r) / 24) - ((7 * Complex.I) / 8))) : ℂ)‖ ≤ (1*(((7*2)/24)+((7*1)/8))) := (nb_mul hNy4 (nb_sub (nb_div (nb_mul (by norm_num) hrN) 24) (nb_div (nb_mul (by norm_num) (by simp)) 8)))
      _ ≤ 2 := by norm_num
  have c11 : ‖(((((-7) * r) / 6) + ((7 * Complex.I) / 4)) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖(((((-7) * r) / 6) + ((7 * Complex.I) / 4)) : ℂ)‖ ≤ (((7*2)/6)+((7*1)/4)) := (nb_add (nb_div (nb_mul (nb_neg (by norm_num)) hrN) 6) (nb_div (nb_mul (by norm_num) (by simp)) 4))
      _ ≤ 5 := by norm_num
  have c12 : ‖(((((-7) * r) / 24) - ((7 * Complex.I) / 8)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((((-7) * r) / 24) - ((7 * Complex.I) / 8)) : ℂ)‖ ≤ (((7*2)/24)+((7*1)/8)) := (nb_sub (nb_div (nb_mul (nb_neg (by norm_num)) hrN) 24) (nb_div (nb_mul (by norm_num) (by simp)) 8))
      _ ≤ 2 := by norm_num
  have c13 : ‖((7 / 12) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((7 / 12) : ℂ)‖ ≤ (7/12) := (nb_div (by norm_num) 12)
      _ ≤ 1 := by norm_num
  have c14 : ‖((((-7) / 24) - (((7 * r) * Complex.I) / 24)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-7) / 24) - (((7 * r) * Complex.I) / 24)) : ℂ)‖ ≤ ((7/24)+(((7*2)*1)/24)) := (nb_sub (nb_div (nb_neg (by norm_num)) 24) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 24))
      _ ≤ 1 := by norm_num
  have c15 : ‖(((((((7 * r) * Complex.I) * x3) * y5) / 12) + (((7 * y3) * y5) / 12)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((((((7 * r) * Complex.I) * x3) * y5) / 12) + (((7 * y3) * y5) / 12)) : ℂ)‖ ≤ ((((((7*2)*1)*1)*1)/12)+(((7*1)*1)/12)) := (nb_add (nb_div (nb_mul (nb_mul (nb_mul (nb_mul (by norm_num) hrN) (by simp)) hNx3) hNy5) 12) (nb_div (nb_mul (nb_mul (by norm_num) hNy3) hNy5) 12))
      _ ≤ 2 := by norm_num
  have c16 : ‖((((-7) / 8) - (((7 * r) * Complex.I) / 24)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-7) / 8) - (((7 * r) * Complex.I) / 24)) : ℂ)‖ ≤ ((7/8)+(((7*2)*1)/24)) := (nb_sub (nb_div (nb_neg (by norm_num)) 8) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 24))
      _ ≤ 2 := by norm_num
  have c17 : ‖(((y5 ^ 2) * ((35 / 24) + (((35 * r) * Complex.I) / 24))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖(((y5 ^ 2) * ((35 / 24) + (((35 * r) * Complex.I) / 24))) : ℂ)‖ ≤ ((1^2)*((35/24)+(((35*2)*1)/24))) := (nb_mul (nb_pow hNy5 2) (nb_add (nb_div (by norm_num) 24) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 24)))
      _ ≤ 5 := by norm_num
  have c18 : ‖(((-7) / 12) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((-7) / 12) : ℂ)‖ ≤ (7/12) := (nb_div (nb_neg (by norm_num)) 12)
      _ ≤ 1 := by norm_num
  have c19 : ‖((((-7) / 12) + (((7 * r) * Complex.I) / 12)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-7) / 12) + (((7 * r) * Complex.I) / 12)) : ℂ)‖ ≤ ((7/12)+(((7*2)*1)/12)) := (nb_add (nb_div (nb_neg (by norm_num)) 12) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 12))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 21682006 * η
  rw [eid]
  calc
    _ ≤ ((((((((((((((((((((2 * (72 * η)) + (2 * (1713373 * η))) + (5 * (1 * η))) + (7 * (1 * η))) + (5 * (12 * η))) + (5 * (24 * η))) + (6 * (120 * η))) + (2 * (348 * η))) + (5 * (612 * η))) + (7 * (1200 * η))) + (2 * (1788 * η))) + (5 * (3578 * η))) + (2 * (10732 * η))) + (1 * (13203 * η))) + (1 * (57192 * η))) + (2 * (25706 * η))) + (2 * (51414 * η))) + (5 * (83755 * η))) + (1 * (400160 * η))) + (2 * (8577774 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg8) (nb_mul c1 pg39)) (nb_mul c2 pg3)) (nb_mul c3 pg4)) (nb_mul c4 pg6)) (nb_mul c5 pg7)) (nb_mul c6 pg9)) (nb_mul c7 pg10)) (nb_mul c8 pg11)) (nb_mul c9 pg12)) (nb_mul c10 pg14)) (nb_mul c11 pg15)) (nb_mul c12 pg17)) (nb_mul c13 pg18)) (nb_mul c14 pg20)) (nb_mul c15 pg24)) (nb_mul c16 pg25)) (nb_mul c17 pg27)) (nb_mul c18 pg31)) (nb_mul c19 pg46))
    _ = 21682006 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 48 by 15225015 times `η` under the
stated assumptions. -/
private theorem step48 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNx2 : ‖x2‖ ≤ 1)
    (hNx5 : ‖x5‖ ≤ 1)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg14 : ‖(x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (1788 : ℝ) * η)
    (pg17 : ‖(x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2) : ℂ)‖ ≤ (10732 : ℝ) * η)
    (pg18 : ‖(x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I) : ℂ)‖ ≤ (13203 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg26 : ‖(x3*y5*(1/2 - r*Complex.I/2) + x5*y4*(-1/2 - r*Complex.I/2) + y1^2 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (56632 : ℝ) * η)
    (pg32 : ‖(x5*y4*(-3/2 + r*Complex.I/2) + y1*y3*y4 + y1*y5^2*(1/2 + r*Complex.I/2) + y2*(-3/2 - r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/2) - 2*y4^2 : ℂ)‖ ≤ (103524 : ℝ) * η)
    (pg35 : ‖(x3*y5*(-1/2 + r*Complex.I/6) + 5*r*Complex.I*x5*y4/6 + y1*y5^2 + y2*(-3/4 + r*Complex.I/4) + y3*y5*(-1/4 - r*Complex.I/4) + y4^2*(-3/4 + 3*r*Complex.I/4) : ℂ)‖ ≤ (663699 : ℝ) * η)
    (pg39 : ‖(x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6) : ℂ)‖ ≤ (1713373 : ℝ) * η)
    (pg42 : ‖(x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24) : ℂ)‖ ≤ (4015510 : ℝ) * η)
    : ‖(x3*y5 - 2*r*Complex.I*y3*y5/3 : ℂ)‖ ≤ (15225015 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x3*y5 - 2*r*Complex.I*y3*y5/3
  let g3 : ℂ := x4*y4 - 1
  let g4 : ℂ := x5*y5 - 1
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause14 : ℂ := x2 + x3*y4*(1/2 - r*Complex.I/2) + x5*y3 + y1*(1/2 - r*Complex.I/2)
  let clause17 : ℂ := x2*y5*(-1 - r*Complex.I) - y1*y5 + y2*y4 + y3*(-1/2 - r*Complex.I/2)
  let clause18 : ℂ :=
      x2*y3*y4 + x2*y5^2*(1/2 + r*Complex.I/2) - r*Complex.I*x5*y4 + y2*(3/2 - r*Complex.I/2) + y3*y5*(1/2 + r*Complex.I/2) + y4^2*(1 - r*Complex.I)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause26 : ℂ :=
      x3*y5*(1/2 - r*Complex.I/2) + x5*y4*(-1/2 - r*Complex.I/2) + y1^2 + y2*(1/2 - r*Complex.I/2)
  let clause32 : ℂ :=
      x5*y4*(-3/2 + r*Complex.I/2) + y1*y3*y4 + y1*y5^2*(1/2 + r*Complex.I/2) + y2*(-3/2 - r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/2) - 2*y4^2
  let optGoal : ℂ :=
      x3*y5*(-1/2 + r*Complex.I/6) + 5*r*Complex.I*x5*y4/6 + y1*y5^2 + y2*(-3/4 + r*Complex.I/4) + y3*y5*(-1/4 - r*Complex.I/4) + y4^2*(-3/4 + 3*r*Complex.I/4)
  let clause39 : ℂ :=
      x3*y5*(1 + r*Complex.I) + x5*y4 + y2*(1/2 + r*Complex.I/2) + y3*y5*(1/2 - r*Complex.I/6) + y4^2*(1/2 + r*Complex.I/6)
  let clause42 : ℂ :=
      x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24)
  have eid : target = ((((((((((((((((y4 * ((2 / 3) + (((2 * r) * Complex.I) / 3))) * g6) + ((y1 * (((-2) / 3) - (((2 * r) * Complex.I) / 3))) * clause42)) + (((((-4) * y1) / 3) + (y2 * (((-2) / 3) - (((2 * r) * Complex.I) / 3)))) * g3)) + ((((x2 * (((-4) / 3) - (((4 * r) * Complex.I) / 3))) - ((4 * y1) / 3)) - (y2 / 3)) * g4)) + ((y5 / 3) * g7)) + ((y4 * (((-2) / 3) - (((2 * r) * Complex.I) / 3))) * g9)) + (((((-4) * y4) / 3) + (y5 * ((-1) - (((2 * r) * Complex.I) / 3)))) * clause12)) + ((((-2) / 3) - (((2 * r) * Complex.I) / 3)) * clause14)) + ((((-4) * x5) / 3) * clause17)) + ((((-2) / 3) - (((2 * r) * Complex.I) / 3)) * clause18)) + (((((((4 * r) * Complex.I) * (y5 ^ 2)) / 3) - (2 / 3)) - (((2 * r) * Complex.I) / 3)) * clause24)) + (((1 / 3) + ((r * Complex.I) / 3)) * clause26)) + (((2 / 3) - (((2 * r) * Complex.I) / 9)) * clause32)) + ((((-5) / 2) - (((5 * r) * Complex.I) / 6)) * optGoal)) + ((((-5) / 12) + (((5 * r) * Complex.I) / 12)) * clause39)) := by
    dsimp only [target, g3, g4, g6, g7, g9, clause12, clause14, clause17, clause18, clause24,
        clause26, clause32, optGoal, clause39, clause42]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y4 * ((2 / 3) + (((2 * r) * Complex.I) / 3))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * ((2 / 3) + (((2 * r) * Complex.I) / 3))) : ℂ)‖ ≤ (1*((2/3)+(((2*2)*1)/3))) := (nb_mul hNy4 (nb_add (nb_div (by norm_num) 3) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3)))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y1 * (((-2) / 3) - (((2 * r) * Complex.I) / 3))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y1 * (((-2) / 3) - (((2 * r) * Complex.I) / 3))) : ℂ)‖ ≤ (1*((2/3)+(((2*2)*1)/3))) := (nb_mul hNy1 (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3)))
      _ ≤ 2 := by norm_num
  have c2 : ‖(((((-4) * y1) / 3) + (y2 * (((-2) / 3) - (((2 * r) * Complex.I) / 3)))) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖(((((-4) * y1) / 3) + (y2 * (((-2) / 3) - (((2 * r) * Complex.I) / 3)))) : ℂ)‖ ≤ (((4*1)/3)+(1*((2/3)+(((2*2)*1)/3)))) := (nb_add (nb_div (nb_mul (nb_neg (by norm_num)) hNy1) 3) (nb_mul hNy2 (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3))))
      _ ≤ 4 := by norm_num
  have c3 : ‖((((x2 * (((-4) / 3) - (((4 * r) * Complex.I) / 3))) - ((4 * y1) / 3)) - (y2 / 3)) : ℂ)‖ ≤ (6 : ℝ) := by
    calc
      ‖((((x2 * (((-4) / 3) - (((4 * r) * Complex.I) / 3))) - ((4 * y1) / 3)) - (y2 / 3)) : ℂ)‖ ≤ (((1*((4/3)+(((4*2)*1)/3)))+((4*1)/3))+(1/3)) := (nb_sub (nb_sub (nb_mul hNx2 (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3))) (nb_div (nb_mul (by norm_num) hNy1) 3)) (nb_div hNy2 3))
      _ ≤ 6 := by norm_num
  have c4 : ‖((y5 / 3) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 / 3) : ℂ)‖ ≤ (1/3) := (nb_div hNy5 3)
      _ ≤ 1 := by norm_num
  have c5 : ‖((y4 * (((-2) / 3) - (((2 * r) * Complex.I) / 3))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * (((-2) / 3) - (((2 * r) * Complex.I) / 3))) : ℂ)‖ ≤ (1*((2/3)+(((2*2)*1)/3))) := (nb_mul hNy4 (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3)))
      _ ≤ 2 := by norm_num
  have c6 : ‖(((((-4) * y4) / 3) + (y5 * ((-1) - (((2 * r) * Complex.I) / 3)))) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖(((((-4) * y4) / 3) + (y5 * ((-1) - (((2 * r) * Complex.I) / 3)))) : ℂ)‖ ≤ (((4*1)/3)+(1*(1+(((2*2)*1)/3)))) := (nb_add (nb_div (nb_mul (nb_neg (by norm_num)) hNy4) 3) (nb_mul hNy5 (nb_sub (nb_neg (by norm_num)) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3))))
      _ ≤ 4 := by norm_num
  have c7 : ‖((((-2) / 3) - (((2 * r) * Complex.I) / 3)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-2) / 3) - (((2 * r) * Complex.I) / 3)) : ℂ)‖ ≤ ((2/3)+(((2*2)*1)/3)) := (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3))
      _ ≤ 2 := by norm_num
  have c8 : ‖((((-4) * x5) / 3) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-4) * x5) / 3) : ℂ)‖ ≤ ((4*1)/3) := (nb_div (nb_mul (nb_neg (by norm_num)) hNx5) 3)
      _ ≤ 2 := by norm_num
  have c9 : ‖((((-2) / 3) - (((2 * r) * Complex.I) / 3)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-2) / 3) - (((2 * r) * Complex.I) / 3)) : ℂ)‖ ≤ ((2/3)+(((2*2)*1)/3)) := (nb_sub (nb_div (nb_neg (by norm_num)) 3) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3))
      _ ≤ 2 := by norm_num
  have c10 : ‖(((((((4 * r) * Complex.I) * (y5 ^ 2)) / 3) - (2 / 3)) - (((2 * r) * Complex.I) / 3)) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖(((((((4 * r) * Complex.I) * (y5 ^ 2)) / 3) - (2 / 3)) - (((2 * r) * Complex.I) / 3)) : ℂ)‖ ≤ ((((((4*2)*1)*(1^2))/3)+(2/3))+(((2*2)*1)/3)) := (nb_sub (nb_sub (nb_div (nb_mul (nb_mul (nb_mul (by norm_num) hrN) (by simp)) (nb_pow hNy5 2)) 3) (nb_div (by norm_num) 3)) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3))
      _ ≤ 5 := by norm_num
  have c11 : ‖(((1 / 3) + ((r * Complex.I) / 3)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((1 / 3) + ((r * Complex.I) / 3)) : ℂ)‖ ≤ ((1/3)+((2*1)/3)) := (nb_add (nb_div (by norm_num) 3) (nb_div (nb_mul hrN (by simp)) 3))
      _ ≤ 1 := by norm_num
  have c12 : ‖(((2 / 3) - (((2 * r) * Complex.I) / 9)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((2 / 3) - (((2 * r) * Complex.I) / 9)) : ℂ)‖ ≤ ((2/3)+(((2*2)*1)/9)) := (nb_sub (nb_div (by norm_num) 3) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 9))
      _ ≤ 2 := by norm_num
  have c13 : ‖((((-5) / 2) - (((5 * r) * Complex.I) / 6)) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((((-5) / 2) - (((5 * r) * Complex.I) / 6)) : ℂ)‖ ≤ ((5/2)+(((5*2)*1)/6)) := (nb_sub (nb_div (nb_neg (by norm_num)) 2) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 6))
      _ ≤ 5 := by norm_num
  have c14 : ‖((((-5) / 12) + (((5 * r) * Complex.I) / 12)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-5) / 12) + (((5 * r) * Complex.I) / 12)) : ℂ)‖ ≤ ((5/12)+(((5*2)*1)/12)) := (nb_add (nb_div (nb_neg (by norm_num)) 12) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 12))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 15225015 * η
  rw [eid]
  calc
    _ ≤ (((((((((((((((2 * (12 * η)) + (2 * (4015510 * η))) + (4 * (1 * η))) + (6 * (1 * η))) + (1 * (24 * η))) + (2 * (120 * η))) + (4 * (1200 * η))) + (2 * (1788 * η))) + (2 * (10732 * η))) + (2 * (13203 * η))) + (5 * (25706 * η))) + (1 * (56632 * η))) + (2 * (103524 * η))) + (5 * (663699 * η))) + (2 * (1713373 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg6) (nb_mul c1 pg42)) (nb_mul c2 pg3)) (nb_mul c3 pg4)) (nb_mul c4 pg7)) (nb_mul c5 pg9)) (nb_mul c6 pg12)) (nb_mul c7 pg14)) (nb_mul c8 pg17)) (nb_mul c9 pg18)) (nb_mul c10 pg24)) (nb_mul c11 pg26)) (nb_mul c12 pg32)) (nb_mul c13 pg35)) (nb_mul c14 pg39))
    _ = 15225015 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 50 by 78224073 times `η` under the
stated assumptions. -/
private theorem step50 (r x2 x3 x4 y1 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg43 : ‖(x4*y5^2*(3/8 + r*Complex.I/8) + r*Complex.I*y1*y5/2 + y3*y4*y5 + y3*(3/2 - r*Complex.I/2) + y5^3*(1/8 + r*Complex.I/8) : ℂ)‖ ≤ (8115294 : ℝ) * η)
    (pg48 : ‖(x3*y5 - 2*r*Complex.I*y3*y5/3 : ℂ)‖ ≤ (15225015 : ℝ) * η)
    : ‖(x4*y5^2 + y1*y5*(1 + r*Complex.I) + y3*(1 - r*Complex.I) + y5^3*(1/2 + r*Complex.I/6) : ℂ)‖ ≤ (78224073 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x4*y5^2 + y1*y5*(1 + r*Complex.I) + y3*(1 - r*Complex.I) + y5^3*(1/2 + r*Complex.I/6)
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause43 : ℂ :=
      x4*y5^2*(3/8 + r*Complex.I/8) + r*Complex.I*y1*y5/2 + y3*y4*y5 + y3*(3/2 - r*Complex.I/2) + y5^3*(1/8 + r*Complex.I/8)
  let clause48 : ℂ := x3*y5 - 2*r*Complex.I*y3*y5/3
  have eid : target = (((((1 + (r * Complex.I)) * walkGoal) + ((y4 * ((-1) - (r * Complex.I))) * clause48)) + ((y5 * (1 - (r * Complex.I))) * clause24)) + ((2 - (((2 * r) * Complex.I) / 3)) * clause43)) := by
    dsimp only [target, walkGoal, clause24, clause43, clause48]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((1 + (r * Complex.I)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((1 + (r * Complex.I)) : ℂ)‖ ≤ (1+(2*1)) := (nb_add (by norm_num) (nb_mul hrN (by simp)))
      _ ≤ 3 := by norm_num
  have c1 : ‖((y4 * ((-1) - (r * Complex.I))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y4 * ((-1) - (r * Complex.I))) : ℂ)‖ ≤ (1*(1+(2*1))) := (nb_mul hNy4 (nb_sub (nb_neg (by norm_num)) (nb_mul hrN (by simp))))
      _ ≤ 3 := by norm_num
  have c2 : ‖((y5 * (1 - (r * Complex.I))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (1 - (r * Complex.I))) : ℂ)‖ ≤ (1*(1+(2*1))) := (nb_mul hNy5 (nb_sub (by norm_num) (nb_mul hrN (by simp))))
      _ ≤ 3 := by norm_num
  have c3 : ‖((2 - (((2 * r) * Complex.I) / 3)) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((2 - (((2 * r) * Complex.I) / 3)) : ℂ)‖ ≤ (2+(((2*2)*1)/3)) := (nb_sub (by norm_num) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 3))
      _ ≤ 4 := by norm_num
  change ‖target‖ ≤ 78224073 * η
  rw [eid]
  calc
    _ ≤ ((((3 * (3578 * η)) + (3 * (15225015 * η))) + (3 * (25706 * η))) + (4 * (8115294 * η))) := (nb_add (nb_add (nb_add (nb_mul c0 pg15) (nb_mul c1 pg48)) (nb_mul c2 pg24)) (nb_mul c3 pg43))
    _ = 78224073 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 51 by 211336778 times `η` under the
stated assumptions. -/
private theorem step51 (r x3 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg44 : ‖(y1*y4*(3/4 - r*Complex.I/4) + r*Complex.I*y2*y3 + y3^2*y5 + y4*y5^2*(1/8 - r*Complex.I/8) + 7*r*Complex.I*y5/4 : ℂ)‖ ≤ (22535283 : ℝ) * η)
    (pg48 : ‖(x3*y5 - 2*r*Complex.I*y3*y5/3 : ℂ)‖ ≤ (15225015 : ℝ) * η)
    : ‖(y1*y4*(3 + r*Complex.I) + y2*y3*(-6 + 2*r*Complex.I) + y4*y5^2 + y5*(-15/2 + 5*r*Complex.I/2) : ℂ)‖ ≤ (211336778 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      y1*y4*(3 + r*Complex.I) + y2*y3*(-6 + 2*r*Complex.I) + y4*y5^2 + y5*(-15/2 + 5*r*Complex.I/2)
  let g2 : ℂ := x3*y3 - 1
  let clause44 : ℂ :=
      y1*y4*(3/4 - r*Complex.I/4) + r*Complex.I*y2*y3 + y3^2*y5 + y4*y5^2*(1/8 - r*Complex.I/8) + 7*r*Complex.I*y5/4
  let clause48 : ℂ := x3*y5 - 2*r*Complex.I*y3*y5/3
  have eid : target = ((((y5 * ((-3) + (r * Complex.I))) * g2) + ((y3 * (3 - (r * Complex.I))) * clause48)) + ((2 + ((2 * r) * Complex.I)) * clause44)) := by
    dsimp only [target, g2, clause44, clause48]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y5 * ((-3) + (r * Complex.I))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((y5 * ((-3) + (r * Complex.I))) : ℂ)‖ ≤ (1*(3+(2*1))) := (nb_mul hNy5 (nb_add (nb_neg (by norm_num)) (nb_mul hrN (by simp))))
      _ ≤ 5 := by norm_num
  have c1 : ‖((y3 * (3 - (r * Complex.I))) : ℂ)‖ ≤ (5 : ℝ) := by
    calc
      ‖((y3 * (3 - (r * Complex.I))) : ℂ)‖ ≤ (1*(3+(2*1))) := (nb_mul hNy3 (nb_sub (by norm_num) (nb_mul hrN (by simp))))
      _ ≤ 5 := by norm_num
  have c2 : ‖((2 + ((2 * r) * Complex.I)) : ℂ)‖ ≤ (6 : ℝ) := by
    calc
      ‖((2 + ((2 * r) * Complex.I)) : ℂ)‖ ≤ (2+((2*2)*1)) := (nb_add (by norm_num) (nb_mul (nb_mul (by norm_num) hrN) (by simp)))
      _ ≤ 6 := by norm_num
  change ‖target‖ ≤ 211336778 * η
  rw [eid]
  calc
    _ ≤ (((5 * (1 * η)) + (5 * (15225015 * η))) + (6 * (22535283 * η))) := (nb_add (nb_add (nb_mul c0 pg2) (nb_mul c1 pg48)) (nb_mul c2 pg44))
    _ = 211336778 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 52 by 70954652 times `η` under the
stated assumptions. -/
private theorem step52 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg10 : ‖(x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3 : ℂ)‖ ≤ (348 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg13 : ‖(x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (588 : ℝ) * η)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    (pg16 : ‖(x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I) : ℂ)‖ ≤ (19559 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg29 : ‖(x4*y5*(-3/2 + r*Complex.I/2) + y1*y4*y5*(-1/2 - r*Complex.I/2) + y1*(-3/2 - r*Complex.I/2) + y2*y3*y5 - 2*y5^2 : ℂ)‖ ≤ (258040 : ℝ) * η)
    (pg36 : ‖(x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4) : ℂ)‖ ≤ (891476 : ℝ) * η)
    (pg42 : ‖(x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24) : ℂ)‖ ≤ (4015510 : ℝ) * η)
    (pg48 : ‖(x3*y5 - 2*r*Complex.I*y3*y5/3 : ℂ)‖ ≤ (15225015 : ℝ) * η)
    : ‖(x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20) : ℂ)‖ ≤ (70954652 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ :=
      x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20)
  let g4 : ℂ := x5*y5 - 1
  let thresholdGoal : ℂ :=
      x1*y3*(1/2 - r*Complex.I/6) + x1*y4*(1 + r*Complex.I/3) + r*Complex.I*x1*y5/3 + x1*(-r/2 + Complex.I/2) + x2*y3*(-1/2 - r*Complex.I/6) + x2*y4*(1 + r*Complex.I/3) + x2*y5*(1 + r*Complex.I/3) + x2*(-r/2 + Complex.I/2) + x3*y2 + Complex.I*x3*y4 + Complex.I*x3*y5 - x4*y2 + x4*y3*(-r/2 + Complex.I/2) + x4*(1/2 + r*Complex.I/2) + x5*y3*(-r/2 + Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + Complex.I*y1 + Complex.I*y2 + y3*(1 + r*Complex.I/3) + y4*(-1 + r*Complex.I/3) + r*Complex.I*y5/3
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let clause13 : ℂ :=
      x1 + x2 + x3*y4*(1/2 - r*Complex.I/2) + x3*y5*(1/2 - r*Complex.I/2) + x4*y3 + x5*y3 + y1*(1/2 - r*Complex.I/2) + y2*(1/2 - r*Complex.I/2)
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let clause16 : ℂ :=
      x1*y3*y5 + x2*y4*y5*(-1/2 - r*Complex.I/2) - r*Complex.I*x4*y5 + y1*(3/2 - r*Complex.I/2) + y5^2*(1 - r*Complex.I)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause29 : ℂ :=
      x4*y5*(-3/2 + r*Complex.I/2) + y1*y4*y5*(-1/2 - r*Complex.I/2) + y1*(-3/2 - r*Complex.I/2) + y2*y3*y5 - 2*y5^2
  let clause36 : ℂ :=
      x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4)
  let clause42 : ℂ :=
      x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24)
  let clause48 : ℂ := x3*y5 - 2*r*Complex.I*y3*y5/3
  have eid : target = (((((((((((((y5 * (((-9) / 5) + (((3 * r) * Complex.I) / 5))) * thresholdGoal) + ((y2 * ((9 / 5) - (((3 * r) * Complex.I) / 5))) * clause48)) + ((y3 * (((3 * r) / 5) - ((9 * Complex.I) / 5))) * g4)) + ((y5 * (((-9) / 5) + (((3 * r) * Complex.I) / 5))) * clause11)) + ((y5 * ((6 / 5) + (((6 * r) * Complex.I) / 5))) * clause12)) + ((y5 * ((((-3) * r) / 5) + ((9 * Complex.I) / 5))) * clause13)) + (((((-3) * r) / 5) - ((9 * Complex.I) / 5)) * walkGoal)) + (((3 / 5) - (((3 * r) * Complex.I) / 5)) * clause16)) + ((((18 * y4) * y5) / 5) * clause24)) + (((6 / 5) + (((6 * r) * Complex.I) / 5)) * clause29)) + (((-3) + ((3 * r) * Complex.I)) * clause36)) + ((((-2) * r) * Complex.I) * clause42)) := by
    dsimp only [target, g4, thresholdGoal, clause11, clause12, clause13, walkGoal, clause16,
        clause24, clause29, clause36, clause42, clause48]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y5 * (((-9) / 5) + (((3 * r) * Complex.I) / 5))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (((-9) / 5) + (((3 * r) * Complex.I) / 5))) : ℂ)‖ ≤ (1*((9/5)+(((3*2)*1)/5))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 5) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 5)))
      _ ≤ 3 := by norm_num
  have c1 : ‖((y2 * ((9 / 5) - (((3 * r) * Complex.I) / 5))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y2 * ((9 / 5) - (((3 * r) * Complex.I) / 5))) : ℂ)‖ ≤ (1*((9/5)+(((3*2)*1)/5))) := (nb_mul hNy2 (nb_sub (nb_div (by norm_num) 5) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 5)))
      _ ≤ 3 := by norm_num
  have c2 : ‖((y3 * (((3 * r) / 5) - ((9 * Complex.I) / 5))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y3 * (((3 * r) / 5) - ((9 * Complex.I) / 5))) : ℂ)‖ ≤ (1*(((3*2)/5)+((9*1)/5))) := (nb_mul hNy3 (nb_sub (nb_div (nb_mul (by norm_num) hrN) 5) (nb_div (nb_mul (by norm_num) (by simp)) 5)))
      _ ≤ 3 := by norm_num
  have c3 : ‖((y5 * (((-9) / 5) + (((3 * r) * Complex.I) / 5))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * (((-9) / 5) + (((3 * r) * Complex.I) / 5))) : ℂ)‖ ≤ (1*((9/5)+(((3*2)*1)/5))) := (nb_mul hNy5 (nb_add (nb_div (nb_neg (by norm_num)) 5) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 5)))
      _ ≤ 3 := by norm_num
  have c4 : ‖((y5 * ((6 / 5) + (((6 * r) * Complex.I) / 5))) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((y5 * ((6 / 5) + (((6 * r) * Complex.I) / 5))) : ℂ)‖ ≤ (1*((6/5)+(((6*2)*1)/5))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 5) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 5)))
      _ ≤ 4 := by norm_num
  have c5 : ‖((y5 * ((((-3) * r) / 5) + ((9 * Complex.I) / 5))) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖((y5 * ((((-3) * r) / 5) + ((9 * Complex.I) / 5))) : ℂ)‖ ≤ (1*(((3*2)/5)+((9*1)/5))) := (nb_mul hNy5 (nb_add (nb_div (nb_mul (nb_neg (by norm_num)) hrN) 5) (nb_div (nb_mul (by norm_num) (by simp)) 5)))
      _ ≤ 3 := by norm_num
  have c6 : ‖(((((-3) * r) / 5) - ((9 * Complex.I) / 5)) : ℂ)‖ ≤ (3 : ℝ) := by
    calc
      ‖(((((-3) * r) / 5) - ((9 * Complex.I) / 5)) : ℂ)‖ ≤ (((3*2)/5)+((9*1)/5)) := (nb_sub (nb_div (nb_mul (nb_neg (by norm_num)) hrN) 5) (nb_div (nb_mul (by norm_num) (by simp)) 5))
      _ ≤ 3 := by norm_num
  have c7 : ‖(((3 / 5) - (((3 * r) * Complex.I) / 5)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((3 / 5) - (((3 * r) * Complex.I) / 5)) : ℂ)‖ ≤ ((3/5)+(((3*2)*1)/5)) := (nb_sub (nb_div (by norm_num) 5) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 5))
      _ ≤ 2 := by norm_num
  have c8 : ‖((((18 * y4) * y5) / 5) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((((18 * y4) * y5) / 5) : ℂ)‖ ≤ (((18*1)*1)/5) := (nb_div (nb_mul (nb_mul (by norm_num) hNy4) hNy5) 5)
      _ ≤ 4 := by norm_num
  have c9 : ‖(((6 / 5) + (((6 * r) * Complex.I) / 5)) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖(((6 / 5) + (((6 * r) * Complex.I) / 5)) : ℂ)‖ ≤ ((6/5)+(((6*2)*1)/5)) := (nb_add (nb_div (by norm_num) 5) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 5))
      _ ≤ 4 := by norm_num
  have c10 : ‖(((-3) + ((3 * r) * Complex.I)) : ℂ)‖ ≤ (9 : ℝ) := by
    calc
      ‖(((-3) + ((3 * r) * Complex.I)) : ℂ)‖ ≤ (3+((3*2)*1)) := (nb_add (nb_neg (by norm_num)) (nb_mul (nb_mul (by norm_num) hrN) (by simp)))
      _ ≤ 9 := by norm_num
  have c11 : ‖((((-2) * r) * Complex.I) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((((-2) * r) * Complex.I) : ℂ)‖ ≤ ((2*2)*1) := (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) (by simp))
      _ ≤ 4 := by norm_num
  change ‖target‖ ≤ 70954652 * η
  rw [eid]
  calc
    _ ≤ ((((((((((((3 * (348 * η)) + (3 * (15225015 * η))) + (3 * (1 * η))) + (3 * (612 * η))) + (4 * (1200 * η))) + (3 * (588 * η))) + (3 * (3578 * η))) + (2 * (19559 * η))) + (4 * (25706 * η))) + (4 * (258040 * η))) + (9 * (891476 * η))) + (4 * (4015510 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg10) (nb_mul c1 pg48)) (nb_mul c2 pg4)) (nb_mul c3 pg11)) (nb_mul c4 pg12)) (nb_mul c5 pg13)) (nb_mul c6 pg15)) (nb_mul c7 pg16)) (nb_mul c8 pg24)) (nb_mul c9 pg29)) (nb_mul c10 pg36)) (nb_mul c11 pg42))
    _ = 70954652 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 53 by 629176076 times `η` under the
stated assumptions. -/
private theorem step53 (r x4 y1 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg43 : ‖(x4*y5^2*(3/8 + r*Complex.I/8) + r*Complex.I*y1*y5/2 + y3*y4*y5 + y3*(3/2 - r*Complex.I/2) + y5^3*(1/8 + r*Complex.I/8) : ℂ)‖ ≤ (8115294 : ℝ) * η)
    (pg50 : ‖(x4*y5^2 + y1*y5*(1 + r*Complex.I) + y3*(1 - r*Complex.I) + y5^3*(1/2 + r*Complex.I/6) : ℂ)‖ ≤ (78224073 : ℝ) * η)
    (pg52 : ‖(x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20) : ℂ)‖ ≤ (70954652 : ℝ) * η)
    : ‖(y1*y5*(-15/4 - 5*r*Complex.I/4) - r*Complex.I*y3/4 + y5^3 : ℂ)‖ ≤ (629176076 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y1*y5*(-15/4 - 5*r*Complex.I/4) - r*Complex.I*y3/4 + y5^3
  let clause43 : ℂ :=
      x4*y5^2*(3/8 + r*Complex.I/8) + r*Complex.I*y1*y5/2 + y3*y4*y5 + y3*(3/2 - r*Complex.I/2) + y5^3*(1/8 + r*Complex.I/8)
  let clause50 : ℂ :=
      x4*y5^2 + y1*y5*(1 + r*Complex.I) + y3*(1 - r*Complex.I) + y5^3*(1/2 + r*Complex.I/6)
  let clause52 : ℂ :=
      x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20)
  have eid : target = ((((((-5) / 4) + (((5 * r) * Complex.I) / 4)) * clause43) + ((y5 * ((5 / 4) - (((5 * r) * Complex.I) / 4))) * clause52)) + (((33 / 16) - (((11 * r) * Complex.I) / 16)) * clause50)) := by
    dsimp only [target, clause43, clause50, clause52]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-5) / 4) + (((5 * r) * Complex.I) / 4)) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((((-5) / 4) + (((5 * r) * Complex.I) / 4)) : ℂ)‖ ≤ ((5/4)+(((5*2)*1)/4)) := (nb_add (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 4))
      _ ≤ 4 := by norm_num
  have c1 : ‖((y5 * ((5 / 4) - (((5 * r) * Complex.I) / 4))) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖((y5 * ((5 / 4) - (((5 * r) * Complex.I) / 4))) : ℂ)‖ ≤ (1*((5/4)+(((5*2)*1)/4))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 4) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 4)))
      _ ≤ 4 := by norm_num
  have c2 : ‖(((33 / 16) - (((11 * r) * Complex.I) / 16)) : ℂ)‖ ≤ (4 : ℝ) := by
    calc
      ‖(((33 / 16) - (((11 * r) * Complex.I) / 16)) : ℂ)‖ ≤ ((33/16)+(((11*2)*1)/16)) := (nb_sub (nb_div (by norm_num) 16) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 16))
      _ ≤ 4 := by norm_num
  change ‖target‖ ≤ 629176076 * η
  rw [eid]
  calc
    _ ≤ (((4 * (8115294 * η)) + (4 * (70954652 * η))) + (4 * (78224073 * η))) := (nb_add (nb_add (nb_mul c0 pg43) (nb_mul c1 pg52)) (nb_mul c2 pg50))
    _ = 629176076 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 54 by 54177578 times `η` under the
stated assumptions. -/
private theorem step54 (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η)
    (pg6 : ‖(x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4 : ℂ)‖ ≤ (12 : ℝ) * η)
    (pg7 : ‖(x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3 : ℂ)‖ ≤ (24 : ℝ) * η)
    (pg9 : ‖(x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1 : ℂ)‖ ≤ (120 : ℝ) * η)
    (pg11 : ‖(x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3) : ℂ)‖ ≤ (612 : ℝ) * η)
    (pg12 : ‖(x1*y4 + x2*y5 + y3 : ℂ)‖ ≤ (1200 : ℝ) * η)
    (pg15 : ‖(x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2) : ℂ)‖ ≤ (3578 : ℝ) * η)
    (pg24 : ‖(x2 + y1*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (25706 : ℝ) * η)
    (pg27 : ‖(x1 + y2*(1/2 - r*Complex.I/2) : ℂ)‖ ≤ (83755 : ℝ) * η)
    (pg46 : ‖(y1*y3*y5 + y2*y5^2*(4/7 + 4*r*Complex.I/7) + y3^2*(-2/7 - 2*r*Complex.I/7) + 6*y4*y5/7 + 3/2 - r*Complex.I/2 : ℂ)‖ ≤ (8577774 : ℝ) * η)
    (pg47 : ‖(y2*y5^2 + 5*y3^2/4 + y4*y5*(-1/2 + r*Complex.I/2) : ℂ)‖ ≤ (21682006 : ℝ) * η)
    (pg48 : ‖(x3*y5 - 2*r*Complex.I*y3*y5/3 : ℂ)‖ ≤ (15225015 : ℝ) * η)
    : ‖(y3^2 + y4*y5*(-3/7 + 3*r*Complex.I/7) + 4*r*Complex.I/7 : ℂ)‖ ≤ (54177578 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y3^2 + y4*y5*(-3/7 + 3*r*Complex.I/7) + 4*r*Complex.I/7
  let g4 : ℂ := x5*y5 - 1
  let g6 : ℂ :=
      x1*y2 + x1*y4*(1/2 - r*Complex.I/2) + x1*y5 + x2*y3 + x2*y5*(1/2 - r*Complex.I/2) + x2 + x3*y1 + x3*y4 + x3*(1/2 - r*Complex.I/2) + x4*y1*(1/2 - r*Complex.I/2) + x4*y2 + x4*y5 + x5*y2*(1/2 - r*Complex.I/2) + x5*y3 + x5 + y1 + y3*(1/2 - r*Complex.I/2) + y4
  let g7 : ℂ := x1*y4 + x2*y5 + x3 + x4*y1 + x5*y2 + y3
  let g9 : ℂ := x1*y2 + x2 + x3*y4 + x4*y5 + x5*y3 + y1
  let clause11 : ℂ :=
      x1*y4*(-1 + r*Complex.I/3) - r*Complex.I*x1*y5/3 + x2*y3*(1/2 + r*Complex.I/6) + x2*y5*(-1 + r*Complex.I/3) + x2*(r/2 - Complex.I/2) - Complex.I*x3*y4 + x4*y2 + x5*y3*(r/2 - Complex.I/2) + x5*(1/2 - r*Complex.I/2) - Complex.I*y1 + y3*(-1 + r*Complex.I/3) + y4*(1 - r*Complex.I/3)
  let clause12 : ℂ := x1*y4 + x2*y5 + y3
  let walkGoal : ℂ := x2*y5*(1/2 + r*Complex.I/2) + x3*y4*y5 + y1*y5 + y3*(1/2 + r*Complex.I/2)
  let clause24 : ℂ := x2 + y1*(1/2 - r*Complex.I/2)
  let clause27 : ℂ := x1 + y2*(1/2 - r*Complex.I/2)
  let clause46 : ℂ :=
      y1*y3*y5 + y2*y5^2*(4/7 + 4*r*Complex.I/7) + y3^2*(-2/7 - 2*r*Complex.I/7) + 6*y4*y5/7 + 3/2 - r*Complex.I/2
  let clause47 : ℂ := y2*y5^2 + 5*y3^2/4 + y4*y5*(-1/2 + r*Complex.I/2)
  let clause48 : ℂ := x3*y5 - 2*r*Complex.I*y3*y5/3
  have eid : target = (((((((((((((y5 * (((-3) / 7) - ((r * Complex.I) / 7))) * g6) + ((y1 * ((3 / 7) + ((r * Complex.I) / 7))) * clause48)) + ((((((-2) * r) * y3) / 7) + (((2 * r) * Complex.I) / 7)) * g4)) + ((y5 * ((3 / 7) - ((r * Complex.I) / 7))) * g7)) + ((y5 * ((3 / 7) + ((r * Complex.I) / 7))) * g9)) + ((y5 * ((3 / 7) + ((r * Complex.I) / 7))) * clause11)) + (((4 * y5) / 7) * clause12)) + ((((-r) / 7) + ((3 * Complex.I) / 7)) * walkGoal)) + ((((2 * y3) * y5) / 7) * clause24)) + (((y5 ^ 2) * ((2 / 7) + (((2 * r) * Complex.I) / 7))) * clause27)) + ((((-3) / 7) + (((3 * r) * Complex.I) / 7)) * clause46)) + ((20 / 49) * clause47)) := by
    dsimp only [target, g4, g6, g7, g9, clause11, clause12, walkGoal, clause24, clause27, clause46,
        clause47, clause48]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((y5 * (((-3) / 7) - ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * (((-3) / 7) - ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1*((3/7)+((2*1)/7))) := (nb_mul hNy5 (nb_sub (nb_div (nb_neg (by norm_num)) 7) (nb_div (nb_mul hrN (by simp)) 7)))
      _ ≤ 1 := by norm_num
  have c1 : ‖((y1 * ((3 / 7) + ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y1 * ((3 / 7) + ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1*((3/7)+((2*1)/7))) := (nb_mul hNy1 (nb_add (nb_div (by norm_num) 7) (nb_div (nb_mul hrN (by simp)) 7)))
      _ ≤ 1 := by norm_num
  have c2 : ‖((((((-2) * r) * y3) / 7) + (((2 * r) * Complex.I) / 7)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((((-2) * r) * y3) / 7) + (((2 * r) * Complex.I) / 7)) : ℂ)‖ ≤ ((((2*2)*1)/7)+(((2*2)*1)/7)) := (nb_add (nb_div (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) hNy3) 7) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7))
      _ ≤ 2 := by norm_num
  have c3 : ‖((y5 * ((3 / 7) - ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((3 / 7) - ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1*((3/7)+((2*1)/7))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 7) (nb_div (nb_mul hrN (by simp)) 7)))
      _ ≤ 1 := by norm_num
  have c4 : ‖((y5 * ((3 / 7) + ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((3 / 7) + ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1*((3/7)+((2*1)/7))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 7) (nb_div (nb_mul hrN (by simp)) 7)))
      _ ≤ 1 := by norm_num
  have c5 : ‖((y5 * ((3 / 7) + ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((3 / 7) + ((r * Complex.I) / 7))) : ℂ)‖ ≤ (1*((3/7)+((2*1)/7))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 7) (nb_div (nb_mul hrN (by simp)) 7)))
      _ ≤ 1 := by norm_num
  have c6 : ‖(((4 * y5) / 7) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((4 * y5) / 7) : ℂ)‖ ≤ ((4*1)/7) := (nb_div (nb_mul (by norm_num) hNy5) 7)
      _ ≤ 1 := by norm_num
  have c7 : ‖((((-r) / 7) + ((3 * Complex.I) / 7)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-r) / 7) + ((3 * Complex.I) / 7)) : ℂ)‖ ≤ ((2/7)+((3*1)/7)) := (nb_add (nb_div (nb_neg hrN) 7) (nb_div (nb_mul (by norm_num) (by simp)) 7))
      _ ≤ 1 := by norm_num
  have c8 : ‖((((2 * y3) * y5) / 7) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((2 * y3) * y5) / 7) : ℂ)‖ ≤ (((2*1)*1)/7) := (nb_div (nb_mul (nb_mul (by norm_num) hNy3) hNy5) 7)
      _ ≤ 1 := by norm_num
  have c9 : ‖(((y5 ^ 2) * ((2 / 7) + (((2 * r) * Complex.I) / 7))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((y5 ^ 2) * ((2 / 7) + (((2 * r) * Complex.I) / 7))) : ℂ)‖ ≤ ((1^2)*((2/7)+(((2*2)*1)/7))) := (nb_mul (nb_pow hNy5 2) (nb_add (nb_div (by norm_num) 7) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7)))
      _ ≤ 1 := by norm_num
  have c10 : ‖((((-3) / 7) + (((3 * r) * Complex.I) / 7)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-3) / 7) + (((3 * r) * Complex.I) / 7)) : ℂ)‖ ≤ ((3/7)+(((3*2)*1)/7)) := (nb_add (nb_div (nb_neg (by norm_num)) 7) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 7))
      _ ≤ 2 := by norm_num
  have c11 : ‖((20 / 49) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((20 / 49) : ℂ)‖ ≤ (20/49) := (nb_div (by norm_num) 49)
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 54177578 * η
  rw [eid]
  calc
    _ ≤ ((((((((((((1 * (12 * η)) + (1 * (15225015 * η))) + (2 * (1 * η))) + (1 * (24 * η))) + (1 * (120 * η))) + (1 * (612 * η))) + (1 * (1200 * η))) + (1 * (3578 * η))) + (1 * (25706 * η))) + (1 * (83755 * η))) + (2 * (8577774 * η))) + (1 * (21682006 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg6) (nb_mul c1 pg48)) (nb_mul c2 pg4)) (nb_mul c3 pg7)) (nb_mul c4 pg9)) (nb_mul c5 pg11)) (nb_mul c6 pg12)) (nb_mul c7 pg15)) (nb_mul c8 pg24)) (nb_mul c9 pg27)) (nb_mul c10 pg46)) (nb_mul c11 pg47))
    _ = 54177578 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 55 by 288049639 times `η` under the
stated assumptions. -/
private theorem step55 (r y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg44 : ‖(y1*y4*(3/4 - r*Complex.I/4) + r*Complex.I*y2*y3 + y3^2*y5 + y4*y5^2*(1/8 - r*Complex.I/8) + 7*r*Complex.I*y5/4 : ℂ)‖ ≤ (22535283 : ℝ) * η)
    (pg51 : ‖(y1*y4*(3 + r*Complex.I) + y2*y3*(-6 + 2*r*Complex.I) + y4*y5^2 + y5*(-15/2 + 5*r*Complex.I/2) : ℂ)‖ ≤ (211336778 : ℝ) * η)
    (pg54 : ‖(y3^2 + y4*y5*(-3/7 + 3*r*Complex.I/7) + 4*r*Complex.I/7 : ℂ)‖ ≤ (54177578 : ℝ) * η)
    : ‖(y1*y4*(-1/4 - r*Complex.I/4) + y2*y3 + 61*y5/48 : ℂ)‖ ≤ (288049639 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y1*y4*(-1/4 - r*Complex.I/4) + y2*y3 + 61*y5/48
  let clause44 : ℂ :=
      y1*y4*(3/4 - r*Complex.I/4) + r*Complex.I*y2*y3 + y3^2*y5 + y4*y5^2*(1/8 - r*Complex.I/8) + 7*r*Complex.I*y5/4
  let clause51 : ℂ :=
      y1*y4*(3 + r*Complex.I) + y2*y3*(-6 + 2*r*Complex.I) + y4*y5^2 + y5*(-15/2 + 5*r*Complex.I/2)
  let clause54 : ℂ := y3^2 + y4*y5*(-3/7 + 3*r*Complex.I/7) + 4*r*Complex.I/7
  have eid : target = ((((((7 * r) * Complex.I) / 72) * clause44) + ((((((-7) * r) * Complex.I) * y5) / 72) * clause54)) + ((((-31) / 192) - (((31 * r) * Complex.I) / 576)) * clause51)) := by
    dsimp only [target, clause44, clause51, clause54]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((7 * r) * Complex.I) / 72) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((7 * r) * Complex.I) / 72) : ℂ)‖ ≤ (((7*2)*1)/72) := (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 72)
      _ ≤ 1 := by norm_num
  have c1 : ‖((((((-7) * r) * Complex.I) * y5) / 72) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((((-7) * r) * Complex.I) * y5) / 72) : ℂ)‖ ≤ ((((7*2)*1)*1)/72) := (nb_div (nb_mul (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) (by simp)) hNy5) 72)
      _ ≤ 1 := by norm_num
  have c2 : ‖((((-31) / 192) - (((31 * r) * Complex.I) / 576)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-31) / 192) - (((31 * r) * Complex.I) / 576)) : ℂ)‖ ≤ ((31/192)+(((31*2)*1)/576)) := (nb_sub (nb_div (nb_neg (by norm_num)) 192) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 576))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 288049639 * η
  rw [eid]
  calc
    _ ≤ (((1 * (22535283 * η)) + (1 * (54177578 * η))) + (1 * (211336778 * η))) := (nb_add (nb_add (nb_mul c0 pg44) (nb_mul c1 pg54)) (nb_mul c2 pg51))
    _ = 288049639 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 56 by 652476996 times `η` under the
stated assumptions. -/
private theorem step56 (r x3 x4 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg29 : ‖(x4*y5*(-3/2 + r*Complex.I/2) + y1*y4*y5*(-1/2 - r*Complex.I/2) + y1*(-3/2 - r*Complex.I/2) + y2*y3*y5 - 2*y5^2 : ℂ)‖ ≤ (258040 : ℝ) * η)
    (pg36 : ‖(x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4) : ℂ)‖ ≤ (891476 : ℝ) * η)
    (pg42 : ‖(x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24) : ℂ)‖ ≤ (4015510 : ℝ) * η)
    (pg52 : ‖(x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20) : ℂ)‖ ≤ (70954652 : ℝ) * η)
    (pg55 : ‖(y1*y4*(-1/4 - r*Complex.I/4) + y2*y3 + 61*y5/48 : ℂ)‖ ≤ (288049639 : ℝ) * η)
    : ‖(x4*y5 + y1*(7/12 + 7*r*Complex.I/12) + y5^2*(617/288 + 617*r*Complex.I/864) : ℂ)‖ ≤ (652476996 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := x4*y5 + y1*(7/12 + 7*r*Complex.I/12) + y5^2*(617/288 + 617*r*Complex.I/864)
  let clause29 : ℂ :=
      x4*y5*(-3/2 + r*Complex.I/2) + y1*y4*y5*(-1/2 - r*Complex.I/2) + y1*(-3/2 - r*Complex.I/2) + y2*y3*y5 - 2*y5^2
  let clause36 : ℂ :=
      x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4)
  let clause42 : ℂ :=
      x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24)
  let clause52 : ℂ :=
      x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20)
  let clause55 : ℂ := y1*y4*(-1/4 - r*Complex.I/4) + y2*y3 + 61*y5/48
  have eid : target = ((((((((-5) / 6) - (((5 * r) * Complex.I) / 18)) * clause29) + ((y5 * ((5 / 6) + (((5 * r) * Complex.I) / 18))) * clause55)) + (((((-5) * r) * Complex.I) / 18) * clause36)) + (((5 / 36) + (((5 * r) * Complex.I) / 36)) * clause42)) + (((5 / 72) - (((5 * r) * Complex.I) / 216)) * clause52)) := by
    dsimp only [target, clause29, clause36, clause42, clause52, clause55]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-5) / 6) - (((5 * r) * Complex.I) / 18)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-5) / 6) - (((5 * r) * Complex.I) / 18)) : ℂ)‖ ≤ ((5/6)+(((5*2)*1)/18)) := (nb_sub (nb_div (nb_neg (by norm_num)) 6) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 18))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y5 * ((5 / 6) + (((5 * r) * Complex.I) / 18))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y5 * ((5 / 6) + (((5 * r) * Complex.I) / 18))) : ℂ)‖ ≤ (1*((5/6)+(((5*2)*1)/18))) := (nb_mul hNy5 (nb_add (nb_div (by norm_num) 6) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 18)))
      _ ≤ 2 := by norm_num
  have c2 : ‖(((((-5) * r) * Complex.I) / 18) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((-5) * r) * Complex.I) / 18) : ℂ)‖ ≤ (((5*2)*1)/18) := (nb_div (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) (by simp)) 18)
      _ ≤ 1 := by norm_num
  have c3 : ‖(((5 / 36) + (((5 * r) * Complex.I) / 36)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((5 / 36) + (((5 * r) * Complex.I) / 36)) : ℂ)‖ ≤ ((5/36)+(((5*2)*1)/36)) := (nb_add (nb_div (by norm_num) 36) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 36))
      _ ≤ 1 := by norm_num
  have c4 : ‖(((5 / 72) - (((5 * r) * Complex.I) / 216)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((5 / 72) - (((5 * r) * Complex.I) / 216)) : ℂ)‖ ≤ ((5/72)+(((5*2)*1)/216)) := (nb_sub (nb_div (by norm_num) 72) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 216))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 652476996 * η
  rw [eid]
  calc
    _ ≤ (((((2 * (258040 * η)) + (2 * (288049639 * η))) + (1 * (891476 * η))) + (1 * (4015510 * η))) + (1 * (70954652 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg29) (nb_mul c1 pg55)) (nb_mul c2 pg36)) (nb_mul c3 pg42)) (nb_mul c4 pg52))
    _ = 652476996 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 57 by 1359877145 times `η` under the
stated assumptions. -/
private theorem step57 (r x4 y1 y3 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg50 : ‖(x4*y5^2 + y1*y5*(1 + r*Complex.I) + y3*(1 - r*Complex.I) + y5^3*(1/2 + r*Complex.I/6) : ℂ)‖ ≤ (78224073 : ℝ) * η)
    (pg53 : ‖(y1*y5*(-15/4 - 5*r*Complex.I/4) - r*Complex.I*y3/4 + y5^3 : ℂ)‖ ≤ (629176076 : ℝ) * η)
    (pg56 : ‖(x4*y5 + y1*(7/12 + 7*r*Complex.I/12) + y5^2*(617/288 + 617*r*Complex.I/864) : ℂ)‖ ≤ (652476996 : ℝ) * η)
    : ‖(y1*y5 + y3*(13/68 + 13*r*Complex.I/68) : ℂ)‖ ≤ (1359877145 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y1*y5 + y3*(13/68 + 13*r*Complex.I/68)
  let clause50 : ℂ :=
      x4*y5^2 + y1*y5*(1 + r*Complex.I) + y3*(1 - r*Complex.I) + y5^3*(1/2 + r*Complex.I/6)
  let clause53 : ℂ := y1*y5*(-15/4 - 5*r*Complex.I/4) - r*Complex.I*y3/4 + y5^3
  let clause56 : ℂ := x4*y5 + y1*(7/12 + 7*r*Complex.I/12) + y5^2*(617/288 + 617*r*Complex.I/864)
  have eid : target = ((((((-144) / 2125) + (((144 * r) * Complex.I) / 2125)) * clause50) + ((y5 * ((144 / 2125) - (((144 * r) * Complex.I) / 2125))) * clause56)) + ((((-473) / 2125) + (((473 * r) * Complex.I) / 6375)) * clause53)) := by
    dsimp only [target, clause50, clause53, clause56]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-144) / 2125) + (((144 * r) * Complex.I) / 2125)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-144) / 2125) + (((144 * r) * Complex.I) / 2125)) : ℂ)‖ ≤ ((144/2125)+(((144*2)*1)/2125)) := (nb_add (nb_div (nb_neg (by norm_num)) 2125) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 2125))
      _ ≤ 1 := by norm_num
  have c1 : ‖((y5 * ((144 / 2125) - (((144 * r) * Complex.I) / 2125))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y5 * ((144 / 2125) - (((144 * r) * Complex.I) / 2125))) : ℂ)‖ ≤ (1*((144/2125)+(((144*2)*1)/2125))) := (nb_mul hNy5 (nb_sub (nb_div (by norm_num) 2125) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 2125)))
      _ ≤ 1 := by norm_num
  have c2 : ‖((((-473) / 2125) + (((473 * r) * Complex.I) / 6375)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-473) / 2125) + (((473 * r) * Complex.I) / 6375)) : ℂ)‖ ≤ ((473/2125)+(((473*2)*1)/6375)) := (nb_add (nb_div (nb_neg (by norm_num)) 2125) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 6375))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 1359877145 * η
  rw [eid]
  calc
    _ ≤ (((1 * (78224073 * η)) + (1 * (652476996 * η))) + (1 * (629176076 * η))) := (nb_add (nb_add (nb_mul c0 pg50) (nb_mul c1 pg56)) (nb_mul c2 pg53))
    _ = 1359877145 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 60 by 2088215779 times `η` under the
stated assumptions. -/
private theorem step60 (r x3 x4 y1 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy4 : ‖y4‖ ≤ 1)
    (pg36 : ‖(x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4) : ℂ)‖ ≤ (891476 : ℝ) * η)
    (pg42 : ‖(x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24) : ℂ)‖ ≤ (4015510 : ℝ) * η)
    (pg52 : ‖(x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20) : ℂ)‖ ≤ (70954652 : ℝ) * η)
    (pg56 : ‖(x4*y5 + y1*(7/12 + 7*r*Complex.I/12) + y5^2*(617/288 + 617*r*Complex.I/864) : ℂ)‖ ≤ (652476996 : ℝ) * η)
    (pg57 : ‖(y1*y5 + y3*(13/68 + 13*r*Complex.I/68) : ℂ)‖ ≤ (1359877145 : ℝ) * η)
    : ‖(y1*(-2124/25043 - 708*r*Complex.I/25043) + y5^2 : ℂ)‖ ≤ (2088215779 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y1*(-2124/25043 - 708*r*Complex.I/25043) + y5^2
  let clause36 : ℂ :=
      x3*y4*(1/2 - r*Complex.I/6) - 5*r*Complex.I*x4*y5/6 + y1*y4*y5 + y1*(3/4 - r*Complex.I/4) + y3*y4*(-1/4 - r*Complex.I/4) + y5^2*(3/4 - 3*r*Complex.I/4)
  let clause42 : ℂ :=
      x3*y4 + x4*y5*(1/8 - r*Complex.I/8) + y1/2 - r*Complex.I*y3*y4/3 + y5^2*(1/8 - r*Complex.I/24)
  let clause52 : ℂ :=
      x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20)
  let clause56 : ℂ := x4*y5 + y1*(7/12 + 7*r*Complex.I/12) + y5^2*(617/288 + 617*r*Complex.I/864)
  let clause57 : ℂ := y1*y5 + y3*(13/68 + 13*r*Complex.I/68)
  have eid : target = ((((((((-4896) / 25043) - (((4896 * r) * Complex.I) / 25043)) * clause36) + ((y4 * ((4896 / 25043) + (((4896 * r) * Complex.I) / 25043))) * clause57)) + (((4896 / 25043) + (((1632 * r) * Complex.I) / 25043)) * clause42)) + (((2688 / 25043) - (((2688 * r) * Complex.I) / 25043)) * clause52)) + (((67176 / 125215) - (((22392 * r) * Complex.I) / 125215)) * clause56)) := by
    dsimp only [target, clause36, clause42, clause52, clause56, clause57]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-4896) / 25043) - (((4896 * r) * Complex.I) / 25043)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-4896) / 25043) - (((4896 * r) * Complex.I) / 25043)) : ℂ)‖ ≤ ((4896/25043)+(((4896*2)*1)/25043)) := (nb_sub (nb_div (nb_neg (by norm_num)) 25043) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 25043))
      _ ≤ 1 := by norm_num
  have c1 : ‖((y4 * ((4896 / 25043) + (((4896 * r) * Complex.I) / 25043))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y4 * ((4896 / 25043) + (((4896 * r) * Complex.I) / 25043))) : ℂ)‖ ≤ (1*((4896/25043)+(((4896*2)*1)/25043))) := (nb_mul hNy4 (nb_add (nb_div (by norm_num) 25043) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 25043)))
      _ ≤ 1 := by norm_num
  have c2 : ‖(((4896 / 25043) + (((1632 * r) * Complex.I) / 25043)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((4896 / 25043) + (((1632 * r) * Complex.I) / 25043)) : ℂ)‖ ≤ ((4896/25043)+(((1632*2)*1)/25043)) := (nb_add (nb_div (by norm_num) 25043) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 25043))
      _ ≤ 1 := by norm_num
  have c3 : ‖(((2688 / 25043) - (((2688 * r) * Complex.I) / 25043)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((2688 / 25043) - (((2688 * r) * Complex.I) / 25043)) : ℂ)‖ ≤ ((2688/25043)+(((2688*2)*1)/25043)) := (nb_sub (nb_div (by norm_num) 25043) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 25043))
      _ ≤ 1 := by norm_num
  have c4 : ‖(((67176 / 125215) - (((22392 * r) * Complex.I) / 125215)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((67176 / 125215) - (((22392 * r) * Complex.I) / 125215)) : ℂ)‖ ≤ ((67176/125215)+(((22392*2)*1)/125215)) := (nb_sub (nb_div (by norm_num) 125215) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 125215))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 2088215779 * η
  rw [eid]
  calc
    _ ≤ (((((1 * (891476 * η)) + (1 * (1359877145 * η))) + (1 * (4015510 * η))) + (1 * (70954652 * η))) + (1 * (652476996 * η))) := (nb_add (nb_add (nb_add (nb_add (nb_mul c0 pg36) (nb_mul c1 pg57)) (nb_mul c2 pg42)) (nb_mul c3 pg52)) (nb_mul c4 pg56))
    _ = 2088215779 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the norm of `y3` by 10876654725 times `η` under the stated assumptions. -/
private theorem step61 (r y1 y3 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy5 : ‖y5‖ ≤ 1)
    (pg53 : ‖(y1*y5*(-15/4 - 5*r*Complex.I/4) - r*Complex.I*y3/4 + y5^3 : ℂ)‖ ≤ (629176076 : ℝ) * η)
    (pg57 : ‖(y1*y5 + y3*(13/68 + 13*r*Complex.I/68) : ℂ)‖ ≤ (1359877145 : ℝ) * η)
    (pg60 : ‖(y1*(-2124/25043 - 708*r*Complex.I/25043) + y5^2 : ℂ)‖ ≤ (2088215779 : ℝ) * η)
    : ‖(y3 : ℂ)‖ ≤ (10876654725 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y3
  let clause53 : ℂ := y1*y5*(-15/4 - 5*r*Complex.I/4) - r*Complex.I*y3/4 + y5^3
  let clause57 : ℂ := y1*y5 + y3*(13/68 + 13*r*Complex.I/68)
  let clause60 : ℂ := y1*(-2124/25043 - 708*r*Complex.I/25043) + y5^2
  have eid : target = (((((((-25043) * r) * Complex.I) / 51408) * clause53) + (((((25043 * r) * Complex.I) * y5) / 51408) * clause60)) + (((7199 / 4032) - (((7199 * r) * Complex.I) / 4032)) * clause57)) := by
    dsimp only [target, clause53, clause57, clause60]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖(((((-25043) * r) * Complex.I) / 51408) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((-25043) * r) * Complex.I) / 51408) : ℂ)‖ ≤ (((25043*2)*1)/51408) := (nb_div (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) (by simp)) 51408)
      _ ≤ 1 := by norm_num
  have c1 : ‖(((((25043 * r) * Complex.I) * y5) / 51408) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((((25043 * r) * Complex.I) * y5) / 51408) : ℂ)‖ ≤ ((((25043*2)*1)*1)/51408) := (nb_div (nb_mul (nb_mul (nb_mul (by norm_num) hrN) (by simp)) hNy5) 51408)
      _ ≤ 1 := by norm_num
  have c2 : ‖(((7199 / 4032) - (((7199 * r) * Complex.I) / 4032)) : ℂ)‖ ≤ (6 : ℝ) := by
    calc
      ‖(((7199 / 4032) - (((7199 * r) * Complex.I) / 4032)) : ℂ)‖ ≤ ((7199/4032)+(((7199*2)*1)/4032)) := (nb_sub (nb_div (by norm_num) 4032) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 4032))
      _ ≤ 6 := by norm_num
  change ‖target‖ ≤ 10876654725 * η
  rw [eid]
  calc
    _ ≤ (((1 * (629176076 * η)) + (1 * (2088215779 * η))) + (6 * (1359877145 * η))) := (nb_add (nb_add (nb_mul c0 pg53) (nb_mul c1 pg60)) (nb_mul c2 pg57))
    _ = 10876654725 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the norm of `y1` by 13688302152 times `η` under the stated assumptions. -/
private theorem step62 (r x4 y1 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy4 : ‖y4‖ ≤ 1)
    (pg52 : ‖(x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20) : ℂ)‖ ≤ (70954652 : ℝ) * η)
    (pg56 : ‖(x4*y5 + y1*(7/12 + 7*r*Complex.I/12) + y5^2*(617/288 + 617*r*Complex.I/864) : ℂ)‖ ≤ (652476996 : ℝ) * η)
    (pg60 : ‖(y1*(-2124/25043 - 708*r*Complex.I/25043) + y5^2 : ℂ)‖ ≤ (2088215779 : ℝ) * η)
    (pg61 : ‖(y3 : ℂ)‖ ≤ (10876654725 : ℝ) * η)
    : ‖(y1 : ℂ)‖ ≤ (13688302152 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y1
  let clause52 : ℂ :=
      x4*y5*(-9/20 - 3*r*Complex.I/20) - 8*r*Complex.I*y1/5 + y3*y4 + y5^2*(1/20 + r*Complex.I/20)
  let clause56 : ℂ := x4*y5 + y1*(7/12 + 7*r*Complex.I/12) + y5^2*(617/288 + 617*r*Complex.I/864)
  let clause60 : ℂ := y1*(-2124/25043 - 708*r*Complex.I/25043) + y5^2
  let clause61 : ℂ := y3
  have eid : target = (((((((25043 * r) * Complex.I) / 88026) * clause52) + ((((((-25043) * r) * Complex.I) * y4) / 88026) * clause61)) + ((((-75129) / 586840) + (((75129 * r) * Complex.I) / 586840)) * clause56)) + (((3330719 / 5633664) - (((3330719 * r) * Complex.I) / 16900992)) * clause60)) := by
    dsimp only [target, clause52, clause56, clause60, clause61]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((25043 * r) * Complex.I) / 88026) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((25043 * r) * Complex.I) / 88026) : ℂ)‖ ≤ (((25043*2)*1)/88026) := (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 88026)
      _ ≤ 1 := by norm_num
  have c1 : ‖((((((-25043) * r) * Complex.I) * y4) / 88026) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((((-25043) * r) * Complex.I) * y4) / 88026) : ℂ)‖ ≤ ((((25043*2)*1)*1)/88026) := (nb_div (nb_mul (nb_mul (nb_mul (nb_neg (by norm_num)) hrN) (by simp)) hNy4) 88026)
      _ ≤ 1 := by norm_num
  have c2 : ‖((((-75129) / 586840) + (((75129 * r) * Complex.I) / 586840)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-75129) / 586840) + (((75129 * r) * Complex.I) / 586840)) : ℂ)‖ ≤ ((75129/586840)+(((75129*2)*1)/586840)) := (nb_add (nb_div (nb_neg (by norm_num)) 586840) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 586840))
      _ ≤ 1 := by norm_num
  have c3 : ‖(((3330719 / 5633664) - (((3330719 * r) * Complex.I) / 16900992)) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖(((3330719 / 5633664) - (((3330719 * r) * Complex.I) / 16900992)) : ℂ)‖ ≤ ((3330719/5633664)+(((3330719*2)*1)/16900992)) := (nb_sub (nb_div (by norm_num) 5633664) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 16900992))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 13688302152 * η
  rw [eid]
  calc
    _ ≤ ((((1 * (70954652 * η)) + (1 * (10876654725 * η))) + (1 * (652476996 * η))) + (1 * (2088215779 * η))) := (nb_add (nb_add (nb_add (nb_mul c0 pg52) (nb_mul c1 pg61)) (nb_mul c2 pg56)) (nb_mul c3 pg60))
    _ = 13688302152 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the residual polynomial norm at certificate step 63 by 21861664606 times `η` under
the stated assumptions. -/
private theorem step63 (r y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy3 : ‖y3‖ ≤ 1)
    (pg54 : ‖(y3^2 + y4*y5*(-3/7 + 3*r*Complex.I/7) + 4*r*Complex.I/7 : ℂ)‖ ≤ (54177578 : ℝ) * η)
    (pg61 : ‖(y3 : ℂ)‖ ≤ (10876654725 : ℝ) * η)
    : ‖(y4*y5 + 1 - r*Complex.I/3 : ℂ)‖ ≤ (21861664606 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := y4*y5 + 1 - r*Complex.I/3
  let clause54 : ℂ := y3^2 + y4*y5*(-3/7 + 3*r*Complex.I/7) + 4*r*Complex.I/7
  let clause61 : ℂ := y3
  have eid : target = (((((-7) / 12) - (((7 * r) * Complex.I) / 12)) * clause54) + ((y3 * ((7 / 12) + (((7 * r) * Complex.I) / 12))) * clause61)) := by
    dsimp only [target, clause54, clause61]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
    ring
  have c0 : ‖((((-7) / 12) - (((7 * r) * Complex.I) / 12)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((((-7) / 12) - (((7 * r) * Complex.I) / 12)) : ℂ)‖ ≤ ((7/12)+(((7*2)*1)/12)) := (nb_sub (nb_div (nb_neg (by norm_num)) 12) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 12))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y3 * ((7 / 12) + (((7 * r) * Complex.I) / 12))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y3 * ((7 / 12) + (((7 * r) * Complex.I) / 12))) : ℂ)‖ ≤ (1*((7/12)+(((7*2)*1)/12))) := (nb_mul hNy3 (nb_add (nb_div (by norm_num) 12) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 12)))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 21861664606 * η
  rw [eid]
  calc
    _ ≤ ((2 * (54177578 * η)) + (2 * (10876654725 * η))) := (nb_add (nb_mul c0 pg54) (nb_mul c1 pg61))
    _ = 21861664606 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the norm of `y5` by 24853006516 times `η` under the stated assumptions. -/
private theorem step64 (r y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hrN : ‖r‖ ≤ 2)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (pg55 : ‖(y1*y4*(-1/4 - r*Complex.I/4) + y2*y3 + 61*y5/48 : ℂ)‖ ≤ (288049639 : ℝ) * η)
    (pg61 : ‖(y3 : ℂ)‖ ≤ (10876654725 : ℝ) * η)
    (pg62 : ‖(y1 : ℂ)‖ ≤ (13688302152 : ℝ) * η)
    : ‖(y5 : ℂ)‖ ≤ (24853006516 : ℝ) * η := by
  let target : ℂ := y5
  let clause55 : ℂ := y1*y4*(-1/4 - r*Complex.I/4) + y2*y3 + 61*y5/48
  let clause61 : ℂ := y3
  let clause62 : ℂ := y1
  have eid : target = ((((48 / 61) * clause55) + ((((-48) * y2) / 61) * clause61)) + ((y4 * ((12 / 61) + (((12 * r) * Complex.I) / 61))) * clause62)) := by
    dsimp only [target, clause55, clause61, clause62]
    ring_nf
  have c0 : ‖((48 / 61) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((48 / 61) : ℂ)‖ ≤ (48/61) := (nb_div (by norm_num) 61)
      _ ≤ 1 := by norm_num
  have c1 : ‖((((-48) * y2) / 61) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((((-48) * y2) / 61) : ℂ)‖ ≤ ((48*1)/61) := (nb_div (nb_mul (nb_neg (by norm_num)) hNy2) 61)
      _ ≤ 1 := by norm_num
  have c2 : ‖((y4 * ((12 / 61) + (((12 * r) * Complex.I) / 61))) : ℂ)‖ ≤ (1 : ℝ) := by
    calc
      ‖((y4 * ((12 / 61) + (((12 * r) * Complex.I) / 61))) : ℂ)‖ ≤ (1*((12/61)+(((12*2)*1)/61))) := (nb_mul hNy4 (nb_add (nb_div (by norm_num) 61) (nb_div (nb_mul (nb_mul (by norm_num) hrN) (by simp)) 61)))
      _ ≤ 1 := by norm_num
  change ‖target‖ ≤ 24853006516 * η
  rw [eid]
  calc
    _ ≤ (((1 * (288049639 * η)) + (1 * (10876654725 * η))) + (1 * (13688302152 * η))) := (nb_add (nb_add (nb_mul c0 pg55) (nb_mul c1 pg61)) (nb_mul c2 pg62))
    _ = 24853006516 * η := by ring

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in

/-- Bounds the norm of the complex unit by 93429342244 times `η` under the stated assumptions. -/
private theorem step65 (r y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3)
    (hrN : ‖r‖ ≤ 2)
    (hNy4 : ‖y4‖ ≤ 1)
    (pg63 : ‖(y4*y5 + 1 - r*Complex.I/3 : ℂ)‖ ≤ (21861664606 : ℝ) * η)
    (pg64 : ‖(y5 : ℂ)‖ ≤ (24853006516 : ℝ) * η)
    : ‖((1 : ℂ) : ℂ)‖ ≤ (93429342244 : ℝ) * η := by
  have hr3 : r ^ 3 = 3 * r := by
    calc r ^ 3 = r ^ 2 * r := by ring
         _ = 3 * r := by rw [hr]
  let target : ℂ := (1 : ℂ)
  let clause63 : ℂ := y4*y5 + 1 - r*Complex.I/3
  let clause64 : ℂ := y5
  have eid : target = ((((3 / 4) + ((r * Complex.I) / 4)) * clause63) + ((y4 * (((-3) / 4) - ((r * Complex.I) / 4))) * clause64)) := by
    dsimp only [target, clause63, clause64]
    ring_nf
    norm_num [hr, hr3, Complex.I_sq]
  have c0 : ‖(((3 / 4) + ((r * Complex.I) / 4)) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖(((3 / 4) + ((r * Complex.I) / 4)) : ℂ)‖ ≤ ((3/4)+((2*1)/4)) := (nb_add (nb_div (by norm_num) 4) (nb_div (nb_mul hrN (by simp)) 4))
      _ ≤ 2 := by norm_num
  have c1 : ‖((y4 * (((-3) / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (2 : ℝ) := by
    calc
      ‖((y4 * (((-3) / 4) - ((r * Complex.I) / 4))) : ℂ)‖ ≤ (1*((3/4)+((2*1)/4))) := (nb_mul hNy4 (nb_sub (nb_div (nb_neg (by norm_num)) 4) (nb_div (nb_mul hrN (by simp)) 4)))
      _ ≤ 2 := by norm_num
  change ‖target‖ ≤ 93429342244 * η
  rw [eid]
  calc
    _ ≤ ((2 * (21861664606 * η)) + (2 * (24853006516 * η))) := (nb_add (nb_mul c0 pg63) (nb_mul c1 pg64))
    _ = 93429342244 * η := by ring

/-- The canonical polynomial residual bounds force one to be at most 93429342244 times `η` under
the stated root and coordinate norm constraints. -/
theorem certificate_barrier (r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 : ℂ) (η : ℝ)
    (hr : r ^ 2 = 3) (hrN : ‖r‖ ≤ 2)
    (hNx2 : ‖x2‖ ≤ 1)
    (hNx3 : ‖x3‖ ≤ 1)
    (hNx4 : ‖x4‖ ≤ 1)
    (hNx5 : ‖x5‖ ≤ 1)
    (hNy1 : ‖y1‖ ≤ 1)
    (hNy2 : ‖y2‖ ≤ 1)
    (hNy3 : ‖y3‖ ≤ 1)
    (hNy4 : ‖y4‖ ≤ 1)
    (hNy5 : ‖y5‖ ≤ 1)
    (h0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ η)
    (h1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ η)
    (h2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ η)
    (h3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ η)
    (h4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ η)
    (h5 : ‖((x1 + x2 + x3 + x4 + x5 + 1) * (y1 + y2 + y3 + y4 + y5 + 1) - 6 : ℂ)‖ ≤ η)
    (h6 : ‖((x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 + r*Complex.I/2) + x3 + x4*(-1/2 - r*Complex.I/2) + x5*(-1/2 + r*Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 - r*Complex.I/2) + y3 + y4*(-1/2 + r*Complex.I/2) + y5*(-1/2 - r*Complex.I/2) + 1) - 6 : ℂ)‖ ≤ η)
    (h7 : ‖((x1*(-1/2 + r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) + x3 + x4*(-1/2 + r*Complex.I/2) + x5*(-1/2 - r*Complex.I/2) + 1) * (y1*(-1/2 - r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) + y3 + y4*(-1/2 - r*Complex.I/2) + y5*(-1/2 + r*Complex.I/2) + 1) - 6 : ℂ)‖ ≤ η)
    (h8 : ‖((x1 + x2 - x3 - x4 - x5 + 1) * (y1 + y2 - y3 - y4 - y5 + 1) - 6 : ℂ)‖ ≤ η)
    (h9 : ‖((x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 + r*Complex.I/2) - x3 + x4*(1/2 + r*Complex.I/2) + x5*(1/2 - r*Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 - r*Complex.I/2) - y3 + y4*(1/2 - r*Complex.I/2) + y5*(1/2 + r*Complex.I/2) + 1) - 6 : ℂ)‖ ≤ η)
    (h10 : ‖((x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) - Complex.I*x3 + x4*(-r/2 + Complex.I/2) + x5*(-r/2 + Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) + Complex.I*y3 + y4*(-r/2 - Complex.I/2) + y5*(-r/2 - Complex.I/2) + 1) - 6 : ℂ)‖ ≤ η)
    (h11 : ‖((x1*(-1/2 + r*Complex.I/2) + x2 - Complex.I*x3 + x4*(r/2 + Complex.I/2) - Complex.I*x5 + 1) * (y1*(-1/2 - r*Complex.I/2) + y2 + Complex.I*y3 + y4*(r/2 - Complex.I/2) + Complex.I*y5 + 1) - 6 : ℂ)‖ ≤ η)
    (h12 : ‖((x1 + x2*(-1/2 + r*Complex.I/2) - Complex.I*x3 - Complex.I*x4 + x5*(r/2 + Complex.I/2) + 1) * (y1 + y2*(-1/2 - r*Complex.I/2) + Complex.I*y3 + Complex.I*y4 + y5*(r/2 - Complex.I/2) + 1) - 6 : ℂ)‖ ≤ η)
    (h13 : ‖((x1*(-1/2 - r*Complex.I/2) + x2*(-1/2 - r*Complex.I/2) + Complex.I*x3 + x4*(r/2 - Complex.I/2) + x5*(r/2 - Complex.I/2) + 1) * (y1*(-1/2 + r*Complex.I/2) + y2*(-1/2 + r*Complex.I/2) - Complex.I*y3 + y4*(r/2 + Complex.I/2) + y5*(r/2 + Complex.I/2) + 1) - 6 : ℂ)‖ ≤ η)
    (h14 : ‖((x1*(-1/2 + r*Complex.I/2) + x2 + Complex.I*x3 + x4*(-r/2 - Complex.I/2) + Complex.I*x5 + 1) * (y1*(-1/2 - r*Complex.I/2) + y2 - Complex.I*y3 + y4*(-r/2 + Complex.I/2) - Complex.I*y5 + 1) - 6 : ℂ)‖ ≤ η)
    : (1 : ℝ) ≤ 93429342244 * η := by
  have b0 : ‖(x1*y1 - 1 : ℂ)‖ ≤ (1 : ℝ) * η := by simpa only [one_mul] using h0
  have b1 : ‖(x2*y2 - 1 : ℂ)‖ ≤ (1 : ℝ) * η := by simpa only [one_mul] using h1
  have b2 : ‖(x3*y3 - 1 : ℂ)‖ ≤ (1 : ℝ) * η := by simpa only [one_mul] using h2
  have b3 : ‖(x4*y4 - 1 : ℂ)‖ ≤ (1 : ℝ) * η := by simpa only [one_mul] using h3
  have b4 : ‖(x5*y5 - 1 : ℂ)‖ ≤ (1 : ℝ) * η := by simpa only [one_mul] using h4
  have b5 := step5 x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η b0 b1 b2 b3 b4 (by simpa only [one_mul] using h5)
  have b6 :=
      step6 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN b0 b1 b2 b3 b4 b5
      (by simpa only [one_mul] using h6)
  have b7 :=
      step7 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN b0 b1 b2 b3 b4 b5 b6
      (by simpa only [one_mul] using h7)
  have b8 :=
      step8 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hrN b0 b1 b2 b3 b4 b5 b6 b7
      (by simpa only [one_mul] using h8)
  have b9 :=
      step9 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN b0 b1 b2 b3 b4 b5 b6 b7 b8
      (by simpa only [one_mul] using h9)
  have b10 :=
      step10 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN b0 b1 b2 b3 b4 b5 b6 b7 b8 b9
      (by simpa only [one_mul] using h10)
  have b11 :=
      step11 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
      (by simpa only [one_mul] using h11)
  have b12 :=
      step12 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11
      (by simpa only [one_mul] using h12)
  have b13 :=
      step13 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10
      (by simpa only [one_mul] using h13)
  have b14 :=
      step14 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b13
      (by simpa only [one_mul] using h14)
  have b15 := step15 r x2 x3 x5 y1 y3 y4 y5 η hr hrN hNy3 hNy5 b4 b14
  have b16 :=
      step16 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy1 hNy3 hNy5 b4 b8 b9 b10 b11 b12 b13 b15
  have b17 := step17 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy3 hNy4 b3 b12 b13 b14 b15
  have b18 := step18 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy2 hNy4 hNy5 b3 b11 b12 b14
  have b19 :=
      step19 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx4 hNy2 hNy5 b3 b4 b7 b12 b13 b14 b17
  have b20 :=
      step20 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx3 hNy2 hNy3 hNy4 hNy5 b2 b3 b4 b6 b7 b9 b10 b11 b12 b14 b17 b18
  have b22 := step22 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy2 hNy4 hNy5 b1 b3 b9 b12 b14
  have b24 :=
      step24 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx2 hNx5 hNy1 hNy4 b3 b4 b7 b12 b14 b17
  have b25 := step25 r x2 y1 y2 η hr hrN hNy2 b1 b24
  have b26 := step26 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy1 b5 b6 b7 b8 b9 b13 b14 b24
  have b27 := step27 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hrN hNx4 hNy2 hNy5 b4 b7 b12 b19 b24
  have b28 := step28 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy2 b9 b14 b27
  have b29 := step29 r x1 x2 x4 y1 y2 y3 y4 y5 η hr hrN hNy3 hNy4 hNy5 b16 b24 b27
  have b31 :=
      step31 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx3 hNy3 hNy4 hNy5 b4 b6 b7 b9 b11 b12 b15 b20 b24 b27
  have b32 := step32 r x2 x5 y1 y2 y3 y4 y5 η hr hrN hNy3 hNy4 hNy5 b18 b24
  have b33 :=
      step33 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy2 hNy3 hNy4 hNy5 b4 b9 b10 b11 b12 b13 b14 b15 b16 b24 b28
  have b34 :=
      step34 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy2 hNy3 hNy5 b2 b10 b11 b12 b13 b14 b18 b24 b27
  have b35 :=
      step35 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx2 hNx5 hNy1 hNy2 hNy3 hNy4 hNy5 b2 b3 b4 b5 b6 b7 b8 b9 b12 b13 b14 b17 b18 b24 b26 b27 b34
  have b36 :=
      step36 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy1 hNy3 hNy4 hNy5 b2 b6 b7 b9 b11 b12 b14 b16 b24 b33
  have b39 :=
      step39 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx2 hNx5 hNy1 hNy2 hNy4 hNy5 b3 b4 b6 b7 b9 b12 b14 b17 b18 b24 b25 b26 b28 b35
  have b41 := step41 r x2 x3 x5 y1 y2 y3 y4 y5 η hr hrN hNy3 hNy4 hNy5 b2 b14 b22 b24 b39
  have b42 :=
      step42 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx2 hNx5 hNy1 hNy2 hNy3 hNy4 hNy5 b4 b10 b11 b12 b13 b14 b15 b16 b17 b24 b28 b29 b36 b39
  have b43 := step43 r x2 x3 x4 y1 y3 y4 y5 η hr hrN hNy5 b15 b24 b42
  have b44 := step44 r x3 x4 y1 y2 y3 y4 y5 η hr hrN hNy4 hNy5 b3 b22 b41 b42
  have b46 :=
      step46 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx3 hNy2 hNy3 hNy4 hNy5 b3 b4 b6 b7 b9 b10 b11 b12 b14 b15 b17 b18 b20 b24 b25 b27 b42
  have b47 :=
      step47 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx3 hNy1 hNy2 hNy3 hNy4 hNy5 b3 b4 b6 b7 b8 b9 b10 b11 b12 b14 b15 b17 b18 b20 b24 b25 b27 b31 b39 b46
  have b48 :=
      step48 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNx2 hNx5 hNy1 hNy2 hNy4 hNy5 b3 b4 b6 b7 b9 b12 b14 b17 b18 b24 b26 b32 b35 b39 b42
  have b50 := step50 r x2 x3 x4 y1 y3 y4 y5 η hr hrN hNy4 hNy5 b15 b24 b43 b48
  have b51 := step51 r x3 y1 y2 y3 y4 y5 η hr hrN hNy3 hNy5 b2 b44 b48
  have b52 :=
      step52 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy2 hNy3 hNy4 hNy5 b4 b10 b11 b12 b13 b15 b16 b24 b29 b36 b42 b48
  have b53 := step53 r x4 y1 y3 y4 y5 η hr hrN hNy5 b43 b50 b52
  have b54 :=
      step54 r x1 x2 x3 x4 x5 y1 y2 y3 y4 y5 η hr hrN hNy1 hNy3 hNy5 b4 b6 b7 b9 b11 b12 b15 b24 b27 b46 b47 b48
  have b55 := step55 r y1 y2 y3 y4 y5 η hr hrN hNy5 b44 b51 b54
  have b56 := step56 r x3 x4 y1 y2 y3 y4 y5 η hr hrN hNy5 b29 b36 b42 b52 b55
  have b57 := step57 r x4 y1 y3 y5 η hr hrN hNy5 b50 b53 b56
  have b60 := step60 r x3 x4 y1 y3 y4 y5 η hr hrN hNy4 b36 b42 b52 b56 b57
  have b61 := step61 r y1 y3 y5 η hr hrN hNy5 b53 b57 b60
  have b62 := step62 r x4 y1 y3 y4 y5 η hr hrN hNy4 b52 b56 b60 b61
  have b63 := step63 r y3 y4 y5 η hr hrN hNy3 b54 b61
  have b64 := step64 r y1 y2 y3 y4 y5 η hrN hNy2 hNy4 b55 b61 b62
  have b65 := step65 r y4 y5 η hr hrN hNy4 b63 b64
  simpa only [norm_one] using b65

end Qatlib.Concepts.UnbiasedBases.T0Neighborhood
