/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.NativeArithmetic.SignedNatMachine.RationalDataSize
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.RedundantRational

abbrev Pair := ℕ × ℕ
namespace Pair

def value (x : Pair) : ℚ := (x.1 : ℚ) - x.2
def add (x y : Pair) : Pair := (x.1 + y.1, x.2 + y.2)
def neg (x : Pair) : Pair := (x.2, x.1)
def mul (x y : Pair) : Pair := (x.1 * y.1 + x.2 * y.2, x.1 * y.2 + x.2 * y.1)
def ofInt (n : ℤ) : Pair := (n.toNat, (-n).toNat)

theorem value_eq_zero (x : Pair) : value x = 0 ↔ x.1 = x.2 := by
    simp only [value, sub_eq_zero, Nat.cast_inj]

theorem value_add (x y : Pair) : value (add x y) = value x + value y := by simp [value, add]; ring

theorem value_neg (x : Pair) : value (neg x) = -value x := by dsimp [value, neg]; ring

theorem value_mul (x y : Pair) : value (mul x y) = value x * value y := by simp [value, mul]; ring

theorem value_ofInt (n : ℤ) : value (ofInt n) = (n : ℚ) := by
  change (n.toNat : ℚ) - ((-n).toNat : ℚ) = (n : ℚ)
  exact_mod_cast Int.toNat_sub_toNat_neg n

theorem mul_ne {x y : Pair} (hx : x.1 ≠ x.2) (hy : y.1 ≠ y.2) : (mul x y).1 ≠ (mul x y).2 := by
  intro h
  have he := (value_eq_zero (mul x y)).mpr h
  rw [value_mul] at he
  exact (mul_ne_zero (mt (value_eq_zero x).mp hx) (mt (value_eq_zero y).mp hy)) he

def Bound (b : ℕ) (x : Pair) : Prop := x.1 ≤ 2 ^ b ∧ x.2 ≤ 2 ^ b

theorem mono {b c : ℕ} {x : Pair} (hx : Bound b x) (h : b ≤ c) : Bound c x := by
  have hp := Nat.pow_le_pow_right (by decide : 0 < 2) h
  exact ⟨hx.1.trans hp, hx.2.trans hp⟩

theorem neg_bound {b : ℕ} {x : Pair} (h : Bound b x) : Bound b (neg x) := ⟨h.2, h.1⟩

theorem add_bound {b : ℕ} {x y : Pair} (hx : Bound b x) (hy : Bound b y) : Bound (b + 1) (add x y) := by
  have hp : 2 ^ (b + 1) = 2 ^ b + 2 ^ b := by rw [Nat.pow_succ]; omega
  constructor
  · change x.1 + y.1 ≤ _
    rw [hp]
    exact Nat.add_le_add hx.1 hy.1
  · change x.2 + y.2 ≤ _
    rw [hp]
    exact Nat.add_le_add hx.2 hy.2

theorem mul_bound {b c : ℕ} {x y : Pair} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 1) (mul x y) := by
  have hp : 2 ^ b * 2 ^ c + 2 ^ b * 2 ^ c = 2 ^ (b + c + 1) := by
    simp only [Nat.pow_add, Nat.pow_one]; ring
  constructor
  · exact (Nat.add_le_add (Nat.mul_le_mul hx.1 hy.1) (Nat.mul_le_mul hx.2 hy.2)).trans_eq hp
  · exact (Nat.add_le_add (Nat.mul_le_mul hx.1 hy.2) (Nat.mul_le_mul hx.2 hy.1)).trans_eq hp

theorem ofInt_bound {b : ℕ} {n : ℤ} (h : n.natAbs ≤ 2 ^ b) : Bound b (ofInt n) := by
  have he := Int.toNat_add_toNat_neg_eq_natAbs n
  constructor <;> dsimp only [ofInt]
  all_goals omega

end Pair

structure Frac where
  num : Pair
  den : Pair
  den_ne : den.1 ≠ den.2
  deriving DecidableEq

def value (x : Frac) : ℚ := Pair.value x.num / Pair.value x.den

def ofNat (n : ℕ) : Frac := ⟨(n, 0), (1, 0), by decide⟩
def ofInt (n : ℤ) : Frac := ⟨Pair.ofInt n, (1, 0), by decide⟩
def ofRat (x : ℚ) : Frac := ⟨Pair.ofInt x.num, (x.den, 0), by have h := x.den_pos; omega⟩
def neg (x : Frac) : Frac := ⟨Pair.neg x.num, x.den, x.den_ne⟩
def mul (x y : Frac) : Frac :=
    ⟨Pair.mul x.num y.num, Pair.mul x.den y.den, Pair.mul_ne x.den_ne y.den_ne⟩
def add (x y : Frac) : Frac :=
  ⟨Pair.add (Pair.mul x.num y.den) (Pair.mul y.num x.den), Pair.mul x.den y.den, Pair.mul_ne x.den_ne y.den_ne⟩
def sub (x y : Frac) : Frac := add x (neg y)
def inv (x : Frac) : Frac := if h : x.num.1 = x.num.2 then ofNat 0 else ⟨x.den, x.num, h⟩
def div (x y : Frac) : Frac := mul x (inv y)
def pow (x : Frac) : ℕ → Frac | 0 => ofNat 1 | n + 1 => mul (pow x n) x

theorem den_value_ne (x : Frac) : Pair.value x.den ≠ 0 := mt (Pair.value_eq_zero x.den).mp x.den_ne

theorem value_ofNat (n : ℕ) : value (ofNat n) = (n : ℚ) := by simp [value, ofNat, Pair.value]

theorem value_ofInt (n : ℤ) : value (ofInt n) = (n : ℚ) := by
  change Pair.value (Pair.ofInt n) / Pair.value (1, 0) = _
  rw [Pair.value_ofInt]
  norm_num [Pair.value]

theorem value_ofRat (x : ℚ) : value (ofRat x) = x := by
  change Pair.value (Pair.ofInt x.num) / Pair.value (x.den, 0) = x
  rw [Pair.value_ofInt]
  simpa only [Pair.value, Nat.cast_zero, sub_zero] using Rat.num_div_den x

theorem value_neg (x : Frac) : value (neg x) = -value x := by
    simp only [value, neg, Pair.value_neg, neg_div]

theorem value_mul (x y : Frac) : value (mul x y) = value x * value y := by
  simp only [value, mul, Pair.value_mul]
  ring

theorem value_add (x y : Frac) : value (add x y) = value x + value y := by
  simp only [value, add, Pair.value_add, Pair.value_mul]
  field_simp [den_value_ne x, den_value_ne y]

theorem value_sub (x y : Frac) : value (sub x y) = value x - value y := by
  simp only [sub, value_add, value_neg, sub_eq_add_neg]

theorem value_inv (x : Frac) : value (inv x) = (value x)⁻¹ := by
  by_cases h : x.num.1 = x.num.2
  · simp [inv, h, value, ofNat, Pair.value]
  · simp [inv, h, value, inv_div]

theorem value_div (x y : Frac) : value (div x y) = value x / value y := by
  simp only [div, value_mul, value_inv, div_eq_mul_inv]

theorem value_pow (x : Frac) (n : ℕ) : value (pow x n) = value x ^ n := by
  induction n with
  | zero => simp [pow, value_ofNat]
  | succ n ih => simp only [pow, value_mul, ih, pow_succ]

def Bound (b : ℕ) (x : Frac) : Prop := Pair.Bound b x.num ∧ Pair.Bound b x.den

theorem mono {b c : ℕ} {x : Frac} (hx : Bound b x) (h : b ≤ c) : Bound c x :=
  ⟨Pair.mono hx.1 h, Pair.mono hx.2 h⟩

theorem ofNat_bound {b n : ℕ} (h : n ≤ 2 ^ b) : Bound b (ofNat n) :=
  ⟨⟨h, Nat.zero_le _⟩, ⟨Nat.one_le_two_pow, Nat.zero_le _⟩⟩

theorem nat_bound (n : ℕ) : Bound n (ofNat n) := ofNat_bound (Nat.lt_two_pow_self (n := n)).le

theorem ofInt_bound {b : ℕ} {n : ℤ} (h : n.natAbs ≤ 2 ^ b) : Bound b (ofInt n) :=
  ⟨Pair.ofInt_bound h, ⟨Nat.one_le_two_pow, Nat.zero_le _⟩⟩

theorem ofRat_bound {b : ℕ} {x : ℚ} (h : RationalDataSize.Bound b x) : Bound b (ofRat x) :=
  ⟨Pair.ofInt_bound h.1, ⟨h.2, Nat.zero_le _⟩⟩

theorem neg_bound {b : ℕ} {x : Frac} (h : Bound b x) : Bound b (neg x) := ⟨Pair.neg_bound h.1, h.2⟩

theorem mul_bound {b c : ℕ} {x y : Frac} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 1) (mul x y) :=
  ⟨Pair.mul_bound hx.1 hy.1, Pair.mul_bound hx.2 hy.2⟩

theorem add_bound {b c : ℕ} {x y : Frac} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 2) (add x y) := by
  have hxy := Pair.mul_bound hx.1 hy.2
  have hyx : Pair.Bound (b + c + 1) (Pair.mul y.num x.den) := by
    simpa only [Nat.add_comm c b] using Pair.mul_bound hy.1 hx.2
  exact ⟨Pair.add_bound hxy hyx, Pair.mono (Pair.mul_bound hx.2 hy.2) (by omega)⟩

theorem sub_bound {b c : ℕ} {x y : Frac} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 2) (sub x y) :=
  add_bound hx (neg_bound hy)

theorem inv_bound {b : ℕ} {x : Frac} (h : Bound b x) : Bound b (inv x) := by
  unfold inv
  split
  · exact ofNat_bound (Nat.zero_le _)
  · exact ⟨h.2, h.1⟩

theorem div_bound {b c : ℕ} {x y : Frac} (hx : Bound b x) (hy : Bound c y) : Bound (b + c + 1) (div x y) :=
  mul_bound hx (inv_bound hy)

theorem pow_bound {b : ℕ} {x : Frac} (hx : Bound b x) (n : ℕ) : Bound (n * (b + 1)) (pow x n) := by
  induction n with
  | zero => exact ofNat_bound (by simp)
  | succ n ih =>
    have h := mul_bound ih hx
    convert! h using 1
    ring

end Qatlib.Concepts.FinitePrecision.ComputableInput.Arithmetic.SignedNatMachine.RedundantRational
