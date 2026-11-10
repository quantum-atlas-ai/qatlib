/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Data

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

private theorem full_adder_value (x y c : Bool) :
    (binomialFullAdder x y c).1.toNat+2*(binomialFullAdder x y c).2.toNat =
      x.toNat+y.toNat+c.toNat := by
  cases x <;> cases y <;> cases c <;> decide

private theorem bit_value_head (xs : List Bool) :
    binomialBitValue xs = (xs.headD false).toNat+2*binomialBitValue xs.tail := by
  cases xs <;> rfl

theorem binomial_bit_add (k : ℕ) (xs ys : List Bool) (c : Bool)
    (hx : xs.length ≤ k) (hy : ys.length ≤ k) :
    binomialBitValue (binomialBitAdd k xs ys c).1 =
      binomialBitValue xs+binomialBitValue ys+c.toNat ∧
    (binomialBitAdd k xs ys c).1.length = k+1 ∧
    (binomialBitAdd k xs ys c).2 = 5*k := by
  induction k generalizing xs ys c with
  | zero =>
    have hx0 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs; subst ys
    simp [binomialBitAdd,binomialBitValue]
  | succ k ih =>
    have hxt : xs.tail.length ≤ k := by simp only [List.length_tail]; omega
    have hyt : ys.tail.length ≤ k := by simp only [List.length_tail]; omega
    let f := binomialFullAdder (xs.headD false) (ys.headD false) c
    obtain ⟨hv,hl,hg⟩ := ih xs.tail ys.tail f.2 hxt hyt
    have hf := full_adder_value (xs.headD false) (ys.headD false) c
    have hxs := bit_value_head xs
    have hys := bit_value_head ys
    refine ⟨?_,?_,?_⟩
    · change f.1.toNat+2*binomialBitValue (binomialBitAdd k xs.tail ys.tail f.2).1 = _
      rw [hv]
      change f.1.toNat+2*f.2.toNat = _ at hf
      omega
    · change (binomialBitAdd k xs.tail ys.tail f.2).1.length+1 = _
      omega
    · change 5+(binomialBitAdd k xs.tail ys.tail f.2).2 = _
      omega

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

private theorem mask_spec (b : Bool) (ys : List Bool) :
    binomialBitValue (binomialBitMask b ys).1 = (if b then binomialBitValue ys else 0) ∧
    (binomialBitMask b ys).1.length = ys.length ∧
    (binomialBitMask b ys).2 = ys.length := by
  induction ys with
  | nil => simp [binomialBitMask,binomialBitValue]
  | cons y ys ih =>
    obtain ⟨hv,hl,hg⟩ := ih
    cases b <;> cases y <;> simp_all [binomialBitMask,binomialBitValue,Nat.add_comm]

theorem binomial_bit_mul (xs ys : List Bool) :
    binomialBitValue (binomialBitMul xs ys).1 = binomialBitValue xs*binomialBitValue ys ∧
    (binomialBitMul xs ys).1.length ≤ 2*xs.length+ys.length ∧
    (binomialBitMul xs ys).2 = 5*xs.length^2+6*xs.length*ys.length := by
  induction xs with
  | nil => simp [binomialBitMul,binomialBitValue]
  | cons b bs ih =>
    obtain ⟨hv,hl,hg⟩ := ih
    obtain ⟨mv,ml,mg⟩ := mask_spec b ys
    let k := 2*bs.length+ys.length+1
    have hx : (false::(binomialBitMul bs ys).1).length ≤ k := by
      simp only [List.length_cons]; dsimp [k]; omega
    have hy : (binomialBitMask b ys).1.length ≤ k := by dsimp [k]; omega
    obtain ⟨av,al,ag⟩ := binomial_bit_add k (false::(binomialBitMul bs ys).1)
      (binomialBitMask b ys).1 false hx hy
    refine ⟨?_,?_,?_⟩
    · change binomialBitValue (binomialBitAdd k _ _ false).1 = _
      rw [av]
      simp only [binomialBitValue,Bool.toNat_false,zero_add,add_zero,hv,mv]
      cases b <;> simp <;> ring
    · change (binomialBitAdd k _ _ false).1.length ≤ _
      rw [al]
      simp only [List.length_cons]
      dsimp [k]
      omega
    · change (binomialBitMul bs ys).2+(binomialBitMask b ys).2+
        (binomialBitAdd k _ _ false).2 = _
      rw [hg,mg,ag]
      simp only [List.length_cons]
      dsimp [k]
      ring

theorem binomial_bit_value_bits (n : ℕ) : binomialBitValue n.bits = n := by
  induction n using Nat.binaryRec' with
  | zero => simp [binomialBitValue]
  | bit b n h ih =>
    rw [Nat.bits_append_bit n b h]
    simp only [binomialBitValue,ih,Nat.bit_val]
    omega

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

theorem binomial_bit_square (n : ℕ) :
    binomialBitValue (binomialBitMul n.bits n.bits).1 = n*n ∧
    (binomialBitMul n.bits n.bits).2 = 11*n.size^2 := by
  obtain ⟨hv,_,hg⟩ := binomial_bit_mul n.bits n.bits
  rw [binomial_bit_value_bits] at hv
  rw [Nat.size_eq_bits_len] at hg
  refine ⟨hv,?_⟩
  rw [hg]
  ring

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
