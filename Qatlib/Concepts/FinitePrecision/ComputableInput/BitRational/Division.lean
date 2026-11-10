/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Comparison

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

private theorem value_head (xs : List Bool) :
    binomialBitValue xs = (xs.headD false).toNat+2*binomialBitValue xs.tail := by
  cases xs <;> rfl

private theorem value_lt (xs : List Bool) : binomialBitValue xs < 2^xs.length := by
  induction xs with
  | nil => simp [binomialBitValue]
  | cons b xs ih =>
    cases b <;> simp only [binomialBitValue,Bool.toNat_false,Bool.toNat_true,
      List.length_cons,pow_succ] <;> omega

private theorem subtract_cell (x y c : Bool) :
    (binomialFullAdder x (!y) c).1.toNat+2*(binomialFullAdder x (!y) c).2.toNat+y.toNat =
      x.toNat+1+c.toNat := by
  cases x <;> cases y <;> cases c <;> decide

private theorem subtract_spec (k : ℕ) (xs ys : List Bool) (c : Bool)
    (hx : xs.length ≤ k) (hy : ys.length ≤ k) :
    let r := binomialBitSubtract k xs ys c
    binomialBitValue r.1.1+2^k*r.1.2.toNat+binomialBitValue ys+1 =
      binomialBitValue xs+2^k+c.toNat ∧ r.1.1.length = k ∧ r.2 = 6*k := by
  induction k generalizing xs ys c with
  | zero =>
    have hx0 : xs = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hy0 : ys = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst xs; subst ys
    simp [binomialBitSubtract,binomialBitValue,Nat.add_comm]
  | succ k ih =>
    have hxt : xs.tail.length ≤ k := by simp only [List.length_tail]; omega
    have hyt : ys.tail.length ≤ k := by simp only [List.length_tail]; omega
    let f := binomialFullAdder (xs.headD false) (!(ys.headD false)) c
    let r := binomialBitSubtract k xs.tail ys.tail f.2
    obtain ⟨hv,hl,hg⟩ := ih xs.tail ys.tail f.2 hxt hyt
    change r.1.1.length = k at hl
    change r.2 = 6*k at hg
    have hf := subtract_cell (xs.headD false) (ys.headD false) c
    have hxs := value_head xs
    have hys := value_head ys
    change f.1.toNat+2*f.2.toNat+(ys.headD false).toNat = _ at hf
    change binomialBitValue r.1.1+2^k*r.1.2.toNat+binomialBitValue ys.tail+1 = _ at hv
    refine ⟨?_,?_,?_⟩
    · change f.1.toNat+2*binomialBitValue r.1.1+2^(k+1)*r.1.2.toNat+
        binomialBitValue ys+1 = _
      rw [pow_succ]
      nlinarith
    · change r.1.1.length+1 = _; omega
    · change 6+r.2 = _; omega

theorem binomial_bit_subtract (k : ℕ) (xs ys : List Bool)
    (hx : xs.length ≤ k) (hy : ys.length ≤ k) (h : binomialBitValue ys ≤ binomialBitValue xs) :
    let r := binomialBitSubtract k xs ys true
    binomialBitValue r.1.1 = binomialBitValue xs-binomialBitValue ys ∧
    r.1.2 = true ∧ r.1.1.length = k ∧ r.2 = 6*k := by
  obtain ⟨hv,hl,hg⟩ := subtract_spec k xs ys true hx hy
  have hb := value_lt (binomialBitSubtract k xs ys true).1.1
  rw [hl] at hb
  have hc : (binomialBitSubtract k xs ys true).1.2 = true := by
    cases he : (binomialBitSubtract k xs ys true).1.2
    · simp only [he,Bool.toNat_false,Bool.toNat_true,mul_zero,add_zero] at hv
      omega
    · rfl
  simp only [hc,Bool.toNat_true,mul_one] at hv
  exact ⟨by omega,hc,hl,hg⟩

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

private theorem division_semantics (ds xs : List Bool) (hd : 0 < binomialBitValue ds) :
    let r := binomialBitDivmod ds xs
    binomialBitValue xs = binomialBitValue r.quotient*binomialBitValue ds+binomialBitValue r.remainder ∧
    binomialBitValue r.remainder < binomialBitValue ds := by
  induction xs with
  | nil => simpa [binomialBitDivmod,binomialBitValue] using hd
  | cons b bs ih =>
    let r := binomialBitDivmod ds bs
    let c := b::r.remainder
    let k := max c.length ds.length
    let cmp := binomialBitCompare k ds c true
    have hc : cmp.1 = true ↔ binomialBitValue ds ≤ binomialBitValue c := by
      simpa only [Bool.toNat_true,Nat.add_le_add_iff_right] using
        (binomial_bit_compare k ds c true (le_max_right _ _) (le_max_left _ _)).1
    have hb : b.toNat ≤ 1 := by cases b <;> decide
    have hv : binomialBitValue c = b.toNat+2*binomialBitValue r.remainder := rfl
    change binomialBitValue bs = binomialBitValue r.quotient*binomialBitValue ds+
      binomialBitValue r.remainder ∧ binomialBitValue r.remainder < binomialBitValue ds at ih
    have hsmall : binomialBitValue c < 2*binomialBitValue ds := by omega
    by_cases h : cmp.1 = true
    · have hge := hc.mp h
      let sub := binomialBitSubtract k c ds true
      have hs := binomial_bit_subtract k c ds (le_max_left _ _) (le_max_right _ _) hge
      have hsum : binomialBitValue sub.1.1+binomialBitValue ds = binomialBitValue c := by
        rw [hs.1,Nat.sub_add_cancel hge]
      have he : binomialBitDivmod ds (b::bs) =
          ⟨true::r.quotient,sub.1.1,r.gates+cmp.2+sub.2,r.columns+1⟩ := by
        change (if cmp.1 then _ else _) = _
        rw [if_pos h]
      simp only [he,binomialBitValue,Bool.toNat_true]
      constructor <;> nlinarith [ih.1]
    · have hlt : binomialBitValue c < binomialBitValue ds := Nat.lt_of_not_ge (mt hc.mpr h)
      have he : binomialBitDivmod ds (b::bs) =
          ⟨false::r.quotient,c,r.gates+cmp.2,r.columns+1⟩ := by
        change (if cmp.1 then _ else _) = _
        rw [if_neg h]
      simp only [he,binomialBitValue,Bool.toNat_false,zero_add]
      constructor
      · nlinarith [ih.1]
      · exact hlt

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

private theorem division_bounds (ds xs : List Bool) :
    let r := binomialBitDivmod ds xs
    r.quotient.length = xs.length ∧ r.remainder.length ≤ xs.length+ds.length ∧
    r.columns = xs.length ∧ r.gates ≤ 11*xs.length*(xs.length+ds.length) := by
  induction xs with
  | nil => simp [binomialBitDivmod]
  | cons b bs ih =>
    let r := binomialBitDivmod ds bs
    let c := b::r.remainder
    let k := max c.length ds.length
    let cmp := binomialBitCompare k ds c true
    change r.quotient.length = bs.length ∧ r.remainder.length ≤ bs.length+ds.length ∧
      r.columns = bs.length ∧ r.gates ≤ 11*bs.length*(bs.length+ds.length) at ih
    have hcl : c.length = r.remainder.length+1 := rfl
    have hk : k ≤ bs.length+ds.length+1 := by dsimp [k]; omega
    have hcg : cmp.2 = 5*k :=
      (binomial_bit_compare k ds c true (le_max_right _ _) (le_max_left _ _)).2
    by_cases h : cmp.1 = true
    · let sub := binomialBitSubtract k c ds true
      obtain ⟨_,hl,hg⟩ := subtract_spec k c ds true (le_max_left _ _) (le_max_right _ _)
      change sub.1.1.length = k at hl
      change sub.2 = 6*k at hg
      have he : binomialBitDivmod ds (b::bs) =
          ⟨true::r.quotient,sub.1.1,r.gates+cmp.2+sub.2,r.columns+1⟩ := by
        change (if cmp.1 then _ else _) = _
        rw [if_pos h]
      simp only [he,List.length_cons]
      refine ⟨by omega,by omega,by omega,?_⟩
      nlinarith [ih.2.2.2]
    · have he : binomialBitDivmod ds (b::bs) =
          ⟨false::r.quotient,c,r.gates+cmp.2,r.columns+1⟩ := by
        change (if cmp.1 then _ else _) = _
        rw [if_neg h]
      simp only [he,List.length_cons]
      refine ⟨by omega,by omega,by omega,?_⟩
      nlinarith [ih.2.2.2]

theorem binomial_bit_divmod (ds xs : List Bool) (hd : 0 < binomialBitValue ds) :
    let r := binomialBitDivmod ds xs
    binomialBitValue r.quotient = binomialBitValue xs/binomialBitValue ds ∧
    binomialBitValue r.remainder = binomialBitValue xs%binomialBitValue ds ∧
    r.quotient.length = xs.length ∧ r.remainder.length ≤ xs.length+ds.length ∧
    r.columns = xs.length ∧ r.gates ≤ 11*xs.length*(xs.length+ds.length) := by
  obtain ⟨he,hr⟩ := division_semantics ds xs hd
  have hq : binomialBitValue xs/binomialBitValue ds =
      binomialBitValue (binomialBitDivmod ds xs).quotient := by
    apply Nat.div_eq_of_lt_le <;> nlinarith
  have hm : binomialBitValue xs%binomialBitValue ds =
      binomialBitValue (binomialBitDivmod ds xs).remainder := by
    simp only [he,Nat.add_mod,Nat.mul_mod_left,zero_add,Nat.mod_eq_of_lt hr]
  exact ⟨hq.symm,hm.symm,division_bounds ds xs⟩

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
