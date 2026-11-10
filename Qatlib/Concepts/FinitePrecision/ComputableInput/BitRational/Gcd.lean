/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Division
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

theorem binomial_bit_any (xs : List Bool) :
    ((binomialBitAny xs).1 = true ↔ binomialBitValue xs ≠ 0) ∧
    (binomialBitAny xs).2 = xs.length := by
  induction xs with
  | nil => simp [binomialBitAny,binomialBitValue]
  | cons b bs ih =>
    cases b <;> simp [binomialBitAny,binomialBitValue,ih.1,ih.2,Nat.add_comm]
end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

private theorem value_lt (xs : List Bool) : binomialBitValue xs < 2^xs.length := by
  induction xs with
  | nil => simp [binomialBitValue]
  | cons b xs ih =>
    cases b <;> simp only [binomialBitValue,List.length_cons,pow_succ,
      Bool.toNat_true,Bool.toNat_false] <;> omega

private theorem value_split (xs : List Bool) (w : ℕ) :
    binomialBitValue xs = binomialBitValue (xs.take w)+2^w*binomialBitValue (xs.drop w) := by
  induction w generalizing xs with
  | zero => simp [binomialBitValue]
  | succ w ih =>
    cases xs with
    | nil => simp [binomialBitValue]
    | cons b xs =>
      simp only [List.take_succ_cons,List.drop_succ_cons,binomialBitValue,pow_succ]
      have h := ih xs
      nlinarith

theorem binomial_bit_take_exact (xs : List Bool) (w : ℕ) (h : binomialBitValue xs < 2^w) :
    binomialBitValue (xs.take w) = binomialBitValue xs := by
  have he := value_split xs w
  have hz : binomialBitValue (xs.drop w) = 0 := by
    by_contra hn
    have hp : 1 ≤ binomialBitValue (xs.drop w) := Nat.one_le_iff_ne_zero.mpr hn
    have hm := Nat.mul_le_mul_left (2^w) hp
    nlinarith
  simpa only [hz,mul_zero,add_zero] using he.symm

private theorem mod_half (b r : ℕ) (hr : 0 < r) (hb : r < b) : 2*(b%r) < b := by
  have hm := Nat.mod_lt b hr
  by_cases h : 2*r ≤ b
  · omega
  · have hq : 1 ≤ b/r := Nat.div_pos hb.le hr
    have he := Nat.mod_add_div b r
    have hp := Nat.mul_le_mul_left r hq
    nlinarith

private theorem gcd_step (a b : ℕ) : Nat.gcd b (a%b) = Nat.gcd a b := by
  rw [Nat.gcd_comm b (a%b),← Nat.gcd_rec b a,Nat.gcd_comm b a]

private theorem division_step (xs ys : List Bool) (w : ℕ)
    (hx : xs.length ≤ w) (hy : ys.length ≤ w) (hp : 0 < binomialBitValue ys) :
    let d := binomialBitDivmod ys xs
    binomialBitValue (d.remainder.take w) = binomialBitValue xs%binomialBitValue ys ∧
    (d.remainder.take w).length ≤ w ∧ d.gates ≤ 22*w^2 := by
  obtain ⟨_,hv,_,_,_,hg⟩ := binomial_bit_divmod ys xs hp
  have hpw : 2^ys.length ≤ 2^w := by gcongr
  have hb : binomialBitValue (binomialBitDivmod ys xs).remainder < 2^w := by
    rw [hv]
    exact (Nat.mod_lt _ hp).trans ((value_lt ys).trans_le hpw)
  have hm := Nat.mul_le_mul hx (Nat.add_le_add hx hy)
  exact ⟨(binomial_bit_take_exact _ w hb).trans hv,by simp,by nlinarith⟩

private theorem run_spec (w k : ℕ) (xs ys : List Bool)
    (hx : xs.length ≤ w) (hy : ys.length ≤ w) (hb : binomialBitValue ys < 2^k) :
    let r := binomialGcdRun w k xs ys
    binomialBitValue r.bits = Nat.gcd (binomialBitValue xs) (binomialBitValue ys) ∧
    r.bits.length ≤ w ∧ r.divisions ≤ 2*k ∧ r.gates ≤ k*(44*w^2+2*w) := by
  induction k generalizing xs ys with
  | zero =>
    have hz : binomialBitValue ys = 0 := by simpa using hb
    simpa [binomialGcdRun,hz] using hx
  | succ k ih =>
    let nz := binomialBitAny ys
    obtain ⟨hn,hng⟩ := binomial_bit_any ys
    change (nz.1 = true ↔ _) at hn
    change nz.2 = _ at hng
    by_cases hz : nz.1 = true
    · have hp : 0 < binomialBitValue ys := Nat.pos_of_ne_zero (hn.mp hz)
      let d := binomialBitDivmod ys xs
      let r := d.remainder.take w
      obtain ⟨hv,hl,hg⟩ := division_step xs ys w hx hy hp
      change binomialBitValue r = _ at hv
      change r.length ≤ w at hl
      change d.gates ≤ _ at hg
      let nr := binomialBitAny r
      obtain ⟨hrn,hrg⟩ := binomial_bit_any r
      change (nr.1 = true ↔ _) at hrn
      change nr.2 = _ at hrg
      by_cases hrz : nr.1 = true
      · have hrp : 0 < binomialBitValue r := Nat.pos_of_ne_zero (hrn.mp hrz)
        let e := binomialBitDivmod r ys
        let s := e.remainder.take w
        obtain ⟨hsv,hsl,hsg⟩ := division_step ys r w hy hl hrp
        change binomialBitValue s = _ at hsv
        change s.length ≤ w at hsl
        change e.gates ≤ _ at hsg
        have hrl : binomialBitValue r < binomialBitValue ys := by rw [hv]; exact Nat.mod_lt _ hp
        have hs : binomialBitValue s < 2^k := by
          have hh := mod_half (binomialBitValue ys) (binomialBitValue r) hrp hrl
          rw [← hsv] at hh
          rw [pow_succ] at hb
          omega
        obtain ⟨hval,hlen,hsteps,hcost⟩ := ih r s hl hsl hs
        have heq : binomialGcdRun w (k+1) xs ys =
            ⟨(binomialGcdRun w k r s).bits,2+(binomialGcdRun w k r s).divisions,
              nz.2+d.gates+nr.2+e.gates+(binomialGcdRun w k r s).gates⟩ := by
          dsimp only [nz] at hz
          dsimp only [nr,r,d] at hrz
          simp only [binomialGcdRun,if_pos hz,if_pos hrz]
          rfl
        simp only [heq]
        refine ⟨?_,hlen,by omega,?_⟩
        · rw [hval,hsv,gcd_step,hv,gcd_step]
        · nlinarith
      · have hr0 : binomialBitValue r = 0 := by
          by_contra h
          exact hrz (hrn.mpr h)
        have hrem : binomialBitValue xs%binomialBitValue ys = 0 := hv.symm.trans hr0
        have heq : binomialGcdRun w (k+1) xs ys = ⟨ys,1,nz.2+d.gates+nr.2⟩ := by
          dsimp only [nz] at hz
          dsimp only [nr,r,d] at hrz
          simp only [binomialGcdRun,if_pos hz,if_neg hrz]
          rfl
        simp only [heq]
        refine ⟨?_,hy,by omega,?_⟩
        · simpa only [hrem,Nat.gcd_zero_right] using
            gcd_step (binomialBitValue xs) (binomialBitValue ys)
        · nlinarith
    · have hy0 : binomialBitValue ys = 0 := by
        by_contra h
        exact hz (hn.mpr h)
      have heq : binomialGcdRun w (k+1) xs ys = ⟨xs,0,nz.2⟩ := by
        dsimp only [nz] at hz
        simp only [binomialGcdRun,if_neg hz]
        rfl
      simp only [heq,hy0,Nat.gcd_zero_right]
      exact ⟨trivial,hx,by omega,by nlinarith⟩

theorem binomial_bit_gcd (xs ys : List Bool) :
    let w := max xs.length ys.length
    let r := binomialBitGcd xs ys
    binomialBitValue r.bits = Nat.gcd (binomialBitValue xs) (binomialBitValue ys) ∧
    r.bits.length ≤ w ∧ r.divisions ≤ 2*w ∧ r.gates ≤ w*(44*w^2+2*w) := by
  let w := max xs.length ys.length
  have hy : ys.length ≤ w := le_max_right _ _
  have hp : 2^ys.length ≤ 2^w := by gcongr
  exact run_spec w w xs ys (le_max_left _ _) hy ((value_lt ys).trans_le hp)

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
