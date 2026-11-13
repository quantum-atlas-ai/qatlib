/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational.Gcd

/-!
# Bitwise fraction reduction

This module verifies fraction reduction by the computed bitwise GCD followed by two binary
divisions. For a positive denominator, `binomial_reduce_fraction` supplies coprimality,
positivity, size monotonicity, and a gate bound, allowing `binomialReducedRat` to construct a
rational value.

For background on classical computation and its resource models, see [KitaevShenVyalyi2002].

## Main statements

* `binomial_reduce_fraction`: correctness and bounds for reduced natural fractions.
* `binomialReducedRat`: rational construction from the verified reduced pair.
* `binomial_reduced_rat`: identifies the constructed rational with `mkRat`.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- Binary division of inputs of length at most `w` with a positive divisor uses at most `22 * w
^ 2` gates. -/
private theorem quotient_cost (xs ys : List Bool) (w : ℕ)
    (hx : xs.length ≤ w) (hy : ys.length ≤ w) (hp : 0 < binomialBitValue ys) :
    (binomialBitDivmod ys xs).gates ≤ 22*w^2 := by
  have hg := (binomial_bit_divmod ys xs hp).2.2.2.2.2
  have hm := Nat.mul_le_mul hx (Nat.add_le_add hx hy)
  nlinarith

/-- For positive `d`, fraction reduction returns `(a / Nat.gcd a d, d / Nat.gcd a d)` with
coprime entries, positive denominator, and entries bounded by the inputs. Its gate count is
at most `w * (44 * w ^ 2 + 2 * w) + 44 * w ^ 2` for `w = max a.size d.size`. -/
theorem binomial_reduce_fraction (a d : ℕ) (hd : 0 < d) :
    let w := max a.size d.size
    let r := binomialReduceFraction a d
    r.1 = (a/Nat.gcd a d,d/Nat.gcd a d) ∧
    Nat.Coprime r.1.1 r.1.2 ∧ 0 < r.1.2 ∧ r.1.1 ≤ a ∧ r.1.2 ≤ d ∧
    r.2 ≤ w*(44*w^2+2*w)+44*w^2 := by
  let w := max a.size d.size
  let g := binomialBitGcd a.bits d.bits
  have hg := binomial_bit_gcd a.bits d.bits
  simp only [binomial_bit_value_bits,Nat.size_eq_bits_len] at hg
  change binomialBitValue g.bits = Nat.gcd a d ∧ g.bits.length ≤ w ∧
    g.divisions ≤ 2*w ∧ g.gates ≤ w*(44*w^2+2*w) at hg
  have hp : 0 < binomialBitValue g.bits := by rw [hg.1]; exact Nat.gcd_pos_of_pos_right a hd
  have hn := (binomial_bit_divmod g.bits a.bits hp).1
  have hb := (binomial_bit_divmod g.bits d.bits hp).1
  simp only [binomial_bit_value_bits,hg.1] at hn hb
  have he : (binomialReduceFraction a d).1 = (a/Nat.gcd a d,d/Nat.gcd a d) :=
    Prod.ext hn hb
  refine ⟨he,?_,?_,?_,?_,?_⟩
  · rw [he]
    exact Nat.gcd_div_gcd_div_gcd_of_pos_right hd
  · rw [he]
    exact Nat.div_pos (Nat.gcd_le_right a hd) (Nat.gcd_pos_of_pos_right a hd)
  · rw [he]; exact Nat.div_le_self _ _
  · rw [he]; exact Nat.div_le_self _ _
  · have ha : a.bits.length ≤ w := by rw [Nat.size_eq_bits_len]; exact le_max_left _ _
    have hdw : d.bits.length ≤ w := by rw [Nat.size_eq_bits_len]; exact le_max_right _ _
    have hn' := quotient_cost a.bits g.bits w ha hg.2.1 hp
    have hd' := quotient_cost d.bits g.bits w hdw hg.2.1 hp
    change g.gates+(binomialBitDivmod g.bits a.bits).gates+
      (binomialBitDivmod g.bits d.bits).gates ≤ w*(44*w^2+2*w)+44*w^2
    nlinarith [hg.2.2.2]

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

namespace Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational

/-- Constructs a rational from the verified reduced numerator and positive denominator,
retaining the reduction gate count. -/
def binomialReducedRat (a d : ℕ) (hd : 0 < d) : ℚ × ℕ :=
  let r := binomialReduceFraction a d
  (⟨(r.1.1 : ℤ),r.1.2,(binomial_reduce_fraction a d hd).2.2.1.ne',
    by simpa only [Int.natAbs_natCast] using (binomial_reduce_fraction a d hd).2.1⟩,r.2)

/-- The value returned by `binomialReducedRat` equals `mkRat (a : ℤ) d`. -/
theorem binomial_reduced_rat (a d : ℕ) (hd : 0 < d) :
    (binomialReducedRat a d hd).1 = mkRat (a : ℤ) d := by
  have h := (binomial_reduce_fraction a d hd).1
  apply Rat.ext
  · change ((binomialReduceFraction a d).1.1 : ℤ) = _
    rw [Rat.num_mkRat,if_neg hd.ne',Int.natAbs_natCast,Nat.gcd_comm d a,h]
    norm_cast
  · change (binomialReduceFraction a d).1.2 = _
    rw [Rat.den_mkRat,if_neg hd.ne',Int.natAbs_natCast,Nat.gcd_comm d a,h]

end Qatlib.Concepts.FinitePrecision.ComputableInput.BitRational
