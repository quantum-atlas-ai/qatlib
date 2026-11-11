/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Nat.Size
import Mathlib.Tactic

/-!
# Power-of-two fourth-root selection

`IntegerFourthRootSelector.select` doubles a positive segment count until the inequality `num ≤
den * segments ^ 4` is reached or its binary-size fuel is exhausted. For positive `den`, the
selected count succeeds, is a power of two, and is less than twice any positive successful
count; `fastSelect` maintains the fourth-power bound incrementally and returns the same result.

For background on classical computation and its resource models, see [KitaevShenVyalyi2002].

## Main statements

* `select_success` and `select_lt_twice`: success and comparison with any feasible count.
* `select_comparisons` and `select_output_size`: comparison and output-size bounds.
* `fastSelect_eq_select`: equivalence of the incremental implementation.

## References

* [Kitaev, Shen and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false
namespace Qatlib.Concepts.FinitePrecision.ComputableInput.IntegerFourthRootSelector

/-- A selected natural segment count together with the number of comparisons performed. -/
structure Selection where
  segments : ℕ
  comparisons : ℕ
  deriving DecidableEq, Repr

/-- With bounded fuel, tests `num ≤ den * r ^ 4` and doubles `r` after each failed comparison. -/
def selectAux (num den : ℕ) : ℕ → ℕ → Selection
  | 0, r => ⟨r, 0⟩
  | fuel + 1, r =>
      if num ≤ den * r^4 then ⟨r, 1⟩
      else
        let out := selectAux num den fuel (2*r)
        ⟨out.segments, out.comparisons + 1⟩

/-- Runs the doubling selector from one segment with fuel equal to the binary size of `num`. -/
def select (num den : ℕ) : Selection := selectAux num den num.size 1

/-- The bounded selector performs at most `fuel` comparisons. -/
theorem selectAux_comparisons (num den fuel r : ℕ) :
    (selectAux num den fuel r).comparisons ≤ fuel := by
  induction fuel generalizing r with
  | zero => simp [selectAux]
  | succ fuel ih =>
      simp only [selectAux]; split_ifs <;> simp_all

/-- The bounded selector returns a positive segment count when its starting count is positive. -/
theorem selectAux_pos (num den fuel r : ℕ) (hr : 0 < r) :
    0 < (selectAux num den fuel r).segments := by
  induction fuel generalizing r with
  | zero => simpa [selectAux] using hr
  | succ fuel ih =>
      simp only [selectAux]
      split_ifs with h
      · exact hr
      · exact ih (2*r) (by omega)

/-- If the largest count reachable within the fuel satisfies the fourth-power inequality, the
bounded selector returns a count satisfying it. -/
theorem selectAux_success (num den fuel r : ℕ)
    (h : num ≤ den * (2^fuel*r)^4) :
    num ≤ den * (selectAux num den fuel r).segments^4 := by
  induction fuel generalizing r with
  | zero => simpa [selectAux] using h
  | succ fuel ih =>
      simp only [selectAux]
      split_ifs with hs
      · exact hs
      · apply ih
        have he : 2^fuel*(2*r) = 2^(fuel+1)*r := by rw [pow_succ]; ring
        rw [he]
        exact h

/-- If `s` satisfies the fourth-power inequality and the initial count is below `2 * s`, the
selected count is also below `2 * s`. -/
theorem selectAux_lt_twice (num den fuel r s : ℕ)
    (hgood : num ≤ den*s^4) (hr : r < 2*s) :
    (selectAux num den fuel r).segments < 2*s := by
  induction fuel generalizing r with
  | zero => simpa [selectAux] using hr
  | succ fuel ih =>
      simp only [selectAux]
      split_ifs with hs
      · exact hr
      · have hsmall : r < s := by
          by_contra h
          have hsr : s ≤ r := by omega
          have hp : s^4 ≤ r^4 := by gcongr
          exact hs (hgood.trans (Nat.mul_le_mul_left den hp))
        exact ih (2*r) (by omega)

/-- The bounded selector returns `2 ^ k * r` for some exponent `k` at most the fuel. -/
theorem selectAux_power_two (num den fuel r : ℕ) :
    ∃ k ≤ fuel, (selectAux num den fuel r).segments = 2^k*r := by
  induction fuel generalizing r with
  | zero => exact ⟨0, by omega, by simp [selectAux]⟩
  | succ fuel ih =>
      simp only [selectAux]
      split_ifs with hs
      · exact ⟨0, by omega, by simp⟩
      · obtain ⟨k, hk, he⟩ := ih (2*r)
        refine ⟨k+1, by omega, ?_⟩
        simpa [pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using he

/-- For a positive denominator, the selected count satisfies `num ≤ den * segments ^ 4`. -/
theorem select_success (num den : ℕ) (hd : 0 < den) :
    num ≤ den * (select num den).segments^4 := by
  apply selectAux_success
  simp only [mul_one]
  have hx : 1 ≤ (2 : ℕ)^num.size := by
    have hpos : 0 < (2 : ℕ)^num.size := by positivity
    omega
  have hp : 2^num.size ≤ (2^num.size)^4 := by
    calc
      2^num.size = 2^num.size*1*1*1 := by ring
      _ ≤ 2^num.size*2^num.size*2^num.size*2^num.size := by gcongr
      _ = _ := by ring
  exact (Nat.lt_size_self num).le.trans
    (hp.trans (by simpa using Nat.mul_le_mul_right ((2^num.size)^4) hd))

/-- The selected segment count is always positive. -/
theorem select_pos (num den : ℕ) : 0 < (select num den).segments :=
  selectAux_pos num den num.size 1 (by omega)

/-- The selector performs at most `num.size` comparisons. -/
theorem select_comparisons (num den : ℕ) :
    (select num den).comparisons ≤ num.size := selectAux_comparisons _ _ _ _

/-- The selected count is strictly less than twice any positive count satisfying the
fourth-power inequality. -/
theorem select_lt_twice (num den s : ℕ) (hs : 0 < s)
    (hgood : num ≤ den*s^4) : (select num den).segments < 2*s :=
  selectAux_lt_twice num den num.size 1 s hgood (by omega)

/-- For zero numerator, the selector returns one segment and performs no comparisons. -/
theorem select_zero (den : ℕ) : select 0 den = ⟨1, 0⟩ := rfl

/-- The selected count is a power of two with exponent at most `num.size`. -/
theorem select_power_two (num den : ℕ) :
    ∃ k ≤ num.size, (select num den).segments = 2^k := by
  simpa [select] using selectAux_power_two num den num.size 1

/-- The selected count has binary size at most `num.size + 1`. -/
theorem select_output_size (num den : ℕ) :
    (select num den).segments.size ≤ num.size + 1 := by
  obtain ⟨k, hk, he⟩ := select_power_two num den
  rw [he, Nat.size_pow]
  omega

/-- If `r ≤ 2 ^ L`, then `den * r ^ 4` has binary size at most `den.size + 4 * L`. -/
theorem comparison_operand_size (den L r : ℕ) (hr : r ≤ 2^L) :
    (den*r^4).size ≤ den.size + 4*L := by
  apply Nat.size_le.mpr
  have hp : r^4 ≤ (2^L)^4 := by gcongr
  calc
    den*r^4 ≤ den*(2^L)^4 := Nat.mul_le_mul_left den hp
    _ < 2^den.size*(2^L)^4 :=
      Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self den) (by positivity)
    _ = 2^(den.size+4*L) := by rw [← pow_mul, ← pow_add]; congr 1; omega

/-- The bounded selector never returns a count smaller than its starting count. -/
theorem selectAux_ge (num den fuel r : ℕ) :
    r ≤ (selectAux num den fuel r).segments := by
  induction fuel generalizing r with
  | zero => simp [selectAux]
  | succ fuel ih =>
      simp only [selectAux]
      split_ifs with hs
      · exact le_rfl
      · exact le_trans (by omega : r ≤ 2*r) (ih (2*r))

/-- The binary size of a natural product is at most the sum of the factor sizes. -/
theorem size_mul_le (a b : ℕ) : (a*b).size ≤ a.size+b.size := by
  apply Nat.size_le.mpr
  rw [pow_add]
  exact (Nat.mul_le_mul_left a (Nat.lt_size_self b).le).trans_lt
    (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self a) (by positivity))

/-- The binary size of a fifth power is at most five times the base's binary size. -/
theorem size_fifth_le (u : ℕ) : (u^5).size ≤ 5*u.size := by
  have h2 := size_mul_le u u
  have h4 := size_mul_le (u*u) (u*u)
  have h5 := size_mul_le ((u*u)*(u*u)) u
  have he : u^5 = ((u*u)*(u*u))*u := by ring
  rw [he]
  omega

example : select 0 1 = ⟨1, 0⟩ := by decide
example : select 16 1 = ⟨2, 2⟩ := by decide
example : select 17 1 = ⟨4, 3⟩ := by decide

/-- Runs a bounded doubling selector while maintaining a comparison bound multiplied by sixteen
after each failed test and accumulating comparisons in `used`. -/
def fastAux (num : ℕ) : ℕ → ℕ → ℕ → ℕ → Selection
  | 0, r, _, used => ⟨r, used⟩
  | fuel+1, r, bound, used =>
      if num ≤ bound then ⟨r, used+1⟩
      else fastAux num fuel (2*r) (16*bound) (used+1)

/-- When initialized with `den * r ^ 4`, the incremental selector returns the same count as
`selectAux` and adds its comparison count to `used`. -/
theorem fastAux_equiv (num den fuel r used : ℕ) :
    fastAux num fuel r (den*r^4) used =
      ⟨(selectAux num den fuel r).segments,
        used+(selectAux num den fuel r).comparisons⟩ := by
  induction fuel generalizing r used with
  | zero => simp [fastAux, selectAux]
  | succ fuel ih =>
      simp only [fastAux, selectAux]
      split_ifs with h
      · rfl
      · have he : 16*(den*r^4) = den*(2*r)^4 := by ring
        rw [he, ih]
        simp [Nat.add_assoc, Nat.add_comm]

/-- Runs the incremental selector from one segment, bound `den`, zero comparisons, and fuel
`num.size`. -/
def fastSelect (num den : ℕ) : Selection := fastAux num num.size 1 den 0

/-- The incremental selector returns exactly the same count and comparison count as `select`. -/
theorem fastSelect_eq_select (num den : ℕ) : fastSelect num den = select num den := by
  simpa [fastSelect, select] using fastAux_equiv num den num.size 1 0

example : fastSelect 16 1 = ⟨2, 2⟩ := by decide
example : fastSelect 17 1 = ⟨4, 3⟩ := by decide

end Qatlib.Concepts.FinitePrecision.ComputableInput.IntegerFourthRootSelector
