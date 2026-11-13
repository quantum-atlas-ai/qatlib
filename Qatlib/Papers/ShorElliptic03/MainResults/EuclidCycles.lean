/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Divisibility.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.IsBotOne
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.SuccPred
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Divisibility.Basic
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Order.Nat
import Mathlib.Order.SuccPred.Nat
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Cycle bounds for the Euclidean algorithm

This module defines `euclidQuotients` and the weighted count `euclidCycles`, with weight `1 + 4
* Nat.log2 q` for each quotient q. It proves Lemma 1 of [ProosZalka2003]: coprime inputs with p
> x ≥ 1 and p > 2 have cycle count at most 4.5 log₂ p, using recursive identities and explicit
logarithmic estimates.

## Main statements

* `euclidQuotients_prod_le`: The product of the Euclidean quotients is bounded by the positive
  first input when the second does not exceed it.
* `euclidCycles_cons`: The cycle count satisfies the Euclidean recursion with the prescribed
  quotient weight.
* `euclidCycles_le`: The cycle count is at most 4.5 log₂ p for the stated coprime inputs.

## References

* [Proos and Zalka, 2003][ProosZalka2003]
-/

set_option autoImplicit false
noncomputable section
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.ShorElliptic03.MainResults.EuclidCycles

/-- The real base-two logarithm used in the cycle bound. -/
def paperLog2 (x : ℝ) : ℝ := Real.logb 2 x

/-- The list of natural-number quotients produced by repeated Euclidean division, terminating
when the second input is zero. -/
def euclidQuotients : ℕ → ℕ → List ℕ
  | _a, 0 => []
  | a, b + 1 => (a / (b + 1)) :: euclidQuotients (b + 1) (a % (b + 1))
termination_by _a b => b
decreasing_by
  simp_wf
  exact Nat.le_of_lt_succ (Nat.mod_lt _ (Nat.succ_pos _))

/-- The length of the Euclidean quotient list plus four times the sum of the natural base-two
logarithms of its entries. -/
def euclidCycles (p x : ℕ) : ℕ :=
  (euclidQuotients p x).length +
    4 * ((euclidQuotients p x).map Nat.log2).sum

/-- For a positive second input, the Euclidean quotient list starts with `a / b` and continues
with the list for `b` and `a % b`. -/
theorem euclidQuotients_cons (a b : ℕ) (hb : 0 < b) :
    euclidQuotients a b = (a / b) :: euclidQuotients b (a % b) := by
  cases b with
  | zero => omega
  | succ b => simp only [euclidQuotients]

/-- For `0 < a` and `b ≤ a`, the product of the Euclidean quotients for `a` and `b` is at most
`a`. -/
theorem euclidQuotients_prod_le (a b : ℕ) (ha : 0 < a) (hb : b ≤ a) :
    (euclidQuotients a b).prod ≤ a := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    cases b with
    | zero =>
      simp only [euclidQuotients, List.prod_nil]
      exact Nat.one_le_of_lt ha
    | succ b =>
      rw [euclidQuotients_cons a (b + 1) (Nat.succ_pos b)]
      simp only [List.prod_cons]
      have hr : a % (b + 1) ≤ b :=
        Nat.le_of_lt_succ (Nat.mod_lt a (Nat.succ_pos b))
      have htail : (euclidQuotients (b + 1) (a % (b + 1))).prod ≤ b + 1 :=
        ih (a % (b + 1)) (Nat.lt_succ_of_le hr) (b + 1) (Nat.succ_pos b)
          (Nat.le_of_lt (Nat.mod_lt a (Nat.succ_pos b)))
      calc
        a / (b + 1) * (euclidQuotients (b + 1) (a % (b + 1))).prod
            ≤ a / (b + 1) * (b + 1) := Nat.mul_le_mul_left _ htail
        _ ≤ a := Nat.div_mul_le_self a (b + 1)

/-- For `b > 0`, the cycle count for `(a, b)` is `1 + 4 * Nat.log2 (a / b)` plus the cycle count
for `(b, a % b)`. -/
theorem euclidCycles_cons (a b : ℕ) (hb : 0 < b) :
    euclidCycles a b = 1 + 4 * Nat.log2 (a / b) + euclidCycles b (a % b) := by
  unfold euclidCycles
  rw [euclidQuotients_cons a b hb]
  simp only [List.length_cons, List.map_cons, List.sum_cons]
  rw [Nat.mul_add]
  omega

/-- The cycle count for `(p, 1)` equals `4 * Nat.log2 p + 1`. -/
theorem euclidCycles_one (p : ℕ) : euclidCycles p 1 = 4 * Nat.log2 p + 1 := by
  have h := euclidCycles_cons p 1 (by norm_num)
  simp only [Nat.div_one, Nat.mod_one, euclidCycles, euclidQuotients,
    List.length_nil, List.map_nil, List.sum_nil] at h ⊢
  omega

/-- For positive naturals `m` and `v`, the inequality `2 ^ u ≤ m ^ v` implies the real bound `2
^ (u / v) ≤ m`. -/
lemma rpow_two_div_le {m u v : ℕ} (hm : 0 < m) (hv : 0 < v) (h : 2 ^ u ≤ m ^ v) :
    (2 : ℝ) ^ ((u : ℝ) / (v : ℝ)) ≤ (m : ℝ) := by
  have hv0 : (v : ℝ) ≠ 0 := by positivity
  rw [div_eq_mul_inv, Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2), Real.rpow_natCast]
  rw [← Real.pow_rpow_inv_natCast (x := (m : ℝ)) (by positivity) (by omega : v ≠ 0)]
  rw [Real.rpow_le_rpow_iff (by positivity) (by positivity) (by positivity)]
  exact_mod_cast h

/-- For positive naturals `m` and `v`, the inequality `2 ^ u ≤ m ^ v` implies `u / v ≤ Real.logb
2 m` over the reals. -/
lemma le_logb_two {m u v : ℕ} (hm : 0 < m) (hv : 0 < v) (h : 2 ^ u ≤ m ^ v) :
    (u : ℝ) / (v : ℝ) ≤ Real.logb 2 (m : ℝ) := by
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by exact_mod_cast hm)]
  exact rpow_two_div_le hm hv h

/-- The real base-two logarithm of three is at least `4/3`. -/
lemma logb_two_three : (4/3 : ℝ) ≤ Real.logb 2 3 := by
  have h := le_logb_two (m := 3) (u := 4) (v := 3) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 4 ≤ 3 ^ 3)
  simpa using h

/-- The real base-two logarithm of five is at least `20/9`. -/
lemma logb_two_five : (20/9 : ℝ) ≤ Real.logb 2 5 := by
  have h := le_logb_two (m := 5) (u := 20) (v := 9) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 20 ≤ 5 ^ 9)
  simpa using h

/-- The real base-two logarithm of two equals one. -/
lemma logb_two_two : Real.logb 2 (2:ℝ) = 1 := Real.logb_self_eq_one (by norm_num)

/-- The real base-two logarithm is monotone between positive ordered inputs. -/
lemma logb_mono {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.logb 2 a ≤ Real.logb 2 b :=
  (Real.logb_le_logb (b := 2) (by norm_num) ha (by linarith)).mpr hab

/-- The real base-two logarithm of nine is at least `28/9`. -/
lemma logb_two_nine : (28/9 : ℝ) ≤ Real.logb 2 9 := by
  have h := le_logb_two (m := 9) (u := 28) (v := 9) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 28 ≤ 9 ^ 9)
  simpa using h

/-- The real base-two logarithm of seven is at least `22/9`. -/
lemma logb_two_seven : (22/9 : ℝ) ≤ Real.logb 2 7 := by
  have h := le_logb_two (m := 7) (u := 22) (v := 9) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 22 ≤ 7 ^ 9)
  simpa using h

/-- The real base-two logarithm of eleven is at least `10/3`. -/
lemma logb_two_eleven : (10/3 : ℝ) ≤ Real.logb 2 11 := by
  have h := le_logb_two (m := 11) (u := 10) (v := 3) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 10 ≤ 11 ^ 3)
  simpa using h

/-- The real base-two logarithm of nineteen is at least `38/9`. -/
lemma logb_two_nineteen : (38/9 : ℝ) ≤ Real.logb 2 19 := by
  have h := le_logb_two (m := 19) (u := 38) (v := 9) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 38 ≤ 19 ^ 9)
  simpa using h

/-- The real base-two logarithm of thirty-five is at least `46/9`. -/
lemma logb_two_thirtyfive : (46/9 : ℝ) ≤ Real.logb 2 35 := by
  have h := le_logb_two (m := 35) (u := 46) (v := 9) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 46 ≤ 35 ^ 9)
  simpa using h

/-- The real base-two logarithm of ten is at least `29/9`. -/
lemma logb_two_ten : (29/9 : ℝ) ≤ Real.logb 2 10 := by
  have h := le_logb_two (m := 10) (u := 29) (v := 9) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 29 ≤ 10 ^ 9)
  simpa using h

/-- The real base-two logarithm of eighteen is at least `25/6`. -/
lemma logb_two_eighteen : (25/6 : ℝ) ≤ Real.logb 2 18 := by
  have h := le_logb_two (m := 18) (u := 25) (v := 6) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 25 ≤ 18 ^ 6)
  simpa using h

/-- For `p ≥ 3`, the expression `4 * Nat.log2 p + 1`, viewed in the reals, is at most `4.5 *
Real.logb 2 p`. -/
theorem cycleBound_base (p : ℕ) (hp : 3 ≤ p) :
    (4 * (Nat.log2 p : ℝ) + 1) ≤ 4.5 * Real.logb 2 (p : ℝ) := by
  have hp0 : p ≠ 0 := by omega
  have hk_le : ((Nat.log2 p : ℕ) : ℝ) ≤ Real.logb 2 (p : ℝ) := by
    have h2 : (2:ℝ) ^ (Nat.log2 p : ℕ) ≤ (p:ℝ) := by
      have h := (Nat.le_log2 hp0).mp le_rfl
      exact_mod_cast h
    have hh := (Real.logb_le_logb (b := 2) (by norm_num) (by positivity) (by positivity)).mpr h2
    rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at hh
  have hk1 : 1 ≤ Nat.log2 p := (Nat.le_log2 hp0).mpr (by omega : 2 ^ 1 ≤ p)
  rcases Nat.lt_or_ge (Nat.log2 p) 2 with hk | hk
  · have hk_eq : Nat.log2 p = 1 := by omega
    have h3 : (3:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp
    have hm := logb_mono (by norm_num : (0:ℝ) < 3) h3
    rw [hk_eq]; push_cast
    nlinarith [logb_two_three]
  · have h2' : (2:ℝ) ≤ (Nat.log2 p : ℝ) := by exact_mod_cast hk
    nlinarith

/-- For `n ≥ 1`, the real value of `4 * Nat.log2 n + 1` is at most `4.5 * Real.logb 2 (n + 1)`. -/
theorem cycleBound_succ (n : ℕ) (hn : 1 ≤ n) :
    (4 * (Nat.log2 n : ℝ) + 1) ≤ 4.5 * Real.logb 2 ((n + 1 : ℕ) : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hcast : ((n + 1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have h2k : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn0).mp le_rfl
  rcases Nat.lt_or_ge (Nat.log2 n) 2 with hk | hk
  · rcases Nat.eq_zero_or_pos (Nat.log2 n) with hk0 | hkpos
    · have hn1 : n = 1 := by
        have h2 : n < 2 ^ (Nat.log2 n + 1) := (Nat.log2_eq_iff hn0).mp rfl |>.2
        rw [hk0] at h2; omega
      subst hn1
      have hlog1 : Nat.log2 1 = 0 := by decide
      have h2 : (((1:ℕ):ℝ) + 1) = 2 := by norm_num
      rw [hlog1, h2, logb_two_two]; norm_num
    · have hk1 : Nat.log2 n = 1 := by omega
      have hn2 : 2 ≤ n := by have : 2 ^ 1 ≤ n := hk1 ▸ h2k; simpa using this
      have hge : (3:ℝ) ≤ (n:ℝ) + 1 := by
        have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 3) hge
      rw [hk1]; push_cast
      nlinarith [logb_two_three]
  · have hk2 : (2:ℝ) ≤ (Nat.log2 n : ℝ) := by exact_mod_cast hk
    have hlt : (2:ℝ) ^ (Nat.log2 n : ℕ) < (n:ℝ) + 1 := by
      have h : (2:ℝ) ^ (Nat.log2 n : ℕ) ≤ (n:ℝ) := by exact_mod_cast h2k
      linarith
    have hlog : (Nat.log2 n : ℝ) < Real.logb 2 ((n:ℝ) + 1) := by
      have h := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hlt
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
    nlinarith

/-- For `n ≥ 1`, the real value of `4 * Nat.log2 n + 2` is at most `4.5 * Real.logb 2 (n + 1)`. -/
theorem cycleBound_succ2 (n : ℕ) (hn : 1 ≤ n) :
    (4 * (Nat.log2 n : ℝ) + 2) ≤ 4.5 * Real.logb 2 ((n + 1 : ℕ) : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have hcast : ((n + 1 : ℕ) : ℝ) = (n:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  have h2k : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn0).mp le_rfl
  have n_lt : n < 2 ^ (Nat.log2 n + 1) := (Nat.log2_eq_iff hn0).mp rfl |>.2
  rcases Nat.lt_or_ge (Nat.log2 n) 4 with hk | hk
  · rcases Nat.eq_zero_or_pos (Nat.log2 n) with hk0 | hkpos
    · have hn1 : n = 1 := by rw [hk0] at n_lt; omega
      subst hn1
      have hlog1 : Nat.log2 1 = 0 := by decide
      have h2 : (((1:ℕ):ℝ) + 1) = 2 := by norm_num
      rw [hlog1, h2, logb_two_two]; norm_num
    · rcases Nat.lt_or_ge (Nat.log2 n) 2 with hk2 | hk2
      · have hk1 : Nat.log2 n = 1 := by omega
        have hn2 : 2 ≤ n := by have : 2 ^ 1 ≤ n := hk1 ▸ h2k; simpa using this
        have hge : (3:ℝ) ≤ (n:ℝ) + 1 := by
          have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
          linarith
        have hm := logb_mono (by norm_num : (0:ℝ) < 3) hge
        rw [hk1]; push_cast
        nlinarith [logb_two_three]
      · rcases Nat.lt_or_ge (Nat.log2 n) 3 with hk3 | hk3
        · have hk1 : Nat.log2 n = 2 := by omega
          have hn4 : 4 ≤ n := by have : 2 ^ 2 ≤ n := hk1 ▸ h2k; simpa using this
          have hge : (5:ℝ) ≤ (n:ℝ) + 1 := by
            have : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn4
            linarith
          have hm := logb_mono (by norm_num : (0:ℝ) < 5) hge
          rw [hk1]; push_cast
          nlinarith [logb_two_five]
        · have hk1 : Nat.log2 n = 3 := by omega
          have hn8 : 8 ≤ n := by have : 2 ^ 3 ≤ n := hk1 ▸ h2k; simpa using this
          have hge : (9:ℝ) ≤ (n:ℝ) + 1 := by
            have : (8:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn8
            linarith
          have hm := logb_mono (by norm_num : (0:ℝ) < 9) hge
          rw [hk1]; push_cast
          nlinarith [logb_two_nine]
  · have hk4 : (4:ℝ) ≤ (Nat.log2 n : ℝ) := by exact_mod_cast hk
    have hlt : (2:ℝ) ^ (Nat.log2 n : ℕ) < (n:ℝ) + 1 := by
      have h : (2:ℝ) ^ (Nat.log2 n : ℕ) ≤ (n:ℝ) := by exact_mod_cast h2k
      linarith
    have hlog : (Nat.log2 n : ℝ) < Real.logb 2 ((n:ℝ) + 1) := by
      have h := Real.logb_lt_logb (b := 2) (by norm_num) (by positivity) hlt
      rwa [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
    nlinarith

/-- For `n ≥ 1`, the real value of `4 * Nat.log2 n + 6` is at most `4.5 * Real.logb 2 (2 * n +
1)`. -/
theorem cycleBound_two_mul (n : ℕ) (hn : 1 ≤ n) :
    (4 * (Nat.log2 n : ℝ) + 6) ≤ 4.5 * Real.logb 2 ((2 * n + 1 : ℕ) : ℝ) := by
  have hn0 : n ≠ 0 := by omega
  have h2k : 2 ^ Nat.log2 n ≤ n := (Nat.le_log2 hn0).mp le_rfl
  have hcast : ((2 * n + 1 : ℕ) : ℝ) = 2 * (n:ℝ) + 1 := by push_cast; ring
  rw [hcast]
  rcases Nat.lt_or_ge (Nat.log2 n) 3 with hk | hk
  · rcases Nat.eq_zero_or_pos (Nat.log2 n) with hk0 | hkpos
    · have hn1 : n = 1 := by
        have h2 : n < 2 ^ (Nat.log2 n + 1) := (Nat.log2_eq_iff hn0).mp rfl |>.2
        rw [hk0] at h2; omega
      subst hn1
      have hlog1 : Nat.log2 1 = 0 := by decide
      have h3 : (2 * ((1:ℕ):ℝ) + 1) = 3 := by norm_num
      rw [hlog1, h3]; push_cast
      nlinarith [logb_two_three]
    · rcases Nat.lt_or_ge (Nat.log2 n) 2 with hk2 | hk2
      · have hk1 : Nat.log2 n = 1 := by omega
        have hn2 : 2 ≤ n := by have : 2 ^ 1 ≤ n := hk1 ▸ h2k; simpa using this
        have hge : (5:ℝ) ≤ 2 * (n:ℝ) + 1 := by
          have : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
          linarith
        have hm := logb_mono (by norm_num : (0:ℝ) < 5) hge
        rw [hk1]; push_cast
        nlinarith [logb_two_five]
      · have hk1 : Nat.log2 n = 2 := by omega
        have hn4 : 4 ≤ n := by have : 2 ^ 2 ≤ n := hk1 ▸ h2k; simpa using this
        have hge : (9:ℝ) ≤ 2 * (n:ℝ) + 1 := by
          have : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn4
          linarith
        have hm := logb_mono (by norm_num : (0:ℝ) < 9) hge
        rw [hk1]; push_cast
        nlinarith [logb_two_nine]
  · have hk3 : (3:ℝ) ≤ (Nat.log2 n : ℝ) := by exact_mod_cast hk
    have hn2 : (2:ℝ) ^ (Nat.log2 n + 1 : ℕ) ≤ 2 * (n:ℝ) := by
      have h : 2 ^ (Nat.log2 n + 1) ≤ 2 * n := by rw [Nat.pow_succ]; omega
      exact_mod_cast h
    have hlt : (2:ℝ) ^ (Nat.log2 n + 1 : ℕ) < 2 * (n:ℝ) + 1 := by linarith
    have hlog : (Nat.log2 n : ℝ) + 1 ≤ Real.logb 2 (2 * (n:ℝ) + 1) := by
      have h :=
          (Real.logb_le_logb (b := 2) (by norm_num) (by positivity) (by positivity)).mpr
          (le_of_lt hlt)
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
      push_cast at h
      exact h
    nlinarith

/-- The real base-two logarithm of six is at least `5/2`. -/
lemma logb_two_six : (5/2 : ℝ) ≤ Real.logb 2 6 := by
  have h := le_logb_two (m := 6) (u := 5) (v := 2) (by norm_num) (by norm_num)
    (by norm_num : 2 ^ 5 ≤ 6 ^ 2)
  simpa using h

/-- For odd `x ≥ 3`, the real value of `7 + 4 * Nat.log2 (x / 2)` is at most `4.5 * Real.logb 2
(x + 2)`. -/
theorem r1two_one (x : ℕ) (hx3 : 3 ≤ x) (hodd : x % 2 = 1) :
    7 + 4 * (Nat.log2 (x / 2) : ℝ) ≤ 4.5 * Real.logb 2 ((x + 2 : ℕ) : ℝ) := by
  have h2k : 2 ^ Nat.log2 (x/2) ≤ x/2 := (Nat.le_log2 (by omega : x/2 ≠ 0)).mp le_rfl
  have hcast : ((x + 2 : ℕ) : ℝ) = (x:ℝ) + 2 := by push_cast; ring
  rw [hcast]
  have hx_low_nat : 2 ^ (Nat.log2 (x/2) + 1) + 1 ≤ x := by
    have h1 : 2 ^ (Nat.log2 (x/2) + 1) ≤ 2 * (x/2) := by rw [Nat.pow_succ]; omega
    have hxodd : x = 2 * (x/2) + 1 := by have := Nat.div_add_mod x 2; omega
    omega
  have hx_low : (2:ℝ) ^ (Nat.log2 (x/2) + 1 : ℕ) + 1 ≤ (x:ℝ) := by exact_mod_cast hx_low_nat
  rcases Nat.lt_or_ge (Nat.log2 (x/2)) 5 with hk | hk
  · interval_cases h : Nat.log2 (x/2)
    · have hxn : (3:ℕ) ≤ x := by have := hx_low_nat; norm_num at this ⊢; exact this
      have hge : (5:ℝ) ≤ (x:ℝ) + 2 := by
        have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxn
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 5) hge
      norm_num
      nlinarith [logb_two_five]
    · have hxn : (5:ℕ) ≤ x := by have := hx_low_nat; norm_num at this ⊢; exact this
      have hge : (7:ℝ) ≤ (x:ℝ) + 2 := by
        have h3 : (5:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxn
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 7) hge
      norm_num
      nlinarith [logb_two_seven]
    · have hxn : (9:ℕ) ≤ x := by have := hx_low_nat; norm_num at this ⊢; exact this
      have hge : (11:ℝ) ≤ (x:ℝ) + 2 := by
        have h3 : (9:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxn
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 11) hge
      norm_num
      nlinarith [logb_two_eleven]
    · have hxn : (17:ℕ) ≤ x := by have := hx_low_nat; norm_num at this ⊢; exact this
      have hge : (19:ℝ) ≤ (x:ℝ) + 2 := by
        have h3 : (17:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxn
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 19) hge
      norm_num
      nlinarith [logb_two_nineteen]
    · have hxn : (33:ℕ) ≤ x := by have := hx_low_nat; norm_num at this ⊢; exact this
      have hge : (35:ℝ) ≤ (x:ℝ) + 2 := by
        have h3 : (33:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxn
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 35) hge
      norm_num
      nlinarith [logb_two_thirtyfive]
  · have hpow_lt : (2:ℝ) ^ (Nat.log2 (x/2) + 1 : ℕ) < (x:ℝ) + 2 := by
      have := hx_low; linarith
    have hlog : (Nat.log2 (x/2) : ℝ) + 1 ≤ Real.logb 2 ((x:ℝ) + 2) := by
      have h :=
          (Real.logb_le_logb (b := 2) (by norm_num) (by positivity) (by positivity)).mpr
          (le_of_lt hpow_lt)
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
      push_cast at h; exact h
    have hk5 : (5:ℝ) ≤ (Nat.log2 (x/2) : ℝ) := by exact_mod_cast hk
    nlinarith

/-- For odd `x ≥ 3`, the real value of `11 + 4 * Nat.log2 (x / 2)` is at most `4.5 * Real.logb 2
(2 * x + 2)`. -/
theorem r1two_two (x : ℕ) (hx3 : 3 ≤ x) (hodd : x % 2 = 1) :
    11 + 4 * (Nat.log2 (x / 2) : ℝ) ≤ 4.5 * Real.logb 2 ((2 * x + 2 : ℕ) : ℝ) := by
  have h2k : 2 ^ Nat.log2 (x/2) ≤ x/2 := (Nat.le_log2 (by omega : x/2 ≠ 0)).mp le_rfl
  have hcast : ((2 * x + 2 : ℕ) : ℝ) = 2 * (x:ℝ) + 2 := by push_cast; ring
  rw [hcast]
  have hsplit : Real.logb 2 (2 * (x:ℝ) + 2) = 1 + Real.logb 2 ((x:ℝ) + 1) := by
    have he : (2:ℝ) * (x:ℝ) + 2 = 2 * ((x:ℝ) + 1) := by ring
    rw [he, Real.logb_mul (by norm_num) (by positivity), logb_two_two]
  rw [hsplit]
  have hx_low_nat : 2 ^ (Nat.log2 (x/2) + 1) + 1 ≤ x := by
    have h1 : 2 ^ (Nat.log2 (x/2) + 1) ≤ 2 * (x/2) := by rw [Nat.pow_succ]; omega
    have hxodd : x = 2 * (x/2) + 1 := by have := Nat.div_add_mod x 2; omega
    omega
  have hx_low : (2:ℝ) ^ (Nat.log2 (x/2) + 1 : ℕ) + 1 ≤ (x:ℝ) := by exact_mod_cast hx_low_nat
  rcases Nat.lt_or_ge (Nat.log2 (x/2)) 4 with hk | hk
  · interval_cases h : Nat.log2 (x/2)
    · have hxn : (3:ℕ) ≤ x := by have := hx_low_nat; norm_num at this ⊢; exact this
      have hge : (4:ℝ) ≤ (x:ℝ) + 1 := by
        have h3 : (3:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxn
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 4) hge
      have h4 : Real.logb 2 (4:ℝ) = 2 := by
        rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.logb_pow, logb_two_two]; norm_num
      norm_num
      nlinarith [hm, h4]
    · have hxn : (5:ℕ) ≤ x := by have := hx_low_nat; norm_num at this ⊢; exact this
      have hge : (6:ℝ) ≤ (x:ℝ) + 1 := by
        have h3 : (5:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxn
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 6) hge
      norm_num
      nlinarith [logb_two_six]
    · have hxn : (9:ℕ) ≤ x := by have := hx_low_nat; norm_num at this ⊢; exact this
      have hge : (10:ℝ) ≤ (x:ℝ) + 1 := by
        have h3 : (9:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxn
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 10) hge
      norm_num
      nlinarith [logb_two_ten]
    · have hxn : (17:ℕ) ≤ x := by have := hx_low_nat; norm_num at this ⊢; exact this
      have hge : (18:ℝ) ≤ (x:ℝ) + 1 := by
        have h3 : (17:ℝ) ≤ (x:ℝ) := by exact_mod_cast hxn
        linarith
      have hm := logb_mono (by norm_num : (0:ℝ) < 18) hge
      norm_num
      nlinarith [logb_two_eighteen]
  · have hpow_lt : (2:ℝ) ^ (Nat.log2 (x/2) + 1 : ℕ) < (x:ℝ) + 1 := by
      have := hx_low; linarith
    have hlog : (Nat.log2 (x/2) : ℝ) + 1 ≤ Real.logb 2 ((x:ℝ) + 1) := by
      have h :=
          (Real.logb_le_logb (b := 2) (by norm_num) (by positivity) (by positivity)).mpr
          (le_of_lt hpow_lt)
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num), mul_one] at h
      push_cast at h; exact h
    have hk4 : (4:ℝ) ≤ (Nat.log2 (x/2) : ℝ) := by exact_mod_cast hk
    nlinarith

/-- If `q = k * x + 2` and `q` is coprime to `x`, then the greatest common divisor of `x` and
two is one. -/
lemma gcd_two_eq_one_of_coprime {q x k : ℕ} (hq : q = k * x + 2) (h : Nat.Coprime q x) :
    x.gcd 2 = 1 := by
  have hgq : x.gcd q = 1 := by rw [Nat.gcd_comm]; exact h
  have hdvd : x.gcd 2 ∣ x.gcd q := by
    apply Nat.dvd_gcd (Nat.gcd_dvd_left x 2)
    have h1 : x.gcd 2 ∣ x := Nat.gcd_dvd_left x 2
    have h2 : x.gcd 2 ∣ 2 := Nat.gcd_dvd_right x 2
    have h3 : x.gcd 2 ∣ k * x + 2 := dvd_add (Dvd.dvd.mul_left h1 k) h2
    rwa [← hq] at h3
  rw [hgq] at hdvd
  exact Nat.dvd_one.mp hdvd

/-- A natural number whose greatest common divisor with two is one has remainder one modulo two. -/
lemma odd_of_gcd_two {x : ℕ} (h : x.gcd 2 = 1) : x % 2 = 1 := by
  have hne : x % 2 ≠ 0 := by
    intro h0
    have hd : 2 ∣ x := Nat.dvd_of_mod_eq_zero h0
    have h2d : 2 ∣ x.gcd 2 := Nat.dvd_gcd hd (dvd_refl 2)
    rw [h] at h2d
    have h1 := Nat.dvd_one.mp h2d
    omega
  have := Nat.mod_lt x (by norm_num : 0 < 2)
  omega

/-- For coprime naturals with `p > x ≥ 1` and `p > 2`, the Euclidean cycle count is at most `4.5
* paperLog2 p`. This is Lemma 1 of [ProosZalka2003]. -/
theorem euclidCycles_le (p x : ℕ) (hp2 : 2 < p) (hx1 : 1 ≤ x) (hxp : x < p)
    (hcop : Nat.Coprime p x) :
    (euclidCycles p x : ℝ) ≤ 4.5 * paperLog2 (p : ℝ) := by
  change (euclidCycles p x : ℝ) ≤ 4.5 * Real.logb 2 (p : ℝ)
  suffices H : ∀ q : ℕ, ∀ y : ℕ, 2 < q → 1 ≤ y → y < q → Nat.Coprime q y →
      (euclidCycles q y : ℝ) ≤ 4.5 * Real.logb 2 (q : ℝ) from H p x hp2 hx1 hxp hcop
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
    intro x hq2 hx1 hxq hcop
    rcases eq_or_lt_of_le hx1 with rfl | hx2
    · have hq3 : 3 ≤ q := by omega
      have heq : (euclidCycles q 1 : ℝ) = 4 * (Nat.log2 q : ℝ) + 1 := by
        rw [euclidCycles_one]; push_cast; ring
      rw [heq]; exact cycleBound_base q hq3
    · rcases eq_or_lt_of_le (Nat.succ_le_of_lt hx2) with rfl | hx3
      · have hodd : q % 2 = 1 := odd_of_gcd_two hcop
        have hqdiv : 1 ≤ q / 2 := Nat.div_pos (by omega : 2 ≤ q) (by norm_num)
        have hqeq : q = 2 * (q/2) + 1 := by have := Nat.div_add_mod q 2; omega
        have h21 : euclidCycles 2 1 = 5 := by rw [euclidCycles_one]; decide
        have hrec : (euclidCycles q 2 : ℝ) = 1 + 4 * (Nat.log2 (q / 2) : ℝ) + (euclidCycles 2 (q % 2) : ℝ) := by
          rw [euclidCycles_cons q 2 (by norm_num)]; push_cast; ring
        have hprof := cycleBound_two_mul (q/2) hqdiv
        have hcastq : (((2 * (q/2) + 1 : ℕ)) : ℝ) = (q:ℝ) := by rw [← hqeq]
        rw [hcastq] at hprof
        rw [hrec, hodd, h21]
        push_cast
        linarith [hcastq]
      · have hxpos : 0 < x := by omega
        have hdm : x * (q / x) + q % x = q := Nat.div_add_mod q x
        have hmod_lt : q % x < x := Nat.mod_lt q hxpos
        have hmod_ne : q % x ≠ 0 := by
          intro h0
          have hdvd : x ∣ q := Nat.dvd_of_mod_eq_zero h0
          have : x ∣ q.gcd x := Nat.dvd_gcd hdvd (dvd_refl x)
          rw [hcop] at this
          have hx1' : x = 1 := Nat.dvd_one.mp this
          omega
        have hcx : x.gcd (q % x) = 1 := by
          rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact hcop
        have hrec : (euclidCycles q x : ℝ) = 1 + 4 * (Nat.log2 (q / x) : ℝ) + (euclidCycles x (q % x) : ℝ) := by
          rw [euclidCycles_cons q x hxpos]; push_cast; ring
        have hq1pos : 1 ≤ q / x := Nat.div_pos (by omega : x ≤ q) hxpos
        rcases Nat.lt_or_ge (q / x) 3 with hq13 | hq13
        · have hq1le : q / x ≤ 2 := by omega
          have hqx : q = x * (q / x) + q % x := by omega
          rcases (by omega : q / x = 1 ∨ q / x = 2) with hq1 | hq1
          · have hq_eq : q = x + q % x := by rw [hq1] at hdm; omega
            rcases Nat.lt_or_ge (q % x) 2 with hr1 | hr1
            · have hr1eq : q % x = 1 := by omega
              have hqX : q = x + 1 := by rw [hq_eq, hr1eq]
              have heq : (euclidCycles q x : ℝ) = 4 * (Nat.log2 x : ℝ) + 2 := by
                rw [hrec, hq1, hr1eq, euclidCycles_one]
                have hlog1 : Nat.log2 1 = 0 := by decide
                rw [hlog1]; push_cast; ring
              rw [heq, hqX]
              exact cycleBound_succ2 x hx1
            · rcases Nat.lt_or_ge (q % x) 3 with hr1' | hr1'
              · have hr1eq : q % x = 2 := by omega
                have hqX : q = x + 2 := by rw [hq_eq, hr1eq]
                have hodd : x % 2 = 1 :=
                  odd_of_gcd_two (gcd_two_eq_one_of_coprime (k := 1) (by rw [hqX]; ring) hcop)
                have hrecx2 : (euclidCycles x 2 : ℝ) = 1 + 4 * (Nat.log2 (x / 2) : ℝ) + (euclidCycles 2 (x % 2) : ℝ) := by
                  rw [euclidCycles_cons x 2 (by norm_num)]; push_cast; ring
                have h21 : euclidCycles 2 1 = 5 := by rw [euclidCycles_one]; decide
                have heq : (euclidCycles q x : ℝ) = 7 + 4 * (Nat.log2 (x / 2) : ℝ) := by
                  rw [hrec, hq1, hr1eq, hrecx2, hodd, h21]
                  have hlog1 : Nat.log2 1 = 0 := by decide
                  rw [hlog1]; push_cast; ring
                rw [heq, hqX]
                exact r1two_one x hx3 hodd
              · have hr1ge : 3 ≤ q % x := hr1'
                have hcr1 : (q % x).gcd (x % (q % x)) = 1 := by
                  rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact hcx
                have hr2pos : 1 ≤ x % (q % x) := by
                  have hne : x % (q % x) ≠ 0 := by
                    intro h0
                    have hdvd : q % x ∣ x := Nat.dvd_of_mod_eq_zero h0
                    have : q % x ∣ x.gcd (q % x) := Nat.dvd_gcd hdvd (dvd_refl _)
                    rw [hcx] at this
                    have h1 : q % x = 1 := Nat.dvd_one.mp this
                    omega
                  have := Nat.mod_lt x (by omega : 0 < q % x)
                  omega
                have hmod2_lt : x % (q % x) < q % x := Nat.mod_lt x (by omega)
                have hih :=
                    ih (q % x) (by omega : q % x < q) (x % (q % x))
                    (by omega : 2 < q % x) hr2pos hmod2_lt hcr1
                have hrec2 : (euclidCycles x (q % x) : ℝ) = 1 + 4 * (Nat.log2 (x / (q % x)) : ℝ) + (euclidCycles (q % x) (x % (q % x)) : ℝ) := by
                  rw [euclidCycles_cons x (q % x) (by omega)]; push_cast; ring
                have heq : (euclidCycles q x : ℝ) = 2 + 4 * (Nat.log2 (q / x) : ℝ) + 4 * (Nat.log2 (x / (q % x)) : ℝ) + (euclidCycles (q % x) (x % (q % x)) : ℝ) := by
                  rw [hrec, hrec2]; ring

                have hxdec : (q % x) * (x / (q % x)) + x % (q % x) = x := Nat.div_add_mod x (q % x)
                have hdmR : (x:ℝ) * ((q/x : ℕ):ℝ) + ((q%x : ℕ):ℝ) = (q:ℝ) := by exact_mod_cast hdm
                have hxdecR : ((q%x : ℕ):ℝ) * ((x/(q%x) : ℕ):ℝ) + ((x % (q%x) : ℕ):ℝ) = (x:ℝ) := by
                  exact_mod_cast hxdec
                have hr2nn : (0:ℝ) ≤ ((x % (q%x) : ℕ):ℝ) := by positivity
                have hq1v : ((q/x : ℕ):ℝ) = 1 := by rw [hq1]; norm_num
                have hprod : (((1 + (q/x) * (x/(q%x)) : ℕ)):ℝ) * ((q%x : ℕ):ℝ) ≤ (q:ℝ) := by
                  have hcast2 : (((1 + (q/x) * (x/(q%x)) : ℕ)):ℝ) * ((q%x : ℕ):ℝ)
                      = ((q%x : ℕ):ℝ) + ((q/x : ℕ):ℝ) * ((x/(q%x) : ℕ):ℝ) * ((q%x : ℕ):ℝ) := by
                    push_cast; ring
                  rw [hcast2]

                  have : (q:ℝ) = (((q%x : ℕ):ℝ) * ((x/(q%x) : ℕ):ℝ) + ((x % (q%x) : ℕ):ℝ)) * ((q/x : ℕ):ℝ) + ((q%x : ℕ):ℝ) := by
                    rw [← hdmR, ← hxdecR]
                  rw [this]
                  have hq1nn : (0:ℝ) ≤ ((q/x : ℕ):ℝ) := by positivity
                  nlinarith [hr2nn, hq1nn]
                have hlog_ge : Real.logb 2 ((q%x : ℕ):ℝ) + Real.logb 2 (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ)
                    ≤ Real.logb 2 (q:ℝ) := by
                  have h1 : (0:ℝ) < ((q%x : ℕ):ℝ) := by positivity
                  have h2 : (0:ℝ) < (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ) := by positivity
                  have hmul : Real.logb 2 (((q%x : ℕ):ℝ) * (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ))
                      = Real.logb 2 ((q%x : ℕ):ℝ) + Real.logb 2 (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ) :=
                    Real.logb_mul (ne_of_gt h1) (ne_of_gt h2)
                  have hle : ((q%x : ℕ):ℝ) * (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ) ≤ (q:ℝ) := by
                    rw [mul_comm]; exact hprod
                  have h1' : (0:ℝ) < ((q%x : ℕ):ℝ) * (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ) :=
                      mul_pos h1 h2
                  have hm := logb_mono h1' hle
                  rw [hmul] at hm
                  linarith

                have hq2pos : 1 ≤ x / (q % x) := Nat.div_pos (by omega : q % x ≤ x) (by omega)
                have hZ := cycleBound_succ2 (x / (q % x)) hq2pos

                have hq2cast : (((x / (q % x) + 1 : ℕ)):ℝ) = ((1 + (q/x)*(x/(q%x)) : ℕ):ℝ) := by
                  rw [hq1]; push_cast; ring
                have hlog1 : Nat.log2 1 = 0 := by decide
                have hq1log : ((Nat.log2 (q/x) : ℕ):ℝ) = 0 := by rw [hq1]; exact_mod_cast hlog1
                have hZ' := hZ
                rw [hq2cast] at hZ'
                rw [hq1log] at heq
                rw [heq]
                nlinarith [hih, hlog_ge, hZ']
          · have hq_eq : q = 2 * x + q % x := by rw [hq1] at hdm; omega
            rcases Nat.lt_or_ge (q % x) 2 with hr1 | hr1
            · have hr1eq : q % x = 1 := by omega
              have hqX : q = 2 * x + 1 := by rw [hq_eq, hr1eq]
              have heq : (euclidCycles q x : ℝ) = 6 + 4 * (Nat.log2 x : ℝ) := by
                rw [hrec, hq1, hr1eq, euclidCycles_one]
                have hlog2 : Nat.log2 2 = 1 := by decide
                rw [hlog2]; push_cast; ring
              rw [heq, hqX]
              linarith [cycleBound_two_mul x hx1]
            · rcases Nat.lt_or_ge (q % x) 3 with hr1' | hr1'
              · have hr1eq : q % x = 2 := by omega
                have hqX : q = 2 * x + 2 := by rw [hq_eq, hr1eq]
                have hodd : x % 2 = 1 :=
                  odd_of_gcd_two (gcd_two_eq_one_of_coprime (k := 2) hqX hcop)
                have hrecx2 : (euclidCycles x 2 : ℝ) = 1 + 4 * (Nat.log2 (x / 2) : ℝ) + (euclidCycles 2 (x % 2) : ℝ) := by
                  rw [euclidCycles_cons x 2 (by norm_num)]; push_cast; ring
                have h21 : euclidCycles 2 1 = 5 := by rw [euclidCycles_one]; decide
                have heq : (euclidCycles q x : ℝ) = 11 + 4 * (Nat.log2 (x / 2) : ℝ) := by
                  rw [hrec, hq1, hr1eq, hrecx2, hodd, h21]
                  have hlog2 : Nat.log2 2 = 1 := by decide
                  rw [hlog2]; push_cast; ring
                rw [heq, hqX]
                exact r1two_two x hx3 hodd
              · have hcr1 : (q % x).gcd (x % (q % x)) = 1 := by
                  rw [Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]; exact hcx
                have hr2pos : 1 ≤ x % (q % x) := by
                  have hne : x % (q % x) ≠ 0 := by
                    intro h0
                    have hdvd : q % x ∣ x := Nat.dvd_of_mod_eq_zero h0
                    have : q % x ∣ x.gcd (q % x) := Nat.dvd_gcd hdvd (dvd_refl _)
                    rw [hcx] at this
                    have h1 : q % x = 1 := Nat.dvd_one.mp this
                    omega
                  have := Nat.mod_lt x (by omega : 0 < q % x)
                  omega
                have hmod2_lt : x % (q % x) < q % x := Nat.mod_lt x (by omega)
                have hih :=
                    ih (q % x) (by omega : q % x < q) (x % (q % x))
                    (by omega : 2 < q % x) hr2pos hmod2_lt hcr1
                have hrec2 : (euclidCycles x (q % x) : ℝ) = 1 + 4 * (Nat.log2 (x / (q % x)) : ℝ) + (euclidCycles (q % x) (x % (q % x)) : ℝ) := by
                  rw [euclidCycles_cons x (q % x) (by omega)]; push_cast; ring
                have heq : (euclidCycles q x : ℝ) = 2 + 4 * (Nat.log2 (q / x) : ℝ) + 4 * (Nat.log2 (x / (q % x)) : ℝ) + (euclidCycles (q % x) (x % (q % x)) : ℝ) := by
                  rw [hrec, hrec2]; ring
                have hxdec : (q % x) * (x / (q % x)) + x % (q % x) = x := Nat.div_add_mod x (q % x)
                have hdmR : (x:ℝ) * ((q/x : ℕ):ℝ) + ((q%x : ℕ):ℝ) = (q:ℝ) := by exact_mod_cast hdm
                have hxdecR : ((q%x : ℕ):ℝ) * ((x/(q%x) : ℕ):ℝ) + ((x % (q%x) : ℕ):ℝ) = (x:ℝ) := by
                  exact_mod_cast hxdec
                have hr2nn : (0:ℝ) ≤ ((x % (q%x) : ℕ):ℝ) := by positivity
                have hq1v : ((q/x : ℕ):ℝ) = 2 := by rw [hq1]; norm_num
                have hprod : (((1 + (q/x) * (x/(q%x)) : ℕ)):ℝ) * ((q%x : ℕ):ℝ) ≤ (q:ℝ) := by
                  have hcast2 : (((1 + (q/x) * (x/(q%x)) : ℕ)):ℝ) * ((q%x : ℕ):ℝ)
                      = ((q%x : ℕ):ℝ) + ((q/x : ℕ):ℝ) * ((x/(q%x) : ℕ):ℝ) * ((q%x : ℕ):ℝ) := by
                    push_cast; ring
                  rw [hcast2]
                  have : (q:ℝ) = (((q%x : ℕ):ℝ) * ((x/(q%x) : ℕ):ℝ) + ((x % (q%x) : ℕ):ℝ)) * ((q/x : ℕ):ℝ) + ((q%x : ℕ):ℝ) := by
                    rw [← hdmR, ← hxdecR]
                  rw [this]
                  have hq1nn : (0:ℝ) ≤ ((q/x : ℕ):ℝ) := by positivity
                  nlinarith [hr2nn, hq1nn]
                have hlog_ge : Real.logb 2 ((q%x : ℕ):ℝ) + Real.logb 2 (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ)
                    ≤ Real.logb 2 (q:ℝ) := by
                  have h1 : (0:ℝ) < ((q%x : ℕ):ℝ) := by positivity
                  have h2 : (0:ℝ) < (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ) := by positivity
                  have hmul : Real.logb 2 (((q%x : ℕ):ℝ) * (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ))
                      = Real.logb 2 ((q%x : ℕ):ℝ) + Real.logb 2 (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ) :=
                    Real.logb_mul (ne_of_gt h1) (ne_of_gt h2)
                  have hle : ((q%x : ℕ):ℝ) * (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ) ≤ (q:ℝ) := by
                    rw [mul_comm]; exact hprod
                  have h1' : (0:ℝ) < ((q%x : ℕ):ℝ) * (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ) :=
                      mul_pos h1 h2
                  have hm := logb_mono h1' hle
                  rw [hmul] at hm
                  linarith
                have hq2pos : 1 ≤ x / (q % x) := Nat.div_pos (by omega : q % x ≤ x) (by omega)
                have hZ := cycleBound_two_mul (x / (q % x)) hq2pos
                have hq2cast : (((2 * (x / (q % x)) + 1 : ℕ)):ℝ) = (((1 + (q/x)*(x/(q%x)) : ℕ)):ℝ) := by
                  rw [hq1]; push_cast; ring
                have hlog2 : Nat.log2 2 = 1 := by decide
                have hq1log : ((Nat.log2 (q/x) : ℕ):ℝ) = 1 := by rw [hq1]; exact_mod_cast hlog2
                have hZ' := hZ
                rw [hq2cast] at hZ'
                rw [hq1log] at heq
                rw [heq]
                nlinarith [hih, hlog_ge, hZ']
        · have hbase := cycleBound_base (q/x) hq13
          have hih : (euclidCycles x (q % x) : ℝ) ≤ 4.5 * Real.logb 2 (x:ℝ) :=
            ih x hxq (q % x) hx3 (by omega) hmod_lt hcx
          have hqx_le : ((q/x : ℕ):ℝ) * (x:ℝ) ≤ (q:ℝ) := by
            have h := Nat.div_mul_le_self q x
            have h' : (((q/x) * x : ℕ):ℝ) ≤ (q:ℝ) := by exact_mod_cast h
            simpa [Nat.cast_mul] using h'
          have hmul : Real.logb 2 (((q/x : ℕ):ℝ) * (x:ℝ)) = Real.logb 2 ((q/x : ℕ):ℝ) + Real.logb 2 (x:ℝ) :=
            Real.logb_mul (by positivity) (by positivity)
          have hmono : Real.logb 2 (((q/x : ℕ):ℝ) * (x:ℝ)) ≤ Real.logb 2 (q:ℝ) :=
            logb_mono (by positivity) hqx_le
          rw [hrec]
          have h4 : 4 * (Nat.log2 (q/x) : ℝ) + 1 + (euclidCycles x (q % x) : ℝ)
              ≤ 4.5 * Real.logb 2 ((q/x:ℕ):ℝ) + 4.5 * Real.logb 2 (x:ℝ) := by
            linarith [hbase, hih]
          calc 1 + 4 * ↑(Nat.log2 (q / x)) + ↑(euclidCycles x (q % x))
              = 4 * ↑(Nat.log2 (q / x)) + 1 + ↑(euclidCycles x (q % x)) := by ring
            _ ≤ 4.5 * Real.logb 2 ((q/x:ℕ):ℝ) + 4.5 * Real.logb 2 (x:ℝ) := h4
            _ = 4.5 * (Real.logb 2 ((q/x:ℕ):ℝ) + Real.logb 2 (x:ℝ)) := by ring
            _ = 4.5 * Real.logb 2 (((q/x:ℕ):ℝ) * (x:ℝ)) := by rw [hmul]
            _ ≤ 4.5 * Real.logb 2 (q:ℝ) := by linarith [hmono]

end Qatlib.Papers.ShorElliptic03.MainResults.EuclidCycles
