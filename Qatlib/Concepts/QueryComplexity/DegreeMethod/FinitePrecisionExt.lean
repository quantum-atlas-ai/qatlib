/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs
import Qatlib.Concepts.SchattenDiamond.DiamondNorm.FiniteDiamondNorm
import Qatlib.Concepts.RawChannelWord.CptpWordBound.RawChannelWord
import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler
import Mathlib.Data.List.TakeDrop
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Order.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Finite-precision arithmetic and machine constructions

This module proves correctness and error bounds for dyadic arithmetic, rational interval
operations, and arithmetic on real names. It establishes square-root, division, sine, and
logarithm lifts with their specified precision and clock guarantees, providing finite-precision
infrastructure for the computational setting of [KitaevShenVyalyi2002].

The module also bounds errors in channel words using `mixedChain` and finite diamond distance,
and develops binary increment, repeated-increment addition, framed parsing, copying, length
counting, and pair-assembly stack programs with explicit execution bounds. For background on
channel norms, see [Watrous2018].

## Main statements

* `name_mul`: correctness of multiplication of real names under magnitude and precision-shift
  assumptions.
* `clause1_v2_sqrt_lift`, `clause1_v2_div_lift`, `clause1_v2_sin_lift`, and
  `clause1_v2_log_lift`: the specified elementary-function lifts.
* `approxWord_distance_bare_le`: a finite diamond distance bound of four times the sum of the
  individual step bounds.
* `word_computesAt`: linear time and space bounds for binary increment.
* `AddLoop.addLoop_complete` and `ParseFramed.parseFramed_total`: termination and clock bounds
  for addition and total framed parsing.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler

set_option autoImplicit false

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Foundations.IntervalArith.IntervalOps
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.CountedTake
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Expansion
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.GuardedCounter
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NatTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.NativeEcho
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.PairZip
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyCompare
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.ReadonlyRepeat
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Simulation
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Stacks
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TinyTag
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ValidatorSemantics
open Qatlib.Concepts.RawChannelWord.CptpWordBound
open Qatlib.Concepts.ReferenceError.DensityToRaw
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs
open Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic
open Qatlib.Concepts.SchattenDiamond.DiamondNorm

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib.Foundations.IntervalArith.IntervalOps (Interval Valid Contains unit width roundDown rounded)
open scoped ENNReal

namespace Dyadic

/-- Conversion to rational numbers preserves dyadic addition. -/
theorem toRat_add (a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : (a.add b).toRat = a.toRat + b.toRat := by
  simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.add,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.toRat]
  have h1 : (2:ℚ) ^ a.exp ≠ 0 := by positivity
  have h2 : (2:ℚ) ^ b.exp ≠ 0 := by positivity
  push_cast
  rw [pow_add]
  field_simp [h1, h2]

/-- Conversion to rational numbers preserves dyadic multiplication. -/
theorem toRat_mul (a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : (a.mul b).toRat = a.toRat * b.toRat := by
  simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.mul,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.toRat]
  have h1 : (2:ℚ) ^ a.exp ≠ 0 := by positivity
  have h2 : (2:ℚ) ^ b.exp ≠ 0 := by positivity
  push_cast
  rw [pow_add]
  field_simp [h1, h2]

/-- Conversion to rational numbers preserves dyadic negation. -/
theorem toRat_neg (a : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : a.neg.toRat = -a.toRat := by
  simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.neg,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.toRat]
  push_cast
  field_simp

/-- Conversion to rational numbers preserves dyadic subtraction. -/
theorem toRat_sub (a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : (a.sub b).toRat = a.toRat - b.toRat := by
  simp only [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.sub]
  rw [toRat_add, toRat_neg]
  ring

/-- The real value of a dyadic number is the real coercion of its rational value. -/
theorem toReal_eq (d : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : d.toReal = (d.toRat : ℝ) := by
  simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.toReal,
      Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.toRat]

/-- Conversion to real numbers preserves dyadic addition. -/
theorem toReal_add (a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : (a.add b).toReal = a.toReal + b.toReal := by
  simp [toReal_eq, toRat_add]

/-- Conversion to real numbers preserves dyadic multiplication. -/
theorem toReal_mul (a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : (a.mul b).toReal = a.toReal * b.toReal := by
  simp [toReal_eq, toRat_mul]

/-- Conversion to real numbers preserves dyadic negation. -/
theorem toReal_neg (a : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : a.neg.toReal = -a.toReal := by
  simp [toReal_eq, toRat_neg]

/-- Conversion to real numbers preserves dyadic subtraction. -/
theorem toReal_sub (a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : (a.sub b).toReal = a.toReal - b.toReal := by
  simp [toReal_eq, toRat_sub]

/-- The dyadic representation with numerator and exponent both zero has real value zero. -/
theorem toReal_zero : (⟨0, 0⟩ : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic).toReal = 0 := by
  simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.toReal]

/-- The dyadic representation with numerator one and exponent zero has real value one. -/
theorem toReal_one : (⟨1, 0⟩ : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic).toReal = 1 := by
  simp [Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic.toReal]

/-- The binary size of a sum of natural numbers is at most one plus the larger input size. -/
theorem nat_size_add_le' (a b : ℕ) : (a + b).size ≤ max a.size b.size + 1 := by
  rw [Nat.size_le]
  have ha : a < 2 ^ a.size := Nat.lt_size_self a
  have hb : b < 2 ^ b.size := Nat.lt_size_self b
  have hm1 : 2 ^ a.size ≤ 2 ^ (max a.size b.size) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_max_left _ _)
  have hm2 : 2 ^ b.size ≤ 2 ^ (max a.size b.size) :=
    pow_le_pow_right₀ (by norm_num) (Nat.le_max_right _ _)
  calc a + b < 2 ^ a.size + 2 ^ b.size := Nat.add_lt_add ha hb
    _ ≤ 2 ^ (max a.size b.size) + 2 ^ (max a.size b.size) := add_le_add hm1 hm2
    _ = 2 ^ (max a.size b.size + 1) := by rw [pow_succ]; ring

/-- Multiplication by `2 ^ k` increases the binary size of a natural number by at most `k`. -/
theorem nat_size_mul_pow_two_le (m k : ℕ) : (m * 2 ^ k).size ≤ m.size + k := by
  rcases Nat.eq_zero_or_pos m with h | h
  · subst h
    simp
  · have hne : m ≠ 0 := by omega
    rw [← Nat.shiftLeft_eq]
    exact le_of_eq (Nat.size_shiftLeft hne k)

/-- The binary size of a product of natural numbers is at most the sum of their binary sizes. -/
theorem nat_size_mul_le (m n : ℕ) : (m * n).size ≤ m.size + n.size := by
  rw [Nat.size_le]
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp
  have hlt : m * n < 2 ^ m.size * 2 ^ n.size :=
    Nat.mul_lt_mul_of_lt_of_le (Nat.lt_size_self m) (Nat.le_of_lt (Nat.lt_size_self n))
      (by positivity)
  have hpow : 2 ^ m.size * 2 ^ n.size = 2 ^ (m.size + n.size) := by rw [pow_add]
  rw [hpow] at hlt
  exact hlt

/-- The size of a dyadic sum is at most `2 * (a.size + b.size + 1)`. -/
theorem size_add (a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : (a.add b).size ≤ 2 * (a.size + b.size + 1) := by
  have habs0 : (a.mant * (2:ℤ) ^ b.exp + b.mant * (2:ℤ) ^ a.exp).natAbs ≤
      (a.mant * (2:ℤ) ^ b.exp).natAbs + (b.mant * (2:ℤ) ^ a.exp).natAbs :=
    Int.natAbs_add_le _ _
  have habs1 : (a.mant * (2:ℤ) ^ b.exp).natAbs = a.mant.natAbs * 2 ^ b.exp := by
    rw [Int.natAbs_mul]
    simp
  have habs2 : (b.mant * (2:ℤ) ^ a.exp).natAbs = b.mant.natAbs * 2 ^ a.exp := by
    rw [Int.natAbs_mul]
    simp
  rw [habs1, habs2] at habs0
  have h1 : ((a.mant * (2:ℤ) ^ b.exp + b.mant * (2:ℤ) ^ a.exp).natAbs).size ≤
      (a.mant.natAbs * 2 ^ b.exp + b.mant.natAbs * 2 ^ a.exp).size :=
    Nat.size_le_size habs0
  have h2 : (a.mant.natAbs * 2 ^ b.exp + b.mant.natAbs * 2 ^ a.exp).size ≤
      max (a.mant.natAbs * 2 ^ b.exp).size (b.mant.natAbs * 2 ^ a.exp).size + 1 :=
    nat_size_add_le' _ _
  have h3 : (a.mant.natAbs * 2 ^ b.exp).size ≤ a.mant.natAbs.size + b.exp :=
    nat_size_mul_pow_two_le _ _
  have h4 : (b.mant.natAbs * 2 ^ a.exp).size ≤ b.mant.natAbs.size + a.exp :=
    nat_size_mul_pow_two_le _ _
  have h5 : max (a.mant.natAbs * 2 ^ b.exp).size (b.mant.natAbs * 2 ^ a.exp).size ≤
      a.mant.natAbs.size + b.exp + (b.mant.natAbs.size + a.exp) :=
    max_le (Nat.le_trans h3 (Nat.le_add_right _ _)) (Nat.le_trans h4 (Nat.le_add_left _ _))
  show (a.mant * (2:ℤ) ^ b.exp + b.mant * (2:ℤ) ^ a.exp).natAbs.size + (a.exp + b.exp) ≤
    2 * (a.mant.natAbs.size + a.exp + (b.mant.natAbs.size + b.exp) + 1)
  calc (a.mant * (2:ℤ) ^ b.exp + b.mant * (2:ℤ) ^ a.exp).natAbs.size + (a.exp + b.exp)
        ≤ (max (a.mant.natAbs * 2 ^ b.exp).size (b.mant.natAbs * 2 ^ a.exp).size + 1) +
            (a.exp + b.exp) :=
          Nat.add_le_add_right (Nat.le_trans h1 h2) _
    _ ≤ (a.mant.natAbs.size + b.exp + (b.mant.natAbs.size + a.exp) + 1) + (a.exp + b.exp) :=
          Nat.add_le_add_right (Nat.add_le_add_right h5 1) _
    _ ≤ 2 * (a.mant.natAbs.size + a.exp + (b.mant.natAbs.size + b.exp) + 1) := by
          omega

/-- The size of a dyadic product is at most the sum of the input sizes. -/
theorem size_mul (a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic) : (a.mul b).size ≤ a.size + b.size := by
  have h1 : (a.mant * b.mant).natAbs = a.mant.natAbs * b.mant.natAbs := by
    exact_mod_cast Int.natAbs_mul a.mant b.mant
  have h2 : ((a.mant * b.mant).natAbs).size = (a.mant.natAbs * b.mant.natAbs).size := by
    rw [h1]
  have h3 : (a.mant.natAbs * b.mant.natAbs).size ≤
      a.mant.natAbs.size + b.mant.natAbs.size := nat_size_mul_le _ _
  show ((a.mant * b.mant).natAbs).size + (a.exp + b.exp) ≤
    a.mant.natAbs.size + a.exp + (b.mant.natAbs.size + b.exp)
  omega

end Dyadic

/-- The interval `cert q k` is valid for every rational center and precision. -/
theorem valid_cert (q : ℚ) (k : ℕ) : Valid (cert q k) := by
  show (q - unit k : ℚ) ≤ q + unit k
  have h : (0:ℚ) ≤ unit k := by
    rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
    positivity
  linarith

/-- The width of `cert q k` is twice `unit k`. -/
theorem width_cert (q : ℚ) (k : ℕ) : width (cert q k) = 2 * unit k := by
  show ((q + unit k) - (q - unit k) : ℚ) = 2 * unit k
  ring

/-- The interval `cert q k` contains its rational center, viewed as a real number. -/
theorem contains_cert_self (q : ℚ) (k : ℕ) : Contains (cert q k) (q : ℝ) := by
  constructor
  · show ((q - unit k : ℚ) : ℝ) ≤ _
    have h : (0:ℝ) ≤ (unit k : ℚ) := by
      rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
      positivity
    push_cast at h ⊢
    linarith
  · show _ ≤ ((q + unit k : ℚ) : ℝ)
    have h : (0:ℝ) ≤ (unit k : ℚ) := by
      rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
      positivity
    push_cast at h ⊢
    linarith

/-- Rounding a rational number down at precision `k` gives a value no greater than the original. -/
theorem roundDown_le (q : ℚ) (k : ℕ) : roundDown q k ≤ q := by
  rw [Qatlib.Foundations.IntervalArith.IntervalOps.roundDown]
  have hp : (0:ℚ) < 2 ^ k := by positivity
  rw [div_le_iff₀ hp]
  exact_mod_cast Int.floor_le (q * (2:ℚ) ^ k)

/-- A rational number lies strictly below its rounded-down value plus `unit k`. -/
theorem lt_roundDown_add_unit (q : ℚ) (k : ℕ) : q < roundDown q k + unit k := by
  rw [Qatlib.Foundations.IntervalArith.IntervalOps.roundDown,
      Qatlib.Foundations.IntervalArith.IntervalOps.unit]
  have hp : (0:ℚ) < 2 ^ k := by positivity
  have hlt := Int.lt_floor_add_one (q * (2:ℚ) ^ k)
  have hform : ((⌊q * (2:ℚ) ^ k⌋ : ℤ) : ℚ) / (2:ℚ) ^ k + 1 / (2:ℚ) ^ k =
      (((⌊q * (2:ℚ) ^ k⌋ : ℤ) : ℚ) + 1) / (2:ℚ) ^ k := by rw [add_div]
  rw [hform, lt_div_iff₀ hp]
  exact_mod_cast hlt

/-- The rounded interval of a rational number is valid. -/
theorem valid_rounded (q : ℚ) (k : ℕ) : Valid (rounded q k) := by
  show (roundDown q k : ℚ) ≤ roundDown q k + unit k
  have h : (0:ℚ) ≤ unit k := by
    rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
    positivity
  linarith

/-- The rounded interval of a rational number contains that number. -/
theorem contains_rounded_self (q : ℚ) (k : ℕ) : Contains (rounded q k) q := by
  constructor
  · show ((roundDown q k : ℚ) : ℝ) ≤ _
    exact_mod_cast roundDown_le q k
  · show _ ≤ ((roundDown q k + unit k : ℚ) : ℝ)
    exact_mod_cast (le_of_lt (lt_roundDown_add_unit q k))

/-- The rounded interval at precision `k` has width `unit k`. -/
theorem width_rounded (q : ℚ) (k : ℕ) : width (rounded q k) = unit k := by
  show ((roundDown q k + unit k) - roundDown q k : ℚ) = unit k
  ring

/-- Interval addition preserves validity. -/
theorem valid_add (a b : Interval) (ha : Valid a) (hb : Valid b) :
    Valid (Qatlib.Foundations.IntervalArith.IntervalOps.add a b) := by
  show (a.lo + b.lo : ℚ) ≤ a.hi + b.hi
  exact add_le_add ha hb

/-- The sum of two values lies in the sum of any intervals containing them. -/
theorem contains_add (a b : Interval) {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (Qatlib.Foundations.IntervalArith.IntervalOps.add a b) (x + y) := by
  constructor
  · show ((a.lo + b.lo : ℚ) : ℝ) ≤ x + y
    push_cast
    exact add_le_add hx.1 hy.1
  · show (x + y) ≤ ((a.hi + b.hi : ℚ) : ℝ)
    push_cast
    exact add_le_add hx.2 hy.2

/-- The width of an interval sum is the sum of the input widths. -/
theorem width_add (a b : Interval) :
    width (Qatlib.Foundations.IntervalArith.IntervalOps.add a b) = width a + width b := by
  show ((a.hi + b.hi) - (a.lo + b.lo) : ℚ) = (a.hi - a.lo) + (b.hi - b.lo)
  ring

/-- Coercion from rational to real numbers preserves the minimum of two values. -/
theorem ratCast_min (u v : ℚ) : ((min u v : ℚ) : ℝ) = min (u:ℝ) (v:ℝ) := by
  rcases le_total u v with h | h
  · rw [min_eq_left h, min_eq_left (by exact_mod_cast h)]
  · rw [min_eq_right h, min_eq_right (by exact_mod_cast h)]

/-- Coercion from rational to real numbers preserves the maximum of two values. -/
theorem ratCast_max (u v : ℚ) : ((max u v : ℚ) : ℝ) = max (u:ℝ) (v:ℝ) := by
  rcases le_total u v with h | h
  · rw [max_eq_right h, max_eq_right (by exact_mod_cast h)]
  · rw [max_eq_left h, max_eq_left (by exact_mod_cast h)]

/-- If `p ≤ x ≤ q`, then `t * x` is bounded below by the smaller endpoint product. -/
theorem mul_left_lower {p q x t : ℝ} (hp : p ≤ x) (hq : x ≤ q) :
    min (t * p) (t * q) ≤ t * x := by
  by_cases ht : 0 ≤ t
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_left hp ht)
  · have htn : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_left hq htn)

/-- If `p ≤ x ≤ q`, then `t * x` is bounded above by the larger endpoint product. -/
theorem mul_left_upper {p q x t : ℝ} (hp : p ≤ x) (hq : x ≤ q) :
    t * x ≤ max (t * p) (t * q) := by
  by_cases ht : 0 ≤ t
  · exact le_trans (mul_le_mul_of_nonneg_left hq ht) (le_max_right _ _)
  · have htn : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    exact le_trans (mul_le_mul_of_nonpos_left hp htn) (le_max_left _ _)

/-- If `p ≤ x ≤ q`, then `x * t` is bounded below by the smaller endpoint product. -/
theorem mul_right_lower {p q x t : ℝ} (hp : p ≤ x) (hq : x ≤ q) :
    min (p * t) (q * t) ≤ x * t := by
  by_cases ht : 0 ≤ t
  · exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right hp ht)
  · have htn : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    exact le_trans (min_le_right _ _) (mul_le_mul_of_nonpos_right hq htn)

/-- If `p ≤ x ≤ q`, then `x * t` is bounded above by the larger endpoint product. -/
theorem mul_right_upper {p q x t : ℝ} (hp : p ≤ x) (hq : x ≤ q) :
    x * t ≤ max (p * t) (q * t) := by
  by_cases ht : 0 ≤ t
  · exact le_trans (mul_le_mul_of_nonneg_right hq ht) (le_max_right _ _)
  · have htn : t ≤ 0 := le_of_lt (lt_of_not_ge ht)
    exact le_trans (mul_le_mul_of_nonpos_right hp htn) (le_max_left _ _)

/-- Interval multiplication preserves validity. -/
theorem valid_mul (a b : Interval) (_ha : Valid a) (_hb : Valid b) :
    Valid (Qatlib.Foundations.IntervalArith.IntervalOps.mul a b) := by
  show (min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)) : ℚ) ≤
    max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi))
  exact le_trans (min_le_left _ _) (le_trans min_le_max (le_max_left _ _))

/-- The product of two values lies in the product of any intervals containing them. -/
theorem contains_mul (a b : Interval) {x y : ℝ} (hx : Contains a x) (hy : Contains b y) :
    Contains (Qatlib.Foundations.IntervalArith.IntervalOps.mul a b) (x * y) := by
  have hpx : (a.lo : ℝ) ≤ x := hx.1
  have hqx : x ≤ (a.hi : ℝ) := hx.2
  have hry : (b.lo : ℝ) ≤ y := hy.1
  have hsy : y ≤ (b.hi : ℝ) := hy.2
  have lower : min (min ((a.lo:ℝ) * b.lo) ((a.lo:ℝ) * b.hi))
        (min ((a.hi:ℝ) * b.lo) ((a.hi:ℝ) * b.hi)) ≤ x * y :=
    le_trans (min_le_min (mul_left_lower hry hsy) (mul_left_lower hry hsy))
      (mul_right_lower hpx hqx)
  have upper : x * y ≤ max (max ((a.lo:ℝ) * b.lo) ((a.lo:ℝ) * b.hi))
        (max ((a.hi:ℝ) * b.lo) ((a.hi:ℝ) * b.hi)) :=
    le_trans (mul_right_upper hpx hqx)
      (max_le_max (mul_left_upper hry hsy) (mul_left_upper hry hsy))
  constructor
  · show ((min (min (a.lo * b.lo) (a.lo * b.hi)) (min (a.hi * b.lo) (a.hi * b.hi)) : ℚ) : ℝ) ≤ x * y
    rw [ratCast_min, ratCast_min]
    push_cast
    exact lower
  · show x * y ≤ ((max (max (a.lo * b.lo) (a.lo * b.hi)) (max (a.hi * b.lo) (a.hi * b.hi)) : ℚ) : ℝ)
    rw [ratCast_max, ratCast_max]
    push_cast
    exact upper

/-- If `divPositive a b gap` returns an interval, that interval contains `x / y` whenever the
inputs contain `x` and `y`. -/
theorem contains_divPositive (a b : Interval) (gap : ℚ) {x y : ℝ}
    (hx : Contains a x) (hy : Contains b y) {c : Interval}
    (h : Qatlib.Foundations.IntervalArith.IntervalOps.divPositive a b gap = some c) :
    Contains c (x / y) := by
  have hcond : (0 < gap ∧ gap ≤ b.lo ∧ Valid a ∧ Valid b) := by
    by_contra hc
    simp [Qatlib.Foundations.IntervalArith.IntervalOps.divPositive, hc] at h
  have hbposq : (0:ℚ) < b.lo := lt_of_lt_of_le hcond.1 hcond.2.1
  have hbloq : b.lo ≤ b.hi := hcond.2.2.2
  have hbpos : (0:ℝ) < b.lo := by exact_mod_cast hbposq
  have hblo : (b.lo : ℝ) ≤ b.hi := by exact_mod_cast hbloq
  have hypos : (0:ℝ) < y := lt_of_lt_of_le hbpos hy.1
  have hrecip : Contains (⟨b.hi⁻¹, b.lo⁻¹⟩ : Interval) (1 / y) := by
    constructor
    · show ((b.hi⁻¹ : ℚ) : ℝ) ≤ 1 / y
      push_cast
      simpa [one_div] using! one_div_le_one_div_of_le (by positivity) hy.2
    · show (1 / y) ≤ ((b.lo⁻¹ : ℚ) : ℝ)
      push_cast
      simpa [one_div] using! one_div_le_one_div_of_le (by positivity) hy.1
  have hvalid : Valid (⟨b.hi⁻¹, b.lo⁻¹⟩ : Interval) := by
    show (b.hi⁻¹ : ℚ) ≤ b.lo⁻¹
    simpa [one_div] using! one_div_le_one_div_of_le hbposq hbloq
  have hrewr : c = Qatlib.Foundations.IntervalArith.IntervalOps.mul a
      (⟨b.hi⁻¹, b.lo⁻¹⟩ : Interval) := by
    simp [Qatlib.Foundations.IntervalArith.IntervalOps.divPositive, hcond] at h
    exact h.symm
  rw [hrewr]
  have hmul := contains_mul a (⟨b.hi⁻¹, b.lo⁻¹⟩ : Interval) hx hrecip
  simpa [mul_one_div] using! hmul

/-- Positive-denominator interval division returns `none` when the supplied gap is nonpositive. -/
theorem divPositive_none_of_gap_le_zero (a b : Interval) {gap : ℚ} (h : gap ≤ 0) :
    Qatlib.Foundations.IntervalArith.IntervalOps.divPositive a b gap = none := by
  have hnot : ¬ (0 < gap ∧ gap ≤ b.lo ∧ Valid a ∧ Valid b) := by
    intro hc
    exact (lt_of_lt_of_le hc.1 h).false
  simp [Qatlib.Foundations.IntervalArith.IntervalOps.divPositive, hnot]

/-- The constant real name associated with a rational number satisfies its specification. -/
theorem const_spec (q : ℚ) : (RealName.const q).Spec (q : ℝ) := by
  refine ⟨?_, ?_⟩
  · show (0:ℕ) < 1
    norm_num
  · intro p
    exact contains_cert_self q p

/-- There exist real names satisfying the specifications for zero and one. -/
theorem name_zero : ∃ N0 N1 : RealName, N0.Spec 0 ∧ N1.Spec 1 := by
  refine ⟨RealName.const 0, RealName.const 1, ?_, ?_⟩
  · simpa using! const_spec 0
  · simpa using! const_spec 1

/-- The certificates centered at zero, one, and negative one contain their centers at every
precision. -/
theorem name_neg_boundary : ∀ p : ℕ, Contains (cert (0 : ℚ) p) 0 ∧
    Contains (cert (1 : ℚ) p) 1 ∧ Contains (cert (-1 : ℚ) p) (-1) := by
  intro p
  exact ⟨by simpa using! contains_cert_self 0 p,
    by simpa using! contains_cert_self 1 p,
    by simpa using! contains_cert_self (-1 : ℚ) p⟩

/-- Real names for the real and imaginary parts combine into a complex name satisfying the
corresponding specification. -/
theorem complex_name_boundary (Nre Nim : RealName) (x y : ℝ)
    (hre : Nre.Spec x) (him : Nim.Spec y) :
    (⟨Nre, Nim⟩ : ComplexName).Spec (⟨x, y⟩ : ℂ) := by
  show Nre.Spec (Complex.re ⟨x, y⟩) ∧ Nim.Spec (Complex.im ⟨x, y⟩)
  simpa using! ⟨hre, him⟩

/-- A positive rational gap satisfies `DivPremise` for its own real value. -/
theorem divPremise_self (gap : ℚ) (h : 0 < gap) : DivPremise gap (gap : ℝ) :=
  ⟨h, le_refl (gap : ℝ)⟩

/-- Negative one fails `SqrtPremise`, and zero fails `LogPremise`. -/
theorem domain_rejection : ¬ SqrtPremise (-1 : ℝ) ∧ ¬ LogPremise (0 : ℝ) := by
  refine ⟨?_, ?_⟩
  · show ¬ (0 ≤ (-1 : ℝ))
    norm_num
  · show ¬ ((0:ℝ) < 0)
    norm_num

/-- Containment in `cert q k` bounds the absolute error from `q` by `unit k`. -/
theorem abs_of_contains_cert {q : ℚ} {k : ℕ} {z : ℝ} (h : Contains (cert q k) z) :
    |(q : ℝ) - z| ≤ (unit k : ℝ) := by
  have h1 : ((q - unit k : ℚ) : ℝ) ≤ z := h.1
  have h2 : z ≤ ((q + unit k : ℚ) : ℝ) := h.2
  push_cast at h1 h2
  apply abs_le.mpr
  constructor <;> linarith

/-- An absolute error bound of `unit k` implies containment in `cert q k`. -/
theorem contains_cert_of_abs (q : ℚ) (k : ℕ) {z : ℝ} (h : |(q : ℝ) - z| ≤ (unit k : ℝ)) :
    Contains (cert q k) z := by
  have h1 : (-(unit k : ℝ) ≤ (q : ℝ) - z) ∧ ((q : ℝ) - z ≤ (unit k : ℝ)) := abs_le.mp h
  constructor
  · show ((q - unit k : ℚ) : ℝ) ≤ z
    push_cast
    linarith
  · show z ≤ ((q + unit k : ℚ) : ℝ)
    push_cast
    linarith

/-- The absolute error of a sum is at most the sum of the two absolute error bounds. -/
theorem abs_add_error {a b x y u v : ℝ} (ha : |a - x| ≤ u) (hb : |b - y| ≤ v) :
    |(a + b) - (x + y)| ≤ u + v := by
  have h : (a + b) - (x + y) = (a - x) + (b - y) := by ring
  rw [h]
  exact (abs_add_le _ _).trans (add_le_add ha hb)

/-- Negating both an approximation and its target preserves an absolute error bound. -/
theorem abs_neg_error {a x u : ℝ} (ha : |a - x| ≤ u) : |-a - -x| ≤ u := by
  have h : -a - -x = -(a - x) := by ring
  rw [h, abs_neg]
  exact ha

/-- Two copies of `unit (p + 1)` sum to `unit p`. -/
theorem two_mul_unit_succ (p : ℕ) : (unit (p + 1) : ℝ) + unit (p + 1) = (unit p : ℝ) := by
  rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit,
      Qatlib.Foundations.IntervalArith.IntervalOps.unit]
  push_cast
  field_simp [pow_succ]
  ring

/-- Adding real names preserves their specifications, with the sum of the input clocks at `p`
bounded by the output clock at `p + 3`. -/
theorem name_add (Nx Ny : RealName) (x y : ℝ) (hx : Nx.Spec x) (hy : Ny.Spec y) :
    (Nx.add Ny).Spec (x + y) ∧
      ∀ p : ℕ, Nx.clock p + Ny.clock p ≤ (Nx.add Ny).clock (p + 3) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show (0:ℕ) < Nx.timeC + Ny.timeC
      exact Nat.add_pos_left hx.1 _
    · intro p
      have ha : |(Nx.approx (p + 1) : ℝ) - x| ≤ (unit (p + 1) : ℝ) :=
        abs_of_contains_cert (hx.2 (p + 1))
      have hb : |(Ny.approx (p + 1) : ℝ) - y| ≤ (unit (p + 1) : ℝ) :=
        abs_of_contains_cert (hy.2 (p + 1))
      have hsum := abs_add_error ha hb
      have hunit : (unit (p + 1) : ℝ) + unit (p + 1) = unit p := two_mul_unit_succ p
      exact contains_cert_of_abs _ _
        (by simpa [RealName.add] using! le_trans hsum (le_of_eq hunit))
  · intro p
    have hd1 : Nx.timeD ≤ max Nx.timeD Ny.timeD + 1 :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
    have hd2 : Ny.timeD ≤ max Nx.timeD Ny.timeD + 1 :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
    have hp1 : (p + 1) ^ Nx.timeD ≤ (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      le_trans (pow_le_pow_left₀ (by omega) (by omega) _) (pow_le_pow_right₀ (by omega) hd1)
    have hp2 : (p + 1) ^ Ny.timeD ≤ (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      le_trans (pow_le_pow_left₀ (by omega) (by omega) _) (pow_le_pow_right₀ (by omega) hd2)
    have h1 : Nx.timeC * (p + 1) ^ Nx.timeD ≤
        Nx.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      Nat.mul_le_mul_left _ hp1
    have h2 : Ny.timeC * (p + 1) ^ Ny.timeD ≤
        Ny.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      Nat.mul_le_mul_left _ hp2
    calc Nx.clock p + Ny.clock p
          = Nx.timeC * (p + 1) ^ Nx.timeD + Ny.timeC * (p + 1) ^ Ny.timeD := rfl
      _ ≤ Nx.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) +
            Ny.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
        Nat.add_le_add h1 h2
      _ = (Nx.timeC + Ny.timeC) * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) := by ring
      _ = (Nx.add Ny).clock (p + 3) := rfl

/-- Negating a real name preserves its specification for the negated value and leaves its clock
unchanged. -/
theorem name_neg (N : RealName) (x : ℝ) (hx : N.Spec x) :
    N.neg.Spec (-x) ∧ ∀ p : ℕ, N.clock p = N.neg.clock p := by
  refine ⟨?_, fun _ => rfl⟩
  refine ⟨hx.1, ?_⟩
  intro p
  have ha : |(N.approx p : ℝ) - x| ≤ (unit p : ℝ) := abs_of_contains_cert (hx.2 p)
  exact contains_cert_of_abs _ _ (by simpa [RealName.neg] using! abs_neg_error ha)

/-- Subtracting real names preserves their specifications, with the sum of the input clocks at
`p` bounded by the output clock at `p + 3`. -/
theorem name_sub (Nx Ny : RealName) (x y : ℝ) (hx : Nx.Spec x) (hy : Ny.Spec y) :
    (Nx.sub Ny).Spec (x - y) ∧
      ∀ p : ℕ, Nx.clock p + Ny.clock p ≤ (Nx.sub Ny).clock (p + 3) := by
  obtain ⟨hn, hcn⟩ := name_neg Ny y hy
  obtain ⟨ha, hca⟩ := name_add Nx Ny.neg x (-y) hx hn
  refine ⟨?_, hca⟩
  simpa [RealName.sub, sub_eq_add_neg] using! ha

/-- Every natural power of two, viewed as a real number, is at least one. -/
theorem one_le_two_pow_real (k : ℕ) : (1:ℝ) ≤ (2:ℝ) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 2) k]

/-- The real value of `unit k` is at most one. -/
theorem unit_le_one (k : ℕ) : (unit k : ℝ) ≤ 1 := by
  rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
  push_cast
  have hp : (0:ℝ) < (2:ℝ) ^ k := by positivity
  rw [div_le_one hp]
  exact one_le_two_pow_real k

/-- Multiplying `unit (k + s)` by `2 ^ s` gives `unit k`. -/
theorem unit_succ_split (k s : ℕ) : (unit (k + s) : ℝ) * (2 : ℝ) ^ s = (unit k : ℝ) := by
  rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit,
      Qatlib.Foundations.IntervalArith.IntervalOps.unit]
  push_cast
  field_simp
  rw [← pow_add, Nat.add_comm]

/-- For targets bounded in absolute value by `B`, product approximation error is at most `B * v
+ B * u + u * v`. -/
theorem mul_error_bound {a b x y u v B : ℝ}
    (ha : |a - x| ≤ u) (hb : |b - y| ≤ v) (hbx : |x| ≤ B) (hby : |y| ≤ B) :
    |a * b - x * y| ≤ B * v + B * u + u * v := by
  have hB0 : (0:ℝ) ≤ B := le_trans (abs_nonneg x) hbx
  have hsplit : a * b - x * y = x * (b - y) + y * (a - x) + (a - x) * (b - y) := by ring
  rw [hsplit]
  have h1 : |x * (b - y)| ≤ B * v := by
    rw [abs_mul]
    exact mul_le_mul hbx hb (abs_nonneg _) hB0
  have h2 : |y * (a - x)| ≤ B * u := by
    rw [abs_mul]
    exact mul_le_mul hby ha (abs_nonneg _) hB0
  have h3 : |(a - x) * (b - y)| ≤ u * v := by
    rw [abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)
  refine le_trans (abs_add_le _ _) (add_le_add ?_ h3)
  refine le_trans (abs_add_le _ _) (add_le_add h1 h2)

/-- Multiplication of real names satisfies the product specification under the magnitude and
precision-shift assumptions, with the stated comparison of input and output clocks. -/
theorem name_mul (Nx Ny : RealName) (s B : ℕ) (x y : ℝ)
    (hx : Nx.Spec x) (hy : Ny.Spec y)
    (hbx : MagnitudeBound B x) (hby : MagnitudeBound B y)
    (hs : 2 * B + 1 ≤ 2 ^ s) :
    (Nx.mul Ny s).Spec (x * y) ∧
      ∀ p : ℕ, Nx.clock p + Ny.clock p ≤ (Nx.mul Ny s).clock (p + 3) := by
  have hBpos : (0:ℝ) ≤ (B:ℝ) := by exact_mod_cast (le_of_lt hbx.1)
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · show (0:ℕ) < Nx.timeC + Ny.timeC
      exact Nat.add_pos_left hx.1 _
    · intro p
      have ha : |(Nx.approx (p + s) : ℝ) - x| ≤ (unit (p + s) : ℝ) :=
        abs_of_contains_cert (hx.2 (p + s))
      have hb : |(Ny.approx (p + s) : ℝ) - y| ≤ (unit (p + s) : ℝ) :=
        abs_of_contains_cert (hy.2 (p + s))
      have hbx' : |x| ≤ (B : ℝ) := by exact_mod_cast hbx.2
      have hby' : |y| ≤ (B : ℝ) := by exact_mod_cast hby.2
      have hmul := mul_error_bound ha hb hbx' hby'
      have hunit : (unit (p + s) : ℝ) * ((B : ℝ) + (B : ℝ) + unit (p + s)) ≤ unit p := by
        have hnn : (0:ℝ) ≤ unit (p + s) := by
          rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
          push_cast
          positivity
        have h1 : ((B:ℝ) + (B:ℝ) + unit (p + s)) ≤ 2 * B + 1 := by
          linarith [unit_le_one (p + s)]
        have h2 : (2 * B + 1 : ℝ) ≤ (2:ℝ) ^ s := by exact_mod_cast hs
        calc (unit (p + s) : ℝ) * ((B:ℝ) + (B:ℝ) + unit (p + s))
            ≤ (unit (p + s) : ℝ) * (2 * B + 1) :=
          mul_le_mul_of_nonneg_left h1 hnn
          _ ≤ (unit (p + s) : ℝ) * (2:ℝ) ^ s :=
          mul_le_mul_of_nonneg_left h2 hnn
          _ = (unit p : ℝ) := unit_succ_split p s
      have hkey : |(Nx.approx (p + s) * Ny.approx (p + s) : ℝ) - x * y| ≤ (unit p : ℝ) := by
        refine le_trans hmul ?_
        have hre : (B:ℝ) * unit (p + s) + B * unit (p + s) + unit (p + s) * unit (p + s)
            = (unit (p + s) : ℝ) * ((B:ℝ) + (B:ℝ) + unit (p + s)) := by ring
        rw [hre]
        exact hunit
      exact contains_cert_of_abs _ _
        (by simpa [RealName.mul] using! hkey)
  · intro p
    have hd1 : Nx.timeD ≤ max Nx.timeD Ny.timeD + 1 :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
    have hd2 : Ny.timeD ≤ max Nx.timeD Ny.timeD + 1 :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
    have hp1 : (p + 1) ^ Nx.timeD ≤ (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      le_trans (pow_le_pow_left₀ (by omega) (by omega) _) (pow_le_pow_right₀ (by omega) hd1)
    have hp2 : (p + 1) ^ Ny.timeD ≤ (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      le_trans (pow_le_pow_left₀ (by omega) (by omega) _) (pow_le_pow_right₀ (by omega) hd2)
    have h1 : Nx.timeC * (p + 1) ^ Nx.timeD ≤
        Nx.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      Nat.mul_le_mul_left _ hp1
    have h2 : Ny.timeC * (p + 1) ^ Ny.timeD ≤
        Ny.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      Nat.mul_le_mul_left _ hp2
    calc Nx.clock p + Ny.clock p
          = Nx.timeC * (p + 1) ^ Nx.timeD + Ny.timeC * (p + 1) ^ Ny.timeD := rfl
      _ ≤ Nx.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) +
            Ny.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
        Nat.add_le_add h1 h2
      _ = (Nx.timeC + Ny.timeC) * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) := by ring
      _ = (Nx.mul Ny s).clock (p + 3) := rfl

/-- The approximation budget of an empty word is zero. -/
theorem budget_nil (D : ℕ) :
    Qatlib.Concepts.RawChannelWord.CptpWordBound.budget
      ([] : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) = 0 :=
  rfl

/-- The approximation budget is additive under concatenation of words. -/
theorem budget_append (D : ℕ)
    (p q : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) :
    Qatlib.Concepts.RawChannelWord.CptpWordBound.budget (p ++ q) =
      Qatlib.Concepts.RawChannelWord.CptpWordBound.budget p + Qatlib.Concepts.RawChannelWord.CptpWordBound.budget q := by
  simp [Qatlib.Concepts.RawChannelWord.CptpWordBound.budget, List.map_append, List.sum_append]

/-- A word's approximation budget is at most its total account when the read clock is
nonnegative. -/
theorem totalAccount_le (D : ℕ)
    (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) {readClock : ℝ}
    (h : 0 ≤ readClock) :
    Qatlib.Concepts.RawChannelWord.CptpWordBound.budget p ≤ totalAccount p readClock := by
  show Qatlib.Concepts.RawChannelWord.CptpWordBound.budget p ≤
    Qatlib.Concepts.RawChannelWord.CptpWordBound.budget p + readClock
  linarith

/-- There exists a family of approximation words whose error lists depend only on the public
parameter and not on the input matrix. -/
theorem layer_family_public : ∃ (D : ℕ)
    (F : ℕ → Matrix (Fin D) (Fin D) ℂ → List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)),
    ∀ (pub : ℕ) (u v : Matrix (Fin D) (Fin D) ℂ),
      (F pub u).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.error =
        (F pub v).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.error := by
  refine ⟨2, fun pub _ => List.replicate pub
      ⟨Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel.id 2, Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel.id 2, 1⟩, ?_⟩
  intro pub u v
  simp

/-- There exists a real-valued probability assignment satisfying `FairCoinLaw`. -/
theorem fair_coin_law : ∃ p : Bool → ℝ, FairCoinLaw p := by
  refine ⟨fun _ => 1 / 2, ?_⟩
  refine ⟨rfl, rfl, ?_⟩
  intro b
  norm_num

/-- An access capability with `adj = false` grants no inverse access. -/
theorem access_inverse_only_when_supplied (c : AccessCap) (h : c.adj = false) :
    c.inverseGranted = none := by
  simp [AccessCap.inverseGranted, h]

/-- An access capability with `ctrl = false` grants no controlled access. -/
theorem access_control_only_when_supplied (c : AccessCap) (h : c.ctrl = false) :
    c.controlGranted = none := by
  simp [AccessCap.controlGranted, h]

/-- The displayed natural-number examples evaluate gcd, modular multiplication, modular
exponentiation, and addition. -/
theorem arithmetic_targets :
    Nat.gcd 12 18 = 6 ∧ (3 * 4) % 5 = 2 ∧ (2 ^ 3) % 5 = 3 ∧ 2 + 3 = 5 := by
  decide

/-- The built fragment of clause 1 combines constant names, dyadic arithmetic and size bounds,
valid interval operations, and the stated boundary and domain properties. -/
theorem clause1_built_fragment :
    (∃ N0 N1 : RealName, N0.Spec 0 ∧ N1.Spec 1) ∧
    (∀ a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic,
        (a.add b).toReal = a.toReal + b.toReal ∧
        (a.sub b).toReal = a.toReal - b.toReal ∧
        (a.mul b).toReal = a.toReal * b.toReal ∧
        (a.neg).toReal = -a.toReal) ∧
    (∀ a b : Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionDefs.Dyadic,
        (a.add b).size ≤ polyBound 2 1 (a.size + b.size) ∧
        (a.mul b).size ≤ polyBound 2 1 (a.size + b.size)) ∧
    (∀ q : ℚ, ∀ p : ℕ,
        Valid (cert q p) ∧ Valid (rounded q p) ∧ Contains (rounded q p) q ∧
        width (rounded q p) = unit p) ∧
    (∀ a b : Interval, Valid a → Valid b →
        Valid (Qatlib.Foundations.IntervalArith.IntervalOps.add a b) ∧
        Valid (Qatlib.Foundations.IntervalArith.IntervalOps.mul a b) ∧
        (∀ x y : ℝ, Contains a x → Contains b y →
            Contains (Qatlib.Foundations.IntervalArith.IntervalOps.add a b) (x + y)) ∧
        (∀ x y : ℝ, Contains a x → Contains b y →
            Contains (Qatlib.Foundations.IntervalArith.IntervalOps.mul a b) (x * y)) ∧
        width (Qatlib.Foundations.IntervalArith.IntervalOps.add a b) = width a + width b) ∧
    (∀ a b : Interval, ∀ gap : ℚ, ∀ x y : ℝ,
        Valid a → Valid b → Contains a x → Contains b y → DivPremise gap y →
        ∀ c : Interval,
          Qatlib.Foundations.IntervalArith.IntervalOps.divPositive a b gap = some c →
          Contains c (x / y)) ∧
    (∀ a b : Interval, ∀ gap : ℚ, gap ≤ 0 →
        Qatlib.Foundations.IntervalArith.IntervalOps.divPositive a b gap = none) ∧
    (∀ p : ℕ, Contains (cert (0 : ℚ) p) 0 ∧ Contains (cert (1 : ℚ) p) 1 ∧
        Contains (cert (-1 : ℚ) p) (-1)) ∧
    (∀ Nre Nim : RealName, ∀ x y : ℝ, Nre.Spec x → Nim.Spec y →
        (⟨Nre, Nim⟩ : ComplexName).Spec ⟨x, y⟩) ∧
    (∀ gap : ℚ, 0 < gap → DivPremise gap (gap : ℝ)) ∧
    (¬ SqrtPremise (-1 : ℝ) ∧ ¬ LogPremise (0 : ℝ)) := by
  refine ⟨name_zero, ?_, ?_, ?_, ?_, ?_, ?_, name_neg_boundary, complex_name_boundary,
    divPremise_self, domain_rejection⟩
  · intro a b
    exact ⟨Dyadic.toReal_add a b, Dyadic.toReal_sub a b, Dyadic.toReal_mul a b,
      Dyadic.toReal_neg a⟩
  · intro a b
    have ha := Dyadic.size_add a b
    have hb := Dyadic.size_mul a b
    show (a.add b).size ≤ polyBound 2 1 (a.size + b.size) ∧
      (a.mul b).size ≤ polyBound 2 1 (a.size + b.size)
    simp only [polyBound, Nat.pow_one]
    exact ⟨ha, le_trans hb (by omega)⟩
  · intro q p
    exact ⟨valid_cert q p, valid_rounded q p, contains_rounded_self q p, width_rounded q p⟩
  · intro a b ha hb
    exact ⟨valid_add a b ha hb, valid_mul a b ha hb,
      fun x y hx hy => contains_add a b hx hy,
      fun x y hx hy => contains_mul a b hx hy,
      width_add a b⟩
  · intro a b gap x y ha hb hx hy hprem c hdiv
    exact contains_divPositive a b gap hx hy hdiv
  · intro a b gap h
    exact divPositive_none_of_gap_le_zero a b h

/-- For `0 ≤ a ≤ x`, the difference of square roots is at most `Real.sqrt (x - a)`. -/
theorem sqrt_sub_sqrt_le {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x)
    (hax : a ≤ x) :
    Real.sqrt x - Real.sqrt a ≤ Real.sqrt (x - a) := by
  have hnn : 0 ≤ x - a := sub_nonneg.mpr hax
  have ha2 : a = Real.sqrt a * Real.sqrt a :=
    (Real.sq_sqrt ha).symm.trans (pow_two _)
  have hx2 : x = Real.sqrt x * Real.sqrt x :=
    (Real.sq_sqrt hx).symm.trans (pow_two _)
  have hm : Real.sqrt a ≤ Real.sqrt x := Real.sqrt_le_sqrt hax
  have hkey : (Real.sqrt x - Real.sqrt a) * (Real.sqrt x - Real.sqrt a) ≤ x - a := by
    have h1 : (Real.sqrt x - Real.sqrt a) * (Real.sqrt x - Real.sqrt a)
        = x + a - 2 * Real.sqrt a * Real.sqrt x := by
      linear_combination -hx2 - ha2
    have h2 : Real.sqrt a * Real.sqrt a ≤ Real.sqrt a * Real.sqrt x :=
      mul_le_mul_of_nonneg_left hm (Real.sqrt_nonneg a)
    rw [← ha2] at h2
    rw [h1]; linarith
  have hmono : Real.sqrt ((Real.sqrt x - Real.sqrt a) * (Real.sqrt x - Real.sqrt a))
      ≤ Real.sqrt (x - a) := Real.sqrt_le_sqrt hkey
  rwa [Real.sqrt_mul_self (sub_nonneg.mpr hm)] at hmono

/-- The square-root function satisfies the one-half Hölder estimate on nonnegative real numbers. -/
theorem sqrt_hoelder {a x : ℝ} (ha : 0 ≤ a) (hx : 0 ≤ x) :
    |Real.sqrt a - Real.sqrt x| ≤ Real.sqrt |a - x| := by
  rcases le_total a x with hax | hax
  · rw [abs_sub_comm (Real.sqrt a) (Real.sqrt x),
      abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hax)),
      abs_sub_comm a x, abs_of_nonneg (sub_nonneg.mpr hax)]
    exact sqrt_sub_sqrt_le ha hx hax
  · rw [abs_of_nonneg (sub_nonneg.mpr (Real.sqrt_le_sqrt hax)),
      abs_of_nonneg (sub_nonneg.mpr hax)]
    exact sqrt_sub_sqrt_le hx ha hax

/-- Every natural power of two is positive in the rational numbers. -/
private theorem two_pow_pos (k : ℕ) : (0:ℚ) < 2 ^ k := by positivity

/-- For a nonnegative rational `a`, the scaled radicand used by `ratSqrtLo` has nonnegative
integer floor. -/
private theorem ratSqrtLo_radicand_nonneg (a : ℚ) (k : ℕ) (ha : 0 ≤ a) :
    0 ≤ ⌊a * (2 : ℚ) ^ (2 * k)⌋ := by
  have h0 : (0:ℚ) ≤ a * (2 : ℚ) ^ (2 * k) := mul_nonneg ha (le_of_lt (two_pow_pos _))
  have h1 : (⌊a * (2:ℚ)^(2*k)⌋ : ℚ) ≤ a * (2:ℚ)^(2*k) := Int.floor_le _
  have h2 : a * (2:ℚ)^(2*k) < (⌊a * (2:ℚ)^(2*k)⌋ : ℚ) + 1 := Int.lt_floor_add_one _
  have h3 : (-1:ℤ) < ⌊a * (2:ℚ)^(2*k)⌋ := by
    have h4 : (-1:ℚ) < (⌊a * (2:ℚ)^(2*k)⌋ : ℚ) := by linarith
    exact_mod_cast h4
  omega

/-- The square of the real coercion of rational `2 ^ k` equals the coercion of `2 ^ (2 * k)`. -/
private theorem ratSqrtLo_denom (k : ℕ) : ((2:ℚ)^k : ℝ) * ((2:ℚ)^k : ℝ)
    = ((2:ℚ)^(2*k) : ℝ) := by
  push_cast
  rw [← pow_add]
  congr 1
  omega

/-- The rational approximation `ratSqrtLo a k` is a lower bound for the square root of
nonnegative `a`. -/
theorem ratSqrtLo_le (a : ℚ) (k : ℕ) (ha : 0 ≤ a) :
    (ratSqrtLo a k : ℝ) ≤ Real.sqrt a := by
  have hm0 : 0 ≤ ⌊a * (2 : ℚ) ^ (2 * k)⌋ := ratSqrtLo_radicand_nonneg a k ha
  have htoNat : (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat = ⌊a * (2 : ℚ) ^ (2 * k)⌋ :=
    Int.toNat_of_nonneg hm0
  have hn2 : ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ))
      * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ))
      ≤ ⌊a * (2 : ℚ) ^ (2 * k)⌋ := by
    have h1 : ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ))
        * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ))
        ≤ ((⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ) := by
      exact_mod_cast (Nat.le_sqrt).mp (le_refl _)
    rwa [htoNat] at h1
  have hnn : (0:ℝ) ≤ (Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ)
      / ((2:ℚ)^k : ℝ) := by positivity
  have hsq : ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) / ((2:ℚ)^k : ℝ))
      * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) / ((2:ℚ)^k : ℝ)) ≤ a := by
    have hrw : ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) / ((2:ℚ)^k : ℝ))
        * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) / ((2:ℚ)^k : ℝ))
        = ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ)
            * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ)))
          / (((2:ℚ)^k : ℝ) * ((2:ℚ)^k : ℝ)) := by
      field_simp
    rw [hrw, ratSqrtLo_denom,
      div_le_iff₀ (show (0:ℝ) < ((2:ℚ)^(2*k):ℝ) by positivity)]
    calc ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ))
        * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ))
        ≤ ((⌊a * (2 : ℚ) ^ (2 * k)⌋ : ℝ)) := by exact_mod_cast hn2
      _ ≤ ((a * (2:ℚ)^(2*k) : ℝ)) := by exact_mod_cast Int.floor_le _
      _ = (a:ℝ) * ((2:ℚ)^(2*k):ℝ) := by push_cast; ring
  have hfinal : Real.sqrt (((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ)
      / ((2:ℚ)^k : ℝ)) * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ)
      / ((2:ℚ)^k : ℝ))) ≤ Real.sqrt a := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_mul_self hnn] at hfinal
  have hcast : (ratSqrtLo a k : ℝ)
      = (Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) / ((2:ℚ)^k : ℝ) := by
    simp only [ratSqrtLo]
    push_cast
    simp
  rw [hcast]
  exact hfinal

/-- The square root of nonnegative `a` is strictly below `ratSqrtLo a k + unit k`. -/
theorem sqrt_lt_ratSqrtLo_add (a : ℚ) (k : ℕ) (ha : 0 ≤ a) :
    Real.sqrt a < (ratSqrtLo a k : ℝ) + (unit k : ℝ) := by
  have hm0 : 0 ≤ ⌊a * (2 : ℚ) ^ (2 * k)⌋ := ratSqrtLo_radicand_nonneg a k ha
  have htoNat : (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat = ⌊a * (2 : ℚ) ^ (2 * k)⌋ :=
    Int.toNat_of_nonneg hm0
  have hlt : (⌊a * (2 : ℚ) ^ (2 * k)⌋ : ℤ)
      < ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ) + 1)
        * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ) + 1) := by
    have h1 : ((⌊a * (2 : ℚ) ^ (2 * k)⌋ : ℤ))
        < ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ) + 1)
          * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ) + 1) := by
      have h2 : ((⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ)
          < ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ) + 1)
            * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℤ) + 1) := by
        exact_mod_cast Nat.lt_succ_sqrt _
      rwa [htoNat] at h2
    exact h1
  have hfloor : a * (2 : ℚ) ^ (2 * k)
      < (⌊a * (2 : ℚ) ^ (2 * k)⌋ : ℚ) + 1 := Int.lt_floor_add_one _
  have hcast : (ratSqrtLo a k : ℝ) + (unit k : ℝ)
      = ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) + 1) / ((2:ℚ)^k : ℝ) := by
    simp only [ratSqrtLo]
    rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
    push_cast
    rw [add_div]
  rw [hcast]
  refine (Real.sqrt_lt (by positivity) (by positivity)).mpr ?_
  have hrw : ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) + 1) / ((2:ℚ)^k : ℝ)
      * (((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) + 1) / ((2:ℚ)^k : ℝ))
      = (((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) + 1)
          * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) + 1))
        / (((2:ℚ)^k : ℝ) * ((2:ℚ)^k : ℝ)) := by
    field_simp
  rw [sq, hrw, ratSqrtLo_denom,
    lt_div_iff₀ (show (0:ℝ) < ((2:ℚ)^(2*k):ℝ) by positivity)]
  calc (a:ℝ) * ((2:ℚ)^(2*k):ℝ) < ((⌊a * (2 : ℚ) ^ (2 * k)⌋ : ℝ)) + 1 := by
        push_cast
        exact_mod_cast hfloor
    _ ≤ (((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) + 1)
        * ((Nat.sqrt (⌊a * (2 : ℚ) ^ (2 * k)⌋).toNat : ℝ) + 1)) := by
        exact_mod_cast hlt

/-- The product of two precision units equals the precision unit at the sum of their indices. -/
private theorem unit_mul_unit (k j : ℕ) : (unit k : ℚ) * unit j = unit (k + j) := by
  rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit, Qatlib.Foundations.IntervalArith.IntervalOps.unit,
    Qatlib.Foundations.IntervalArith.IntervalOps.unit]
  field_simp
  rw [← pow_add]

/-- The square root of `unit (2 * p + 4)` equals `unit (p + 2)`. -/
private theorem sqrt_unit (p : ℕ) :
    Real.sqrt ((unit (2 * p + 4) : ℝ)) = (unit (p + 2) : ℝ) := by
  have hnn : (0:ℝ) ≤ (unit (p + 2) : ℝ) := by
    rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
    push_cast
    positivity
  have hidx : (p + 2) + (p + 2) = 2 * p + 4 := by omega
  have h1 : (unit (p + 2) : ℚ) * unit (p + 2) = unit (2 * p + 4) := by
    rw [unit_mul_unit, hidx]
  have hsq : (unit (p + 2) : ℝ) * (unit (p + 2) : ℝ) = (unit (2 * p + 4) : ℝ) := by
    exact_mod_cast h1
  rw [← hsq, Real.sqrt_mul_self hnn]

/-- The sum of `unit (p + 1)` and `unit (p + 2)` is at most `unit p`. -/
private theorem unit_add_half (p : ℕ) :
    (unit (p + 1) : ℝ) + unit (p + 2) ≤ (unit p : ℝ) := by
  have e1 := two_mul_unit_succ p
  have e2 := two_mul_unit_succ (p + 1)
  have hu1 : (0:ℝ) ≤ (unit (p + 1)) := by
    rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
    push_cast
    positivity
  linarith

/-- The square-root lift satisfies `Clause1V2SqrtLift`, including the specified approximation
and clock guarantees for nonnegative inputs. -/
theorem clause1_v2_sqrt_lift : Clause1V2SqrtLift := by
  intro N x hx hxp
  have hu : ∀ p : ℕ, |(N.approx (2 * p + 4) : ℝ) - x| ≤ (unit (2 * p + 4) : ℝ) :=
    fun p => abs_of_contains_cert (hx.2 _)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show 0 < N.timeC * 5 ^ N.timeD
    exact Nat.mul_pos hx.1 (by positivity)
  · intro p
    have habs := hu p
    have hA0 : (0:ℝ) ≤ max (N.approx (2 * p + 4) : ℝ) 0 := le_max_right _ _
    have hcastA : ((max (N.approx (2 * p + 4)) 0 : ℚ) : ℝ)
        = max (N.approx (2 * p + 4) : ℝ) 0 := by
      rw [ratCast_max]
      simp
    have hAq0 : (0:ℚ) ≤ max (N.approx (2 * p + 4)) 0 := by
      rcases le_total (0:ℚ) (N.approx (2 * p + 4)) with h | h
      · rw [max_eq_left h]; exact h
      · rw [max_eq_right h]
    have hx0 : (0:ℝ) ≤ x := hxp
    have hclip : |max (N.approx (2 * p + 4) : ℝ) 0 - x|
        ≤ |(N.approx (2 * p + 4) : ℝ) - x| := by
      rcases le_total 0 (N.approx (2 * p + 4) : ℝ) with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h, zero_sub, abs_neg, abs_of_nonneg hx0,
          abs_of_nonpos (by linarith : (N.approx (2 * p + 4) : ℝ) - x ≤ 0)]
        linarith
    have hhoel : |Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0) - Real.sqrt x|
        ≤ (unit (p + 2) : ℝ) := by
      have h1 := sqrt_hoelder hA0 hxp
      have h2 : |max (N.approx (2 * p + 4) : ℝ) 0 - x| ≤ (unit (2 * p + 4) : ℝ) :=
        le_trans hclip habs
      have h3 : (0:ℝ) ≤ (unit (2 * p + 4) : ℝ) := by
        rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
        push_cast
        positivity
      have h4 : |max (N.approx (2 * p + 4) : ℝ) 0 - x| ≤ (unit (2 * p + 4) : ℝ) := h2
      have h5 : Real.sqrt |max (N.approx (2 * p + 4) : ℝ) 0 - x|
          ≤ Real.sqrt (unit (2 * p + 4) : ℝ) := Real.sqrt_le_sqrt h2
      rw [sqrt_unit p] at h5
      exact le_trans h1 h5
    have hlo := ratSqrtLo_le (max (N.approx (2 * p + 4)) 0) (p + 1) hAq0
    have hhi := sqrt_lt_ratSqrtLo_add (max (N.approx (2 * p + 4)) 0) (p + 1) hAq0
    rw [hcastA] at hlo hhi
    have hbound : |(ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1) : ℝ)
        - Real.sqrt x| ≤ (unit p : ℝ) := by
      have h6 : |(ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1) : ℝ)
          - Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0)|
          ≤ (unit (p + 1) : ℝ) := by
        apply abs_le.mpr
        constructor
        · have : (ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1) : ℝ)
              ≤ Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0) := hlo
          linarith
        · have : Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0)
              < (ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1) : ℝ)
              + (unit (p + 1) : ℝ) := hhi
          linarith
      have hsplit : (ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1) : ℝ)
          - Real.sqrt x
          = ((ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1) : ℝ)
              - Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0))
            + (Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0) - Real.sqrt x) := by ring
      rw [hsplit]
      have hsum := abs_add_le
        ((ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1) : ℝ)
          - Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0))
        (Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0) - Real.sqrt x)
      have htotal : (unit (p + 1) : ℝ) + (unit (p + 2) : ℝ) ≤ (unit p : ℝ) :=
        unit_add_half p
      have hfinal : |(ratSqrtLo (max (N.approx (2 * p + 4)) 0) (p + 1) : ℝ)
          - Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0)|
          + |Real.sqrt (max (N.approx (2 * p + 4) : ℝ) 0) - Real.sqrt x|
          ≤ (unit p : ℝ) := le_trans (add_le_add h6 hhoel) htotal
      exact le_trans hsum hfinal
    exact contains_cert_of_abs _ _ (by
      simpa only [RealName.sqrtName] using! hbound)
  · intro p
    show N.timeC * (2 * p + 4 + 1) ^ N.timeD
        ≤ N.timeC * 5 ^ N.timeD * (p + 1) ^ (2 * N.timeD + 2)
    have hle : 2 * p + 4 + 1 ≤ 5 * (p + 1) := by omega
    have hmono : (2 * p + 4 + 1) ^ N.timeD ≤ (5 * (p + 1)) ^ N.timeD :=
      pow_le_pow_left₀ (by omega) hle N.timeD
    have hsplit : (5 * (p + 1)) ^ N.timeD = 5 ^ N.timeD * (p + 1) ^ N.timeD := by
      rw [mul_pow]
    have hgrow : (p + 1) ^ N.timeD ≤ (p + 1) ^ (2 * N.timeD + 2) :=
      pow_le_pow_right₀ (by omega : (1:ℕ) ≤ p + 1) (by omega)
    calc N.timeC * (2 * p + 4 + 1) ^ N.timeD
        ≤ N.timeC * (5 * (p + 1)) ^ N.timeD := Nat.mul_le_mul_left _ hmono
      _ = N.timeC * (5 ^ N.timeD * (p + 1) ^ N.timeD) := by rw [hsplit]
      _ ≤ N.timeC * (5 ^ N.timeD * (p + 1) ^ (2 * N.timeD + 2)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_left _ hgrow
      _ = N.timeC * 5 ^ N.timeD * (p + 1) ^ (2 * N.timeD + 2) := by ring

/-- Under the stated magnitude and positive-denominator bounds, common input error `u` gives
quotient error at most `u * 2 ^ s`. -/
private theorem div_error_bound {a b x y u B g : ℝ} {s : ℕ}
    (hbx : |x| ≤ B) (hby : |y| ≤ B) (hg : 0 < g) (hxg : g ≤ y)
    (hb : g / 2 ≤ b) (hea : |a - x| ≤ u) (heb : |b - y| ≤ u)
    (hcond : 4 * B ≤ g * g * 2 ^ s) :
    |a / b - x / y| ≤ u * 2 ^ s := by
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le hg hxg
  have hg2 : (0:ℝ) < g / 2 := by positivity
  have hb0 : (0:ℝ) < b := lt_of_lt_of_le hg2 hb
  have hprod : g * g / 2 ≤ b * y := by
    calc b * y ≥ (g / 2) * y := mul_le_mul_of_nonneg_right hb hy0.le
      _ ≥ (g / 2) * g := mul_le_mul_of_nonneg_left hxg (by positivity)
      _ = g * g / 2 := by ring
  have hnum : |a * y - x * b| ≤ 2 * B * u := by
    have hex : a * y - x * b = y * (a - x) + x * (y - b) := by ring
    rw [hex]
    have c1 : |y * (a - x)| ≤ B * u := by
      rw [abs_mul]
      exact mul_le_mul hby hea (abs_nonneg _) (le_trans (abs_nonneg y) hby)
    have heb' : |y - b| ≤ u := by rw [abs_sub_comm]; exact heb
    have c2 : |x * (y - b)| ≤ B * u := by
      rw [abs_mul]
      exact mul_le_mul hbx heb' (abs_nonneg _) (le_trans (abs_nonneg x) hbx)
    have hsum := abs_add_le (y * (a - x)) (x * (y - b))
    linarith
  have hsplit : a / b - x / y = (a * y - x * b) / (b * y) := by
    field_simp
  rw [hsplit, abs_div, abs_of_nonneg (mul_nonneg hb0.le hy0.le)]
  rw [div_le_iff₀ (mul_pos hb0 hy0)]
  have hgrow : 2 * B * u ≤ u * 2 ^ s * (b * y) := by
    have hu2s : (0:ℝ) ≤ u * 2 ^ s :=
      mul_nonneg (le_trans (abs_nonneg (a - x)) hea) (pow_nonneg (by norm_num) s)
    have hstep1 : u * 2 ^ s * (g * g / 2) ≤ u * 2 ^ s * (b * y) :=
      mul_le_mul_of_nonneg_left hprod hu2s
    have hstep2 : 2 * B * u ≤ u * 2 ^ s * (g * g / 2) := by
      have hu : (0:ℝ) ≤ u := le_trans (abs_nonneg (a - x)) hea
      have hkey : (4 * B) * u ≤ (g * g * 2 ^ s) * u :=
        mul_le_mul_of_nonneg_right hcond hu
      nlinarith [hkey, hg]
    exact le_trans hstep2 hstep1
  exact le_trans hnum hgrow

/-- The division lift satisfies `Clause1V2DivLift` under its magnitude, positive-gap, and
precision-shift assumptions. -/
theorem clause1_v2_div_lift : Clause1V2DivLift := by
  intro Nx Ny s B x y gap hx hy hgap hbx hby h1 h2
  have hypos : (0:ℝ) < y := lt_of_lt_of_le (by exact_mod_cast hgap.1 : (0:ℝ) < gap)
    hgap.2
  have hcondR : 4 * (B:ℝ) ≤ (gap:ℝ) * gap * (2:ℝ) ^ s := by
    have hq : (4:ℚ) * B ≤ gap * gap * 2 ^ s := by rw [← sq]; exact h2
    exact_mod_cast hq
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show 0 < Nx.timeC + Ny.timeC
    exact Nat.add_pos_left hx.1 _
  · intro p
    have ea : |(Nx.approx (p + s) : ℝ) - x| ≤ (unit (p + s) : ℝ) :=
      abs_of_contains_cert (hx.2 _)
    have eb : |(Ny.approx (p + s) : ℝ) - y| ≤ (unit (p + s) : ℝ) :=
      abs_of_contains_cert (hy.2 _)
    have hu_half : (unit (p + s) : ℝ) * 2 ≤ (gap:ℝ) := by
      have hpow : ((2:ℚ) ^ s) ≤ ((2:ℚ) ^ (p + s)) :=
        pow_le_pow_right₀ (by norm_num : (1:ℚ) ≤ 2) (by omega)
      have h2p : (2:ℚ) ≤ gap * ((2:ℚ) ^ (p + s)) :=
        le_trans h1 (mul_le_mul_of_nonneg_left hpow
          (le_of_lt (by exact_mod_cast hgap.1 : (0:ℚ) < gap)))
      have hq : (unit (p + s) : ℚ) * 2 ≤ gap := by
        rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
        field_simp
        linarith [h2p]
      exact_mod_cast hq
    have hgapy : (gap:ℝ) ≤ y := hgap.2
    have hbge : (gap:ℝ) / 2 ≤ (Ny.approx (p + s) : ℝ) := by
      have hlower : (gap:ℝ) - (unit (p + s) : ℝ) ≤ (Ny.approx (p + s) : ℝ) := by
        have hc1 := (abs_le.mp eb).1
        have hc2 := (abs_le.mp eb).2
        linarith [hgapy, hc1, hc2]
      have hhalf : (gap:ℝ) / 2 ≤ (gap:ℝ) - (unit (p + s) : ℝ) := by
        rw [div_le_iff₀ (by norm_num : (0:ℝ) < 2)]
        linarith [hu_half]
      exact le_trans hhalf hlower
    have hcore := div_error_bound (a := (Nx.approx (p + s) : ℝ))
      (b := (Ny.approx (p + s) : ℝ)) (x := x) (y := y)
      (u := (unit (p + s) : ℝ)) (B := (B:ℝ)) (g := (gap:ℝ)) (s := s)
      (by exact_mod_cast hbx.2) (by exact_mod_cast hby.2)
      (by exact_mod_cast hgap.1 : (0:ℝ) < gap) hgap.2 hbge ea eb hcondR
    have hunit : (unit (p + s) : ℝ) * ((2:ℝ) ^ s) = (unit p : ℝ) := by
      have hus := unit_succ_split p s
      push_cast at hus
      exact hus
    have hbound : |(Nx.approx (p + s) / Ny.approx (p + s) : ℝ) - x / y|
        ≤ (unit p : ℝ) := by
      rw [← hunit]
      exact hcore
    exact contains_cert_of_abs _ _ (by
      have hopen : ((Nx.divName Ny s).approx p : ℝ)
          = (Nx.approx (p + s) : ℝ) / (Ny.approx (p + s) : ℝ) := by
        simp only [RealName.divName]
        push_cast
        simp
      rw [hopen]
      exact hbound)
  · intro p
    have hd1 : Nx.timeD ≤ max Nx.timeD Ny.timeD + 1 :=
      Nat.le_trans (Nat.le_max_left _ _) (Nat.le_succ _)
    have hd2 : Ny.timeD ≤ max Nx.timeD Ny.timeD + 1 :=
      Nat.le_trans (Nat.le_max_right _ _) (Nat.le_succ _)
    have hp1 : (p + 1) ^ Nx.timeD ≤ (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      le_trans (pow_le_pow_left₀ (by omega) (by omega) _)
        (pow_le_pow_right₀ (by omega : (1:ℕ) ≤ p + 4) hd1)
    have hp2 : (p + 1) ^ Ny.timeD ≤ (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      le_trans (pow_le_pow_left₀ (by omega) (by omega) _)
        (pow_le_pow_right₀ (by omega : (1:ℕ) ≤ p + 4) hd2)
    have hc1 : Nx.timeC * (p + 1) ^ Nx.timeD
        ≤ Nx.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      Nat.mul_le_mul_left _ hp1
    have hc2 : Ny.timeC * (p + 1) ^ Ny.timeD
        ≤ Ny.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
      Nat.mul_le_mul_left _ hp2
    calc Nx.clock p + Ny.clock p
          = Nx.timeC * (p + 1) ^ Nx.timeD + Ny.timeC * (p + 1) ^ Ny.timeD := rfl
      _ ≤ Nx.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) +
            Ny.timeC * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) :=
            Nat.add_le_add hc1 hc2
      _ = (Nx.timeC + Ny.timeC) * (p + 4) ^ (max Nx.timeD Ny.timeD + 1) := by ring
      _ = (Nx.divName Ny s).clock (p + 3) := rfl

section Taylor

/-- The first `K` odd-degree Taylor terms for the sine function. -/
noncomputable def oddPoly (x : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * x ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)

/-- The first `K` even-degree Taylor terms for the cosine function. -/
noncomputable def evenPoly (x : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * x ^ (2 * k) / ((2 * k).factorial : ℝ)

/-- The difference between sine and its `K`-term polynomial `oddPoly`. -/
noncomputable def sinRem (x : ℝ) (K : ℕ) : ℝ := Real.sin x - oddPoly x K

/-- The difference between cosine and its `K`-term polynomial `evenPoly`. -/
noncomputable def cosRem (x : ℝ) (K : ℕ) : ℝ := Real.cos x - evenPoly x K

/-- The first `K` terms of the alternating power series for `Real.log (1 + t)`. -/
noncomputable def logPoly (t : ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * t ^ (k + 1) / ((k + 1 : ℕ) : ℝ)

/-- The difference between `Real.log (1 + t)` and its `K`-term polynomial `logPoly`. -/
noncomputable def logRem (t : ℝ) (K : ℕ) : ℝ := Real.log (1 + t) - logPoly t K

/-- The derivative of `oddPoly` with `K` terms is `evenPoly` with `K` terms. -/
private theorem oddPoly_hasDerivAt (x : ℝ) (K : ℕ) :
    HasDerivAt (fun y => oddPoly y K) (evenPoly x K) x := by
  have hfun : (fun y : ℝ => oddPoly y K)
      = (∑ k ∈ Finset.range K,
        (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k + 1)
          / ((2 * k + 1).factorial : ℝ))) := by
    funext y
    simp only [oddPoly, Finset.sum_apply]
  rw [hfun]
  have hsum : HasDerivAt (∑ k ∈ Finset.range K,
      (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k + 1) / ((2 * k + 1).factorial : ℝ)))
    (∑ k ∈ Finset.range K,
      (-1 : ℝ) ^ k * (((2 * k + 1 : ℕ) : ℝ) * x ^ (2 * k + 1 - 1))
        / ((2 * k + 1).factorial : ℝ)) x :=
    HasDerivAt.sum (fun k _ =>
      HasDerivAt.div_const (HasDerivAt.const_mul ((-1 : ℝ) ^ k)
        (hasDerivAt_pow (2 * k + 1) x)) ((2 * k + 1).factorial : ℝ))
  refine hsum.congr_deriv ?_
  simp only [evenPoly]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hexp : (2 * k + 1 - 1 : ℕ) = 2 * k := by omega
  have hfac : ((2 * k + 1).factorial : ℝ)
      = ((2 * k).factorial : ℝ) * ((2 * k + 1 : ℕ) : ℝ) := by
    rw [Nat.factorial_succ]
    push_cast
    ring
  rw [hexp, hfac]
  field_simp

/-- The derivative of `evenPoly` with `K` terms is the negation of `oddPoly` with `K - 1` terms. -/
private theorem evenPoly_hasDerivAt (x : ℝ) (K : ℕ) :
    HasDerivAt (fun y => evenPoly y K) (-oddPoly x (K - 1)) x := by
  have hfun : (fun y : ℝ => evenPoly y K)
      = (∑ k ∈ Finset.range K,
        (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k)
          / ((2 * k).factorial : ℝ))) := by
    funext y
    simp only [evenPoly, Finset.sum_apply]
  rw [hfun]
  have hsum : HasDerivAt (∑ k ∈ Finset.range K,
      (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (2 * k) / ((2 * k).factorial : ℝ)))
    (∑ k ∈ Finset.range K,
      (-1 : ℝ) ^ k * (((2 * k : ℕ) : ℝ) * x ^ (2 * k - 1)) / ((2 * k).factorial : ℝ)) x :=
    HasDerivAt.sum (fun k _ =>
      HasDerivAt.div_const (HasDerivAt.const_mul ((-1 : ℝ) ^ k)
        (hasDerivAt_pow (2 * k) x)) ((2 * k).factorial : ℝ))
  refine hsum.congr_deriv ?_
  rcases K with _ | K'
  · simp [oddPoly]
  · rw [show K' + 1 - 1 = K' from rfl]
    simp only [oddPoly]
    rw [Finset.sum_range_succ']
    have hzero : ((-1 : ℝ) ^ 0) * (((2 * 0 : ℕ) : ℝ) * x ^ (2 * 0 - 1))
        / ((2 * 0).factorial : ℝ) = 0 := by norm_num
    rw [hzero, add_zero, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show (2 * (k + 1) - 1 : ℕ) = 2 * k + 1 from by omega]
    rw [show (2 * (k + 1) : ℕ) = 2 * k + 2 from by omega, Nat.factorial_succ, pow_succ]
    push_cast
    field_simp
    ring

/-- A global derivative representation with the stated local bound implies `|f v - f u| ≤ C * |v
- u|`. -/
private theorem mvt_abs_le2 {f f' : ℝ → ℝ} (u v : ℝ)
    (hderiv : ∀ ξ : ℝ, HasDerivAt f (f' ξ) ξ) {C : ℝ}
    (hbound : ∀ ξ : ℝ, |ξ - u| ≤ |v - u| → |f' ξ| ≤ C) : |f v - f u| ≤ C * |v - u| := by
  rcases lt_trichotomy u v with hlt | heq | hlt
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun z _ => (hderiv z).continuousAt.continuousWithinAt) (fun z _ => hderiv z)
    have hne : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hlt))
    have hmul := (eq_div_iff hne).mp hslope
    have hnear : |ξ - u| ≤ |v - u| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hξ.1.le), abs_of_nonneg (sub_nonneg.mpr hlt.le)]
      exact sub_le_sub_right hξ.2.le u
    have hC := hbound ξ hnear
    rw [← hmul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    exact mul_le_mul hC (le_refl _) (sub_nonneg.mpr hlt.le) (le_trans (abs_nonneg (f' ξ)) hC)
  · subst heq
    simp
  · obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt
      (fun z _ => (hderiv z).continuousAt.continuousWithinAt) (fun z _ => hderiv z)
    have hne : u - v ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hlt))
    have hmul := (eq_div_iff hne).mp hslope
    have hξu : ξ ≤ u := hξ.2.le
    have hnear : |ξ - u| ≤ |v - u| := by
      rw [abs_sub_comm ξ u, abs_sub_comm v u,
        abs_of_nonneg (sub_nonneg.mpr hξu), abs_of_nonneg (sub_nonneg.mpr hlt.le)]
      exact sub_le_sub_left hξ.1.le u
    have hC := hbound ξ hnear
    have hvu : |v - u| = u - v := by
      rw [abs_sub_comm v u, abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    rw [abs_sub_comm (f v) (f u), ← hmul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlt.le), hvu]
    exact mul_le_mul hC (le_refl _) (sub_nonneg.mpr hlt.le) (le_trans (abs_nonneg (f' ξ)) hC)

/-- The sine remainder vanishes at zero for every truncation length. -/
private theorem sinRem_zero (K : ℕ) : sinRem 0 K = 0 := by
  have h : oddPoly 0 K = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [zero_pow (by omega), mul_zero, zero_div]
  simp [sinRem, h]

/-- The cosine polynomial with `K + 1` terms takes value one at zero. -/
private theorem evenPoly_zero_succ (K : ℕ) : evenPoly 0 (K + 1) = 1 := by
  induction K with
  | zero => simp [evenPoly]
  | succ K ih =>
    simp only [evenPoly, Finset.sum_range_succ] at ih ⊢
    rw [ih]
    have hz : ((-1 : ℝ) ^ (K + 1)) * 0 ^ (2 * (K + 1))
        / (((2 * (K + 1)).factorial : ℝ)) = 0 := by
      rw [zero_pow (by omega), mul_zero, zero_div]
    rw [hz]
    norm_num

/-- The cosine remainder with `K + 1` terms vanishes at zero. -/
private theorem cosRem_zero_succ (K : ℕ) : cosRem 0 (K + 1) = 0 := by
  simp [cosRem, evenPoly_zero_succ K]

/-- The sine remainder with `K` terms and cosine remainder with `K + 1` terms are bounded by
`|x| ^ (2 * K + 1)` and `|x| ^ (2 * K + 2)`, respectively. -/
private theorem remainders_coupled : ∀ K : ℕ,
    (∀ x : ℝ, |sinRem x K| ≤ |x| ^ (2 * K + 1)) ∧
      (∀ x : ℝ, |cosRem x (K + 1)| ≤ |x| ^ (2 * K + 2)) := by
  intro K
  induction K with
  | zero =>
    constructor
    · intro x
      have h := Real.abs_sin_sub_sin_le x 0
      simp only [sinRem, oddPoly, Finset.sum_range_zero, Real.sin_zero, sub_zero,
        Nat.mul_zero, Nat.zero_add, pow_one] at h ⊢
      exact h
    · intro x
      have hd : ∀ ξ : ℝ, HasDerivAt (fun y => cosRem y 1) (-Real.sin ξ + oddPoly ξ 0) ξ := by
        intro ξ
        refine (HasDerivAt.sub (HasDerivAt.cos (hasDerivAt_id ξ))
          (evenPoly_hasDerivAt ξ 1)).congr_deriv ?_
        simp only [id_eq, mul_one, sub_neg_eq_add, Nat.sub_self]
      have hb : ∀ ξ : ℝ, |ξ - (0:ℝ)| ≤ |x - 0| → |-Real.sin ξ + oddPoly ξ 0| ≤ |x| := by
        intro ξ hξ
        simp only [oddPoly, Finset.sum_range_zero, add_zero, abs_neg]
        have h := Real.abs_sin_sub_sin_le ξ 0
        have h2 : |Real.sin ξ| ≤ |ξ| := by simpa using! h
        have hξ' : |ξ| ≤ |x| := by simpa using! hξ
        exact le_trans h2 hξ'
      have hkey := mvt_abs_le2 (0:ℝ) x hd (C := |x|) hb
      have h0 : cosRem 0 1 = 0 := cosRem_zero_succ 0
      simp only [h0, sub_zero] at hkey
      show |cosRem x 1| ≤ |x| ^ 2
      rw [pow_two]
      exact hkey
  | succ K ih =>
    have hsin : ∀ x : ℝ, |sinRem x (K + 1)| ≤ |x| ^ (2 * (K + 1) + 1) := by
      intro x
      have hd : ∀ ξ : ℝ, HasDerivAt (fun y => sinRem y (K + 1)) (cosRem ξ (K + 1)) ξ := by
        intro ξ
        refine (HasDerivAt.sub (HasDerivAt.sin (hasDerivAt_id ξ))
          (oddPoly_hasDerivAt ξ (K + 1))).congr_deriv ?_
        simp only [id_eq, mul_one, cosRem]
      have hb : ∀ ξ : ℝ, |ξ - (0:ℝ)| ≤ |x - 0| →
          |cosRem ξ (K + 1)| ≤ |x| ^ (2 * K + 2) := by
        intro ξ hξ
        have hξ' : |ξ| ≤ |x| := by simpa using! hξ
        exact le_trans (ih.2 ξ) (pow_le_pow_left₀ (abs_nonneg ξ) hξ' (2 * K + 2))
      have hkey := mvt_abs_le2 (0:ℝ) x hd (C := |x| ^ (2 * K + 2)) hb
      simp only [sinRem_zero, sub_zero] at hkey
      rw [show 2 * (K + 1) + 1 = 2 * K + 2 + 1 from rfl, pow_succ]
      exact hkey
    refine ⟨hsin, fun x => ?_⟩
    have hd : ∀ ξ : ℝ,
        HasDerivAt (fun y => cosRem y (K + 2)) (-(sinRem ξ (K + 1))) ξ := by
      intro ξ
      have h1 : HasDerivAt (fun y : ℝ => Real.cos y) (-(Real.sin ξ)) ξ := by
        simpa only [id_eq, mul_one] using! HasDerivAt.cos (hasDerivAt_id ξ)
      have h2 : HasDerivAt (fun y => evenPoly y (K + 2)) (-oddPoly ξ (K + 1)) ξ :=
        evenPoly_hasDerivAt ξ (K + 2)
      have hderiv : HasDerivAt (fun y => cosRem y (K + 2))
          (-(Real.sin ξ) - (-oddPoly ξ (K + 1))) ξ := h1.sub h2
      exact hderiv.congr_deriv (by simp only [sinRem]; ring)
    have hb : ∀ ξ : ℝ, |ξ - (0:ℝ)| ≤ |x - 0| →
        |-(sinRem ξ (K + 1))| ≤ |x| ^ (2 * K + 3) := by
      intro ξ hξ
      have hξ' : |ξ| ≤ |x| := by simpa using! hξ
      rw [abs_neg]
      exact le_trans (hsin ξ) (pow_le_pow_left₀ (abs_nonneg ξ) hξ' (2 * (K + 1) + 1))
    have hkey := mvt_abs_le2 (0:ℝ) x hd (C := |x| ^ (2 * K + 3)) hb
    have h0 : cosRem 0 (K + 2) = 0 := cosRem_zero_succ (K + 1)
    simp only [h0, sub_zero] at hkey
    show |cosRem x (K + 2)| ≤ |x| ^ (2 * K + 3 + 1)
    rw [pow_succ]
    exact hkey

/-- The logarithm remainder vanishes at zero for every truncation length. -/
private theorem logRem_zero (K : ℕ) : logRem 0 K = 0 := by
  have h : logPoly 0 K = 0 := by
    refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [zero_pow (by omega), mul_zero, zero_div]
  simp [logRem, h, Real.log_one]

/-- Away from `t = -1`, the derivative of the logarithm remainder is `(-t) ^ K / (1 + t)`. -/
private theorem logRem_hasDerivAt (t : ℝ) (K : ℕ) (ht : t ≠ -1) :
    HasDerivAt (fun y => logRem y K) ((-t) ^ K / (1 + t)) t := by
  have hlog : HasDerivAt (fun y : ℝ => Real.log (1 + y)) (1 / (1 + t)) t := by
    have h1 : HasDerivAt (fun y : ℝ => 1 + y) 1 t := by
      have h := HasDerivAt.add (hasDerivAt_const t 1) (hasDerivAt_id t)
      have hfun : ((fun _ : ℝ => (1:ℝ)) + _root_.id) = (fun y : ℝ => (1:ℝ) + y) := by
        funext y
        simp
      rw [hfun] at h
      simpa only [zero_add] using! h
    have hne : (1 : ℝ) + t ≠ 0 := by
      intro hcon
      exact ht (by linarith)
    simpa only [zero_add] using! h1.log hne
  have hpoly : HasDerivAt (fun y : ℝ => logPoly y K)
      (∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * t ^ k) t := by
    have hfun : (fun y : ℝ => logPoly y K)
        = (∑ k ∈ Finset.range K,
          (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ))) := by
      funext y
      simp only [logPoly, Finset.sum_apply]
    rw [hfun]
    have hsum : HasDerivAt (∑ k ∈ Finset.range K,
        (fun y : ℝ => (-1 : ℝ) ^ k * y ^ (k + 1) / ((k + 1 : ℕ) : ℝ)))
      (∑ k ∈ Finset.range K,
        (-1 : ℝ) ^ k * (((k + 1 : ℕ) : ℝ) * t ^ ((k + 1 : ℕ) - 1))
          / ((k + 1 : ℕ) : ℝ)) t :=
      HasDerivAt.sum (fun k _ =>
        HasDerivAt.div_const (HasDerivAt.const_mul ((-1 : ℝ) ^ k)
          (hasDerivAt_pow (k + 1) t)) ((k + 1 : ℕ) : ℝ))
    refine hsum.congr_deriv ?_
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show ((k + 1 : ℕ) - 1 : ℕ) = k from rfl]
    field_simp
  refine (hlog.sub hpoly).congr_deriv ?_
  have hne1 : (1 : ℝ) + t ≠ 0 := by
    intro hcon
    exact ht (by linarith)
  have hne2 : (-t : ℝ) ≠ 1 := by
    intro hcon
    exact ht (by linarith)
  have hgeom : ∑ k ∈ Finset.range K, (-t : ℝ) ^ k
      = ((-t) ^ K - 1) / (-t - 1) := geom_sum_eq hne2 K
  have hterm : ∀ k : ℕ, (-1 : ℝ) ^ k * t ^ k = (-t) ^ k := by
    intro k
    rw [← mul_pow, neg_mul, one_mul]
  calc (1 : ℝ) / (1 + t) - ∑ k ∈ Finset.range K, (-1 : ℝ) ^ k * t ^ k
      = (1 : ℝ) / (1 + t) - ∑ k ∈ Finset.range K, (-t) ^ k := by
        rw [← Finset.sum_congr rfl (fun k _ => hterm k)]
    _ = (1 : ℝ) / (1 + t) - (((-t) ^ K - 1) / (-t - 1)) := by rw [hgeom]
    _ = (-t) ^ K / (1 + t) := by
        field_simp
        ring

/-- A point between zero and `t` has absolute value at most `|t|`. -/
private theorem abs_le_of_mem_icc {t y : ℝ}
    (hy : y ∈ Set.Icc (min (0:ℝ) t) (max (0:ℝ) t)) : |y| ≤ |t| := by
  rcases lt_trichotomy 0 t with hpos | hzero | hneg
  · rw [min_eq_left hpos.le, max_eq_right hpos.le] at hy
    rw [abs_of_nonneg hy.1, abs_of_pos hpos]
    exact hy.2
  · rw [hzero, min_self, max_self] at hy
    have hy0 : y = t := le_antisymm hy.2 hy.1
    rw [hy0, ← hzero]
  · rw [min_eq_right hneg.le, max_eq_left hneg.le] at hy
    rw [abs_of_nonpos hy.2, abs_of_neg hneg]
    exact neg_le_neg hy.1

/-- Continuity on the closed interval and a bounded derivative on its interior imply `|f v - f
u| ≤ C * |v - u|`. -/
private theorem mvt_abs_le2' {f f' : ℝ → ℝ} (u v : ℝ)
    (hcont : ContinuousOn f (Set.Icc (min u v) (max u v)))
    (hderiv : ∀ ξ ∈ Set.Ioo (min u v) (max u v), HasDerivAt f (f' ξ) ξ) {C : ℝ}
    (hbound : ∀ ξ : ℝ, |ξ - u| ≤ |v - u| → |f' ξ| ≤ C) : |f v - f u| ≤ C * |v - u| := by
  rcases lt_trichotomy u v with hlt | heq | hlt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hcont hderiv
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt hcont hderiv
    have hne : v - u ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hlt))
    have hmul := (eq_div_iff hne).mp hslope
    have hnear : |ξ - u| ≤ |v - u| := by
      rw [abs_of_nonneg (sub_nonneg.mpr hξ.1.le), abs_of_nonneg (sub_nonneg.mpr hlt.le)]
      exact sub_le_sub_right hξ.2.le u
    have hC := hbound ξ hnear
    rw [← hmul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    exact mul_le_mul hC (le_refl _) (sub_nonneg.mpr hlt.le) (le_trans (abs_nonneg (f' ξ)) hC)
  · subst heq
    simp
  · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hcont hderiv
    obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f' hlt hcont hderiv
    have hne : u - v ≠ 0 := sub_ne_zero.mpr (Ne.symm (ne_of_lt hlt))
    have hmul := (eq_div_iff hne).mp hslope
    have hξu : ξ ≤ u := hξ.2.le
    have hnear : |ξ - u| ≤ |v - u| := by
      rw [abs_sub_comm ξ u, abs_sub_comm v u,
        abs_of_nonneg (sub_nonneg.mpr hξu), abs_of_nonneg (sub_nonneg.mpr hlt.le)]
      exact sub_le_sub_left hξ.1.le u
    have hC := hbound ξ hnear
    have hvu : |v - u| = u - v := by
      rw [abs_sub_comm v u, abs_of_nonneg (sub_nonneg.mpr hlt.le)]
    rw [abs_sub_comm (f v) (f u), ← hmul, abs_mul, abs_of_nonneg (sub_nonneg.mpr hlt.le), hvu]
    exact mul_le_mul hC (le_refl _) (sub_nonneg.mpr hlt.le) (le_trans (abs_nonneg (f' ξ)) hC)

/-- For `|t| ≤ 1 / 2`, the logarithm remainder is bounded by `2 * |t| ^ (K + 1)`. -/
private theorem logRem_bound (t : ℝ) (K : ℕ) (h : |t| ≤ 1 / 2) :
    |logRem t K| ≤ 2 * |t| ^ (K + 1) := by
  have hderiv : ∀ ξ ∈ Set.Ioo (min (0:ℝ) t) (max (0:ℝ) t),
      HasDerivAt (fun y => logRem y K) ((-ξ) ^ K / (1 + ξ)) ξ := by
    intro ξ hξm
    have hicc : ξ ∈ Set.Icc (min (0:ℝ) t) (max (0:ℝ) t) :=
      Set.Ioo_subset_Icc_self hξm
    have hξ' : |ξ| ≤ |t| := abs_le_of_mem_icc hicc
    refine logRem_hasDerivAt ξ K ?_
    intro hcon
    have h1 : |ξ| = 1 := by rw [hcon]; simp
    have h2 : |ξ| ≤ 1 / 2 := le_trans hξ' h
    linarith
  have hcont : ContinuousOn (fun y => logRem y K) (Set.Icc (min (0:ℝ) t) (max (0:ℝ) t)) := by
    intro y hy
    have hξ' : |y| ≤ |t| := abs_le_of_mem_icc hy
    refine (logRem_hasDerivAt y K ?_).continuousAt.continuousWithinAt
    intro hcon
    have h1 : |y| = 1 := by rw [hcon]; simp
    have h2 : |y| ≤ 1 / 2 := le_trans hξ' h
    linarith
  have hb : ∀ ξ : ℝ, |ξ - (0:ℝ)| ≤ |t - 0| → |(-ξ) ^ K / (1 + ξ)| ≤ 2 * |t| ^ K := by
    intro ξ hξ
    have hξ' : |ξ| ≤ |t| := by simpa using! hξ
    have h1 : (1/2 : ℝ) ≤ 1 + ξ := by
      have hx := abs_le.mp (le_trans hξ' h)
      linarith
    have h2 : |(-ξ) ^ K| = |ξ| ^ K := by rw [abs_pow, abs_neg]
    rw [abs_div, h2, abs_of_nonneg (show (0:ℝ) ≤ 1 + ξ by linarith),
      div_le_iff₀ (show (0:ℝ) < 1 + ξ by linarith)]
    have hgrow : (1 : ℝ) ≤ 2 * (1 + ξ) := by linarith
    calc |ξ| ^ K ≤ |t| ^ K := pow_le_pow_left₀ (abs_nonneg ξ) hξ' K
      _ ≤ |t| ^ K * (2 * (1 + ξ)) := by
          have hp : (0:ℝ) ≤ |t| ^ K := pow_nonneg (abs_nonneg t) K
          nlinarith [mul_le_mul hgrow le_rfl hp (by positivity : (0:ℝ) ≤ 2 * (1 + ξ))]
      _ = 2 * |t| ^ K * (1 + ξ) := by ring
  have hkey := mvt_abs_le2' (0:ℝ) t hcont hderiv (C := 2 * |t| ^ K) hb
  simp only [logRem_zero, sub_zero] at hkey
  have heq : 2 * |t| ^ K * |t| = 2 * |t| ^ (K + 1) := by
    rw [pow_succ]
    ring
  rw [← heq]
  exact hkey

/-- Coercing the rational sine partial sum to the reals yields `oddPoly`. -/
private theorem cast_sinPartial (a : ℚ) (K : ℕ) :
    (sinPartial a K : ℝ) = oddPoly (a : ℝ) K := by
  simp only [sinPartial, oddPoly, Rat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  simp

/-- Coercing the rational logarithm partial sum to the reals yields `logPoly`. -/
private theorem cast_logPartial (t : ℚ) (K : ℕ) :
    (logPartial t K : ℝ) = logPoly (t : ℝ) K := by
  simp only [logPartial, logPoly, Rat.cast_sum]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  push_cast
  simp

end Taylor

/-- Every precision unit has nonnegative real value. -/
private theorem unit_ge_zero (k : ℕ) : (0:ℝ) ≤ unit k := by
  rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
  push_cast
  positivity

/-- The real power `(1 / 2) ^ k` equals the real value of `unit k`. -/
private theorem half_pow_eq_unit (k : ℕ) : (1 / 2 : ℝ) ^ k = (unit k : ℝ) := by
  rw [Qatlib.Foundations.IntervalArith.IntervalOps.unit]
  push_cast
  rw [div_pow]
  simp

/-- Increasing the precision index by one does not increase the precision unit. -/
private theorem unit_le_of_succ (p : ℕ) : (unit (p + 1) : ℝ) ≤ unit p := by
  have h := two_mul_unit_succ p
  have h0 : (0:ℝ) ≤ unit (p + 1) := unit_ge_zero (p + 1)
  linarith

/-- The real value of `unit (p + 3)` is at most one eighth. -/
private theorem unit3_le_eighth (p : ℕ) : (unit (p + 3) : ℝ) ≤ 1 / 8 := by
  rw [← half_pow_eq_unit]
  have h := pow_le_pow_of_le_one (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num : (1:ℝ)/2 ≤ 1) (by omega : (3:ℕ) ≤ p + 3)
  calc (1/2 : ℝ) ^ (p + 3) ≤ (1/2 : ℝ) ^ 3 := h
    _ = 1 / 8 := by norm_num

/-- The sine lift satisfies `Clause1V2SinLift`, with the specified approximation and clock
guarantees for inputs with absolute value at most one quarter. -/
theorem clause1_v2_sin_lift : Clause1V2SinLift := by
  intro N x hx hxwin
  have hu : ∀ p : ℕ, |(N.approx (p + 3) : ℝ) - x| ≤ (unit (p + 3) : ℝ) :=
    fun p => abs_of_contains_cert (hx.2 _)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show 0 < N.timeC * 5 ^ N.timeD
    exact Nat.mul_pos hx.1 (by positivity)
  · intro p
    have habs := hu p
    have hxabs : |x| ≤ 1 / 4 := hxwin
    have hu3 : (unit (p + 3) : ℝ) ≤ 1 / 8 := unit3_le_eighth p
    have htri : |(N.approx (p + 3) : ℝ)| ≤ |x| + |(N.approx (p + 3) : ℝ) - x| := by
      have h2 := abs_sub_abs_le_abs_sub (N.approx (p + 3) : ℝ) x
      linarith
    have hale : |(N.approx (p + 3) : ℝ)| ≤ 1 / 2 := by
      have h1 : |(N.approx (p + 3) : ℝ) - x| ≤ 1 / 8 := le_trans habs hu3
      linarith
    have hbound : |(sinPartial (N.approx (p + 3)) (p + 2) : ℝ) - Real.sin x|
        ≤ (unit p : ℝ) := by
      rw [cast_sinPartial]
      have hsplit : oddPoly (N.approx (p + 3) : ℝ) (p + 2) - Real.sin x
          = (Real.sin (N.approx (p + 3) : ℝ) - Real.sin x)
            - sinRem (N.approx (p + 3) : ℝ) (p + 2) := by
        simp only [sinRem]
        ring
      rw [hsplit]
      have hstep : |(Real.sin (N.approx (p + 3) : ℝ) - Real.sin x)
          - sinRem (N.approx (p + 3) : ℝ) (p + 2)|
          ≤ |Real.sin (N.approx (p + 3) : ℝ) - Real.sin x|
            + |sinRem (N.approx (p + 3) : ℝ) (p + 2)| :=
        abs_sub _ _
      have h1 : |Real.sin (N.approx (p + 3) : ℝ) - Real.sin x| ≤ (unit (p + 3) : ℝ) :=
        le_trans (Real.abs_sin_sub_sin_le _ _) habs
      have h2 : |sinRem (N.approx (p + 3) : ℝ) (p + 2)| ≤ (unit (p + 3) : ℝ) := by
        have hrem := (remainders_coupled (p + 2)).1 (N.approx (p + 3) : ℝ)
        have hp1 : |(N.approx (p + 3) : ℝ)| ^ (2 * (p + 2) + 1)
            ≤ (1/2 : ℝ) ^ (p + 3) := by
          have e1 : |(N.approx (p + 3) : ℝ)| ^ (2 * (p + 2) + 1)
              ≤ (1/2 : ℝ) ^ (2 * (p + 2) + 1) :=
            pow_le_pow_left₀ (abs_nonneg _) hale _
          have e2 : (1/2 : ℝ) ^ (2 * (p + 2) + 1) ≤ (1/2 : ℝ) ^ (p + 3) :=
            pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
          exact le_trans e1 e2
        exact le_trans (le_trans hrem hp1) (half_pow_eq_unit (p + 3)).le
      have hsum : (unit (p + 3) : ℝ) + (unit (p + 3) : ℝ) ≤ (unit p : ℝ) := by
        have e1 : (unit (p + 3) : ℝ) + unit (p + 3) = unit (p + 2) :=
          two_mul_unit_succ (p + 2)
        have e2 := unit_le_of_succ (p + 1)
        have e3 := unit_le_of_succ p
        have h0 : (0:ℝ) ≤ unit (p + 3) := unit_ge_zero (p + 3)
        linarith
      exact le_trans (le_trans hstep (add_le_add h1 h2)) hsum
    exact contains_cert_of_abs _ _ (by
      simpa only [RealName.sinName] using! hbound)
  · intro p
    show N.timeC * (p + 1) ^ N.timeD
        ≤ N.timeC * 5 ^ N.timeD * ((p + 2) + 1) ^ (N.timeD + 3)
    have hle : p + 1 ≤ 5 * (p + 3) := by omega
    have hmono : (p + 1) ^ N.timeD ≤ (5 * (p + 3)) ^ N.timeD :=
      pow_le_pow_left₀ (by omega) hle N.timeD
    have hsplit : (5 * (p + 3)) ^ N.timeD = 5 ^ N.timeD * (p + 3) ^ N.timeD := by
      rw [mul_pow]
    have hgrow : (p + 3) ^ N.timeD ≤ (p + 3) ^ (N.timeD + 3) :=
      pow_le_pow_right₀ (by omega : (1:ℕ) ≤ p + 3) (by omega)
    calc N.timeC * (p + 1) ^ N.timeD
        ≤ N.timeC * (5 * (p + 3)) ^ N.timeD := Nat.mul_le_mul_left _ hmono
      _ = N.timeC * (5 ^ N.timeD * (p + 3) ^ N.timeD) := by rw [hsplit]
      _ ≤ N.timeC * (5 ^ N.timeD * (p + 3) ^ (N.timeD + 3)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_left _ hgrow
      _ = N.timeC * 5 ^ N.timeD * (p + 3) ^ (N.timeD + 3) := by ring

/-- The logarithm lift satisfies `Clause1V2LogLift`, with the specified approximation and clock
guarantees for inputs within one quarter of one. -/
theorem clause1_v2_log_lift : Clause1V2LogLift := by
  intro N x hx hxwin
  have hu : ∀ p : ℕ, |(N.approx (p + 3) : ℝ) - x| ≤ (unit (p + 3) : ℝ) :=
    fun p => abs_of_contains_cert (hx.2 _)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show 0 < N.timeC * 5 ^ N.timeD
    exact Nat.mul_pos hx.1 (by positivity)
  · intro p
    have habs := hu p
    have hu3 : (unit (p + 3) : ℝ) ≤ 1 / 8 := unit3_le_eighth p
    have htau : |x - 1| ≤ 1 / 4 := hxwin
    have hbound : |(logPartial (N.approx (p + 3) - 1) (p + 2) : ℝ) - Real.log x|
        ≤ (unit p : ℝ) := by
      have hcast : (logPartial (N.approx (p + 3) - 1) (p + 2) : ℝ)
          = logPoly ((N.approx (p + 3) : ℝ) - 1) (p + 2) := by
        have h0 : ((N.approx (p + 3) - 1 : ℚ) : ℝ) = (N.approx (p + 3) : ℝ) - 1 := by
          push_cast
          ring
        rw [cast_logPartial, h0]
      rw [hcast]
      set t : ℝ := (N.approx (p + 3) : ℝ) - 1 with hte
      have htube : |t - (x - 1)| ≤ (unit (p + 3) : ℝ) := by
        have hre : t - (x - 1) = (N.approx (p + 3) : ℝ) - x := by
          rw [hte]
          ring
        rw [hre]
        exact habs
      have htube8 : |t - (x - 1)| ≤ 1 / 8 := le_trans htube hu3
      have ht38 : |t| ≤ 3 / 8 := by
        have h2 := abs_sub_abs_le_abs_sub t (x - 1)
        linarith
      have hale : |t| ≤ 1 / 2 := by linarith
      have hsplit : logPoly t (p + 2) - Real.log x
          = (Real.log (1 + t) - Real.log x) - logRem t (p + 2) := by
        simp only [logRem]
        ring
      rw [hsplit]
      have hstep : |(Real.log (1 + t) - Real.log x) - logRem t (p + 2)|
          ≤ |Real.log (1 + t) - Real.log x| + |logRem t (p + 2)| :=
        abs_sub _ _
      have hu5 : (1/2 : ℝ) ≤ 1 + t := by
        have h2 := (abs_le.mp ht38).1
        linarith
      have hv4 : (1/2 : ℝ) ≤ x := by
        have h2 := (abs_le.mp htau).1
        linarith
      have hlog1 : |Real.log (1 + t) - Real.log x| ≤ (unit (p + 2) : ℝ) := by
        have hcont : ContinuousOn Real.log (Set.Icc (min (1 + t) x) (max (1 + t) x)) := by
          intro y hy
          have hy1 : (1/2 : ℝ) ≤ y := le_trans (le_min hu5 hv4) hy.1
          exact (Real.hasDerivAt_log (by linarith)).continuousAt.continuousWithinAt
        have hderiv : ∀ ξ ∈ Set.Ioo (min (1 + t) x) (max (1 + t) x),
            HasDerivAt Real.log ((fun z : ℝ => z⁻¹) ξ) ξ := by
          intro ξ hξm
          have hicc : ξ ∈ Set.Icc (min (1 + t) x) (max (1 + t) x) :=
            Set.Ioo_subset_Icc_self hξm
          have hy1 : (1/2 : ℝ) ≤ ξ := le_trans (le_min hu5 hv4) hicc.1
          exact Real.hasDerivAt_log (by linarith)
        have hb2 : ∀ ξ : ℝ, |ξ - (1 + t)| ≤ |x - (1 + t)| → |ξ⁻¹| ≤ 2 := by
          intro ξ hξ
          have hdist : |x - (1 + t)| ≤ 1 / 8 := by
            have hre : x - (1 + t) = -(t - (x - 1)) := by ring
            rw [hre, abs_neg]
            exact htube8
          have hu58 : (5/8 : ℝ) ≤ 1 + t := by
            have h2 := (abs_le.mp ht38).1
            linarith
          have hlo := (abs_le.mp hξ).1
          have hξpos : (0:ℝ) < ξ := by linarith
          rw [abs_of_pos (inv_pos.2 hξpos)]
          rw [inv_eq_one_div, one_div_le hξpos (by norm_num : (0:ℝ) < 2)]
          linarith
        have hmvt := mvt_abs_le2' (1 + t) x hcont hderiv (C := 2) hb2
        rw [abs_sub_comm] at hmvt
        have hdist2 : |x - (1 + t)| ≤ (unit (p + 3) : ℝ) := by
          have hre : x - (1 + t) = -(t - (x - 1)) := by ring
          rw [hre, abs_neg]
          exact htube
        have h2u : (2:ℝ) * (unit (p + 3) : ℝ) = unit (p + 2) := by
          have h := two_mul_unit_succ (p + 2)
          have h0 : (0:ℝ) ≤ unit (p + 3) := unit_ge_zero (p + 3)
          linarith
        calc |Real.log (1 + t) - Real.log x| ≤ 2 * |x - (1 + t)| := hmvt
          _ ≤ 2 * (unit (p + 3) : ℝ) :=
              mul_le_mul_of_nonneg_left hdist2 (by norm_num)
          _ = (unit (p + 2) : ℝ) := h2u
      have hrem2 : |logRem t (p + 2)| ≤ (unit (p + 2) : ℝ) := by
        have hrb : |logRem t (p + 2)| ≤ 2 * |t| ^ (p + 3) := by
          rw [show (p + 3 : ℕ) = p + 2 + 1 from rfl]
          exact logRem_bound t (p + 2) hale
        have hp1 : |t| ^ (p + 3) ≤ (1/2 : ℝ) ^ (p + 3) :=
          pow_le_pow_left₀ (abs_nonneg t) hale _
        have h2u : (2:ℝ) * (unit (p + 3) : ℝ) = unit (p + 2) := by
          have h := two_mul_unit_succ (p + 2)
          have h0 : (0:ℝ) ≤ unit (p + 3) := unit_ge_zero (p + 3)
          linarith
        calc |logRem t (p + 2)| ≤ 2 * |t| ^ (p + 3) := hrb
          _ ≤ 2 * (1/2 : ℝ) ^ (p + 3) :=
              mul_le_mul_of_nonneg_left hp1 (by norm_num)
          _ = 2 * (unit (p + 3) : ℝ) := by rw [half_pow_eq_unit]
          _ = (unit (p + 2) : ℝ) := h2u
      have hsum : (unit (p + 2) : ℝ) + (unit (p + 2) : ℝ) ≤ (unit p : ℝ) := by
        have e1 : (unit (p + 2) : ℝ) + unit (p + 2) = unit (p + 1) :=
          two_mul_unit_succ (p + 1)
        have e3 := unit_le_of_succ p
        have h0 : (0:ℝ) ≤ unit (p + 2) := unit_ge_zero (p + 2)
        linarith
      exact le_trans (le_trans hstep (add_le_add hlog1 hrem2)) hsum
    exact contains_cert_of_abs _ _ (by
      simpa only [RealName.logName] using! hbound)
  · intro p
    show N.timeC * (p + 1) ^ N.timeD
        ≤ N.timeC * 5 ^ N.timeD * ((p + 2) + 1) ^ (N.timeD + 3)
    have hle : p + 1 ≤ 5 * (p + 3) := by omega
    have hmono : (p + 1) ^ N.timeD ≤ (5 * (p + 3)) ^ N.timeD :=
      pow_le_pow_left₀ (by omega) hle N.timeD
    have hsplit : (5 * (p + 3)) ^ N.timeD = 5 ^ N.timeD * (p + 3) ^ N.timeD := by
      rw [mul_pow]
    have hgrow : (p + 3) ^ N.timeD ≤ (p + 3) ^ (N.timeD + 3) :=
      pow_le_pow_right₀ (by omega : (1:ℕ) ≤ p + 3) (by omega)
    calc N.timeC * (p + 1) ^ N.timeD
        ≤ N.timeC * (5 * (p + 3)) ^ N.timeD := Nat.mul_le_mul_left _ hmono
      _ = N.timeC * (5 ^ N.timeD * (p + 3) ^ N.timeD) := by rw [hsplit]
      _ ≤ N.timeC * (5 ^ N.timeD * (p + 3) ^ (N.timeD + 3)) := by
          apply Nat.mul_le_mul_left
          exact Nat.mul_le_mul_left _ hgrow
      _ = N.timeC * 5 ^ N.timeD * (p + 3) ^ (N.timeD + 3) := by ring

/-- The finite diamond distance satisfies the triangle inequality. -/
theorem finiteDiamondDistance_tri {D E : ℕ} (T S R : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondDistance T R ≤ finiteDiamondDistance T S + finiteDiamondDistance S R := by
  have htri := (finiteDiamondNorm_algebra D E E (T - S) (S - R)
    (0 : Operator E →ₗ[ℂ] Operator E)).1
  have hsub : (T - S) + (S - R) = T - R := by
    ext x
    simp
  rw [hsub] at htri
  unfold finiteDiamondDistance
  have hmul : (1/2 : ℝ≥0∞) * (finiteDiamondNorm (T - S) + finiteDiamondNorm (S - R))
      = (1/2 : ℝ≥0∞) * finiteDiamondNorm (T - S)
        + (1/2 : ℝ≥0∞) * finiteDiamondNorm (S - R) := by
    ring
  calc (1/2 : ℝ≥0∞) * finiteDiamondNorm (T - R)
      ≤ (1/2 : ℝ≥0∞) * (finiteDiamondNorm (T - S) + finiteDiamondNorm (S - R)) :=
        mul_le_mul_right htri _
    _ = (1/2 : ℝ≥0∞) * finiteDiamondNorm (T - S)
          + (1/2 : ℝ≥0∞) * finiteDiamondNorm (S - R) := hmul

/-- The finite diamond distance between the endpoints of a chain is bounded by the sum of the
assumed successive distance bounds. -/
theorem finiteDiamondDistance_chain_le {D E : ℕ}
    (F : ℕ → Operator D →ₗ[ℂ] Operator E) (L : ℕ)
    (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < L → finiteDiamondDistance (F i) (F (i + 1)) ≤ ε i) :
    finiteDiamondDistance (F 0) (F L) ≤ ∑ i ∈ Finset.range L, ε i := by
  induction L with
  | zero =>
    show finiteDiamondDistance (F 0) (F 0) ≤ 0
    simp [finiteDiamondDistance, finiteDiamondNorm_zero]
  | succ L ih =>
    have h1 : finiteDiamondDistance (F 0) (F (L + 1)) ≤
        finiteDiamondDistance (F 0) (F L) + finiteDiamondDistance (F L) (F (L + 1)) :=
      finiteDiamondDistance_tri (F 0) (F L) (F (L + 1))
    have h2 := ih (fun i hi => hstep i (by omega))
    have h3 := hstep L (by omega)
    rw [Finset.sum_range_succ]
    exact le_trans h1 (add_le_add h2 h3)

/-- Negation preserves the finite diamond norm. -/
theorem finiteDiamondNorm_neg {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondNorm (-T) = finiteDiamondNorm T := by
  unfold finiteDiamondNorm
  refine iSup_congr (fun r => iSup_congr (fun X => ?_))
  have htl : tensorLeft (-T) X = -(tensorLeft T X) := by
    ext a b
    simp [tensorLeft]
  rw [htl, Matrix.traceNorm_neg]

/-- The finite diamond distance is symmetric. -/
theorem finiteDiamondDistance_sym {D E : ℕ} (T S : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondDistance T S = finiteDiamondDistance S T := by
  have hsub : S - T = -(T - S) := by
    ext x
    simp
  unfold finiteDiamondDistance
  rw [hsub, finiteDiamondNorm_neg]

/-- Postcomposition by a linear map increases finite diamond distance by at most the finite
diamond norm of that map. -/
theorem finiteDiamondDistance_comp_le {D E F : ℕ}
    (R : Operator E →ₗ[ℂ] Operator F) (T S : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondDistance (R.comp T) (R.comp S) ≤
      finiteDiamondNorm R * finiteDiamondDistance T S := by
  have hsub : R.comp T - R.comp S = R.comp (T - S) := by
    ext x
    simp
  have hcomp := (finiteDiamondNorm_algebra D E F (T - S)
    (0 : Operator D →ₗ[ℂ] Operator E) R).2.1
  unfold finiteDiamondDistance
  rw [hsub]
  have hmul : (1/2 : ℝ≥0∞) * (finiteDiamondNorm R * finiteDiamondNorm (T - S))
      = finiteDiamondNorm R * ((1/2 : ℝ≥0∞) * finiteDiamondNorm (T - S)) := by
    ring
  calc (1/2 : ℝ≥0∞) * finiteDiamondNorm (R.comp (T - S))
      ≤ (1/2 : ℝ≥0∞) * (finiteDiamondNorm R * finiteDiamondNorm (T - S)) :=
        mul_le_mul_right hcomp _
    _ = finiteDiamondNorm R * ((1/2 : ℝ≥0∞) * finiteDiamondNorm (T - S)) := hmul

/-- A chain from the ideal word to the actual word bounds their finite diamond distance by the
sum of its step bounds. -/
theorem approxWord_distance_le {D : ℕ} (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D))
    (G : ℕ → Operator D →ₗ[ℂ] Operator D)
    (hG0 : G 0 = (Qatlib.Concepts.RawChannelWord.CptpWordBound.idealWord p).map)
    (hGL : G p.length = (Qatlib.Concepts.RawChannelWord.CptpWordBound.actualWord p).map)
    (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ i, i < p.length → finiteDiamondDistance (G i) (G (i + 1)) ≤ ε i) :
    finiteDiamondDistance (Qatlib.Concepts.RawChannelWord.CptpWordBound.actualWord p).map
        (Qatlib.Concepts.RawChannelWord.CptpWordBound.idealWord p).map ≤
      ∑ i ∈ Finset.range p.length, ε i := by
  have h := finiteDiamondDistance_chain_le G p.length ε hstep
  rw [hG0, hGL] at h
  rwa [finiteDiamondDistance_sym] at h

/-- The channel word using actual steps in the first `i` positions and ideal steps thereafter. -/
noncomputable def mixedChain {D : ℕ} (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) :
    ℕ → Operator D →ₗ[ℂ] Operator D :=
  fun i => (Qatlib.Concepts.RawChannelWord.CptpWordBound.run
    ((p.take i).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.actual
      ++ (p.drop i).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.ideal)).map

/-- At index zero, `mixedChain` equals the ideal channel word. -/
theorem mixedChain_ideal {D : ℕ} (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) :
    mixedChain p 0 = (Qatlib.Concepts.RawChannelWord.CptpWordBound.idealWord p).map := by
  simp [mixedChain, Qatlib.Concepts.RawChannelWord.CptpWordBound.idealWord]

/-- At the word length, `mixedChain` equals the actual channel word. -/
theorem mixedChain_actual {D : ℕ} (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) :
    mixedChain p p.length = (Qatlib.Concepts.RawChannelWord.CptpWordBound.actualWord p).map := by
  simp [mixedChain, Qatlib.Concepts.RawChannelWord.CptpWordBound.actualWord]

/-- Channel amplification preserves complex scalar multiplication of its matrix input. -/
theorem diamondAmplification_smul {D E r : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (c : ℂ) (X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    ChannelAmplification T r (c • X) = c • ChannelAmplification T r X := by
  ext x y
  exact congrArg (· x.2 y.2) (T.map_smul c _)

/-- Channel amplification preserves addition of matrix inputs. -/
theorem diamondAmplification_add {D E r : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (X Y : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    ChannelAmplification T r (X + Y) =
      ChannelAmplification T r X + ChannelAmplification T r Y := by
  ext x y
  exact congrArg (· x.2 y.2) (T.map_add _ _)

/-- The matrix `Complex.I • (X - X.conjTranspose)` is Hermitian. -/
theorem diamondSkewPart_hermitian {n : Type*} [Fintype n] [DecidableEq n]
    (X : Matrix n n ℂ) :
    ((Complex.I) • (X - X.conjTranspose)).IsHermitian := by
  show ((Complex.I) • (X - X.conjTranspose)).conjTranspose
      = (Complex.I) • (X - X.conjTranspose)
  rw [Matrix.conjTranspose_smul, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_conjTranspose]
  have hI : star (Complex.I) = -(Complex.I : ℂ) := Complex.conj_I
  rw [hI, neg_smul]
  module

/-- The finite diamond norm of a quantum channel's linear map is at most two. -/
theorem finiteDiamondNorm_channel_le_two {D E : ℕ} (T : QuantumChannel D E) :
    finiteDiamondNorm T.map ≤ (2:ℝ≥0∞) := by
  rw [finiteDiamondNorm_left_reference D E T.map]
  refine iSup_le fun r => iSup_le fun X => ?_
  split_ifs with hX
  · set S : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ :=
      X - X.conjTranspose with hSdef
    set A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ :=
      (2:ℂ)⁻¹ • (X + X.conjTranspose) with hAdef
    set Hm : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ :=
      (Complex.I) • S with hHmdef
    have hA : A.IsHermitian :=
      (Matrix.isHermitian_add_transpose_self X).smul (by
        unfold IsSelfAdjoint; norm_num)
    have hH : Hm.IsHermitian := diamondSkewPart_hermitian X
    have hcoef : ((2:ℂ)⁻¹ * (Complex.I)⁻¹) • Hm = (2:ℂ)⁻¹ • S := by
      rw [hHmdef, smul_smul, mul_assoc,
        inv_mul_cancel₀ (show (Complex.I:ℂ) ≠ 0 by norm_num), mul_one]
    have hsplit : X = A + (2:ℂ)⁻¹ • S := by
      rw [hAdef, hSdef]
      have hrw : (2:ℂ)⁻¹ • (X + X.conjTranspose) + (2:ℂ)⁻¹ • (X - X.conjTranspose)
          = ((2:ℂ)⁻¹ + (2:ℂ)⁻¹) • X := by
        rw [add_smul]
        module
      rw [hrw, show (2:ℂ)⁻¹ + (2:ℂ)⁻¹ = 1 from by norm_num, one_smul]
    have hsplitH : X = A + ((2:ℂ)⁻¹ * (Complex.I)⁻¹) • Hm := by
      rw [hcoef, hsplit]
    have hamp : ChannelAmplification T.map r X = ChannelAmplification T.map r A
        + ((2:ℂ)⁻¹ * (Complex.I)⁻¹) • ChannelAmplification T.map r Hm := by
      conv_lhs => rw [hsplitH]
      rw [diamondAmplification_add, diamondAmplification_smul, diamondAmplification_smul]
    have hA1 : A.traceNorm ≤ 1 := by
      rw [hAdef, Matrix.traceNorm_smul,
        show ‖((2:ℂ)⁻¹)‖ = 1/2 from by norm_num]
      have h2 : (X + X.conjTranspose).traceNorm
          ≤ X.traceNorm + X.traceNorm := by
        have h := Matrix.traceNorm_add_le X X.conjTranspose
        rwa [Matrix.traceNorm_conjTranspose] at h
      calc (1/2 : ℝ) * (X + X.conjTranspose).traceNorm
          ≤ (1/2 : ℝ) * (X.traceNorm + X.traceNorm) :=
            mul_le_mul_of_nonneg_left h2 (by norm_num)
        _ = X.traceNorm := by ring
        _ ≤ 1 := hX
    have hH2 : Hm.traceNorm ≤ 2 := by
      rw [hHmdef, hSdef, Matrix.traceNorm_smul,
        show ‖(Complex.I:ℂ)‖ = 1 from by norm_num, one_mul]
      have h2 : (X - X.conjTranspose).traceNorm
          ≤ X.traceNorm + X.traceNorm := by
        have h := Matrix.traceNorm_add_le X (-X.conjTranspose)
        rw [← sub_eq_add_neg, Matrix.traceNorm_neg,
          Matrix.traceNorm_conjTranspose] at h
        exact h
      linarith
    have c1 := channel_reference_hermitian_trace_contraction T hA
    have c2 := channel_reference_hermitian_trace_contraction T hH
    have h2H : (1/2 : ℝ) * (ChannelAmplification T.map r Hm).traceNorm ≤ 1 := by
      have hstep : (1/2 : ℝ) * (ChannelAmplification T.map r Hm).traceNorm
          ≤ (1/2 : ℝ) * Hm.traceNorm :=
        mul_le_mul_of_nonneg_left c2 (by norm_num)
      have hval : (1/2 : ℝ) * Hm.traceNorm ≤ (1/2 : ℝ) * 2 :=
        mul_le_mul_of_nonneg_left hH2 (by norm_num)
      exact (hstep.trans hval).trans_eq (by norm_num : (1/2:ℝ) * 2 = 1)
    have hsplit2 : (ChannelAmplification T.map r A
        + ((2:ℂ)⁻¹ * (Complex.I)⁻¹) • ChannelAmplification T.map r Hm).traceNorm
        ≤ (ChannelAmplification T.map r A).traceNorm
          + (1/2 : ℝ) * (ChannelAmplification T.map r Hm).traceNorm := by
      have h := Matrix.traceNorm_add_le (ChannelAmplification T.map r A)
        (((2:ℂ)⁻¹ * (Complex.I)⁻¹) • ChannelAmplification T.map r Hm)
      rw [Matrix.traceNorm_smul,
        show ‖((2:ℂ)⁻¹ * (Complex.I)⁻¹)‖ = 1/2 from by norm_num] at h
      exact h
    have hchain : (ChannelAmplification T.map r X).traceNorm ≤ 2 := by
      calc (ChannelAmplification T.map r X).traceNorm
          = (ChannelAmplification T.map r A
              + ((2:ℂ)⁻¹ * (Complex.I)⁻¹) • ChannelAmplification T.map r Hm).traceNorm :=
            by rw [hamp]
        _ ≤ (ChannelAmplification T.map r A).traceNorm
            + (1/2 : ℝ) * (ChannelAmplification T.map r Hm).traceNorm := hsplit2
        _ ≤ A.traceNorm + 1 := add_le_add c1 h2H
        _ ≤ 1 + 1 := add_le_add hA1 le_rfl
        _ = 2 := by norm_num
    have h2e : (2:ℝ≥0∞) = ENNReal.ofReal 2 := by norm_num
    rw [h2e]
    exact ENNReal.ofReal_le_ofReal hchain
  · norm_num

/-- Precomposition by a quantum channel multiplies finite diamond distance by at most two. -/
theorem finiteDiamondDistance_pre_comp_le {D E F : ℕ}
    (T S : Operator E →ₗ[ℂ] Operator F) (C : QuantumChannel D E) :
    finiteDiamondDistance (T.comp C.map) (S.comp C.map) ≤
      (2:ℝ≥0∞) * finiteDiamondDistance T S := by
  have hsub : T.comp C.map - S.comp C.map = (T - S).comp C.map := by
    ext x; simp
  have hcomp := (finiteDiamondNorm_algebra D E F C.map
    (0 : Operator D →ₗ[ℂ] Operator E) (T - S)).2.1
  have hC := finiteDiamondNorm_channel_le_two C
  have hmono : finiteDiamondNorm (T - S) * finiteDiamondNorm C.map
      ≤ finiteDiamondNorm (T - S) * (2:ℝ≥0∞) :=
    mul_le_mul_right hC (finiteDiamondNorm (T - S))
  unfold finiteDiamondDistance
  rw [hsub]
  calc (1/2 : ℝ≥0∞) * finiteDiamondNorm ((T - S).comp C.map)
      = finiteDiamondNorm ((T - S).comp C.map) * (1/2 : ℝ≥0∞) := mul_comm _ _
    _ ≤ (finiteDiamondNorm (T - S) * finiteDiamondNorm C.map) * (1/2 : ℝ≥0∞) :=
        mul_le_mul_left hcomp _
    _ ≤ (finiteDiamondNorm (T - S) * (2:ℝ≥0∞)) * (1/2 : ℝ≥0∞) :=
        mul_le_mul_left hmono _
    _ = (2:ℝ≥0∞) * ((1/2 : ℝ≥0∞) * finiteDiamondNorm (T - S)) := by ring

/-- Postcomposition by a quantum channel multiplies finite diamond distance by at most two. -/
theorem finiteDiamondDistance_post_comp_le {D E F : ℕ}
    (C : QuantumChannel E F) (T S : Operator D →ₗ[ℂ] Operator E) :
    finiteDiamondDistance (C.map.comp T) (C.map.comp S) ≤
      (2:ℝ≥0∞) * finiteDiamondDistance T S := by
  have h1 := finiteDiamondDistance_comp_le C.map T S
  have hC := finiteDiamondNorm_channel_le_two C
  exact h1.trans (mul_le_mul_left hC (finiteDiamondDistance T S))

/-- One replacement in `mixedChain` has finite diamond distance at most four times the distance
between that step's actual and ideal channels. -/
theorem mixedChain_step_bare_le {D : ℕ}
    (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) {i : ℕ}
    (hi : i < p.length) :
    finiteDiamondDistance (mixedChain p i) (mixedChain p (i+1)) ≤
      (4:ℝ≥0∞) * finiteDiamondDistance (p[i].actual.map) (p[i].ideal.map) := by
  have hdrop : p.drop i = p[i] :: p.drop (i+1) :=
    (List.cons_getElem_drop_succ (h := hi)).symm
  have htake : (p.take (i+1)).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.actual
      = (p.take i).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.actual
        ++ [p[i].actual] := by
    rw [← List.take_concat_get' p i hi, List.map_append, List.map_singleton]
  have hI : mixedChain p i = (((Qatlib.Concepts.RawChannelWord.CptpWordBound.run
        ((p.drop (i+1)).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.ideal)).comp
        p[i].ideal).comp (Qatlib.Concepts.RawChannelWord.CptpWordBound.run
        ((p.take i).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.actual))).map := by
    unfold mixedChain
    rw [hdrop, List.map_cons, Qatlib.Concepts.RawChannelWord.CptpWordBound.run_append]
    rfl
  have hA : mixedChain p (i+1) = (((Qatlib.Concepts.RawChannelWord.CptpWordBound.run
        ((p.drop (i+1)).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.ideal)).comp
        p[i].actual).comp (Qatlib.Concepts.RawChannelWord.CptpWordBound.run
        ((p.take i).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.actual))).map := by
    unfold mixedChain
    rw [htake, List.append_assoc, List.singleton_append,
      Qatlib.Concepts.RawChannelWord.CptpWordBound.run_append]
    rfl
  set Xc := ((Qatlib.Concepts.RawChannelWord.CptpWordBound.run
        ((p.drop (i+1)).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.ideal)).comp
        p[i].actual).comp (Qatlib.Concepts.RawChannelWord.CptpWordBound.run
        ((p.take i).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.actual)) with hXcset
  have hdiff : mixedChain p i - mixedChain p (i+1)
      = ((Qatlib.Concepts.RawChannelWord.CptpWordBound.run
          ((p.drop (i+1)).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.ideal)).map.comp
          (p[i].ideal.map - p[i].actual.map)).comp
          ((Qatlib.Concepts.RawChannelWord.CptpWordBound.run
            ((p.take i).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.actual)).map) := by
    rw [hI, hA, hXcset]
    ext x
    simp only [QuantumChannel.comp, LinearMap.coe_comp, Function.comp_apply,
      LinearMap.sub_apply, LinearMap.map_sub]
  set X := (Qatlib.Concepts.RawChannelWord.CptpWordBound.run
      ((p.drop (i+1)).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.ideal)).map with hXm
  set g := (Qatlib.Concepts.RawChannelWord.CptpWordBound.run
      ((p.take i).map Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep.actual)).map with hgm
  set Φ := p[i].ideal.map - p[i].actual.map with hΦm
  have hXle : finiteDiamondNorm X ≤ 2 := finiteDiamondNorm_channel_le_two _
  have hgle : finiteDiamondNorm g ≤ 2 := finiteDiamondNorm_channel_le_two _
  have h1 : finiteDiamondNorm (X.comp Φ) ≤ finiteDiamondNorm X * finiteDiamondNorm Φ :=
    (finiteDiamondNorm_algebra D D D Φ (0 : Operator D →ₗ[ℂ] Operator D) X).2.1
  have h2 : finiteDiamondNorm ((X.comp Φ).comp g)
      ≤ finiteDiamondNorm (X.comp Φ) * finiteDiamondNorm g :=
    (finiteDiamondNorm_algebra D D D g (0 : Operator D →ₗ[ℂ] Operator D)
      (X.comp Φ)).2.1
  unfold finiteDiamondDistance
  rw [hdiff, hXm, hgm, hΦm]
  calc (1/2 : ℝ≥0∞) * finiteDiamondNorm ((X.comp Φ).comp g)
      ≤ (1/2 : ℝ≥0∞) * (finiteDiamondNorm (X.comp Φ) * finiteDiamondNorm g) :=
        mul_le_mul_right h2 (1/2 : ℝ≥0∞)
    _ ≤ (1/2 : ℝ≥0∞) * ((finiteDiamondNorm X * finiteDiamondNorm Φ)
          * finiteDiamondNorm g) :=
        mul_le_mul_right (mul_le_mul_left h1 (finiteDiamondNorm g)) (1/2 : ℝ≥0∞)
    _ ≤ (1/2 : ℝ≥0∞) * (((2:ℝ≥0∞) * finiteDiamondNorm Φ) * finiteDiamondNorm g) :=
        mul_le_mul_right (mul_le_mul_left
          (mul_le_mul_left hXle (finiteDiamondNorm Φ)) (finiteDiamondNorm g))
          (1/2 : ℝ≥0∞)
    _ ≤ (1/2 : ℝ≥0∞) * (((2:ℝ≥0∞) * finiteDiamondNorm Φ) * (2:ℝ≥0∞)) :=
        mul_le_mul_right (mul_le_mul_right hgle ((2:ℝ≥0∞) * finiteDiamondNorm Φ))
          (1/2 : ℝ≥0∞)
    _ = (4:ℝ≥0∞) * ((1/2 : ℝ≥0∞) * finiteDiamondNorm
          (p[i].actual.map - p[i].ideal.map)) := by
          have hn : Φ = -(p[i].actual.map - p[i].ideal.map) := by
            rw [hΦm]; exact (neg_sub _ _).symm
          rw [hn, finiteDiamondNorm_neg]
          ring

/-- The finite diamond distance between the actual and ideal words is at most four times the sum
of the assumed individual step bounds. -/
theorem approxWord_distance_bare_le {D : ℕ}
    (p : List (Qatlib.Concepts.RawChannelWord.CptpWordBound.ApproxStep D)) (ε : ℕ → ℝ≥0∞)
    (hstep : ∀ i (_ : i < p.length),
      finiteDiamondDistance (p[i].actual.map) (p[i].ideal.map) ≤ ε i) :
    finiteDiamondDistance
      (Qatlib.Concepts.RawChannelWord.CptpWordBound.actualWord p).map
      (Qatlib.Concepts.RawChannelWord.CptpWordBound.idealWord p).map ≤
      (4:ℝ≥0∞) * ∑ i ∈ Finset.range p.length, ε i := by
  have hsteps : ∀ i (_ : i < p.length),
      finiteDiamondDistance (mixedChain p i) (mixedChain p (i+1))
        ≤ (4:ℝ≥0∞) * ε i := by
    intro i hi
    refine (mixedChain_step_bare_le p hi).trans ?_
    exact mul_le_mul_right (hstep i hi) 4
  have h := approxWord_distance_le p (mixedChain p) (mixedChain_ideal p)
    (mixedChain_actual p) (fun i => (4:ℝ≥0∞) * ε i) hsteps
  rw [Finset.mul_sum]
  exact h

section Clause3BinaryAddition

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Runs natBits framed binaryValue Bits)

section SuccessorMachine

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM
open Turing

/-- A two-label tape program that increments a binary word and returns the head to its starting
position. -/
def incProgram (l : Fin 2) : TM1.Stmt Symbol (Fin 2) Unit :=
  if l = 0 then
    .branch (fun a _ => a.isSome)
      (.branch (fun a _ => a.getD false)
        (.write (fun _ _ => some false) (.move .right (.goto (fun _ _ => 0))))
        (.write (fun _ _ => some true) (.goto (fun _ _ => 1))))
      (.write (fun _ _ => some true) (.goto (fun _ _ => 1)))
  else
    .move .left (.branch (fun a _ => a.isSome)
      (.goto (fun _ _ => 1)) (.move .right .halt))

/-- The increment program's return phase halts on `left.reverse ++ right` in `left.length + 1`
source steps, with displacement `-left.length`. -/
theorem inc_return (left right : Bits) :
    SourceTrace incProgram ⟨some 1,(),Tape.mk₂ (left.map some) (right.map some)⟩
      ⟨none,(),Tape.mk₁ ((left.reverse++right).map some)⟩ (left.length+1)
      (-(left.length : ℤ)) := by
  induction left generalizing right with
  | nil =>
    apply SourceTrace.one
    · simp only [TM1.step,incProgram,show (1 : Fin 2)≠0 by decide,if_false,TM1.stepAux]
      rw [show ((Tape.mk₂ ([].map some) (right.map some)).move .left).head=none by rfl]
      simp only [Option.isSome_none,cond_false,Tape.move_left_right,
        List.reverse_nil,List.nil_append,List.map_nil,Tape.mk₁]
    · simp [incProgram,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtShift,
        Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtOffset,Tape.mk₂,Tape.move_left_mk',
        show (default : Symbol)=none from rfl]
  | cons b left ih =>
    have ht := (ih (b::right)).prepend (l := (1 : Fin 2))
      (tape := Tape.mk₂ ((b::left).map some) (right.map some))
      (by
        simp only [TM1.step,incProgram,show (1 : Fin 2)≠0 by decide,if_false,TM1.stepAux]
        have hm : (Tape.mk₂ ((b::left).map some) (right.map some)).move .left =
            Tape.mk₂ (left.map some) ((b::right).map some) := by
          simp [Tape.mk₂,Tape.move_left_mk',ListBlank.cons_mk]
        rw [hm]
        rfl)
      (s := -1) (by
        simp [incProgram,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtShift,
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtOffset,Tape.mk₂,Tape.move_left_mk'])
    convert! ht using 1 <;> simp [List.reverse_cons,List.append_assoc,Int.add_comm]

/-- The carry phase replaces an initial block of ones by zeros and the following zero by one in
`ones + 1` source steps, with displacement `ones`. -/
theorem inc_carry (left : Bits) (ones : ℕ) (rest : Bits) :
    SourceTrace incProgram ⟨some 0,(),Tape.mk₂ (left.map some)
        ((List.replicate ones true ++ false::rest).map some)⟩
      ⟨some 1,(),Tape.mk₂ ((List.replicate ones false ++ left).map some)
        ((true::rest).map some)⟩ (ones+1) (ones : ℤ) := by
  induction ones generalizing left with
  | zero =>
    apply SourceTrace.one
    · rfl
    · simp [incProgram,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtShift,Tape.mk₂]
  | succ ones ih =>
    have hinput : List.replicate (ones+1) true ++ false::rest
        = true :: (List.replicate ones true ++ false::rest) := by
      rw [List.replicate_succ, List.cons_append]
    have hmid : List.replicate ones false ++ [false]
        = List.replicate (ones+1) false := by
      rw [← List.replicate_one, ← List.replicate_add, Nat.add_comm]
    have hca : List.replicate ones false ++ (false :: left)
        = false :: (List.replicate ones false ++ left) := by
      rw [show false :: left = [false] ++ left from rfl, ← List.append_assoc,
        hmid, List.replicate_succ, List.cons_append]
    have hdc : (1 : ℤ) + (ones : ℤ) = ↑(ones+1) := by
      rw [Nat.cast_succ]; omega
    rw [hinput]
    have hw : (Tape.mk₂ (left.map some)
        ((true::List.replicate ones true ++ false::rest).map some)).write
        ((fun _ _ => some false) () (some true)) =
        Tape.mk₂ (left.map some)
          ((false::List.replicate ones true ++ false::rest).map some) := by
      simp [Tape.mk₂,Tape.write_mk',ListBlank.cons_mk]
    have hm : (Tape.mk₂ (left.map some)
        ((false::List.replicate ones true ++ false::rest).map some)).move .right =
        Tape.mk₂ ((false::left).map some)
          ((List.replicate ones true ++ false::rest).map some) := by
      simp [Tape.mk₂,Tape.move_right_mk',ListBlank.cons_mk]
    have ht := (ih (false::left)).prepend (l := (0 : Fin 2))
      (tape := Tape.mk₂ (left.map some)
        ((true::List.replicate ones true ++ false::rest).map some))
      (by
        change some (TM1.stepAux (incProgram 0) () (Tape.mk₂ (left.map some)
          ((true::List.replicate ones true ++ false::rest).map some))) = _
        change some (⟨some 0,(),
          (((Tape.mk₂ (left.map some)
            ((true::List.replicate ones true ++ false::rest).map some)).write
            ((fun _ _ => some false) () (some true))).move .right)⟩ :
            TM1.Cfg Symbol (Fin 2) Unit) = _
        rw [hw,hm])
      (s := 1) (by
        simp [incProgram,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtShift,Tape.mk₂,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtOffset])
    rw [hca, hdc] at ht
    exact ht

/-- On an all-ones suffix, the carry phase replaces the ones by zeros and writes a new final one
in `ones + 1` source steps. -/
theorem inc_carry_overflow (left : Bits) (ones : ℕ) :
    SourceTrace incProgram ⟨some 0,(),Tape.mk₂ (left.map some)
        ((List.replicate ones true).map some)⟩
      ⟨some 1,(),Tape.mk₂ ((List.replicate ones false ++ left).map some) [some true]⟩
      (ones+1) (ones : ℤ) := by
  induction ones generalizing left with
  | zero =>
    apply SourceTrace.one
    · rfl
    · show Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtShift (incProgram 0) () (Tape.mk₂ (left.map some)
          ((List.replicate 0 true).map some)) = 0
      simp only [List.replicate,Tape.mk₂,List.map_nil,ListBlank.mk]
      rfl
  | succ ones ih =>
    have hinput : (List.replicate (ones+1) true).map some
        = (true::List.replicate ones true).map some := by
      rw [List.replicate_succ]
    have hmid : List.replicate ones false ++ [false]
        = List.replicate (ones+1) false := by
      rw [← List.replicate_one, ← List.replicate_add, Nat.add_comm]
    have hca : List.replicate ones false ++ (false :: left)
        = false :: (List.replicate ones false ++ left) := by
      rw [show false :: left = [false] ++ left from rfl, ← List.append_assoc,
        hmid, List.replicate_succ, List.cons_append]
    have hdc : (1 : ℤ) + (ones : ℤ) = ↑(ones+1) := by
      rw [Nat.cast_succ]; omega
    rw [hinput]
    have hw : (Tape.mk₂ (left.map some) ((true::List.replicate ones true).map some)).write
        ((fun _ _ => some false) () (some true)) =
        Tape.mk₂ (left.map some) ((false::List.replicate ones true).map some) := by
      simp [Tape.mk₂,Tape.write_mk',ListBlank.cons_mk]
    have hm : (Tape.mk₂ (left.map some) ((false::List.replicate ones true).map some)).move .right =
        Tape.mk₂ ((false::left).map some) ((List.replicate ones true).map some) := by
      simp [Tape.mk₂,Tape.move_right_mk',ListBlank.cons_mk]
    have ht := (ih (false::left)).prepend (l := (0 : Fin 2))
      (tape := Tape.mk₂ (left.map some) ((true::List.replicate ones true).map some))
      (by
        change some (TM1.stepAux (incProgram 0) () (Tape.mk₂ (left.map some)
          ((true::List.replicate ones true).map some))) = _
        change some (⟨some 0,(),
          (((Tape.mk₂ (left.map some) ((true::List.replicate ones true).map some)).write
            ((fun _ _ => some false) () (some true))).move .right)⟩ :
            TM1.Cfg Symbol (Fin 2) Unit) = _
        rw [hw,hm])
      (s := 1) (by
        simp [incProgram,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtShift,Tape.mk₂,Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtOffset])
    rw [hca, hdc] at ht
    exact ht

/-- The increment program has TM1 tick bound at most five. -/
theorem inc_tickBound : tm1TickBound incProgram ≤ 5 := by
  apply Finset.sup_le
  intro l _
  by_cases h : l = 0 <;> simp [incProgram, h, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.stmtTicks]

/-- The compiled increment machine correctly increments an all-ones word of length `n`, with
time and space bounds `10 * n + 10`. -/
theorem inc_runs_ones (n : ℕ) :
    Runs (tm1Machine incProgram) (List.replicate n true)
      (Increment.word (List.replicate n true)) (10*n+10) (10*n+10) := by
  have hc := inc_carry_overflow [] n
  rw [List.append_nil] at hc
  have hr := inc_return (List.replicate n false) [true]
  have hall := hc.trans hr
  rw [List.length_replicate, show n+1+(n+1) = 2*n+2 from by omega,
    List.reverse_replicate, show (↑n : ℤ) + -↑n = 0 from by omega] at hall
  have hw : Increment.word (List.replicate n true)
      = List.replicate n false ++ [true] := Increment.overflow_word n
  rw [hw]
  apply tm1_finite_runs incProgram _ _ (2*n+2) (10*n+10)
    ⟨none,(),Tape.mk₁ ((List.replicate n false ++ [true]).map some)⟩
  · simpa only [List.length_nil, List.map_nil, Nat.add_zero, Tape.mk₂,
      List.nil_append, TM1.init] using! hall.reached
  · rfl
  · exact hall.shift_eq
  · simp only [List.length_replicate]; omega
  · have hb := Nat.mul_le_mul_left (2*n+2) inc_tickBound
    have hlen : (List.replicate n true).length = n := by simp
    calc (2*n+2)*tm1TickBound incProgram ≤ (2*n+2)*5 := hb
      _ = 10*n+10 := by ring
  · intro i
    simp [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀,ListBlank.nth_mk,
      List.getI_eq_getElem?_getD,show (default : Symbol)=none from rfl]
  · intro i
    rfl

/-- The compiled increment machine computes `Increment.word` on every input, with time and space
bounds `10 * input.length + 10`. -/
theorem inc_runs (input : Bits) :
    Runs (tm1Machine incProgram) input (Increment.word input)
      (10*input.length+10) (10*input.length+10) := by
  rcases Increment.true_split input with ⟨ones,rest,rfl⟩ | he
  · have hc := inc_carry [] ones rest
    rw [List.append_nil] at hc
    have hr := inc_return (List.replicate ones false) (true::rest)
    have hall := hc.trans hr
    rw [List.length_replicate, show ones+1+(ones+1) = 2*ones+2 from by omega,
      List.reverse_replicate, show (↑ones : ℤ) + -↑ones = 0 from by omega] at hall
    have hw : Increment.word (List.replicate ones true ++ false::rest)
        = List.replicate ones false ++ true::rest := Increment.finite_word ones rest
    rw [hw]
    apply tm1_finite_runs incProgram _ _ (2*ones+2)
      (10*(List.replicate ones true ++ false::rest).length+10)
      ⟨none,(),Tape.mk₁ ((List.replicate ones false ++ true::rest).map some)⟩
    · simpa only [List.length_nil, List.map_nil, Nat.add_zero, Tape.mk₂,
        List.nil_append, TM1.init] using! hall.reached
    · rfl
    · exact hall.shift_eq
    · simp only [List.length_append, List.length_replicate]; omega
    · have hb := Nat.mul_le_mul_left (2*ones+2) inc_tickBound
      have hlen : (List.replicate ones true ++ false::rest).length = ones+1+rest.length := by
        simp [List.length_append, List.length_replicate]; omega
      calc (2*ones+2)*tm1TickBound incProgram ≤ (2*ones+2)*5 := hb
        _ = 10*ones+10 := by ring
        _ ≤ 10*(ones+1+rest.length)+10 := by omega
        _ = 10*(List.replicate ones true ++ false::rest).length+10 := by
            rw [hlen]
    · intro i
      simp [Tape.mk₁,Tape.mk₂,Tape.mk'_right₀,ListBlank.nth_mk,
        List.getI_eq_getElem?_getD,show (default : Symbol)=none from rfl]
    · intro i
      rfl
  · have h := inc_runs_ones input.length
    rw [← he] at h
    exact h

/-- Binary increment satisfies `ComputesAt` with both time and space bounded by ten times the
input length plus ten. -/
theorem word_computesAt :
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ComputesAt Increment.word
      (fun x => 10*x.length+10) (fun x => 10*x.length+10) :=
  ⟨(tm1Support incProgram).card, tm1Machine incProgram, fun input => inc_runs input⟩

end SuccessorMachine

section AddLoop

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM (Symbol)
open Turing

namespace AddLoop

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM (Symbol)
open Turing

/-- The accumulator, counter, and temporary stack slots used by the addition loop. -/
inductive Slot | acc | cnt | tmp deriving DecidableEq, Fintype
instance : Inhabited Slot := ⟨.tmp⟩

/-- The control labels for decrementing the counter, branching, incrementing the accumulator,
and halting. -/
inductive Label
  | dec : Counter.Label → Label
  | branch
  | inc : Increment.Label → Label
  | done
  deriving DecidableEq

/-- Maps the decrement subroutine's two stack slots to the counter and temporary slots. -/
def cntCode (k : Fin 2) : Slot := if k = 0 then .cnt else .tmp
/-- Maps the increment subroutine's two stack slots to the accumulator and temporary slots. -/
def accCode (k : Fin 2) : Slot := if k = 0 then .acc else .tmp

/-- A stack program that repeatedly decrements a counter and increments an accumulator until the
counter is exhausted. -/
def addProgram : Label → TM2.Stmt (fun _ : Slot => Bool) Label Counter.Local
  | .dec l => StackCall.stmt cntCode Label.dec .branch id (fun _ s => s) (Counter.program l)
  | .branch => .branch (fun v => v.1)
      (.goto (fun _ => .inc .carry)) (.goto (fun _ => .done))
  | .inc l => StackCall.stmt accCode Label.inc (.dec .borrow)
      Prod.snd (fun v s => (v.1, s)) (Increment.program l)
  | .done => .halt

/-- Embeds a two-stack counter store into the addition-loop store while fixing the accumulator. -/
def cntFrame (acc : Bits) (S : Fin 2 → Bits) : Slot → Bits
  | .acc => acc | .cnt => S 0 | .tmp => S 1

/-- Embeds a two-stack accumulator store into the addition-loop store while fixing the counter. -/
def accFrame (cnt : Bits) (S : Fin 2 → Bits) : Slot → Bits
  | .acc => S 0 | .cnt => cnt | .tmp => S 1

/-- Evaluating `cntFrame` at a slot selected by `cntCode` recovers the corresponding subroutine
stack. -/
theorem cntFrame_at (acc : Bits) (S : Fin 2 → Bits) (k : Fin 2) :
    cntFrame acc S (cntCode k) = S k := by
  fin_cases k <;> simp [cntFrame, cntCode]

/-- Updating a counter subroutine stack commutes with embedding it through `cntFrame`. -/
theorem cntFrame_update (acc : Bits) (S : Fin 2 → Bits) (k : Fin 2) (bits : Bits) :
    cntFrame acc (Function.update S k bits)
      = Function.update (cntFrame acc S) (cntCode k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [cntFrame, cntCode]

/-- Evaluating `accFrame` at a slot selected by `accCode` recovers the corresponding subroutine
stack. -/
theorem accFrame_at (cnt : Bits) (S : Fin 2 → Bits) (k : Fin 2) :
    accFrame cnt S (accCode k) = S k := by
  fin_cases k <;> simp [accFrame, accCode]

/-- Updating an accumulator subroutine stack commutes with embedding it through `accFrame`. -/
theorem accFrame_update (cnt : Bits) (S : Fin 2 → Bits) (k : Fin 2) (bits : Bits) :
    accFrame cnt (Function.update S k bits)
      = Function.update (accFrame cnt S) (accCode k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [accFrame, accCode]

/-- The addition-loop store with the given accumulator and counter and an empty temporary stack. -/
def fullStore (acc cnt : Bits) : Slot → Bits := cntFrame acc (Stacks.stackPair cnt [])

/-- The full addition-loop store can equivalently be expressed using `accFrame`. -/
theorem fullStore_eq (acc cnt : Bits) : fullStore acc cnt = accFrame cnt (Stacks.stackPair acc []) := by
  funext j
  cases j <;> simp [fullStore, cntFrame, accFrame, Stacks.stackPair]

/-- A positive counter is decremented without changing its length, preserving the accumulator
and reaching the branch label with clock at most `10 * (1 + cnt.length) ^ 2`. -/
theorem dec_positive (acc cnt : Bits) (v : Counter.Local) (hp : 0 < binaryValue cnt) :
    ∃ ticks next, next.length = cnt.length ∧ binaryValue next + 1 = binaryValue cnt ∧
      Stacks.stackRun addProgram ticks ⟨some (.dec .borrow), v, fullStore acc cnt⟩ =
        some ⟨some .branch, (true, none), fullStore acc next⟩ ∧
      Stacks.stackRunClock addProgram ticks ⟨some (.dec .borrow), v, fullStore acc cnt⟩ ≤
        10*(1+cnt.length)^2 := by
  obtain ⟨ticks, next, _, hlen, hval, hr, hc⟩ := Counter.decrement_positive cnt v hp
  obtain ⟨hN, hNC⟩ := StackCall.execution cntCode Label.dec Label.branch id (fun _ s => s)
    (cntFrame acc) (cntFrame_at acc) (cntFrame_update acc) (fun _ _ => by rfl) (fun _ _ _ => rfl)
    Counter.program addProgram (fun _ => rfl) v ticks _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one, fullStore,
    cntFrame] at hN hNC
  exact ⟨ticks, next, hlen, hval, hN, hNC.trans_le hc⟩

/-- A zero-valued counter becomes an all-ones word of the same length and reaches the branch
label with a false flag in `2 * cnt.length + 2` steps and the stated quadratic clock bound. -/
theorem dec_zero (acc cnt : Bits) (v : Counter.Local) (hz : binaryValue cnt = 0) :
    Stacks.stackRun addProgram (2*cnt.length+2)
      ⟨some (.dec .borrow), v, fullStore acc cnt⟩ =
        some ⟨some .branch, (false, none),
          fullStore acc (List.replicate cnt.length true)⟩ ∧
      Stacks.stackRunClock addProgram (2*cnt.length+2)
      ⟨some (.dec .borrow), v, fullStore acc cnt⟩ ≤ 10*(1+cnt.length)^2 := by
  obtain ⟨hr, hc⟩ := Counter.decrement_zero cnt v hz
  obtain ⟨hN, hNC⟩ := StackCall.execution cntCode Label.dec Label.branch id (fun _ s => s)
    (cntFrame acc) (cntFrame_at acc) (cntFrame_update acc) (fun _ _ => by rfl) (fun _ _ _ => rfl)
    Counter.program addProgram (fun _ => rfl) v (2*cnt.length+2) _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one, fullStore,
    cntFrame] at hN hNC
  exact ⟨hN, hNC.trans_le hc⟩

/-- The addition-loop branch selects accumulator increment when the flag is true and the done
label otherwise. -/
theorem branch_step (v : Counter.Local) (acc cnt : Bits) :
    TM2.step addProgram ⟨some .branch, v, fullStore acc cnt⟩ =
      some ⟨some (if v.1 then .inc .carry else .done), v, fullStore acc cnt⟩ := by
  cases h : v.1 <;> simp [h, TM2.step, addProgram, TM2.stepAux]

/-- One addition-loop branch step has clock at most two. -/
theorem branch_clock (v : Counter.Local) (acc cnt : Bits) :
    Stacks.stackRunClock addProgram 1 ⟨some .branch, v, fullStore acc cnt⟩ ≤ 2 := by
  rcases hv : v.1 with _ | _ <;>
    simp [Stacks.stackRunClock, Stacks.stackRun, addProgram, TM2.step, Stacks.stackClock, hv] <;>
    omega

/-- The addition-loop done label halts in one step without changing the local state or stacks. -/
theorem halt_run (v : Counter.Local) (acc cnt : Bits) :
    Stacks.stackRun addProgram 1 ⟨some .done, v, fullStore acc cnt⟩ =
      some ⟨none, v, fullStore acc cnt⟩ := by
  simp [Stacks.stackRun, addProgram, TM2.step]

/-- One step at the addition-loop done label has clock at most one. -/
theorem halt_clock (v : Counter.Local) (acc cnt : Bits) :
    Stacks.stackRunClock addProgram 1 ⟨some .done, v, fullStore acc cnt⟩ ≤ 1 := by
  simp [Stacks.stackRunClock, Stacks.stackRun, addProgram, TM2.step, Stacks.stackClock]

/-- The accumulator increment subroutine returns to counter decrement with the counter and
Boolean flag preserved, using clock at most `50 * (1 + acc.length) ^ 2`. -/
theorem inc_call (acc cnt : Bits) (b : Bool) :
    ∃ ticks, Stacks.stackRun addProgram ticks ⟨some (.inc .carry), (b, none), fullStore acc cnt⟩ =
        some ⟨some (.dec .borrow), (b, none), fullStore (Increment.word acc) cnt⟩ ∧
      Stacks.stackRunClock addProgram ticks ⟨some (.inc .carry), (b, none), fullStore acc cnt⟩ ≤
        50*(1+acc.length)^2 := by
  obtain ⟨ticks, _, hr, hc⟩ := Increment.complete acc [] none
  rw [show List.length ([] : Bits) = 0 from rfl, Nat.add_zero] at hc
  obtain ⟨hN, hNC⟩ := StackCall.execution accCode Label.inc (.dec .borrow)
    Prod.snd (fun v s => (v.1, s))
    (accFrame cnt) (accFrame_at cnt) (accFrame_update cnt) (fun _ _ => by rfl) (fun _ _ _ => rfl)
    Increment.program addProgram (fun _ => rfl) (b, none) ticks _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, Stacks.stackPair_zero, Stacks.stackPair_one, List.reverse_nil,
    List.nil_append, fullStore_eq, accFrame] at hN hNC
  exact ⟨ticks, hN, hNC.trans_le hc⟩

/-- Starting with counter value `n`, the addition loop halts with the accumulator incremented
`n` times and an all-ones counter. Both accumulated and maximum clocks satisfy the displayed
bound. -/
theorem addLoop_complete (n : ℕ) (acc cnt : Bits) (hnum : binaryValue cnt = n) :
    ∀ v : Counter.Local, ∃ ticks,
      Stacks.stackRun addProgram ticks
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ =
        some ⟨none, (false, none), fullStore (Increment.word^[n] acc)
          (List.replicate cnt.length true)⟩ ∧
      Stacks.stackRunClock addProgram ticks
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ ≤
        (2*n+4)*(10*(1+cnt.length)^2+50*(1+acc.length+n+1)^2+10) ∧
      Stacks.stackRunMaxClock addProgram ticks
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ ≤
        (2*n+4)*(10*(1+cnt.length)^2+50*(1+acc.length+n+1)^2+10) := by
  induction n generalizing acc cnt with
  | zero =>
    intro v
    obtain ⟨hD, hDC⟩ := dec_zero acc cnt v (by omega)
    have hb := branch_step (false, none) acc (List.replicate cnt.length true)
    have hrun : Stacks.stackRun addProgram ((2*cnt.length+2)+1)
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ =
        some ⟨some .done, (false, none), fullStore acc (List.replicate cnt.length true)⟩ := by
      rw [Stacks.run_add, hD, Option.bind_some]
      simpa only [fullStore, cntFrame, Stacks.stackPair] using! hb
    have hhalt := halt_run (false, none) acc (List.replicate cnt.length true)
    have hhalt' : Stacks.stackRun addProgram (((2*cnt.length+2)+1)+1)
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ =
        some ⟨none, (false, none), fullStore acc
          (List.replicate cnt.length true)⟩ := by
      rw [Stacks.run_add, hrun, Option.bind_some]
      exact hhalt
    have hclock : Stacks.stackRunClock addProgram (((2*cnt.length+2)+1)+1)
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ ≤
        (2*0+4)*(10*(1+cnt.length)^2+50*(1+acc.length+0+1)^2+10) := by
      have hs1 := Stacks.clock_add addProgram ((2*cnt.length+2)+1) 1
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩
        ⟨some .done, (false, none), fullStore acc (List.replicate cnt.length true)⟩ hrun
      have hs2 := Stacks.clock_add addProgram (2*cnt.length+2) 1
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩
        ⟨some .branch, (false, none), fullStore acc (List.replicate cnt.length true)⟩ hD
      have hc1 := branch_clock (false, none) acc (List.replicate cnt.length true)
      have hc2 := halt_clock (false, none) acc (List.replicate cnt.length true)
      omega
    refine ⟨((2*cnt.length+2)+1)+1, hhalt', hclock, ?_⟩
    exact Stacks.maxClock_le_clock _ _ _ |>.trans hclock
  | succ n ih =>
    intro v
    have hp : 0 < binaryValue cnt := by omega
    obtain ⟨decTicks, next, hlen, hval, hD, hDC⟩ := dec_positive acc cnt v hp
    have hnext : binaryValue next = n := by omega
    have hb := branch_step (true, none) acc next
    obtain ⟨incTicks, hI, hIC⟩ := inc_call acc next true
    obtain ⟨iterTicks, hIrun, hIclock, _⟩ := ih (Increment.word acc) next hnext (true, none)
    have hstep1 : Stacks.stackRun addProgram (decTicks+1)
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ =
        some ⟨some (.inc .carry), (true, none), fullStore acc next⟩ := by
      rw [Stacks.run_add, hD, Option.bind_some]
      simpa only [fullStore, cntFrame, Stacks.stackPair] using! hb
    have hstep2 : Stacks.stackRun addProgram ((decTicks+1)+incTicks)
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ =
        some ⟨some (.dec .borrow), (true, none), fullStore (Increment.word acc) next⟩ := by
      rw [Stacks.run_add, hstep1, Option.bind_some, hI]
    have hiter : Increment.word^[n+1] acc = Increment.word^[n] (Increment.word acc) := by
      rw [Function.iterate_succ_apply]
    have hfull : Stacks.stackRun addProgram (((decTicks+1)+incTicks)+iterTicks)
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ =
        some ⟨none, (false, none), fullStore (Increment.word^[n+1] acc)
          (List.replicate cnt.length true)⟩ := by
      rw [hlen] at hIrun
      rw [Stacks.run_add, hstep2, Option.bind_some, hiter]
      exact hIrun
    have hclock : Stacks.stackRunClock addProgram (((decTicks+1)+incTicks)+iterTicks)
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩ ≤
        (2*(n+1)+4)*(10*(1+cnt.length)^2+50*(1+acc.length+(n+1)+1)^2+10) := by
      have hs3 := Stacks.clock_add addProgram ((decTicks+1)+incTicks) iterTicks
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩
        ⟨some (.dec .borrow), (true, none), fullStore (Increment.word acc) next⟩ hstep2
      have hs2 := Stacks.clock_add addProgram (decTicks+1) incTicks
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩
        ⟨some (.inc .carry), (true, none), fullStore acc next⟩ hstep1
      have hs1 := Stacks.clock_add addProgram decTicks 1
        ⟨some (.dec .borrow), v, fullStore acc cnt⟩
        ⟨some .branch, (true, none), fullStore acc next⟩ hD
      have hbc := branch_clock (true, none) acc next
      have hlen' : (Increment.word acc).length ≤ acc.length+1 :=
        WordValidator.word_increment_length acc
      have hmono : (1+(Increment.word acc).length+n+1)^2 ≤ (1+acc.length+n+1+1)^2 := by
        have hle : 1+(Increment.word acc).length+n+1 ≤ 1+acc.length+n+1+1 := by omega
        have h0 : 0 ≤ 1+(Increment.word acc).length+n+1 := by omega
        have h0' : 0 ≤ 1+acc.length+n+1+1 := by omega
        nlinarith only [hle, h0, h0']
      have hBle : (1+acc.length)^2 ≤ (1+acc.length+n+1+1)^2 := by
        have hle : 1+acc.length ≤ 1+acc.length+n+1+1 := by omega
        have h0 : 0 ≤ 1+acc.length := by omega
        have h0' : 0 ≤ 1+acc.length+n+1+1 := by omega
        nlinarith only [hle, h0, h0']
      rw [hlen] at hIclock
      nlinarith only [hs1, hs2, hs3, hDC, hIC, hIclock, hbc, hmono, hBle]
    refine ⟨((decTicks+1)+incTicks)+iterTicks, hfull, hclock, ?_⟩
    exact Stacks.maxClock_le_clock _ _ _ |>.trans hclock

end AddLoop

end AddLoop

section ParseFramed

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM (Symbol)
open Turing

namespace ParseFramed

/-- The seven stack slots for framed-word parsing, including raw input, length fields, temporary
storage, and output. -/
inductive PSlot | raw | parse | num | num2 | spare | acc1 | acc deriving DecidableEq, Fintype
instance : Inhabited PSlot := ⟨.spare⟩
/-- The parser's local state, consisting of a counter state and an optional saved bit. -/
abbrev PLocal := Counter.Local × Option Bool
/-- The control labels for transferring input, parsing a natural length, extracting a counted
payload, reversing output, and halting. -/
inductive PLabel
  | read : Fin 1 → PLabel
  | nat : Fin 3 → PLabel
  | nflip : Fin 1 → PLabel
  | tk : Counter.Label → PLabel
  | pbranch
  | tkBody
  | clear
  | flip : Fin 1 → PLabel
  | pdone
  deriving DecidableEq
/-- Maps input-transfer stack slots to the parser's raw and parsing slots. -/
def readCode (k : Fin 2) : PSlot := if k = 0 then .raw else .parse
/-- Maps natural-number parser stack slots to the parsing, spare, and length slots. -/
def natCode (k : Fin 3) : PSlot :=
  if k = 0 then .parse else if k = 1 then .spare else .num
/-- Maps length-reversal stack slots to the parser's `num` and `num2` slots. -/
def nflipCode (k : Fin 2) : PSlot := if k = 0 then .num else .num2
/-- Maps counter subroutine slots to the parser's `num2` and spare slots. -/
def tkCode (k : Fin 2) : PSlot := if k = 0 then .num2 else .spare
/-- Maps payload-reversal stack slots to the intermediate and final accumulator slots. -/
def flipCode (k : Fin 2) : PSlot := if k = 0 then .acc1 else .acc

/-- A stack program that parses a natural-number length and extracts that many payload bits,
padding missing bits with false. -/
def parseProgram : PLabel → TM2.Stmt (fun _ : PSlot => Bool) PLabel PLocal
  | .read l => StackCall.stmt readCode PLabel.read (.nat 0)
      Prod.snd (fun v b => (v.1, b)) (Stacks.transferProgram l)
  | .nat l => StackCall.stmt natCode PLabel.nat (.nflip 0)
      Prod.snd (fun v b => (v.1, b)) (Parsing.natProgram l)
  | .nflip l => StackCall.stmt nflipCode PLabel.nflip (.tk .borrow)
      Prod.snd (fun v b => (v.1, b)) (Stacks.transferProgram l)
  | .tk l => StackCall.stmt tkCode PLabel.tk .pbranch
      Prod.fst (fun v s => (s, v.2)) (Counter.program l)
  | .pbranch => .branch (fun v => v.1.1)
      (.goto (fun _ => .tkBody)) (.goto (fun _ => .clear))
  | .clear => .load (fun s => (s.1, none)) (.goto (fun _ => .flip 0))
  | .tkBody => .pop PSlot.parse (fun s b => (s.1, b))
      (.push PSlot.acc1 (fun s => s.2.getD false) (.goto (fun _ => .tk .borrow)))
  | .flip l => StackCall.stmt flipCode PLabel.flip .pdone
      Prod.snd (fun v b => (v.1, b)) (Stacks.transferProgram l)
  | .pdone => .halt
/-- The parser store assigning the supplied bit words to its seven named stack slots. -/
def pstore (raw parse num num2 spare acc1 acc : Bits) : PSlot → Bits
  | .raw => raw | .parse => parse | .num => num | .num2 => num2 | .spare => spare
  | .acc1 => acc1 | .acc => acc
/-- Embeds the input-transfer store into the parser store with the other stacks empty. -/
def readFrame (S : Fin 2 → Bits) : PSlot → Bits :=
  pstore (S 0) (S 1) [] [] [] [] []
/-- Evaluating `readFrame` at a slot selected by `readCode` recovers the corresponding transfer
stack. -/
def readFrame_at (S : Fin 2 → Bits) (k : Fin 2) : readFrame S (readCode k) = S k := by
  fin_cases k <;> simp [readFrame, readCode, pstore]
/-- Updating an input-transfer stack commutes with embedding it through `readFrame`. -/
def readFrame_update (S : Fin 2 → Bits) (k : Fin 2) (bits : Bits) :
    readFrame (Function.update S k bits) = Function.update (readFrame S) (readCode k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [readFrame, readCode, pstore, Function.update_apply]
/-- Embeds the natural-number parser's three stacks into the framed-parser store with the
specified background stacks. -/
def natFrame (raw spare acc1 acc : Bits) (S : Fin 3 → Bits) : PSlot → Bits :=
  pstore raw (S 0) (S 2) [] (S 1) acc1 acc
/-- Evaluating `natFrame` at a slot selected by `natCode` recovers the corresponding
natural-number parser stack. -/
def natFrame_at (raw spare acc1 acc : Bits) (S : Fin 3 → Bits) (k : Fin 3) :
    natFrame raw spare acc1 acc S (natCode k) = S k := by
  fin_cases k <;> simp [natFrame, natCode, pstore]
/-- Updating a natural-number parser stack commutes with embedding it through `natFrame`. -/
def natFrame_update (raw spare acc1 acc : Bits) (S : Fin 3 → Bits) (k : Fin 3) (bits : Bits) :
    natFrame raw spare acc1 acc (Function.update S k bits)
      = Function.update (natFrame raw spare acc1 acc S) (natCode k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [natFrame, natCode, pstore, Function.update_apply]
/-- Embeds the counter subroutine's two stacks into the framed-parser store with the specified
background stacks. -/
def tkFrame (raw parse num spare acc1 acc : Bits) (S : Fin 2 → Bits) : PSlot → Bits :=
  pstore raw parse num (S 0) (S 1) acc1 acc
/-- Evaluating `tkFrame` at a slot selected by `tkCode` recovers the corresponding counter
stack. -/
def tkFrame_at (raw parse num spare acc1 acc : Bits) (S : Fin 2 → Bits) (k : Fin 2) :
    tkFrame raw parse num spare acc1 acc S (tkCode k) = S k := by
  fin_cases k <;> simp [tkFrame, tkCode, pstore]
/-- Updating a counter stack commutes with embedding it through `tkFrame`. -/
def tkFrame_update (raw parse num spare acc1 acc : Bits) (S : Fin 2 → Bits) (k : Fin 2) (bits : Bits) :
    tkFrame raw parse num spare acc1 acc (Function.update S k bits)
      = Function.update (tkFrame raw parse num spare acc1 acc S) (tkCode k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [tkFrame, tkCode, pstore, Function.update_apply]
/-- Embeds the length-reversal store into the parser store with the specified background stacks. -/
def nflipFrame (raw parse spare acc1 acc : Bits) (S : Fin 2 → Bits) : PSlot → Bits :=
  pstore raw parse (S 0) (S 1) spare acc1 acc
/-- Evaluating `nflipFrame` at a slot selected by `nflipCode` recovers the corresponding
length-reversal stack. -/
def nflipFrame_at (raw parse spare acc1 acc : Bits) (S : Fin 2 → Bits) (k : Fin 2) :
    nflipFrame raw parse spare acc1 acc S (nflipCode k) = S k := by
  fin_cases k <;> simp [nflipFrame, nflipCode, pstore]
/-- Updating a length-reversal stack commutes with embedding it through `nflipFrame`. -/
def nflipFrame_update (raw parse spare acc1 acc : Bits) (S : Fin 2 → Bits) (k : Fin 2) (bits : Bits) :
    nflipFrame raw parse spare acc1 acc (Function.update S k bits)
      = Function.update (nflipFrame raw parse spare acc1 acc S) (nflipCode k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [nflipFrame, nflipCode, pstore, Function.update_apply]
/-- Embeds the payload-reversal store into the parser store with the specified background
stacks. -/
def flipFrame (raw parse num num2 spare : Bits) (S : Fin 2 → Bits) : PSlot → Bits :=
  pstore raw parse num num2 spare (S 0) (S 1)
/-- Evaluating `flipFrame` at a slot selected by `flipCode` recovers the corresponding
payload-reversal stack. -/
def flipFrame_at (raw parse num num2 spare : Bits) (S : Fin 2 → Bits) (k : Fin 2) :
    flipFrame raw parse num num2 spare S (flipCode k) = S k := by
  fin_cases k <;> simp [flipFrame, flipCode, pstore]
/-- Updating a payload-reversal stack commutes with embedding it through `flipFrame`. -/
def flipFrame_update (raw parse num num2 spare : Bits) (S : Fin 2 → Bits) (k : Fin 2) (bits : Bits) :
    flipFrame raw parse num num2 spare (Function.update S k bits)
      = Function.update (flipFrame raw parse num num2 spare S) (flipCode k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [flipFrame, flipCode, pstore, Function.update_apply]
set_option maxHeartbeats 1000000 in

/-- The input-transfer call moves the raw word in reverse order to the parsing stack and reaches
natural-number parsing with clock at most `9 * (1 + raw.length) ^ 2`. -/
theorem read_call (raw : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.read 0), ((false,none),none), pstore raw [] [] [] [] [] []⟩ =
      some ⟨some (.nat 0), ((false,none),none), pstore [] raw.reverse [] [] [] [] []⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.read 0), ((false,none),none), pstore raw [] [] [] [] [] []⟩ ≤
        9*(1+raw.length)^2 := by
  have hr := Stacks.transfer_run raw [] none
  obtain ⟨hN, hNC⟩ := StackCall.execution readCode PLabel.read (.nat 0)
    Prod.snd (fun v b => (v.1, b))
    (readFrame) (readFrame_at) (readFrame_update) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Stacks.transferProgram parseProgram (fun _ => rfl) ((false,none),none)
    (raw.length+1) _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one, readFrame,
    pstore, List.reverse_nil, List.nil_append, List.append_nil] at hN hNC
  refine ⟨raw.length+1, hN, ?_⟩
  have hb := Stacks.transfer_clock raw [] none
  simp only [List.length_nil, Nat.add_zero] at hb
  have h0 : (0:ℕ) ≤ raw.length := Nat.zero_le _
  nlinarith only [hNC, hb, h0]
set_option maxHeartbeats 1000000 in

/-- Parsing the length prefix of `natBits w.length ++ (w ++ rest)` leaves the payload and suffix
intact and stores the reversed binary length, with the stated quadratic clock bound. -/
theorem nat_call (w rest : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.nat 0), ((false,none),none), pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)) [] [] [] [] []⟩ =
      some ⟨some (.nflip 0), ((false,none),none),
        pstore [] (w ++ rest) w.length.bits.reverse [] [] [] []⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.nat 0), ((false,none),none),
          pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)) [] [] [] [] []⟩ ≤
        40*(1+(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)).length)^2 := by
  have hr := Parsing.nat_run w.length (w ++ rest) [] none
  have hc := Parsing.nat_clock_bound w.length (w ++ rest) [] none
  obtain ⟨hN, hNC⟩ := StackCall.execution natCode PLabel.nat (.nflip 0)
    Prod.snd (fun v b => (v.1, b))
    (natFrame [] [] [] []) (natFrame_at [] [] [] []) (natFrame_update [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    Parsing.natProgram parseProgram (fun _ => rfl) ((false,none),none)
    (2*w.length.bits.length+3) _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one,
    Parsing.triple_two, Parsing.triple_one, Parsing.triple_zero, natFrame, pstore,
    List.append_nil, List.reverse_nil, List.nil_append, List.append_nil] at hN hNC
  exact ⟨2*w.length.bits.length+3, hN, hNC.trans_le hc⟩
set_option maxHeartbeats 1000000 in

/-- The length-reversal call moves the reversed binary payload length into `num2` in forward
order, with clock at most `9 * (1 + w.length.bits.length) ^ 2`. -/
theorem nflip_call (w rest : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.nflip 0), ((false,none),none),
          pstore [] (w ++ rest) w.length.bits.reverse [] [] [] []⟩ =
      some ⟨some (.tk .borrow), ((false,none),none),
        pstore [] (w ++ rest) [] w.length.bits [] [] []⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.nflip 0), ((false,none),none),
          pstore [] (w ++ rest) w.length.bits.reverse [] [] [] []⟩ ≤
        9*(1+w.length.bits.length)^2 := by
  have hr := Stacks.transfer_run w.length.bits.reverse [] none
  rw [List.reverse_reverse] at hr
  obtain ⟨hN, hNC⟩ := StackCall.execution nflipCode PLabel.nflip (.tk .borrow)
    Prod.snd (fun v b => (v.1, b))
    (nflipFrame [] (w ++ rest) [] [] []) (nflipFrame_at [] (w ++ rest) [] [] [])
    (nflipFrame_update [] (w ++ rest) [] [] []) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Stacks.transferProgram parseProgram (fun _ => rfl) ((false,none),none)
    (w.length.bits.reverse.length+1) _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one, nflipFrame,
    pstore, List.reverse_nil, List.nil_append, List.append_nil,
    List.length_reverse] at hN hNC
  refine ⟨w.length.bits.length+1, hN, ?_⟩
  have hb := Stacks.transfer_clock w.length.bits.reverse [] none
  rw [List.length_reverse] at hb
  simp only [List.length_nil, Nat.add_zero] at hb
  have h0 : (0:ℕ) ≤ w.length.bits.length := Nat.zero_le _
  nlinarith only [hNC, hb, h0]
set_option maxHeartbeats 1000000 in

/-- A positive parser counter is decremented without changing its length, reaching the parser
branch with a true flag and the stated quadratic clock bound. -/
theorem tk_dec_positive (drop num numw acc1 raw acc : Bits) (v : PLocal)
    (hp : 0 < binaryValue numw) :
    ∃ ticks next, next.length = numw.length ∧ binaryValue next + 1 = binaryValue numw ∧
      Stacks.stackRun parseProgram ticks
        ⟨some (.tk .borrow), v, pstore raw drop num numw [] acc1 acc⟩ =
        some ⟨some .pbranch, ((true,none), v.2), pstore raw drop num next [] acc1 acc⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.tk .borrow), v, pstore raw drop num numw [] acc1 acc⟩ ≤
        10*(1+numw.length)^2 := by
  obtain ⟨ticks, next, _, hlen, hval, hr, hc⟩ := Counter.decrement_positive numw v.1 hp
  obtain ⟨hN, hNC⟩ := StackCall.execution tkCode PLabel.tk .pbranch
    Prod.fst (fun v s => (s, v.2))
    (tkFrame raw drop num [] acc1 acc) (tkFrame_at raw drop num [] acc1 acc)
    (tkFrame_update raw drop num [] acc1 acc) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Counter.program parseProgram (fun _ => rfl) v ticks _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one, tkFrame,
    pstore, List.append_nil, List.reverse_nil, List.nil_append] at hN hNC
  exact ⟨ticks, next, hlen, hval, hN, hNC.trans_le hc⟩
set_option maxHeartbeats 1000000 in

/-- A zero-valued parser counter becomes an all-ones word and reaches the parser branch with a
false flag in `2 * numw.length + 2` steps, with the stated clock bound. -/
theorem tk_dec_zero (drop num numw acc1 raw acc : Bits) (v : PLocal)
    (hz : binaryValue numw = 0) :
    Stacks.stackRun parseProgram (2*numw.length+2)
      ⟨some (.tk .borrow), v, pstore raw drop num numw [] acc1 acc⟩ =
        some ⟨some .pbranch, ((false,none), v.2),
          pstore raw drop num (List.replicate numw.length true) [] acc1 acc⟩ ∧
      Stacks.stackRunClock parseProgram (2*numw.length+2)
      ⟨some (.tk .borrow), v, pstore raw drop num numw [] acc1 acc⟩ ≤
        10*(1+numw.length)^2 := by
  obtain ⟨hr, hc⟩ := Counter.decrement_zero numw v.1 hz
  obtain ⟨hN, hNC⟩ := StackCall.execution tkCode PLabel.tk .pbranch
    Prod.fst (fun v s => (s, v.2))
    (tkFrame raw drop num [] acc1 acc) (tkFrame_at raw drop num [] acc1 acc)
    (tkFrame_update raw drop num [] acc1 acc) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Counter.program parseProgram (fun _ => rfl) v (2*numw.length+2) _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one, tkFrame,
    pstore, List.append_nil, List.reverse_nil, List.nil_append] at hN hNC
  exact ⟨hN, hNC.trans_le hc⟩

/-- The parser branch selects payload extraction when the counter flag is true and local-state
clearing otherwise. -/
theorem pbranch_step (v : PLocal) (st : PSlot → Bits) :
    TM2.step parseProgram ⟨some .pbranch, v, st⟩ =
      some ⟨some (if v.1.1 then .tkBody else .clear), v, st⟩ := by
  cases h : v.1.1 <;> simp [h, TM2.step, parseProgram, TM2.stepAux]

/-- One parser branch step has clock at most two. -/
theorem pbranch_clock (v : PLocal) (st : PSlot → Bits) :
    Stacks.stackRunClock parseProgram 1 ⟨some .pbranch, v, st⟩ ≤ 2 := by
  rcases hv : v.1.1 with _ | _ <;>
    simp [Stacks.stackRunClock, Stacks.stackRun, parseProgram, TM2.step,
      Stacks.stackClock, hv] <;> omega

/-- The parser's clear label resets the saved bit to `none` and enters payload reversal without
changing the stacks. -/
theorem clear_step (v : PLocal) (st : PSlot → Bits) :
    TM2.step parseProgram ⟨some .clear, v, st⟩ =
      some ⟨some (.flip 0), (v.1, none), st⟩ := by
  simp [TM2.step, parseProgram, TM2.stepAux]

/-- One parser clear step has clock at most two. -/
theorem clear_clock (v : PLocal) (st : PSlot → Bits) :
    Stacks.stackRunClock parseProgram 1 ⟨some .clear, v, st⟩ ≤ 2 := by
  simp [Stacks.stackRunClock, Stacks.stackRun, parseProgram, TM2.step, Stacks.stackClock]

/-- Updating the parsing slot of `pstore` replaces exactly its parsing word. -/
theorem pstore_upd_parse (raw parse num num2 spare acc1 acc drop : Bits) :
    Function.update (pstore raw parse num num2 spare acc1 acc) PSlot.parse drop
      = pstore raw drop num num2 spare acc1 acc := by
  funext j
  cases j <;> simp [pstore, Function.update_apply]

/-- Updating the parsing slot of `pstore` leaves its intermediate accumulator unchanged. -/
theorem pstore_upd_parse_acc1 (raw parse num num2 spare acc1 acc drop : Bits) :
    (Function.update (pstore raw parse num num2 spare acc1 acc) PSlot.parse drop) PSlot.acc1
      = acc1 := by
  simp [pstore, Function.update_apply]

/-- Popping the parsing word's head and pushing it onto the intermediate accumulator produces
the corresponding updated `pstore`. -/
theorem tkbody_store (b : Bool) (raw drop num num2 spare acc1 acc : Bits) :
    Function.update (Function.update (pstore raw (b::drop) num num2 spare acc1 acc)
        PSlot.parse drop) PSlot.acc1
      (b :: (Function.update (pstore raw (b::drop) num num2 spare acc1 acc)
        PSlot.parse drop) PSlot.acc1)
      = pstore raw drop num num2 spare (b::acc1) acc := by
  funext j
  cases j <;> simp [pstore, Function.update_apply]

/-- A payload-extraction step moves the leading parsing bit to the intermediate accumulator and
returns to counter decrement. -/
theorem tkbody_step (b : Bool) (raw drop num num2 spare acc1 acc : Bits) (v : PLocal) :
    TM2.step parseProgram ⟨some .tkBody, v, pstore raw (b::drop) num num2 spare acc1 acc⟩ =
      some ⟨some (.tk .borrow), (v.1, some b),
        pstore raw drop num num2 spare (b::acc1) acc⟩ := by
  simp only [TM2.step, parseProgram, TM2.stepAux, pstore, List.head?_cons, List.tail_cons,
    Option.getD_some]
  rw [tkbody_store]

/-- A payload-extraction step has clock at most `2 * ((b :: drop).length + acc1.length) + 10`. -/
theorem tkbody_clock (b : Bool) (raw drop num num2 spare acc1 acc : Bits) (v : PLocal) :
    Stacks.stackRunClock parseProgram 1
        ⟨some .tkBody, v, pstore raw (b::drop) num num2 spare acc1 acc⟩ ≤
      2*((b::drop).length+acc1.length)+10 := by
  simp only [Stacks.stackRunClock, parseProgram, TM2.step,
    Stacks.stackClock, pstore, List.head?_cons, List.tail_cons,
    pstore_upd_parse_acc1, List.length_cons]
  omega
set_option maxHeartbeats 1000000 in

/-- When the counter value and payload length are `k`, the extraction loop transfers the
reversed payload to the intermediate accumulator, leaves the suffix, and reaches reversal
with the displayed clock bound. -/
theorem tk_loop : ∀ (k : ℕ) (drop rest numw acc1 raw num acc : Bits) (v : PLocal),
    binaryValue numw = k → drop.length = k →
    ∃ ticks,
      Stacks.stackRun parseProgram ticks
        ⟨some (.tk .borrow), v, pstore raw (drop ++ rest) num numw [] acc1 acc⟩ =
        some ⟨some (.flip 0), ((false,none), none),
          pstore raw rest num (List.replicate numw.length true) []
            (drop.reverse ++ acc1) acc⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.tk .borrow), v, pstore raw (drop ++ rest) num numw [] acc1 acc⟩ ≤
        (2*k+4)*(10*(1+numw.length)^2
          +50*(1+(drop++rest).length+acc1.length+k)^2+10) := by
  intro k
  induction k with
  | zero =>
    intro drop rest numw acc1 raw num acc v hk hk2
    have hdrop : drop = [] := List.length_eq_zero_iff.mp hk2
    subst hdrop
    simp only [List.nil_append, List.reverse_nil] at hk2 ⊢
    obtain ⟨hD, hDC⟩ := tk_dec_zero rest num numw acc1 raw acc v (by omega)
    have hb := pbranch_step ((false,none), v.2)
      (pstore raw rest num (List.replicate numw.length true) [] acc1 acc)
    have hc := clear_step ((false,none), v.2)
      (pstore raw rest num (List.replicate numw.length true) [] acc1 acc)
    have hrun1 : Stacks.stackRun parseProgram ((2*numw.length+2)+1)
        ⟨some (.tk .borrow), v, pstore raw rest num numw [] acc1 acc⟩ =
        some ⟨some .clear, ((false,none), v.2),
          pstore raw rest num (List.replicate numw.length true) [] acc1 acc⟩ := by
      rw [Stacks.run_add, hD, Option.bind_some]
      simpa only [pstore] using! hb
    have hrun : Stacks.stackRun parseProgram (((2*numw.length+2)+1)+1)
        ⟨some (.tk .borrow), v, pstore raw rest num numw [] acc1 acc⟩ =
        some ⟨some (.flip 0), ((false,none), none),
          pstore raw rest num (List.replicate numw.length true) [] acc1 acc⟩ := by
      rw [Stacks.run_add, hrun1, Option.bind_some]
      simpa only [pstore] using! hc
    refine ⟨((2*numw.length+2)+1)+1, hrun, ?_⟩
    have hbc := pbranch_clock ((false,none), v.2)
      (pstore raw rest num (List.replicate numw.length true) [] acc1 acc)
    have hcc := clear_clock ((false,none), v.2)
      (pstore raw rest num (List.replicate numw.length true) [] acc1 acc)
    have hsB := Stacks.clock_add parseProgram ((2*numw.length+2)+1) 1
      ⟨some (.tk .borrow), v, pstore raw rest num numw [] acc1 acc⟩
      ⟨some .clear, ((false,none), v.2),
        pstore raw rest num (List.replicate numw.length true) [] acc1 acc⟩ hrun1
    have hsA := Stacks.clock_add parseProgram (2*numw.length+2) 1
      ⟨some (.tk .borrow), v, pstore raw rest num numw [] acc1 acc⟩
      ⟨some .pbranch, ((false,none), v.2),
        pstore raw rest num (List.replicate numw.length true) [] acc1 acc⟩ hD
    have hq1 : (0:ℕ) ≤ (1+numw.length)^2 := Nat.zero_le _
    have hq2 : (0:ℕ) ≤ (1+rest.length+acc1.length+0)^2 := Nat.zero_le _
    nlinarith only [hsA, hsB, hDC, hbc, hcc, hq1, hq2]
  | succ k ih =>
    intro drop rest numw acc1 raw num acc v hk hk2
    cases drop with
    | nil => simp at hk2
    | cons b drop' =>
      simp only [List.length_cons] at hk2
      rw [List.cons_append]
      have hp : 0 < binaryValue numw := by omega
      obtain ⟨decTicks, next, hlen, hval, hD, hDC⟩ :=
        tk_dec_positive (b :: (drop' ++ rest)) num numw acc1 raw acc v hp
      have hnext : binaryValue next = k := by omega
      have hk2' : drop'.length = k := by omega
      have hb := pbranch_step ((true,none), v.2)
        (pstore raw (b :: (drop' ++ rest)) num next [] acc1 acc)
      have hrun1 : Stacks.stackRun parseProgram (decTicks+1)
          ⟨some (.tk .borrow), v, pstore raw (b :: (drop' ++ rest)) num numw [] acc1 acc⟩ =
          some ⟨some .tkBody, ((true,none), v.2),
            pstore raw (b :: (drop' ++ rest)) num next [] acc1 acc⟩ := by
        rw [Stacks.run_add, hD, Option.bind_some]
        simpa only [pstore] using! hb
      have hrun2 : Stacks.stackRun parseProgram ((decTicks+1)+1)
          ⟨some (.tk .borrow), v, pstore raw (b :: (drop' ++ rest)) num numw [] acc1 acc⟩ =
          some ⟨some (.tk .borrow), ((true,none), some b),
            pstore raw (drop' ++ rest) num next [] (b::acc1) acc⟩ := by
        rw [Stacks.run_add, hrun1, Option.bind_some]
        exact tkbody_step b raw (drop' ++ rest) num next [] acc1 acc ((true,none), v.2)
      obtain ⟨iterTicks, hIrun, hIclock⟩ := ih drop' rest next (b::acc1) raw num acc
        ((true,none), some b) hnext hk2'
      have hfull : Stacks.stackRun parseProgram (((decTicks+1)+1)+iterTicks)
          ⟨some (.tk .borrow), v, pstore raw (b :: (drop' ++ rest)) num numw [] acc1 acc⟩ =
          some ⟨some (.flip 0), ((false,none), none),
            pstore raw rest num (List.replicate numw.length true) []
              ((b :: drop').reverse ++ acc1) acc⟩ := by
        rw [← hlen, List.reverse_cons, List.append_assoc, List.singleton_append,
          Stacks.run_add, hrun2, Option.bind_some]
        exact hIrun
      refine ⟨((decTicks+1)+1)+iterTicks, hfull, ?_⟩
      have hbc := pbranch_clock ((true,none), v.2)
        (pstore raw (b :: (drop' ++ rest)) num next [] acc1 acc)
      have htb := tkbody_clock b raw (drop' ++ rest) num next [] acc1 acc ((true,none), v.2)
      have hs3 := Stacks.clock_add parseProgram ((decTicks+1)+1) iterTicks
        ⟨some (.tk .borrow), v, pstore raw (b :: (drop' ++ rest)) num numw [] acc1 acc⟩
        ⟨some (.tk .borrow), ((true,none), some b),
          pstore raw (drop' ++ rest) num next [] (b::acc1) acc⟩ hrun2
      have hs2 := Stacks.clock_add parseProgram (decTicks+1) 1
        ⟨some (.tk .borrow), v, pstore raw (b :: (drop' ++ rest)) num numw [] acc1 acc⟩
        ⟨some .tkBody, ((true,none), v.2),
          pstore raw (b :: (drop' ++ rest)) num next [] acc1 acc⟩ hrun1
      have hs1 := Stacks.clock_add parseProgram decTicks 1
        ⟨some (.tk .borrow), v, pstore raw (b :: (drop' ++ rest)) num numw [] acc1 acc⟩
        ⟨some .pbranch, ((true,none), v.2),
          pstore raw (b :: (drop' ++ rest)) num next [] acc1 acc⟩ hD
      rw [hlen] at hIclock
      have hmono : (1+(drop'++rest).length+(b::acc1).length+k)^2
          ≤ (1+(b::(drop'++rest)).length+acc1.length+(k+1))^2 := by
        have h1 : 1+(drop'++rest).length+(b::acc1).length+k
            ≤ 1+(b::(drop'++rest)).length+acc1.length+(k+1) := by
          simp only [List.cons_append, List.length_cons]
          omega
        have h0 : 0 ≤ 1+(drop'++rest).length+(b::acc1).length+k := by
          simp only [List.length_cons]
          omega
        have h0' : 0 ≤ 1+(b::(drop'++rest)).length+acc1.length+(k+1) := by
          simp only [List.cons_append, List.length_cons]
          omega
        nlinarith only [h1, h0, h0']
      have hP : (drop'++rest).length+(b::acc1).length
          ≤ (b::(drop'++rest)).length+acc1.length+1 := by
        simp only [List.cons_append, List.length_cons]
        omega
      have hnn : (0:ℕ) ≤ 1+(b::(drop'++rest)).length+acc1.length+(k+1) := by
        simp only [List.cons_append, List.length_cons]
        omega
      have hkk : (0:ℕ) ≤ 2*k+4 := by omega
      have hmul : (2*k+4)*(10*(1+numw.length)^2
            +50*(1+(drop'++rest).length+(b::acc1).length+k)^2+10)
          ≤ (2*k+4)*(10*(1+numw.length)^2
            +50*(1+(b::(drop'++rest)).length+acc1.length+(k+1))^2+10) := by
        have hm := Nat.mul_le_mul_left (2*k+4) hmono
        have he1 : (2*k+4)*(10*(1+numw.length)^2
            +50*(1+(drop'++rest).length+(b::acc1).length+k)^2+10)
            = (2*k+4)*(10*(1+numw.length)^2)
              +(2*k+4)*(50*(1+(drop'++rest).length+(b::acc1).length+k)^2)
              +(2*k+4)*10 := by ring
        have he2 : (2*k+4)*(10*(1+numw.length)^2
            +50*(1+(b::(drop'++rest)).length+acc1.length+(k+1))^2+10)
            = (2*k+4)*(10*(1+numw.length)^2)
              +(2*k+4)*(50*(1+(b::(drop'++rest)).length+acc1.length+(k+1))^2)
              +(2*k+4)*10 := by ring
        rw [he1, he2]
        gcongr <;> linarith
      have hlin : 2*((b::(drop'++rest)).length)+2*acc1.length
          ≤ 100*(1+(b::(drop'++rest)).length+acc1.length+(k+1))^2 := by
        have h1 : (b::(drop'++rest)).length
            ≤ 1+(b::(drop'++rest)).length+acc1.length+(k+1) := by omega
        have h2 : acc1.length ≤ 1+(b::(drop'++rest)).length+acc1.length+(k+1) := by omega
        have h0 : (1:ℕ) ≤ 1+(b::(drop'++rest)).length+acc1.length+(k+1) := by omega
        have hs1 : (1+(b::(drop'++rest)).length+acc1.length+(k+1))
            *(1+(b::(drop'++rest)).length+acc1.length+(k+1))
            ≥ (1+(b::(drop'++rest)).length+acc1.length+(k+1)) := by
          nlinarith only [h0]
        nlinarith only [h1, h2, hs1]
      have htq : (2*(k+1)+4)*(10*(1+numw.length)^2
            +50*(1+(b::(drop'++rest)).length+acc1.length+(k+1))^2+10)
          = (2*k+4)*(10*(1+numw.length)^2
              +50*(1+(b::(drop'++rest)).length+acc1.length+(k+1))^2+10)
            +20*(1+numw.length)^2
            +100*(1+(b::(drop'++rest)).length+acc1.length+(k+1))^2+20 := by ring
      have hqq : (1:ℕ) ≤ (1+numw.length)^2 := by
        nlinarith [show (0:ℕ) ≤ numw.length from Nat.zero_le _]
      have hc1 : Stacks.stackRunClock parseProgram (((decTicks+1)+1)+iterTicks)
          ⟨some (.tk .borrow), v, pstore raw (b :: (drop' ++ rest)) num numw [] acc1 acc⟩ ≤
          10*(1+numw.length)^2+2+(2*((b::(drop'++rest)).length)+2*acc1.length+12)
            +(2*k+4)*(10*(1+numw.length)^2
              +50*(1+(b::(drop'++rest)).length+acc1.length+(k+1))^2+10) := by
        have hiter := hIclock.trans hmul
        linarith only [hs1, hs2, hs3, hDC, hbc, htb, hiter]
      rw [htq]
      linarith only [hc1, hlin, hqq]
set_option maxHeartbeats 1000000 in

/-- The payload-reversal call moves the intermediate accumulator in reverse order into the empty
final accumulator, with clock at most `9 * (1 + acc1.length) ^ 2`. -/
theorem flip_call (acc1 raw parse num num2 spare : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.flip 0), ((false,none),none),
          pstore raw parse num num2 spare acc1 []⟩ =
      some ⟨some .pdone, ((false,none),none),
        pstore raw parse num num2 spare [] acc1.reverse⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.flip 0), ((false,none),none),
          pstore raw parse num num2 spare acc1 []⟩ ≤
        9*(1+acc1.length)^2 := by
  have hr := Stacks.transfer_run acc1 [] none
  obtain ⟨hN, hNC⟩ := StackCall.execution flipCode PLabel.flip .pdone
    Prod.snd (fun v b => (v.1, b))
    (flipFrame raw parse num num2 spare) (flipFrame_at raw parse num num2 spare)
    (flipFrame_update raw parse num num2 spare) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Stacks.transferProgram parseProgram (fun _ => rfl) ((false,none),none)
    (acc1.length+1) _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one, flipFrame,
    pstore, List.reverse_nil, List.nil_append, List.append_nil] at hN hNC
  refine ⟨acc1.length+1, hN, ?_⟩
  have hb := Stacks.transfer_clock acc1 [] none
  simp only [List.length_nil, Nat.add_zero] at hb
  have h0 : (0:ℕ) ≤ acc1.length := Nat.zero_le _
  nlinarith only [hNC, hb, h0]

/-- The parser done label halts in one step without changing its stacks. -/
theorem pdone_run (st : PSlot → Bits) :
    Stacks.stackRun parseProgram 1 ⟨some .pdone, ((false,none),none), st⟩ =
      some ⟨none, ((false,none),none), st⟩ := by
  simp [Stacks.stackRun, parseProgram, TM2.step]

/-- One step at the parser done label has clock at most one. -/
theorem pdone_clock (st : PSlot → Bits) :
    Stacks.stackRunClock parseProgram 1 ⟨some .pdone, ((false,none),none), st⟩ ≤ 1 := by
  simp [Stacks.stackRunClock, Stacks.stackRun, parseProgram, TM2.step, Stacks.stackClock]
set_option maxHeartbeats 1000000 in

/-- Parsing the reversed raw encoding of `framed w ++ rest` halts with payload `w` and
unconsumed suffix `rest`, with the displayed clock bound. -/
theorem parseFramed_run (w rest : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.read 0), ((false,none),none),
          pstore (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse [] [] [] [] [] []⟩ =
      some ⟨none, ((false,none),none),
        pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.read 0), ((false,none),none),
          pstore (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse [] [] [] [] [] []⟩ ≤
        9*(1+((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse).length)^2
          +40*(1+(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)).length)^2
          +9*(1+w.length.bits.length)^2
          +(2*w.length+4)*(10*(1+w.length.bits.length)^2
            +50*(1+(w ++ rest).length+0+w.length)^2+10)
          +9*(1+w.length)^2+1 := by
  obtain ⟨t1, h1, h1c⟩ :=
      read_call (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse
  obtain ⟨t2, h2, h2c⟩ := nat_call w rest
  obtain ⟨t3, h3, h3c⟩ := nflip_call w rest
  obtain ⟨t4, h4, h4c⟩ := tk_loop w.length w rest w.length.bits [] [] [] []
    ((false,none),none) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits w.length) rfl
  simp only [List.length_nil] at h4c
  obtain ⟨t5, h5, h5c⟩ := flip_call (w.reverse ++ ([] : Bits)) [] rest []
    (List.replicate w.length.bits.length true) []
  have hw : (w.reverse ++ ([] : Bits)).reverse = w := by
    simp
  rw [hw] at h5
  simp only [List.length_append, List.length_reverse, List.length_nil, Nat.add_zero] at h5c
  have hr12 : Stacks.stackRun parseProgram (t1+t2)
      ⟨some (.read 0), ((false,none),none),
        pstore (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse [] [] [] [] [] []⟩ =
      some ⟨some (.nflip 0), ((false,none),none),
        pstore [] (w ++ rest) w.length.bits.reverse [] [] [] []⟩ := by
    rw [Stacks.run_add, h1, Option.bind_some]
    rw [List.reverse_reverse, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed,
        List.append_assoc]
    exact h2
  have hr3 : Stacks.stackRun parseProgram ((t1+t2)+t3)
      ⟨some (.read 0), ((false,none),none),
        pstore (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse [] [] [] [] [] []⟩ =
      some ⟨some (.tk .borrow), ((false,none),none),
        pstore [] (w ++ rest) [] w.length.bits [] [] []⟩ := by
    rw [Stacks.run_add, hr12, Option.bind_some]
    exact h3
  have hr4 : Stacks.stackRun parseProgram (((t1+t2)+t3)+t4)
      ⟨some (.read 0), ((false,none),none),
        pstore (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse [] [] [] [] [] []⟩ =
      some ⟨some (.flip 0), ((false,none),none),
        pstore [] rest [] (List.replicate w.length.bits.length true) []
          (w.reverse ++ ([] : Bits)) []⟩ := by
    rw [Stacks.run_add, hr3, Option.bind_some]
    exact h4
  have hr5 : Stacks.stackRun parseProgram ((((t1+t2)+t3)+t4)+t5)
      ⟨some (.read 0), ((false,none),none),
        pstore (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse [] [] [] [] [] []⟩ =
      some ⟨some .pdone, ((false,none),none),
        pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w⟩ := by
    rw [Stacks.run_add, hr4, Option.bind_some]
    exact h5
  have hfull : Stacks.stackRun parseProgram (((((t1+t2)+t3)+t4)+t5)+1)
      ⟨some (.read 0), ((false,none),none),
        pstore (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse [] [] [] [] [] []⟩ =
      some ⟨none, ((false,none),none),
        pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w⟩ := by
    rw [Stacks.run_add, hr5, Option.bind_some]
    exact pdone_run (pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w)
  refine ⟨((((t1+t2)+t3)+t4)+t5)+1, hfull, ?_⟩
  have hs12 := Stacks.clock_add parseProgram t1 t2 _ _ h1
  have hclock2 : Stacks.stackRunClock parseProgram t2
      ⟨some (.nat 0), ((false,none),none),
        pstore [] (List.reverse (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest)).reverse [] [] [] [] []⟩ =
      Stacks.stackRunClock parseProgram t2
      ⟨some (.nat 0), ((false,none),none),
        pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)) [] [] [] [] []⟩ := by
    congr 1
    rw [List.reverse_reverse, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed,
        List.append_assoc]
  have hs3 := Stacks.clock_add parseProgram (t1+t2) t3 _ _ hr12
  have hs4 := Stacks.clock_add parseProgram ((t1+t2)+t3) t4 _ _ hr3
  have hs5 := Stacks.clock_add parseProgram (((t1+t2)+t3)+t4) t5 _ _ hr4
  have hsf := Stacks.clock_add parseProgram ((((t1+t2)+t3)+t4)+t5) 1 _ _ hr5
  have hpc := pdone_clock
    (pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w)
  nlinarith only [hs12, hs3, hs4, hs5, hsf, h1c, h2c, h3c, h4c, h5c, hpc, hclock2]

set_option maxHeartbeats 1000000 in

/-- Starting at natural-number parsing on `framed w ++ rest` halts with payload `w` and suffix
`rest`, with the displayed clock bound. -/
theorem parseFramed_run_from (w rest : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.nat 0), ((false,none),none),
          pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest) [] [] [] [] []⟩ =
      some ⟨none, ((false,none),none),
        pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.nat 0), ((false,none),none),
          pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest) [] [] [] [] []⟩ ≤
        40*(1+(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)).length)^2
          +9*(1+w.length.bits.length)^2
          +(2*w.length+4)*(10*(1+w.length.bits.length)^2
            +50*(1+(w ++ rest).length+0+w.length)^2+10)
          +9*(1+w.length)^2+1 := by
  have hstart : pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest) [] [] [] [] []
      = pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)) [] [] [] [] [] := by
    simp [Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed, List.append_assoc]
  rw [hstart]
  obtain ⟨t2, h2, h2c⟩ := nat_call w rest
  obtain ⟨t3, h3, h3c⟩ := nflip_call w rest
  obtain ⟨t4, h4, h4c⟩ := tk_loop w.length w rest w.length.bits [] [] [] []
    ((false,none),none) (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits w.length) rfl
  simp only [List.length_nil] at h4c
  obtain ⟨t5, h5, h5c⟩ := flip_call (w.reverse ++ ([] : Bits)) [] rest []
    (List.replicate w.length.bits.length true) []
  have hw : (w.reverse ++ ([] : Bits)).reverse = w := by
    simp
  rw [hw] at h5
  simp only [List.length_append, List.length_reverse, List.length_nil, Nat.add_zero] at h5c
  have hr3 : Stacks.stackRun parseProgram (t2+t3)
      ⟨some (.nat 0), ((false,none),none),
        pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)) [] [] [] [] []⟩ =
      some ⟨some (.tk .borrow), ((false,none),none),
        pstore [] (w ++ rest) [] w.length.bits [] [] []⟩ := by
    rw [Stacks.run_add, h2, Option.bind_some]
    exact h3
  have hr4 : Stacks.stackRun parseProgram ((t2+t3)+t4)
      ⟨some (.nat 0), ((false,none),none),
        pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)) [] [] [] [] []⟩ =
      some ⟨some (.flip 0), ((false,none),none),
        pstore [] rest [] (List.replicate w.length.bits.length true) []
          (w.reverse ++ ([] : Bits)) []⟩ := by
    rw [Stacks.run_add, hr3, Option.bind_some]
    exact h4
  have hr5 : Stacks.stackRun parseProgram (((t2+t3)+t4)+t5)
      ⟨some (.nat 0), ((false,none),none),
        pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)) [] [] [] [] []⟩ =
      some ⟨some .pdone, ((false,none),none),
        pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w⟩ := by
    rw [Stacks.run_add, hr4, Option.bind_some]
    exact h5
  have hfull : Stacks.stackRun parseProgram ((((t2+t3)+t4)+t5)+1)
      ⟨some (.nat 0), ((false,none),none),
        pstore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)) [] [] [] [] []⟩ =
      some ⟨none, ((false,none),none),
        pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w⟩ := by
    rw [Stacks.run_add, hr5, Option.bind_some]
    exact pdone_run (pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w)
  refine ⟨((((t2+t3)+t4)+t5)+1), hfull, ?_⟩
  have hs23 := Stacks.clock_add parseProgram t2 t3 _ _ h2
  have hs34 := Stacks.clock_add parseProgram (t2+t3) t4 _ _ hr3
  have hs45 := Stacks.clock_add parseProgram ((t2+t3)+t4) t5 _ _ hr4
  have hsf := Stacks.clock_add parseProgram (((t2+t3)+t4)+t5) 1 _ _ hr5
  have hpc := pdone_clock
    (pstore [] rest [] (List.replicate w.length.bits.length true) [] [] w)
  nlinarith only [hs23, hs34, hs45, hsf, h2c, h3c, h4c, h5c, hpc]

end ParseFramed

end ParseFramed

/-- Binary-word addition defined by iterating increment on `x` exactly `binaryValue y` times. -/
def bitsAdd (x y : Bits) : Bits :=
  Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word^[binaryValue y] x

/-- Iterating binary increment `k` times on `n.bits` yields `(n + k).bits`. -/
theorem succIterate_bits (k n : ℕ) :
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word^[k]) n.bits = (n+k).bits := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih,
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word_bits]
    congr 1

/-- Iterating binary increment `k` times increases the represented natural number by `k`. -/
theorem succIterate_value (k : ℕ) (x : Bits) :
    binaryValue ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word^[k]) x)
      = binaryValue x + k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply',
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word_value, ih]
    omega

/-- The binary value of `bitsAdd x y` is the sum of the input values. -/
theorem bitsAdd_value (x y : Bits) :
    binaryValue (bitsAdd x y) = binaryValue x + binaryValue y :=
  succIterate_value (binaryValue y) x

/-- Adding the canonical binary words for `n` and `m` yields the canonical binary word for `n +
m`. -/
theorem bitsAdd_bits (n m : ℕ) :
    bitsAdd n.bits m.bits = (n+m).bits := by
  rw [bitsAdd, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits m,
    succIterate_bits]

/-- Iterating addition of `x` exactly `n` times adds `n * binaryValue x` to the initial binary
value. -/
theorem mulIterate_value (n : ℕ) (z x : Bits) :
    binaryValue ((fun w => bitsAdd w x)^[n] z) = binaryValue z + n*binaryValue x := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', bitsAdd_value, ih]
    ring

/-- Iterating addition of `x` exactly `n` times on `m.bits` yields `(m + n * binaryValue
x).bits`. -/
theorem mulIterate_bits (n m : ℕ) (x : Bits) :
    (fun w => bitsAdd w x)^[n] m.bits = (m + n*binaryValue x).bits := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    have hx : bitsAdd (m + n*binaryValue x).bits x
        = bitsAdd (m + n*binaryValue x).bits (binaryValue x).bits := by
      rw [bitsAdd, bitsAdd, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
    rw [hx, bitsAdd_bits]
    congr 1
    ring

/-- Binary-word multiplication defined by repeatedly adding `x` to the empty word `binaryValue
y` times. -/
def bitsMul (x y : Bits) : Bits :=
  (fun z => bitsAdd z x)^[binaryValue y] []

/-- The binary value of `bitsMul x y` is the product of the input values. -/
theorem bitsMul_value (x y : Bits) :
    binaryValue (bitsMul x y) = binaryValue x * binaryValue y := by
  rw [bitsMul, mulIterate_value, show binaryValue ([] : Bits) = 0 from rfl]
  ring

/-- Multiplying the canonical binary words for `n` and `m` yields the canonical binary word for
`n * m`. -/
theorem bitsMul_bits (n m : ℕ) :
    bitsMul n.bits m.bits = (n*m).bits := by
  rw [bitsMul, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits,
    show ([] : Bits) = (0:ℕ).bits from rfl, mulIterate_bits,
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]
  congr 1
  ring

/-- The number of consecutive true bits at the beginning of a bit word. -/
def countTrues : Bits → ℕ
  | [] => 0
  | true :: rest => countTrues rest + 1
  | false :: _ => 0

/-- Splits a natural-number encoding into its binary value and residual input, using the leading
run of true bits to determine the field length. -/
def natBitsSplit (input : Bits) : ℕ × Bits :=
  let k := countTrues input
  let rest := input.drop (k + 1)
  (binaryValue (rest.take k), rest.drop k)

/-- Splits a framed word into the payload specified by its encoded length and the residual
input, padding a short payload with false. -/
def frameSplit (input : Bits) : Bits × Bits :=
  let (n, body) := natBitsSplit input
  (body.take n ++ List.replicate (n - body.length) false, body.drop n)

/-- The encoding of a pair of bit words as the concatenation of their framed encodings. -/
def pairEnc (acc cnt : Bits) : Bits := framed acc ++ framed cnt

/-- Decodes two framed words, adds the second to the first, and encodes the updated first word
together with the unchanged second word. -/
def bitsAddPair (w : Bits) : Bits :=
  let (acc, rest) := frameSplit w
  let (cnt, _) := frameSplit rest
  framed (bitsAdd acc cnt) ++ framed cnt

/-- A prefix of `k` true bits followed by false has leading true count `k`, independently of the
suffix. -/
theorem countTrues_prefix (k : ℕ) (rest : Bits) :
    countTrues (List.replicate k true ++ [false] ++ rest) = k := by
  induction k generalizing rest with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    show countTrues ((List.replicate k true ++ [false]) ++ rest) + 1 = k + 1
    rw [ih]

/-- Dropping `k` bits from `k` true bits followed by false and a suffix leaves false followed by
that suffix. -/
theorem drop_prefix (k : ℕ) (rest : Bits) :
    List.drop k (List.replicate k true ++ [false] ++ rest) = false :: rest := by
  induction k generalizing rest with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, List.cons_append]
    exact ih rest

/-- Taking `l.length` bits from `l ++ rest` recovers `l`. -/
theorem take_append_self (l rest : Bits) :
    List.take l.length (l ++ rest) = l := by
  induction l generalizing rest with
  | nil => rfl
  | cons a l ih => exact congrArg (a :: ·) (ih rest)

/-- Dropping `l.length` bits from `l ++ rest` recovers `rest`. -/
theorem drop_append_self (l rest : Bits) :
    List.drop l.length (l ++ rest) = rest := by
  induction l generalizing rest with
  | nil => rfl
  | cons a l ih => exact ih rest

/-- Splitting `natBits n ++ rest` recovers the number `n` and the unchanged suffix. -/
theorem natBitsSplit_natBits (n : ℕ) (rest : Bits) :
    natBitsSplit (natBits n ++ rest) = (n, rest) := by
  have hassoc : natBits n ++ rest
      = List.replicate n.bits.length true ++ [false] ++ (n.bits ++ rest) := by
    unfold natBits
    simp only [List.append_assoc]
  have hk : countTrues (natBits n ++ rest) = n.bits.length := by
    rw [hassoc, countTrues_prefix]
  have hd : List.drop n.bits.length (natBits n ++ rest)
      = false :: (n.bits ++ rest) := by rw [hassoc, drop_prefix]
  have htl : (natBits n ++ rest).drop (n.bits.length + 1) = n.bits ++ rest := by
    rw [← List.drop_drop, hd]
    rfl
  have htk : (n.bits ++ rest).take n.bits.length = n.bits := take_append_self n.bits rest
  have hdr : (n.bits ++ rest).drop n.bits.length = rest := drop_append_self n.bits rest
  unfold natBitsSplit
  simp only [hk, htl, htk, hdr, Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue_bits]

/-- Splitting `framed w ++ rest` recovers the payload `w` and the unchanged suffix. -/
theorem frameSplit_framed (w : Bits) (rest : Bits) :
    frameSplit (framed w ++ rest) = (w, rest) := by
  have h : framed w ++ rest = natBits w.length ++ (w ++ rest) := by
    unfold framed
    simp only [List.append_assoc]
  have hlen : w.length ≤ (w ++ rest).length := by
    simp only [List.length_append]
    omega
  rw [h]
  simp only [frameSplit, natBitsSplit_natBits, take_append_self, drop_append_self,
    Nat.sub_eq_zero_of_le hlen, List.replicate_zero, List.append_nil]

/-- Splitting `pairEnc acc cnt` recovers `acc` and the framed encoding of `cnt`. -/
theorem frameSplit_pair (acc cnt : Bits) :
    frameSplit (pairEnc acc cnt) = (acc, framed cnt) := by
  rw [pairEnc, frameSplit_framed]

/-- Applying `bitsAddPair` to an encoded pair adds the counter word to the accumulator word and
preserves the counter. -/
theorem bitsAddPair_pairEnc (acc cnt : Bits) :
    bitsAddPair (pairEnc acc cnt) = pairEnc (bitsAdd acc cnt) cnt := by
  have h2 : frameSplit (framed cnt) = (cnt, []) := by
    have h := frameSplit_framed cnt []
    rwa [List.append_nil] at h
  have ha := frameSplit_framed acc (framed cnt)
  simp only [bitsAddPair, pairEnc, ha, h2]

/-- Iterating `bitsAddPair` preserves pair encoding and iterates addition of the counter word to
the accumulator. -/
theorem bitsAddPair_iterate (n : ℕ) (acc cnt : Bits) :
    (bitsAddPair^[n]) (pairEnc acc cnt)
      = pairEnc ((fun z => bitsAdd z cnt)^[n] acc) cnt := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, bitsAddPair_pairEnc,
      Function.iterate_succ_apply']

/-- Iterating `bitsAddPair` on the pair of an empty accumulator and `x` exactly `binaryValue y`
times produces the pair of `bitsMul x y` and `x`. -/
theorem bitsMul_pair (x y : Bits) :
    (bitsAddPair^[binaryValue y]) (pairEnc [] x) = pairEnc (bitsMul x y) x := by
  rw [bitsAddPair_iterate, bitsMul]

/-- Given a `ComputesAt` implementation of increment, each pair of input words has a machine
computing their sum from the specified framed input, with the displayed bounds involving the
iteration costs. -/
theorem bitsAdd_runs (tw sw : Bits → ℕ)
    (hf : Qatlib.Concepts.BitWordCompiler.CanonicalCodec.ComputesAt
      Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word tw sw)
    (y x : Bits) :
    ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))) (C : ℕ), 0 < C ∧
      Runs M (natBits (binaryValue y) ++ framed x) (bitsAdd x y)
        (C*(1+(natBits (binaryValue y)++framed x).length+binaryValue y+
          (bitsAdd x y).length+
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word tw (binaryValue y) x+
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word List.length
            (binaryValue y) x)^2)
        (C*(1+(natBits (binaryValue y)++framed x).length+binaryValue y+
          (bitsAdd x y).length+
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word sw (binaryValue y) x+
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word List.length
            (binaryValue y) x)^2) := by
  obtain ⟨q,M,C,hC,h⟩ := Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.uniform_iterates
    Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word tw sw hf
  exact ⟨q,M,C,hC,h (binaryValue y) x⟩

/-- Each pair of input words has a machine computing their sum from the specified framed input,
with the displayed bounds obtained from the linear time and space bounds for increment. -/
theorem bitsAdd_runs' (y x : Bits) :
    ∃ (q : ℕ) (M : Turing.TM0.Machine (Option Bool) (Fin (q+1))) (C : ℕ), 0 < C ∧
      Runs M (natBits (binaryValue y) ++ framed x) (bitsAdd x y)
        (C*(1+(natBits (binaryValue y)++framed x).length+binaryValue y+
          (bitsAdd x y).length+
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word
            (fun x => 10*x.length+10) (binaryValue y) x+
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word List.length
            (binaryValue y) x)^2)
        (C*(1+(natBits (binaryValue y)++framed x).length+binaryValue y+
          (bitsAdd x y).length+
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word
            (fun x => 10*x.length+10) (binaryValue y) x+
          Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.iterSum
            Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment.word List.length
            (binaryValue y) x)^2) :=
  bitsAdd_runs (fun x => 10*x.length+10) (fun x => 10*x.length+10)
    word_computesAt y x

section PairCopy

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM (Symbol)
open Turing

namespace PairCopy

/-- The source, temporary, and two destination stack slots used to duplicate a bit word. -/
inductive Slot | src | tmp | d1 | d2 deriving DecidableEq, Fintype
instance : Inhabited Slot := ⟨.tmp⟩

/-- The control labels for reversing the source, copying each bit to both destinations, and
halting. -/
inductive Label
  | mv : Fin 1 → Label
  | cp
  | done
  deriving DecidableEq

/-- Maps the transfer subroutine's two slots to the source and temporary slots. -/
def mvCode (k : Fin 2) : Slot := if k = 0 then .src else .tmp

/-- A stack program that reverses the source into temporary storage, then transfers each bit to
both destination stacks. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Symbol
  | .mv l => StackCall.stmt mvCode Label.mv .cp id (fun _ v => v) (Stacks.transferProgram l)
  | .cp => .pop .tmp (fun _ bit => bit) (.branch (fun bit => bit.isSome)
      (.push .d1 (fun bit => bit.getD false)
        (.push .d2 (fun bit => bit.getD false) (.goto (fun _ => .cp))))
      (.goto (fun _ => .done)))
  | .done => .halt

/-- The four-stack store for a source word, a temporary word, and two destination words. -/
def cstore (src tmp d1 d2 : Bits) : Slot → Bits
  | .src => src | .tmp => tmp | .d1 => d1 | .d2 => d2

/-- Embeds the source-transfer store into the copying store while fixing the two destination
stacks. -/
def mvFrame (d1 d2 : Bits) (S : Fin 2 → Bits) : Slot → Bits :=
  cstore (S 0) (S 1) d1 d2

/-- Evaluating `mvFrame` at a slot selected by `mvCode` recovers the corresponding transfer
stack. -/
theorem mvFrame_at (d1 d2 : Bits) (S : Fin 2 → Bits) (k : Fin 2) :
    mvFrame d1 d2 S (mvCode k) = S k := by
  fin_cases k <;> simp [mvFrame, mvCode, cstore]

/-- Updating a transfer stack commutes with embedding it through `mvFrame`. -/
theorem mvFrame_update (d1 d2 : Bits) (S : Fin 2 → Bits) (k : Fin 2) (bits : Bits) :
    mvFrame d1 d2 (Function.update S k bits)
      = Function.update (mvFrame d1 d2 S) (mvCode k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [mvFrame, mvCode, cstore, Function.update_apply]

/-- The transfer phase empties the source into the temporary stack in reverse order and reaches
copying with clock at most `9 * (1 + w.length) ^ 2`. -/
theorem mv_run (w d1 d2 : Bits) (v : Symbol) :
    ∃ ticks, Stacks.stackRun program ticks ⟨some (.mv 0), v, cstore w [] d1 d2⟩ =
      some ⟨some .cp, none, cstore [] w.reverse d1 d2⟩ ∧
      Stacks.stackRunClock program ticks ⟨some (.mv 0), v, cstore w [] d1 d2⟩ ≤
        9*(1+w.length)^2 := by
  have hr := Stacks.transfer_run w [] v
  rw [List.append_nil] at hr
  obtain ⟨hN, hNC⟩ := StackCall.execution mvCode Label.mv .cp id (fun _ v => v)
    (mvFrame d1 d2) (mvFrame_at d1 d2) (mvFrame_update d1 d2) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Stacks.transferProgram program (fun _ => rfl) v (w.length+1) _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one,
    mvFrame, cstore] at hN hNC
  refine ⟨w.length+1, hN, ?_⟩
  have hb := Stacks.transfer_clock w [] v
  simp only [List.length_nil, Nat.add_zero] at hb
  have h0 : (0:ℕ) ≤ w.length := Nat.zero_le _
  nlinarith only [hNC, hb, h0]

/-- Popping one temporary bit and pushing it to both destinations produces the corresponding
updated copying store. -/
theorem cp_store (b : Bool) (src rest d1 d2 : Bits) :
    Function.update (Function.update (Function.update (cstore src (b::rest) d1 d2)
        Slot.tmp rest) Slot.d1 (b::d1)) Slot.d2 (b::d2)
      = cstore src rest (b::d1) (b::d2) := by
  funext j
  cases j <;> simp [cstore, Function.update_apply]

/-- Updating the temporary slot after removing its leading bit replaces only that stack. -/
theorem cstore_upd_tmp (b : Bool) (src rest d1 d2 : Bits) :
    Function.update (cstore src (b::rest) d1 d2) Slot.tmp rest = cstore src rest d1 d2 := by
  funext j
  cases j <;> simp [cstore, Function.update_apply]

/-- Pushing a bit to the first destination gives the corresponding update of `cstore`. -/
theorem cstore_upd_d1 (b : Bool) (src rest d1 d2 : Bits) :
    Function.update (cstore src rest d1 d2) Slot.d1 (b::d1) = cstore src rest (b::d1) d2 := by
  funext j
  cases j <;> simp [cstore, Function.update_apply]

/-- Pushing a bit to the second destination gives the corresponding update of `cstore`. -/
theorem cstore_upd_d2 (b : Bool) (src rest d1 d2 : Bits) :
    Function.update (cstore src rest (b::d1) d2) Slot.d2 (b::d2)
      = cstore src rest (b::d1) (b::d2) := by
  funext j
  cases j <;> simp [cstore, Function.update_apply]

/-- A copying step removes the leading temporary bit and pushes it onto both destination stacks. -/
theorem cp_step (b : Bool) (src rest d1 d2 : Bits) (v : Symbol) :
    TM2.step program ⟨some .cp, v, cstore src (b::rest) d1 d2⟩ =
      some ⟨some .cp, some b, cstore src rest (b::d1) (b::d2)⟩ := by
  simp [TM2.step, program, TM2.stepAux, cstore]
  exact cp_store b src rest d1 d2

/-- A copying step on an empty temporary stack enters the done label and clears the saved bit. -/
theorem cp_stop (src d1 d2 : Bits) (v : Symbol) :
    TM2.step program ⟨some .cp, v, cstore src [] d1 d2⟩ =
      some ⟨some .done, none, cstore src [] d1 d2⟩ := by
  simp [TM2.step, program, TM2.stepAux, cstore]

/-- One copying step has clock at most `2 * (tmp.length + d1.length + d2.length) + 20`. -/
theorem cp_step_clock (src tmp d1 d2 : Bits) (v : Symbol) :
    Stacks.stackRunClock program 1 ⟨some .cp, v, cstore src tmp d1 d2⟩ ≤
      2*(tmp.length + d1.length + d2.length) + 20 := by
  cases tmp with
  | nil => simp [Stacks.stackRunClock, program, TM2.step, Stacks.stackClock, cstore]
  | cons b rest =>
    simp only [Stacks.stackRunClock, program, TM2.step, TM2.stepAux, Stacks.stackClock,
      cstore, List.head?_cons, List.tail_cons, Option.isSome_some, if_true, Option.getD_some,
      List.length_cons, cstore_upd_tmp, cstore_upd_d1, cstore_upd_d2]
    omega

/-- In `w.length + 1` steps, the copying loop empties `w` and prefixes its reverse to both
destination stacks, with the displayed clock bound. -/
theorem cp_loop (w src d1 d2 : Bits) (v : Symbol) :
    Stacks.stackRun program (w.length+1) ⟨some .cp, v, cstore src w d1 d2⟩ =
      some ⟨some .done, none, cstore src [] (w.reverse ++ d1) (w.reverse ++ d2)⟩ ∧
    Stacks.stackRunClock program (w.length+1) ⟨some .cp, v, cstore src w d1 d2⟩ ≤
      (w.length+1)*(2*(w.length+d1.length+d2.length)+2*w.length+20) := by
  induction w generalizing d1 d2 v with
  | nil =>
    have hstep := cp_stop src d1 d2 v
    constructor
    · simpa only [List.reverse_nil, List.nil_append] using!
        (by simp [Stacks.stackRun, hstep] :
          Stacks.stackRun program 1 ⟨some .cp, v, cstore src [] d1 d2⟩ =
            some ⟨some .done, none, cstore src [] d1 d2⟩)
    · simpa only [List.length_nil, Nat.zero_add, Nat.add_zero, Nat.one_mul] using!
        cp_step_clock src [] d1 d2 v
  | cons b w ih =>
    have hstep := cp_step b src w d1 d2 v
    obtain ⟨hI, hIC⟩ := ih (b::d1) (b::d2) (some b)
    have hstepRun : Stacks.stackRun program 1 ⟨some .cp, v, cstore src (b::w) d1 d2⟩ =
        some ⟨some .cp, some b, cstore src w (b::d1) (b::d2)⟩ := by
      simp [Stacks.stackRun, hstep]
    have hrun : Stacks.stackRun program (1+(w.length+1))
        ⟨some .cp, v, cstore src (b::w) d1 d2⟩ =
        some ⟨some .done, none, cstore src []
          ((b::w).reverse ++ d1) ((b::w).reverse ++ d2)⟩ := by
      rw [Stacks.run_add, hstepRun, Option.bind_some]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using! hI
    have htick : (b::w).length+1 = 1+(w.length+1) := by
      simp only [List.length_cons]; omega
    refine ⟨?_, ?_⟩
    · rw [htick]; exact hrun
    · rw [htick]
      have hs := Stacks.clock_add program 1 (w.length+1) _ _ hstepRun
      have h1c := cp_step_clock src (b::w) d1 d2 v
      simp only [List.length_cons] at h1c hIC hs ⊢
      nlinarith only [h1c, hIC, hs]

/-- The copying program's done label halts in one step without changing the local state or
stacks. -/
theorem done_run (src tmp d1 d2 : Bits) (v : Symbol) :
    Stacks.stackRun program 1 ⟨some .done, v, cstore src tmp d1 d2⟩ =
      some ⟨none, v, cstore src tmp d1 d2⟩ := by
  simp [Stacks.stackRun, program, TM2.step]

/-- The copying program halts with two copies of the input and empty source and temporary
stacks, with clock at most `30 * (1 + w.length) ^ 2`. -/
theorem copyTwo_run (w : Bits) (v : Symbol) :
    ∃ ticks, Stacks.stackRun program ticks ⟨some (.mv 0), v, cstore w [] [] []⟩ =
      some ⟨none, none, cstore [] [] w w⟩ ∧
      Stacks.stackRunClock program ticks ⟨some (.mv 0), v, cstore w [] [] []⟩ ≤
        30*(1+w.length)^2 := by
  obtain ⟨t1, h1, h1c⟩ := mv_run w [] [] v
  obtain ⟨h2, h2c⟩ := cp_loop w.reverse [] [] [] none
  have h2' : Stacks.stackRun program (w.reverse.length+1)
      ⟨some .cp, none, cstore [] w.reverse [] []⟩ =
      some ⟨some .done, none, cstore [] [] w w⟩ := by
    simpa only [List.reverse_reverse, List.nil_append, List.append_nil] using! h2
  have hd := done_run (src := ([] : Bits)) (tmp := ([] : Bits)) (d1 := w) (d2 := w) none
  have h12 : Stacks.stackRun program (t1+(w.reverse.length+1))
      ⟨some (.mv 0), v, cstore w [] [] []⟩ =
      some ⟨some .done, none, cstore [] [] w w⟩ := by
    rw [Stacks.run_add, h1, Option.bind_some]
    exact h2'
  have hrun : Stacks.stackRun program ((t1+(w.reverse.length+1))+1)
      ⟨some (.mv 0), v, cstore w [] [] []⟩ =
      some ⟨none, none, cstore [] [] w w⟩ := by
    rw [Stacks.run_add, h12, Option.bind_some]
    exact hd
  refine ⟨(t1+(w.reverse.length+1))+1, hrun, ?_⟩
  have hs1 := Stacks.clock_add program t1 (w.reverse.length+1) _ _ h1
  have hs2 := Stacks.clock_add program (t1+(w.reverse.length+1)) 1 _ _ h12
  have hpc : Stacks.stackRunClock program 1
      (⟨some .done, none, cstore [] [] w w⟩ : TM2.Cfg (fun _ : Slot => Bool) Label Symbol) = 1 := by
    simp [Stacks.stackRunClock, program, TM2.step, Stacks.stackClock]
  have hl : w.reverse.length = w.length := by simp
  simp only [hl, List.length_nil, Nat.add_zero] at hs1 hs2 h2c ⊢
  nlinarith only [hs1, hs2, h1c, h2c, hpc]

end PairCopy

end PairCopy

section LengthCount

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM (Symbol)
open Turing

namespace LengthCount

/-- The source, counter, and temporary stack slots used for counting a word's length. -/
inductive Slot | src | cnt | tmp deriving DecidableEq, Fintype
instance : Inhabited Slot := ⟨.tmp⟩

/-- The control labels for checking the source, incrementing the length counter, and halting. -/
inductive Label
  | check
  | inc : Increment.Label → Label
  | done
  deriving DecidableEq

/-- Maps the increment subroutine's two stack slots to the counter and temporary slots. -/
def incCode (k : Fin 2) : Slot := if k = 0 then .cnt else .tmp

/-- A stack program that consumes the source word and increments the counter once per bit. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Symbol
  | .check => .pop .src (fun _ bit => bit) (.branch (fun bit => bit.isSome)
      (.goto (fun _ => .inc .carry)) (.goto (fun _ => .done)))
  | .inc l => StackCall.stmt incCode Label.inc .check id (fun _ v => v) (Increment.program l)
  | .done => .halt

/-- The length-counting store assigning words to the source, counter, and temporary slots. -/
def cstore (src cnt tmp : Bits) : Slot → Bits
  | .src => src | .cnt => cnt | .tmp => tmp

/-- Embeds the increment subroutine's store into the length-counting store while fixing the
source. -/
def incFrame (src : Bits) (S : Fin 2 → Bits) : Slot → Bits := cstore src (S 0) (S 1)

/-- Evaluating `incFrame` at a slot selected by `incCode` recovers the corresponding increment
stack. -/
theorem incFrame_at (src : Bits) (S : Fin 2 → Bits) (k : Fin 2) :
    incFrame src S (incCode k) = S k := by
  fin_cases k <;> simp [incFrame, incCode, cstore]

/-- Updating an increment stack commutes with embedding it through `incFrame`. -/
theorem incFrame_update (src : Bits) (S : Fin 2 → Bits) (k : Fin 2) (bits : Bits) :
    incFrame src (Function.update S k bits)
      = Function.update (incFrame src S) (incCode k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [incFrame, incCode, cstore, Function.update_apply]

/-- Removing the source word's leading bit gives the corresponding update of the length-counting
store. -/
theorem check_store (b : Bool) (rest cnt tmp : Bits) :
    Function.update (cstore (b::rest) cnt tmp) Slot.src rest = cstore rest cnt tmp := by
  funext j
  cases j <;> simp [cstore, Function.update_apply]

/-- Checking a nonempty source removes its leading bit and enters the increment subroutine. -/
theorem check_step (b : Bool) (rest cnt tmp : Bits) (v : Symbol) :
    TM2.step program ⟨some .check, v, cstore (b::rest) cnt tmp⟩ =
      some ⟨some (.inc .carry), some b, cstore rest cnt tmp⟩ := by
  simp [TM2.step, program, TM2.stepAux, cstore]
  exact check_store b rest cnt tmp

/-- Checking an empty source enters the done label and clears the saved bit. -/
theorem check_empty (cnt tmp : Bits) (v : Symbol) :
    TM2.step program ⟨some .check, v, cstore [] cnt tmp⟩ =
      some ⟨some .done, none, cstore [] cnt tmp⟩ := by
  simp [TM2.step, program, TM2.stepAux, cstore]

/-- One source-checking step has clock at most `2 * src.length + 10`. -/
theorem check_step_clock (src cnt tmp : Bits) (v : Symbol) :
    Stacks.stackRunClock program 1 ⟨some .check, v, cstore src cnt tmp⟩ ≤
      2*src.length + 10 := by
  cases src with
  | nil => simp [Stacks.stackRunClock, program, TM2.step, Stacks.stackClock, cstore]
  | cons b rest =>
    simp only [Stacks.stackRunClock, program, TM2.step, TM2.stepAux, Stacks.stackClock,
      cstore, Function.update_apply, List.head?_cons, List.tail_cons, Option.isSome_some,
      if_true, List.length_cons]
    omega

/-- The length-counting program's done label halts in one step without changing the local state
or stacks. -/
theorem done_run (src cnt tmp : Bits) (v : Symbol) :
    Stacks.stackRun program 1 ⟨some .done, v, cstore src cnt tmp⟩ =
      some ⟨none, v, cstore src cnt tmp⟩ := by
  simp [Stacks.stackRun, program, TM2.step]

/-- The increment subroutine updates the length counter and returns to checking the source, with
clock at most `50 * (1 + cnt.length) ^ 2`. -/
theorem inc_call (src cnt : Bits) (v : Symbol) :
    ∃ ticks, Stacks.stackRun program ticks ⟨some (.inc .carry), v, cstore src cnt []⟩ =
      some ⟨some .check, none, cstore src (Increment.word cnt) []⟩ ∧
      Stacks.stackRunClock program ticks ⟨some (.inc .carry), v, cstore src cnt []⟩ ≤
        50*(1+cnt.length)^2 := by
  obtain ⟨ticks, _, hr, hc⟩ := Increment.complete cnt [] v
  simp only [List.length_nil, Nat.add_zero] at hc
  obtain ⟨hN, hNC⟩ := StackCall.execution incCode Label.inc .check id (fun _ v => v)
    (incFrame src) (incFrame_at src) (incFrame_update src) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Increment.program program (fun _ => rfl) v ticks _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, Stacks.stackPair_zero, Stacks.stackPair_one,
    incFrame, cstore, List.reverse_nil, List.nil_append, List.append_nil] at hN hNC
  exact ⟨ticks, hN, hNC.trans_le hc⟩

/-- Binary increment increases the length of a word by at most one. -/
theorem word_length_le (cnt : Bits) :
    (Increment.word cnt).length ≤ cnt.length + 1 := by
  induction cnt with
  | nil => simp [Increment.word]
  | cons b rest ih =>
    cases b with
    | false => simp [Increment.word]
    | true =>
      simp only [Increment.word, List.length_cons]
      omega

/-- The counting loop consumes `w` and increments the initial counter `w.length` times before
reaching the done label, with the displayed clock bound. -/
theorem count_loop (w cnt : Bits) (v : Symbol) :
    ∃ ticks,
      Stacks.stackRun program ticks ⟨some .check, v, cstore w cnt []⟩ =
        some ⟨some .done, none, cstore [] ((Increment.word^[w.length]) cnt) []⟩ ∧
      Stacks.stackRunClock program ticks ⟨some .check, v, cstore w cnt []⟩ ≤
        (w.length+1)*(20+50*(2+cnt.length+w.length)^2) := by
  induction w generalizing cnt v with
  | nil =>
    have hstep := check_empty cnt [] v
    have hrun : Stacks.stackRun program 1 ⟨some .check, v, cstore [] cnt []⟩ =
        some ⟨some .done, none, cstore [] ((Increment.word^[0]) cnt) []⟩ := by
      simpa [Stacks.stackRun, hstep]
    refine ⟨1, hrun, ?_⟩
    have h1c := check_step_clock [] cnt [] v
    simp only [List.length_nil, Nat.zero_add, Nat.add_zero, Nat.one_mul] at h1c ⊢
    nlinarith [sq_nonneg (2+cnt.length)]
  | cons b w ih =>
    have hstep := check_step b w cnt [] v
    obtain ⟨t2, h2, h2c⟩ := inc_call w cnt (some b)
    obtain ⟨t3, h3, h3c⟩ := ih (Increment.word cnt) none
    have hstepRun : Stacks.stackRun program 1 ⟨some .check, v, cstore (b::w) cnt []⟩ =
        some ⟨some (.inc .carry), some b, cstore w cnt []⟩ := by
      simp [Stacks.stackRun, hstep]
    have hrun : Stacks.stackRun program (1+(t2+t3))
        ⟨some .check, v, cstore (b::w) cnt []⟩ =
        some ⟨some .done, none, cstore [] ((Increment.word^[(b::w).length]) cnt) []⟩ := by
      rw [Stacks.run_add, hstepRun, Option.bind_some, Stacks.run_add, h2, Option.bind_some]
      simpa only [List.length_cons, Function.iterate_succ_apply] using! h3
    refine ⟨1+(t2+t3), hrun, ?_⟩
    have hs1 := Stacks.clock_add program 1 (t2+t3) _ _ hstepRun
    have hs2 := Stacks.clock_add program t2 t3 _ _ h2
    have h1c := check_step_clock (b::w) cnt [] v
    have hkey : (20+50*(2+(Increment.word cnt).length+w.length)^2)
        ≤ (20+50*(2+cnt.length+(w.length+1))^2) := by
      have hle : 2+(Increment.word cnt).length+w.length ≤ 2+cnt.length+(w.length+1) := by
        have hwl := word_length_le cnt
        omega
      have h0 : (0:ℕ) ≤ 2+(Increment.word cnt).length+w.length := Nat.zero_le _
      have h0' : (0:ℕ) ≤ 2+cnt.length+(w.length+1) := Nat.zero_le _
      nlinarith only [hle, h0, h0']
    have hstepA := Nat.mul_le_mul_left (w.length+1) hkey
    have hsum : (w.length+1)*(20+50*(2+cnt.length+(w.length+1))^2)
        + 50*(1+cnt.length)^2 + 2*(w.length+1) + 10
        ≤ (w.length+2)*(20+50*(2+cnt.length+(w.length+1))^2) := by
      have h0 : (0:ℕ) ≤ w.length := Nat.zero_le _
      have h1 : (0:ℕ) ≤ cnt.length := Nat.zero_le _
      nlinarith [sq_nonneg (w.length), mul_nonneg h0 h1, h0, h1]
    simp only [List.length_cons] at h1c h2c h3c hs1 hs2 hstepA hsum ⊢
    nlinarith only [h1c, h2c, h3c, hs1, hs2, hstepA, hsum]

/-- Starting with an empty counter, the counting program halts with the canonical binary word
for `w.length`, with the displayed cubic clock bound. -/
theorem count_run (w : Bits) (v : Symbol) :
    ∃ ticks, Stacks.stackRun program ticks ⟨some .check, v, cstore w [] []⟩ =
      some ⟨none, none, cstore [] w.length.bits []⟩ ∧
      Stacks.stackRunClock program ticks ⟨some .check, v, cstore w [] []⟩ ≤
        (w.length+1)*(20+50*(2+w.length)^2)+1 := by
  obtain ⟨ticks, hrun, hc⟩ := count_loop w [] v
  have hnil : (Increment.word^[w.length]) ([] : Bits) = w.length.bits := by
    simpa using! succIterate_bits w.length 0
  have hdone : Stacks.stackRun program (ticks+1) ⟨some .check, v, cstore w [] []⟩ =
      some ⟨none, none, cstore [] w.length.bits []⟩ := by
    rw [Stacks.run_add, hrun, Option.bind_some, hnil]
    exact done_run [] w.length.bits [] none
  refine ⟨ticks+1, hdone, ?_⟩
  have hs := Stacks.clock_add program ticks 1 _ _ hrun
  have hpc : Stacks.stackRunClock program 1
      ⟨some .done, none, cstore [] ((Increment.word^[w.length]) ([] : Bits)) []⟩ = 1 := by
    simp [Stacks.stackRunClock, program, TM2.step, Stacks.stackClock]
  simp only [List.length_nil, Nat.add_zero] at hc
  rw [hs, hpc]
  omega

end LengthCount

end LengthCount

section TotalParse

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM (Symbol)
open Turing

namespace ParseFramed

/-- Prepending bit `b` doubles the binary value of the tail and adds one exactly when `b` is
true. -/
theorem binaryValue_cons (b : Bool) (bs : Bits) :
    binaryValue (b :: bs) = 2 * binaryValue bs + (if b then 1 else 0) := rfl

/-- A word consisting entirely of false bits has binary value zero. -/
theorem binaryValue_replicate_false (m : ℕ) :
    binaryValue (List.replicate m false) = 0 := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [List.replicate_succ, binaryValue_cons, if_neg (by decide : ¬(false = true)), ih,
      Nat.mul_zero, Nat.add_zero]

/-- Appending false bits does not change the binary value of a word. -/
theorem binaryValue_pad (bs : Bits) (m : ℕ) :
    binaryValue (bs ++ List.replicate m false) = binaryValue bs := by
  induction bs with
  | nil => exact binaryValue_replicate_false m
  | cons b bs ih => rw [List.cons_append, binaryValue_cons, binaryValue_cons, ih]

/-- The binary length field following the unary prefix, truncated to the indicated width and
padded with false when necessary. -/
def fieldOf (input : Bits) : Bits :=
  (input.drop (countTrues input + 1)).take (countTrues input) ++
    List.replicate (countTrues input - (input.drop (countTrues input + 1)).length) false

/-- The length of `fieldOf input` equals the number of leading true bits of `input`. -/
theorem length_fieldOf (input : Bits) : (fieldOf input).length = countTrues input := by
  have h1 : ((input.drop (countTrues input + 1)).take (countTrues input)).length
      = min (countTrues input) (input.drop (countTrues input + 1)).length := List.length_take ..
  have h2 : (List.replicate (countTrues input - (input.drop (countTrues input + 1)).length)
      false).length = countTrues input - (input.drop (countTrues input + 1)).length :=
    List.length_replicate ..
  simp only [fieldOf, List.length_append, h1, h2]
  omega

/-- The binary value of `fieldOf input` equals the natural number returned by `natBitsSplit
input`. -/
theorem binaryValue_fieldOf (input : Bits) :
    binaryValue (fieldOf input) = (natBitsSplit input).1 := by
  simp only [fieldOf, natBitsSplit, binaryValue_pad]

/-- Framed splitting takes the decoded number of payload bits, pads missing bits with false, and
drops that many bits to obtain the suffix. -/
theorem frameSplit_eq (input : Bits) :
    frameSplit input =
      ((natBitsSplit input).2.take (natBitsSplit input).1 ++
        List.replicate ((natBitsSplit input).1 - (natBitsSplit input).2.length) false,
       (natBitsSplit input).2.drop (natBitsSplit input).1) := by
  rcases h : natBitsSplit input with ⟨n, body⟩
  simp [frameSplit, h]

/-- The payload returned by `frameSplit` is the decoded-length prefix padded with false if the
input is too short. -/
theorem frameSplit_take (input : Bits) :
    (frameSplit input).1 =
      (natBitsSplit input).2.take (natBitsSplit input).1 ++
        List.replicate ((natBitsSplit input).1 - (natBitsSplit input).2.length) false := by
  rw [frameSplit_eq]

/-- The suffix returned by `frameSplit` is obtained by dropping the decoded length from the
remaining input. -/
theorem frameSplit_drop (input : Bits) :
    (frameSplit input).2 = (natBitsSplit input).2.drop (natBitsSplit input).1 := by
  rw [frameSplit_eq]

/-- The payload returned by `frameSplit` has exactly the decoded natural-number length. -/
theorem length_frameSplit (input : Bits) :
    (frameSplit input).1.length = (natBitsSplit input).1 := by
  have h1 : ((natBitsSplit input).2.take (natBitsSplit input).1).length
      = min (natBitsSplit input).1 (natBitsSplit input).2.length := List.length_take ..
  have h2 : (List.replicate ((natBitsSplit input).1 - (natBitsSplit input).2.length)
      false).length = (natBitsSplit input).1 - (natBitsSplit input).2.length :=
    List.length_replicate ..
  rw [frameSplit_take, List.length_append, h1, h2]
  omega

/-- The unary parser halts on an empty source, clears the saved bit, and preserves the count
stack. -/
theorem unary_empty_step (count : Bits) (saved : Option Bool) :
    TM2.step Parsing.unaryProgram
      (⟨some 0, saved, Stacks.stackPair ([] : Bits) count⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) =
      some ⟨none, none, Stacks.stackPair [] count⟩ := by
  simp [Parsing.unaryProgram, TM2.step, TM2.stepAux, Stacks.stackPair, Function.update_apply]

/-- The unary parser halts after removing a leading false bit, saving that bit and preserving
the count stack. -/
theorem unary_false_step (s count : Bits) (saved : Option Bool) :
    TM2.step Parsing.unaryProgram
      (⟨some 0, saved, Stacks.stackPair (false :: s) count⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) =
      some ⟨none, some false, Stacks.stackPair s count⟩ := by
  simp [Parsing.unaryProgram, TM2.step, TM2.stepAux, Stacks.stackPair, Function.update_apply]

/-- The unary parser consumes the leading true run and its terminator when present, prefixing
that many true bits to the count stack. It runs for `countTrues s + 1` steps with the
displayed clock bound. -/
theorem unary_total : ∀ (s count : Bits) (saved : Option Bool),
    Stacks.stackRun Parsing.unaryProgram (countTrues s+1)
      (⟨some 0, saved, Stacks.stackPair s count⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) =
      some ⟨none, (s.drop (countTrues s)).head?,
        Stacks.stackPair (s.drop (countTrues s+1))
          (List.replicate (countTrues s) true ++ count)⟩ ∧
    Stacks.stackRunClock Parsing.unaryProgram (countTrues s+1)
      (⟨some 0, saved, Stacks.stackPair s count⟩ :
        TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) ≤
        (countTrues s+1)*(2*(s.length+count.length)+8)+4 := by
  intro s
  induction s with
  | nil =>
    intro count saved
    have hstep := unary_empty_step count saved
    refine ⟨?_, ?_⟩
    · simpa [countTrues, Stacks.stackRun, hstep]
    · have hc : Stacks.stackRunClock Parsing.unaryProgram 1
          (⟨some 0, saved, Stacks.stackPair ([] : Bits) count⟩ :
            TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) = 3 := by
        simp only [Stacks.stackRunClock, hstep]
        simp [Parsing.unaryProgram, Stacks.stackClock, Stacks.stackPair, List.tail_nil]
      have hle : (3:ℕ) ≤ (countTrues ([] : Bits)+1)*(2*(([] : Bits).length+count.length)+8)+4 := by
        simp only [countTrues, List.length_nil]; omega
      have hck : Stacks.stackRunClock Parsing.unaryProgram (countTrues ([] : Bits)+1)
          (⟨some 0, saved, Stacks.stackPair ([] : Bits) count⟩ :
            TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) =
          Stacks.stackRunClock Parsing.unaryProgram 1
            (⟨some 0, saved, Stacks.stackPair ([] : Bits) count⟩ :
              TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) := by
        simp only [countTrues]
      rw [hck, hc]
      exact hle
  | cons b s ih =>
    intro count saved
    cases b with
    | false =>
      have hstep := unary_false_step s count saved
      refine ⟨?_, ?_⟩
      · simpa [countTrues, Stacks.stackRun, hstep]
      · have hc : Stacks.stackRunClock Parsing.unaryProgram 1
            (⟨some 0, saved, Stacks.stackPair (false :: s) count⟩ :
              TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) =
            1+((false::s).length+(false::s).tail.length+2) := by
          simp only [Stacks.stackRunClock, hstep]
          simp [Parsing.unaryProgram, Stacks.stackClock, Stacks.stackPair]
        have hle : 1+((false::s).length+(false::s).tail.length+2)
            ≤ (countTrues (false::s)+1)*(2*((false::s).length+count.length)+8)+4 := by
          simp only [countTrues, Nat.zero_add, List.length_cons, List.tail_cons]; omega
        have hck : Stacks.stackRunClock Parsing.unaryProgram (countTrues (false::s)+1)
            (⟨some 0, saved, Stacks.stackPair (false :: s) count⟩ :
              TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) =
            Stacks.stackRunClock Parsing.unaryProgram 1
              (⟨some 0, saved, Stacks.stackPair (false :: s) count⟩ :
                TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) := by
          simp only [countTrues, Nat.zero_add]
        rw [hck, hc]
        exact hle
    | true =>
      obtain ⟨hI, hIC⟩ := ih (true::count) (some true)
      have hstep := Parsing.unary_step s count saved
      have hrun : Stacks.stackRun Parsing.unaryProgram (countTrues (true::s)+1)
          (⟨some 0, saved, Stacks.stackPair (true :: s) count⟩ :
            TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) =
          some ⟨none, ((true::s).drop (countTrues (true::s))).head?,
            Stacks.stackPair ((true::s).drop (countTrues (true::s)+1))
              (List.replicate (countTrues (true::s)) true ++ count)⟩ := by
        rw [show countTrues (true::s)+1 = 1+(countTrues s+1) by simp only [countTrues]; omega,
          Stacks.run_add, Stacks.run_one, hstep, Option.bind_some]
        simp only [countTrues, List.drop_succ_cons, List.replicate_succ, List.cons_append,
          Parsing.marker_cons]
        rw [Nat.add_comm 1 (countTrues s + 1), List.drop_succ_cons]
        exact hI
      have hstepRun : Stacks.stackRun Parsing.unaryProgram 1
          (⟨some 0, saved, Stacks.stackPair (true :: s) count⟩ :
            TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) =
          some ⟨some 0, some true, Stacks.stackPair s (true::count)⟩ := by
        rw [Stacks.run_one]; exact hstep
      have hs := Stacks.clock_add Parsing.unaryProgram 1 (countTrues s+1) _ _ hstepRun
      have h1 : Stacks.stackRunClock Parsing.unaryProgram 1
          (⟨some 0, saved, Stacks.stackPair (true :: s) count⟩ :
            TM2.Cfg (fun _ : Fin 2 => Bool) (Fin 1) (Option Bool)) =
          1+((true::s).length+(true::s).tail.length+2+(2*count.length+3)) := by
        simp only [Stacks.stackRunClock, hstep]
        simp [Parsing.unaryProgram, Stacks.stackClock, Stacks.stackPair]
      simp only [List.length_cons, List.tail_cons] at h1 hIC ⊢
      refine ⟨hrun, ?_⟩
      rw [show countTrues (true::s)+1 = 1+(countTrues s+1) by simp only [countTrues]; omega]
      simp only [h1] at hs
      nlinarith

/-- The field parser halts and clears the saved bit when its count stack is empty. -/
theorem field_empty_count (r out : Bits) (saved : Option Bool) :
    TM2.step Parsing.fieldProgram
      (⟨some 0, saved, Parsing.triple r [] out⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) =
      some ⟨none, none, Parsing.triple r [] out⟩ := by
  simp [Parsing.fieldProgram, TM2.step, TM2.stepAux, Parsing.triple]

/-- With a nonempty true count stack and empty input, the field parser removes one count bit and
pushes false to the output. -/
theorem field_nil_step (count out : Bits) (saved : Option Bool) :
    TM2.step Parsing.fieldProgram
      (⟨some 0, saved, Parsing.triple ([] : Bits) (true::count) out⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) =
      some ⟨some 0, none, Parsing.triple [] count (false::out)⟩ := by
  simp [Parsing.fieldProgram, TM2.step, TM2.stepAux, Parsing.triple, Function.update_apply]

/-- With a leading input bit and a nonempty true count stack, the field parser moves the bit to
output and removes one count bit. -/
theorem field_cons_step (b : Bool) (r count out : Bits) (saved : Option Bool) :
    TM2.step Parsing.fieldProgram
      (⟨some 0, saved, Parsing.triple (b::r) (true::count) out⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) =
      some ⟨some 0, some b, Parsing.triple r count (b::out)⟩ := by
  simp [Parsing.fieldProgram, TM2.step, TM2.stepAux, Parsing.triple, Function.update_apply]

/-- The field parser extracts `k` bits, pads missing bits with false, and prefixes the reversed
result to output in `k + 1` steps, with the displayed clock bound. -/
theorem field_total : ∀ (k : ℕ) (r out : Bits) (saved : Option Bool),
    Stacks.stackRun Parsing.fieldProgram (k+1)
      (⟨some 0, saved, Parsing.triple r (List.replicate k true) out⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) =
      some ⟨none, none, Parsing.triple (r.drop k) []
        ((r.take k ++ List.replicate (k - r.length) false).reverse ++ out)⟩ ∧
    Stacks.stackRunClock Parsing.fieldProgram (k+1)
      (⟨some 0, saved, Parsing.triple r (List.replicate k true) out⟩ :
        TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) ≤
        (k+1)*(2*(k+r.length+out.length)+10)+4 := by
  intro k
  induction k with
  | zero =>
    intro r out saved
    have hstep := field_empty_count r out saved
    refine ⟨?_, ?_⟩
    · simpa [Stacks.stackRun, hstep, List.replicate_zero]
    · have hc : Stacks.stackRunClock Parsing.fieldProgram 1
        (⟨some 0, saved, Parsing.triple r (List.replicate 0 true) out⟩ :
          TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) = 3 := by
        simp only [List.replicate_zero, Stacks.stackRunClock, hstep]
        simp [Parsing.fieldProgram, Stacks.stackClock, Parsing.triple, List.tail_nil]
      have hle : (3:ℕ) ≤ (0+1)*(2*(0+r.length+out.length)+10)+4 := by omega
      exact hc.le.trans hle
  | succ k ih =>
    intro r out saved
    cases r with
    | nil =>
      obtain ⟨hI, hIC⟩ := ih [] (false::out) (none : Option Bool)
      have hstep := field_nil_step (List.replicate k true) out saved
      have hstepRun : Stacks.stackRun Parsing.fieldProgram 1
          (⟨some 0, saved, Parsing.triple ([] : Bits) (List.replicate (k+1) true) out⟩ :
            TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) =
          some ⟨some 0, none, Parsing.triple [] (List.replicate k true) (false::out)⟩ := by
        rw [List.replicate_succ, Stacks.run_one]; exact hstep
      have hrun : Stacks.stackRun Parsing.fieldProgram ((k+1)+1)
          (⟨some 0, saved, Parsing.triple ([] : Bits) (List.replicate (k+1) true) out⟩ :
            TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) =
          some ⟨none, none, Parsing.triple (([] : Bits).drop (k+1)) []
            ((([] : Bits).take (k+1) ++ List.replicate (k+1 - ([] : Bits).length) false).reverse
              ++ out)⟩ := by
        rw [show (k+1)+1 = 1+(k+1) by omega, Stacks.run_add, hstepRun, Option.bind_some]
        have hI' := by
          simpa only [List.take_nil, List.drop_nil, List.nil_append, List.reverse_replicate,
            List.length_nil, Nat.sub_zero] using! hI
        simp only [List.take_nil, List.drop_nil, List.nil_append, List.reverse_replicate,
          List.length_nil, Nat.sub_zero]
        rw [List.replicate_succ', List.append_assoc, List.singleton_append]
        exact hI'
      have hs := Stacks.clock_add Parsing.fieldProgram 1 (k+1) _ _ hstepRun
      have h1 : Stacks.stackRunClock Parsing.fieldProgram 1
          (⟨some 0, saved, Parsing.triple ([] : Bits) (List.replicate (k+1) true) out⟩ :
            TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) ≤
          2*k+2*out.length+10 := by
        rw [List.replicate_succ]
        simp only [Stacks.stackRunClock, hstep]
        simp [Parsing.fieldProgram, Stacks.stackClock, Parsing.triple]
        omega
      have hkey : 2*k+2*out.length+10 ≤ 2*(k+out.length+1)+10 := by omega
      refine ⟨hrun, ?_⟩
      simp only [List.drop_nil, List.take_nil, List.nil_append, List.length_nil,
        Nat.sub_zero, List.reverse_replicate] at hs hIC h1
      simp only [List.drop_nil, List.take_nil, List.nil_append, List.length_nil,
        Nat.sub_zero, List.reverse_replicate]
      rw [Nat.add_comm 1 (k+1)] at hs
      simp only [List.length_cons] at hIC
      nlinarith only [hs, hIC, h1, hkey]
    | cons b r' =>
      obtain ⟨hI, hIC⟩ := ih r' (b::out) (some b)
      have hstep := field_cons_step b r' (List.replicate k true) out saved
      have hstepRun : Stacks.stackRun Parsing.fieldProgram 1
          (⟨some 0, saved, Parsing.triple (b::r') (List.replicate (k+1) true) out⟩ :
            TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) =
          some ⟨some 0, some b, Parsing.triple r' (List.replicate k true) (b::out)⟩ := by
        rw [List.replicate_succ, Stacks.run_one]; exact hstep
      have hrun : Stacks.stackRun Parsing.fieldProgram ((k+1)+1)
          (⟨some 0, saved, Parsing.triple (b::r') (List.replicate (k+1) true) out⟩ :
            TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) =
          some ⟨none, none, Parsing.triple ((b::r').drop (k+1)) []
            (((b::r').take (k+1) ++ List.replicate (k+1 - (b::r').length) false).reverse
              ++ out)⟩ := by
        rw [show (k+1)+1 = 1+(k+1) by omega, Stacks.run_add, hstepRun, Option.bind_some]
        simp only [List.drop_succ_cons, List.take_succ_cons, List.length_cons,
          List.cons_append]
        rw [show (k+1) - (r'.length+1) = k - r'.length by omega,
          List.reverse_cons, List.append_assoc, List.singleton_append]
        exact hI
      have hs := Stacks.clock_add Parsing.fieldProgram 1 (k+1) _ _ hstepRun
      have h1 : Stacks.stackRunClock Parsing.fieldProgram 1
          (⟨some 0, saved, Parsing.triple (b::r') (List.replicate (k+1) true) out⟩ :
            TM2.Cfg (fun _ : Fin 3 => Bool) (Fin 1) (Option Bool)) ≤
          2*k+2*r'.length+2*out.length+11 := by
        rw [List.replicate_succ]
        simp only [Stacks.stackRunClock, hstep]
        simp [Parsing.fieldProgram, Stacks.stackClock, Parsing.triple]
        omega
      refine ⟨hrun, ?_⟩
      simp only [List.drop_succ_cons, List.take_succ_cons, List.length_cons,
        Nat.add_sub_cancel] at hs hIC h1
      simp only [List.drop_succ_cons, List.take_succ_cons, List.length_cons,
        Nat.add_sub_cancel]
      rw [Nat.add_comm 1 (k+1)] at hs
      nlinarith only [hs, hIC, h1]

/-- The number of leading true bits of a word is at most its length. -/
theorem countTrues_le (s : Bits) : countTrues s ≤ s.length := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    cases b with
    | false => simp [countTrues] <;> omega
    | true => simp [countTrues] <;> omega

/-- A payload-extraction store update on empty parsing input pushes false to the intermediate
accumulator. -/
theorem tkbody_store_empty (raw num num2 spare acc1 acc : Bits) :
    Function.update (Function.update (pstore raw ([] : Bits) num num2 spare acc1 acc)
        PSlot.parse []) PSlot.acc1
      (false :: (Function.update (pstore raw ([] : Bits) num num2 spare acc1 acc)
        PSlot.parse []) PSlot.acc1)
      = pstore raw ([] : Bits) num num2 spare (false::acc1) acc := by
  funext j
  cases j <;> simp [pstore, Function.update_apply]

/-- A payload-extraction step pops the parsing head when present, pushes its value or false onto
the intermediate accumulator, and returns to counter decrement. -/
theorem tkbody_step_gen (raw s num num2 spare acc1 acc : Bits) (v : PLocal) :
    TM2.step parseProgram ⟨some .tkBody, v, pstore raw s num num2 spare acc1 acc⟩ =
      some ⟨some (.tk .borrow), (v.1, s.head?),
        pstore raw s.tail num num2 spare (s.head?.getD false :: acc1) acc⟩ := by
  cases s with
  | nil =>
    simp only [TM2.step, parseProgram, TM2.stepAux, pstore, List.head?_nil, List.tail_nil,
      Option.getD_none]
    rw [tkbody_store_empty]
  | cons b s' =>
    simp only [TM2.step, parseProgram, TM2.stepAux, pstore, List.head?_cons, List.tail_cons,
      Option.getD_some]
    rw [tkbody_store]

/-- A payload-extraction step on any parsing word has clock at most `2 * (s.length +
acc1.length) + 10`. -/
theorem tkbody_clock_gen (raw s num num2 spare acc1 acc : Bits) (v : PLocal) :
    Stacks.stackRunClock parseProgram 1
        ⟨some .tkBody, v, pstore raw s num num2 spare acc1 acc⟩ ≤
      2*(s.length+acc1.length)+10 := by
  cases s with
  | nil =>
    simp only [Stacks.stackRunClock, parseProgram, TM2.step, Stacks.stackClock, pstore,
      List.head?_nil, List.tail_nil, Option.getD_none, pstore_upd_parse_acc1, List.length_nil]
    omega
  | cons b s' =>
    simp only [Stacks.stackRunClock, parseProgram, TM2.step, Stacks.stackClock, pstore,
      List.head?_cons, List.tail_cons, Option.getD_some, pstore_upd_parse_acc1,
      List.length_cons]
    omega

/-- Taking a default-false head followed by a padded prefix of the tail equals the padded prefix
of length `k + 1`. -/
theorem take_pad_succ (k : ℕ) (s : Bits) :
    s.head?.getD false :: (s.tail.take k ++ List.replicate (k - s.tail.length) false)
      = s.take (k+1) ++ List.replicate ((k+1) - s.length) false := by
  cases s with
  | nil =>
    simp only [List.head?_nil, Option.getD_none, List.tail_nil, List.take_nil,
      List.length_nil, Nat.sub_zero, List.nil_append]
    exact (List.replicate_succ (n := k) (a := (false : Bool))).symm
  | cons b s' =>
    have h : k + 1 - (s'.length + 1) = k - s'.length := by omega
    simp [List.take_succ_cons, List.length_cons, List.cons_append, h]

set_option maxHeartbeats 1000000 in

/-- For counter value `k`, the extraction loop consumes `k` payload positions, pads missing bits
with false, and reaches reversal with the displayed clock bound. -/
theorem tk_loop_gen : ∀ (k : ℕ) (s numw acc1 raw num acc : Bits) (v : PLocal),
    binaryValue numw = k →
    ∃ ticks,
      Stacks.stackRun parseProgram ticks
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩ =
        some ⟨some (.flip 0), ((false,none), none),
          pstore raw (s.drop k) num (List.replicate numw.length true) []
            ((s.take k ++ List.replicate (k - s.length) false).reverse ++ acc1) acc⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩ ≤
        (2*k+4)*(10*(1+numw.length)^2
          +50*(1+s.length+acc1.length+k)^2+10) := by
  intro k
  induction k with
  | zero =>
    intro s numw acc1 raw num acc v hk
    obtain ⟨hD, hDC⟩ := tk_dec_zero s num numw acc1 raw acc v hk
    have hb := pbranch_step ((false,none), v.2)
      (pstore raw s num (List.replicate numw.length true) [] acc1 acc)
    have hc := clear_step ((false,none), v.2)
      (pstore raw s num (List.replicate numw.length true) [] acc1 acc)
    have hrun1 : Stacks.stackRun parseProgram ((2*numw.length+2)+1)
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩ =
        some ⟨some .clear, ((false,none), v.2),
          pstore raw s num (List.replicate numw.length true) [] acc1 acc⟩ := by
      rw [Stacks.run_add, hD, Option.bind_some]
      simpa only [pstore] using! hb
    have hrun : Stacks.stackRun parseProgram (((2*numw.length+2)+1)+1)
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩ =
        some ⟨some (.flip 0), ((false,none), none),
          pstore raw s num (List.replicate numw.length true) [] acc1 acc⟩ := by
      rw [Stacks.run_add, hrun1, Option.bind_some]
      simpa only [pstore] using! hc
    refine ⟨((2*numw.length+2)+1)+1, ?_, ?_⟩
    · simpa only [List.drop_zero, List.take_zero, Nat.zero_sub, List.replicate_zero,
        List.reverse_nil, List.nil_append] using! hrun
    · have hbc := pbranch_clock ((false,none), v.2)
        (pstore raw s num (List.replicate numw.length true) [] acc1 acc)
      have hcc := clear_clock ((false,none), v.2)
        (pstore raw s num (List.replicate numw.length true) [] acc1 acc)
      have hsB := Stacks.clock_add parseProgram ((2*numw.length+2)+1) 1
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩
        ⟨some .clear, ((false,none), v.2),
          pstore raw s num (List.replicate numw.length true) [] acc1 acc⟩ hrun1
      have hsA := Stacks.clock_add parseProgram (2*numw.length+2) 1
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩
        ⟨some .pbranch, ((false,none), v.2),
          pstore raw s num (List.replicate numw.length true) [] acc1 acc⟩ hD
      have hq1 : (0:ℕ) ≤ (1+numw.length)^2 := Nat.zero_le _
      have hq2 : (0:ℕ) ≤ (1+s.length+acc1.length+0)^2 := Nat.zero_le _
      nlinarith only [hsA, hsB, hDC, hbc, hcc, hq1, hq2]
  | succ k ih =>
    intro s numw acc1 raw num acc v hk
    have hp : 0 < binaryValue numw := by omega
    obtain ⟨decTicks, next, hlen, hval, hD, hDC⟩ :=
      tk_dec_positive s num numw acc1 raw acc v hp
    have hnext : binaryValue next = k := by omega
    have hb := pbranch_step ((true,none), v.2)
      (pstore raw s num next [] acc1 acc)
    have hrun1 : Stacks.stackRun parseProgram (decTicks+1)
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩ =
        some ⟨some .tkBody, ((true,none), v.2),
          pstore raw s num next [] acc1 acc⟩ := by
      rw [Stacks.run_add, hD, Option.bind_some]
      simpa only [pstore] using! hb
    have hrun2 : Stacks.stackRun parseProgram ((decTicks+1)+1)
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩ =
        some ⟨some (.tk .borrow), ((true,none), s.head?),
          pstore raw s.tail num next [] (s.head?.getD false :: acc1) acc⟩ := by
      rw [Stacks.run_add, hrun1, Option.bind_some]
      exact tkbody_step_gen raw s num next [] acc1 acc ((true,none), v.2)
    obtain ⟨iterTicks, hIrun, hIclock⟩ := ih s.tail next (s.head?.getD false :: acc1)
      raw num acc ((true,none), s.head?) hnext
    have hfull : Stacks.stackRun parseProgram (((decTicks+1)+1)+iterTicks)
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩ =
        some ⟨some (.flip 0), ((false,none), none),
          pstore raw (s.drop (k+1)) num (List.replicate numw.length true) []
            ((s.take (k+1) ++ List.replicate ((k+1) - s.length) false).reverse ++ acc1) acc⟩ := by
      rw [← take_pad_succ k s, List.reverse_cons, List.append_assoc, List.singleton_append,
        show s.drop (k+1) = s.tail.drop k by cases s <;> simp, ← hlen,
        Stacks.run_add, hrun2, Option.bind_some]
      exact hIrun
    refine ⟨((decTicks+1)+1)+iterTicks, hfull, ?_⟩
    have hbc := pbranch_clock ((true,none), v.2)
      (pstore raw s num next [] acc1 acc)
    have htb := tkbody_clock_gen raw s num next [] acc1 acc ((true,none), v.2)
    have hs3 := Stacks.clock_add parseProgram ((decTicks+1)+1) iterTicks
      ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩
      ⟨some (.tk .borrow), ((true,none), s.head?),
        pstore raw s.tail num next [] (s.head?.getD false :: acc1) acc⟩ hrun2
    have hs2 := Stacks.clock_add parseProgram (decTicks+1) 1
      ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩
      ⟨some .tkBody, ((true,none), v.2), pstore raw s num next [] acc1 acc⟩ hrun1
    have hs1 := Stacks.clock_add parseProgram decTicks 1
      ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩
      ⟨some .pbranch, ((true,none), v.2), pstore raw s num next [] acc1 acc⟩ hD
    rw [hlen] at hIclock
    have h1 : 1+s.tail.length+(s.head?.getD false :: acc1).length+k
        ≤ 1+s.length+acc1.length+(k+1) := by
      cases s <;> simp [List.length_cons, List.tail_cons, List.head?_cons, List.length_nil,
        List.tail_nil, List.head?_nil] <;> omega
    have h0 : (0:ℕ) ≤ 1+s.tail.length+(s.head?.getD false :: acc1).length+k := by
      cases s <;> simp [List.length_cons, List.tail_cons, List.head?_cons, List.length_nil,
        List.tail_nil, List.head?_nil] <;> omega
    have h0' : (0:ℕ) ≤ 1+s.length+acc1.length+(k+1) := by
      cases s <;> simp [List.length_cons, List.tail_cons, List.head?_cons, List.length_nil,
        List.tail_nil, List.head?_nil] <;> omega
    have hmono : (1+s.tail.length+(s.head?.getD false :: acc1).length+k)^2
        ≤ (1+s.length+acc1.length+(k+1))^2 := by
      nlinarith only [h1, h0, h0']
    have hmul : (2*k+4)*(10*(1+numw.length)^2
          +50*(1+s.tail.length+(s.head?.getD false :: acc1).length+k)^2+10)
        ≤ (2*k+4)*(10*(1+numw.length)^2
          +50*(1+s.length+acc1.length+(k+1))^2+10) := by
      have hm := Nat.mul_le_mul_left (2*k+4) hmono
      have he1 : (2*k+4)*(10*(1+numw.length)^2
            +50*(1+s.tail.length+(s.head?.getD false :: acc1).length+k)^2+10)
          = (2*k+4)*(10*(1+numw.length)^2)
            +(2*k+4)*(50*(1+s.tail.length+(s.head?.getD false :: acc1).length+k)^2)
            +(2*k+4)*10 := by ring
      have he2 : (2*k+4)*(10*(1+numw.length)^2
            +50*(1+s.length+acc1.length+(k+1))^2+10)
          = (2*k+4)*(10*(1+numw.length)^2)
            +(2*k+4)*(50*(1+s.length+acc1.length+(k+1))^2)
            +(2*k+4)*10 := by ring
      rw [he1, he2]
      gcongr <;> linarith
    have hlin : 2*s.length+2*acc1.length+12
        ≤ 100*(1+s.length+acc1.length+(k+1))^2 := by
      have h1' : s.length ≤ 1+s.length+acc1.length+(k+1) := by omega
      have h2' : acc1.length ≤ 1+s.length+acc1.length+(k+1) := by omega
      have h3' : (1:ℕ) ≤ 1+s.length+acc1.length+(k+1) := by omega
      have hs1' : (1+s.length+acc1.length+(k+1))*(1+s.length+acc1.length+(k+1))
          ≥ (1+s.length+acc1.length+(k+1)) := by
        nlinarith only [h3']
      nlinarith only [h1', h2', hs1']
    have htq : (2*(k+1)+4)*(10*(1+numw.length)^2
          +50*(1+s.length+acc1.length+(k+1))^2+10)
        = (2*k+4)*(10*(1+numw.length)^2
            +50*(1+s.length+acc1.length+(k+1))^2+10)
          +20*(1+numw.length)^2
          +100*(1+s.length+acc1.length+(k+1))^2+20 := by ring
    have hqq : (1:ℕ) ≤ (1+numw.length)^2 := by
      nlinarith [show (0:ℕ) ≤ numw.length from Nat.zero_le _]
    have hc1 : Stacks.stackRunClock parseProgram (((decTicks+1)+1)+iterTicks)
        ⟨some (.tk .borrow), v, pstore raw s num numw [] acc1 acc⟩ ≤
        10*(1+numw.length)^2+2+(2*s.length+2*acc1.length+12)
          +(2*k+4)*(10*(1+numw.length)^2
            +50*(1+s.length+acc1.length+(k+1))^2+10) := by
      have hiter := hIclock.trans hmul
      linarith only [hs1, hs2, hs3, hDC, hbc, htb, hiter]
    rw [htq]
    linarith only [hc1, hlin, hqq]

set_option maxHeartbeats 1000000 in

/-- The length-reversal phase moves `num` into the empty `num2` stack in reverse order and
reaches counter decrement with clock at most `9 * (1 + num.length) ^ 2`. -/
theorem nflip_total (ps num spare acc1 acc : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.nflip 0), ((false,none),none), pstore [] ps num [] spare acc1 acc⟩ =
      some ⟨some (.tk .borrow), ((false,none),none),
        pstore [] ps [] num.reverse spare acc1 acc⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.nflip 0), ((false,none),none), pstore [] ps num [] spare acc1 acc⟩ ≤
        9*(1+num.length)^2 := by
  have hr := Stacks.transfer_run num [] none
  obtain ⟨hN, hNC⟩ := StackCall.execution nflipCode PLabel.nflip (.tk .borrow)
    Prod.snd (fun v b => (v.1, b))
    (nflipFrame [] ps spare acc1 acc) (nflipFrame_at [] ps spare acc1 acc)
    (nflipFrame_update [] ps spare acc1 acc) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Stacks.transferProgram parseProgram (fun _ => rfl) ((false,none),none)
    (num.length+1) _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one, nflipFrame,
    pstore, List.reverse_nil, List.nil_append, List.append_nil] at hN hNC
  refine ⟨num.length+1, hN, ?_⟩
  have hb := Stacks.transfer_clock num [] none
  simp only [List.length_nil, Nat.add_zero] at hb
  have h0 : (0:ℕ) ≤ num.length := Nat.zero_le _
  nlinarith only [hNC, hb, h0]

set_option maxHeartbeats 1000000 in

/-- On arbitrary input, the natural-number parser returns the suffix from `natBitsSplit` and
prefixes the reversed padded field to output in `2 * countTrues s + 3` steps, with the
stated quadratic clock bound. -/
theorem natProgram_total (s out : Bits) (saved : Option Bool) :
    Stacks.stackRun Parsing.natProgram (2*countTrues s+3)
      ⟨some 0, saved, Parsing.triple s [] out⟩ =
      some ⟨none, none, Parsing.triple (natBitsSplit s).2 [] ((fieldOf s).reverse ++ out)⟩ ∧
    Stacks.stackRunClock Parsing.natProgram (2*countTrues s+3)
      ⟨some 0, saved, Parsing.triple s [] out⟩ ≤ 40*(1+s.length+out.length)^2 := by
  have hcodeU : ∀ l : Fin 1, Parsing.natProgram 0
      = StackCall.stmt Fin.castSucc (fun _ : Fin 1 => (0 : Fin 3)) 1 id (fun _ v => v)
          (Parsing.unaryProgram l) := by intro l; rfl
  have hcodeF : ∀ l : Fin 1, Parsing.natProgram 1
      = StackCall.stmt id (fun _ : Fin 1 => (1 : Fin 3)) 2 id (fun _ v => v)
          (Parsing.fieldProgram l) := by intro l; rfl
  obtain ⟨hu, huc⟩ := unary_total s [] saved
  obtain ⟨hN, hNC⟩ := StackCall.execution Fin.castSucc (fun _ : Fin 1 => (0 : Fin 3)) 1
    id (fun _ v => v) (Parsing.unaryFrame out) (Parsing.unaryFrame_at out)
    (Parsing.unaryFrame_update out) (fun _ _ => rfl) (fun _ _ _ => rfl)
    Parsing.unaryProgram Parsing.natProgram hcodeU saved (countTrues s+1) _ _ hu
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Parsing.unaryFrame, Stacks.stackPair_zero, Stacks.stackPair_one,
    List.append_nil] at hN hNC
  obtain ⟨hf, hfc⟩ := field_total (countTrues s) (s.drop (countTrues s+1)) out
    ((s.drop (countTrues s)).head?)
  obtain ⟨hF, hFC⟩ := StackCall.execution id (fun _ : Fin 1 => (1 : Fin 3)) 2
    id (fun _ v => v) id (fun _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ => rfl) Parsing.fieldProgram Parsing.natProgram hcodeF
    ((s.drop (countTrues s)).head?) (countTrues s+1) _ _ hf
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq] at hF hFC
  have htot : 2*countTrues s+3 = ((countTrues s+1)+(countTrues s+1))+1 := by omega
  have hUF : Stacks.stackRun Parsing.natProgram ((countTrues s+1)+(countTrues s+1))
      ⟨some 0, saved, Parsing.triple s [] out⟩ =
      some ⟨some 2, none, Parsing.triple (natBitsSplit s).2 [] ((fieldOf s).reverse ++ out)⟩ := by
    rw [Stacks.run_add, hN, Option.bind_some]
    exact hF
  have hD : Stacks.stackRun Parsing.natProgram 1
      ⟨some 2, none, Parsing.triple (natBitsSplit s).2 [] ((fieldOf s).reverse ++ out)⟩ =
      some ⟨none, none, Parsing.triple (natBitsSplit s).2 [] ((fieldOf s).reverse ++ out)⟩ := by
    simp [Stacks.stackRun, TM2.step, Parsing.natProgram, TM2.stepAux]
  have hfull : Stacks.stackRun Parsing.natProgram (2*countTrues s+3)
      ⟨some 0, saved, Parsing.triple s [] out⟩ =
      some ⟨none, none, Parsing.triple (natBitsSplit s).2 [] ((fieldOf s).reverse ++ out)⟩ := by
    rw [htot, Stacks.run_add, hUF, Option.bind_some]
    exact hD
  refine ⟨hfull, ?_⟩
  have hsU := Stacks.clock_add Parsing.natProgram (countTrues s+1) (countTrues s+1)
    ⟨some 0, saved, Parsing.triple s [] out⟩
    ⟨some 1, (s.drop (countTrues s)).head?,
      Parsing.triple (s.drop (countTrues s+1)) (List.replicate (countTrues s) true) out⟩ hN
  have hsUF := Stacks.clock_add Parsing.natProgram ((countTrues s+1)+(countTrues s+1)) 1
    ⟨some 0, saved, Parsing.triple s [] out⟩
    ⟨some 2, none, Parsing.triple (natBitsSplit s).2 [] ((fieldOf s).reverse ++ out)⟩ hUF
  have hDc : Stacks.stackRunClock Parsing.natProgram 1
      ⟨some 2, none, Parsing.triple (natBitsSplit s).2 [] ((fieldOf s).reverse ++ out)⟩ = 1 := by
    simp [Stacks.stackRunClock, TM2.step, Parsing.natProgram, TM2.stepAux, Stacks.stackClock]
  have bU : Stacks.stackRunClock Parsing.natProgram (countTrues s+1)
      ⟨some 0, saved, Parsing.triple s [] out⟩ ≤ (countTrues s+1)*(2*s.length+8)+4 := by
    rw [hNC]
    simpa only [List.length_nil, Nat.add_zero] using! huc
  have bF : Stacks.stackRunClock Parsing.natProgram (countTrues s+1)
      ⟨some 1, (s.drop (countTrues s)).head?,
        Parsing.triple (s.drop (countTrues s+1)) (List.replicate (countTrues s) true) out⟩ ≤
      (countTrues s+1)*(2*(countTrues s+(s.drop (countTrues s+1)).length+out.length)+10)+4 := by
    rw [hFC]
    exact hfc
  have hk : countTrues s ≤ s.length := countTrues_le s
  have hd : (s.drop (countTrues s+1)).length ≤ s.length := by
    have h : (s.drop (countTrues s+1)).length = s.length - (countTrues s+1) := List.length_drop
    omega
  have hmU : (countTrues s+1)*(2*s.length+8) ≤ (s.length+1)*(2*s.length+8) :=
    Nat.mul_le_mul_right (2*s.length+8) (Nat.succ_le_succ hk)
  have hmF : (countTrues s+1)*(2*(countTrues s+(s.drop (countTrues s+1)).length+out.length)+10)
      ≤ (s.length+1)*(2*(s.length+s.length+out.length)+10) := by
    have h1 : countTrues s+1 ≤ s.length+1 := Nat.succ_le_succ hk
    have h2 : 2*(countTrues s+(s.drop (countTrues s+1)).length+out.length)+10
        ≤ 2*(s.length+s.length+out.length)+10 := by omega
    exact Nat.mul_le_mul h1 h2
  have bU' : Stacks.stackRunClock Parsing.natProgram (countTrues s+1)
      ⟨some 0, saved, Parsing.triple s [] out⟩ ≤ (s.length+1)*(2*s.length+8)+4 := by
    have h := Nat.add_le_add_right hmU 4
    linarith only [bU, h]
  have bF' : Stacks.stackRunClock Parsing.natProgram (countTrues s+1)
      ⟨some 1, (s.drop (countTrues s)).head?,
        Parsing.triple (s.drop (countTrues s+1)) (List.replicate (countTrues s) true) out⟩ ≤
      (s.length+1)*(2*(s.length+s.length+out.length)+10)+4 := by
    have h := Nat.add_le_add_right hmF 4
    linarith only [bF, h]
  have hfin : (s.length+1)*(2*s.length+8)+4
      +(s.length+1)*(2*(s.length+s.length+out.length)+10)+4+1
      ≤ 40*(1+s.length+out.length)^2 := by
    nlinarith
  rw [htot, hsUF, hDc, hsU]
  linarith only [bU', bF', hfin]

set_option maxHeartbeats 1000000 in

/-- The embedded natural-number parser splits arbitrary input and stores the reversed padded
length field before entering length reversal, with clock at most `40 * (1 + s.length) ^ 2`. -/
theorem nat_total (s : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.nat 0), ((false,none),none), pstore [] s [] [] [] [] []⟩ =
      some ⟨some (.nflip 0), ((false,none),none),
        pstore [] (natBitsSplit s).2 (fieldOf s).reverse [] [] [] []⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.nat 0), ((false,none),none), pstore [] s [] [] [] [] []⟩ ≤
        40*(1+s.length)^2 := by
  obtain ⟨hr, hrc⟩ := natProgram_total s [] none
  obtain ⟨hN, hNC⟩ := StackCall.execution natCode PLabel.nat (.nflip 0)
    Prod.snd (fun v b => (v.1, b))
    (natFrame [] [] [] []) (natFrame_at [] [] [] []) (natFrame_update [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    Parsing.natProgram parseProgram (fun _ => rfl) ((false,none),none)
    (2*countTrues s+3) _ _ hr
  simp only [StackCall.cfg, Option.map_some, Option.getD_some, Option.map_none,
    Option.getD_none, id_eq, Stacks.stackPair_zero, Stacks.stackPair_one,
    Parsing.triple_two, Parsing.triple_one, Parsing.triple_zero, natFrame, pstore,
    List.append_nil, List.reverse_nil, List.nil_append] at hN hNC
  refine ⟨2*countTrues s+3, hN, ?_⟩
  simp only [List.length_nil, Nat.add_zero] at hrc
  exact hNC.trans_le hrc

/-- An explicit clock allowance for parsing an arbitrary framed input from the initial raw-input
transfer phase. -/
def parseCost (input : Bits) : ℕ :=
  9*(1+input.length)^2 + 40*(1+input.length)^2 + 9*(1+countTrues input)^2
    + (2*(natBitsSplit input).1+4)*(10*(1+countTrues input)^2
      +50*(1+(natBitsSplit input).2.length+(natBitsSplit input).1)^2+10)
    + 9*(1+(frameSplit input).1.length)^2 + 1

/-- An explicit clock allowance for parsing an arbitrary framed input starting directly at
natural-number parsing. -/
def parseCostFrom (input : Bits) : ℕ :=
  40*(1+input.length)^2 + 9*(1+countTrues input)^2
    + (2*(natBitsSplit input).1+4)*(10*(1+countTrues input)^2
      +50*(1+(natBitsSplit input).2.length+(natBitsSplit input).1)^2+10)
    + 9*(1+(frameSplit input).1.length)^2 + 1

set_option maxHeartbeats 1000000 in

/-- The framed parser terminates on every raw input with the payload and suffix specified by
`frameSplit`, and its clock is bounded by `parseCost input`. -/
theorem parseFramed_total (input : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.read 0), ((false,none),none), pstore input.reverse [] [] [] [] [] []⟩ =
      some ⟨none, ((false,none),none),
        pstore [] (frameSplit input).2 [] (List.replicate (countTrues input) true) [] []
          (frameSplit input).1⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.read 0), ((false,none),none), pstore input.reverse [] [] [] [] [] []⟩ ≤
        parseCost input := by
  obtain ⟨t1, h1, h1c⟩ := read_call input.reverse
  obtain ⟨t2, h2, h2c⟩ := nat_total input
  obtain ⟨t3, h3, h3c⟩ := nflip_total (natBitsSplit input).2 ((fieldOf input).reverse) [] [] []
  obtain ⟨t4, h4, h4c⟩ := tk_loop_gen (binaryValue (fieldOf input)) ((natBitsSplit input).2)
    (fieldOf input) [] [] [] [] ((false,none),none) rfl
  obtain ⟨t5, h5, h5c⟩ := flip_call
    (((natBitsSplit input).2.take (binaryValue (fieldOf input))
        ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
          false).reverse)
    [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
    (List.replicate (fieldOf input).length true) []
  have h1' : Stacks.stackRun parseProgram t1
      ⟨some (.read 0), ((false,none),none), pstore input.reverse [] [] [] [] [] []⟩ =
      some ⟨some (.nat 0), ((false,none),none), pstore [] input [] [] [] [] []⟩ := by
    simpa only [List.reverse_reverse] using! h1
  have h12 : Stacks.stackRun parseProgram (t1+t2)
      ⟨some (.read 0), ((false,none),none), pstore input.reverse [] [] [] [] [] []⟩ =
      some ⟨some (.nflip 0), ((false,none),none),
        pstore [] (natBitsSplit input).2 (fieldOf input).reverse [] [] [] []⟩ := by
    rw [Stacks.run_add, h1', Option.bind_some]
    exact h2
  have h123 : Stacks.stackRun parseProgram (t1+t2+t3)
      ⟨some (.read 0), ((false,none),none), pstore input.reverse [] [] [] [] [] []⟩ =
      some ⟨some (.tk .borrow), ((false,none),none),
        pstore [] (natBitsSplit input).2 [] (fieldOf input) [] [] []⟩ := by
    rw [Stacks.run_add, h12, Option.bind_some]
    simpa only [List.reverse_reverse] using! h3
  have h1234 : Stacks.stackRun parseProgram ((t1+t2+t3)+t4)
      ⟨some (.read 0), ((false,none),none), pstore input.reverse [] [] [] [] [] []⟩ =
      some ⟨some (.flip 0), ((false,none),none),
        pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
          (List.replicate (fieldOf input).length true) []
          (((natBitsSplit input).2.take (binaryValue (fieldOf input))
            ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
              false).reverse) []⟩ := by
    rw [Stacks.run_add, h123, Option.bind_some]
    simpa only [List.append_nil] using! h4
  have h12345 : Stacks.stackRun parseProgram (((t1+t2+t3)+t4)+t5)
      ⟨some (.read 0), ((false,none),none), pstore input.reverse [] [] [] [] [] []⟩ =
      some ⟨some .pdone, ((false,none),none),
        pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
          (List.replicate (fieldOf input).length true) [] []
          (((natBitsSplit input).2.take (binaryValue (fieldOf input))
            ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
              false).reverse).reverse⟩ := by
    rw [Stacks.run_add, h1234, Option.bind_some]
    exact h5
  have hfull : Stacks.stackRun parseProgram (((((t1+t2)+t3)+t4)+t5)+1)
      ⟨some (.read 0), ((false,none),none), pstore input.reverse [] [] [] [] [] []⟩ =
      some ⟨none, ((false,none),none),
        pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
          (List.replicate (fieldOf input).length true) [] []
          (((natBitsSplit input).2.take (binaryValue (fieldOf input))
            ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
              false).reverse).reverse⟩ := by
    rw [Stacks.run_add, h12345, Option.bind_some]
    exact pdone_run _
  refine ⟨((((t1+t2)+t3)+t4)+t5)+1, ?_, ?_⟩
  · simpa only [binaryValue_fieldOf, length_fieldOf, List.reverse_reverse, frameSplit_take,
      frameSplit_drop] using! hfull
  · have hs12 := Stacks.clock_add parseProgram t1 t2 _ _ h1'
    have hs3 := Stacks.clock_add parseProgram (t1+t2) t3 _ _ h12
    have hs4 := Stacks.clock_add parseProgram ((t1+t2)+t3) t4 _ _ h123
    have hs5 := Stacks.clock_add parseProgram (((t1+t2)+t3)+t4) t5 _ _ h1234
    have hsf := Stacks.clock_add parseProgram ((((t1+t2)+t3)+t4)+t5) 1 _ _ h12345
    have hpc : Stacks.stackRunClock parseProgram 1
        ⟨some .pdone, ((false,none),none),
          pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input)))
            [] (List.replicate (fieldOf input).length true) [] []
            (((natBitsSplit input).2.take (binaryValue (fieldOf input))
              ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
                false).reverse).reverse⟩ ≤ 1 :=
      pdone_clock _
    have h1c' : Stacks.stackRunClock parseProgram t1
        ⟨some (.read 0), ((false,none),none), pstore input.reverse [] [] [] [] [] []⟩ ≤
        9*(1+input.length)^2 := by
      simpa only [List.length_reverse] using! h1c
    have h3c' : Stacks.stackRunClock parseProgram t3
        ⟨some (.nflip 0), ((false,none),none),
          pstore [] (natBitsSplit input).2 (fieldOf input).reverse [] [] [] []⟩ ≤
        9*(1+countTrues input)^2 := by
      simpa only [List.length_reverse, length_fieldOf] using! h3c
    have h4c' : Stacks.stackRunClock parseProgram t4
        ⟨some (.tk .borrow), ((false,none),none),
          pstore [] (natBitsSplit input).2 [] (fieldOf input) [] [] []⟩ ≤
        (2*(natBitsSplit input).1+4)*(10*(1+countTrues input)^2
          +50*(1+(natBitsSplit input).2.length+(natBitsSplit input).1)^2+10) := by
      simpa only [List.length_nil, Nat.add_zero, binaryValue_fieldOf, length_fieldOf] using! h4c
    have h5c' : Stacks.stackRunClock parseProgram t5
        ⟨some (.flip 0), ((false,none),none),
          pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
            (List.replicate (fieldOf input).length true) []
            (((natBitsSplit input).2.take (binaryValue (fieldOf input))
              ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
                false).reverse) []⟩ ≤
        9*(1+(frameSplit input).1.length)^2 := by
      simpa only [List.length_reverse, binaryValue_fieldOf, ← frameSplit_take] using! h5c
    simp only [parseCost]
    linarith only [hs12, hs3, hs4, hs5, hsf, h1c', h2c, h3c', h4c', h5c', hpc]

set_option maxHeartbeats 1000000 in

/-- Starting directly at natural-number parsing, the framed parser terminates on every input
with the payload and suffix specified by `frameSplit`, and its clock is bounded by
`parseCostFrom input`. -/
theorem parseFramed_total_from (input : Bits) :
    ∃ ticks, Stacks.stackRun parseProgram ticks
        ⟨some (.nat 0), ((false,none),none), pstore [] input [] [] [] [] []⟩ =
      some ⟨none, ((false,none),none),
        pstore [] (frameSplit input).2 [] (List.replicate (countTrues input) true) [] []
          (frameSplit input).1⟩ ∧
      Stacks.stackRunClock parseProgram ticks
        ⟨some (.nat 0), ((false,none),none), pstore [] input [] [] [] [] []⟩ ≤
        parseCostFrom input := by
  obtain ⟨t2, h2, h2c⟩ := nat_total input
  obtain ⟨t3, h3, h3c⟩ := nflip_total (natBitsSplit input).2 ((fieldOf input).reverse) [] [] []
  obtain ⟨t4, h4, h4c⟩ := tk_loop_gen (binaryValue (fieldOf input)) ((natBitsSplit input).2)
    (fieldOf input) [] [] [] [] ((false,none),none) rfl
  obtain ⟨t5, h5, h5c⟩ := flip_call
    (((natBitsSplit input).2.take (binaryValue (fieldOf input))
        ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
          false).reverse)
    [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
    (List.replicate (fieldOf input).length true) []
  have h23 : Stacks.stackRun parseProgram (t2+t3)
      ⟨some (.nat 0), ((false,none),none), pstore [] input [] [] [] [] []⟩ =
      some ⟨some (.tk .borrow), ((false,none),none),
        pstore [] (natBitsSplit input).2 [] (fieldOf input) [] [] []⟩ := by
    rw [Stacks.run_add, h2, Option.bind_some]
    simpa only [List.reverse_reverse] using! h3
  have h234 : Stacks.stackRun parseProgram ((t2+t3)+t4)
      ⟨some (.nat 0), ((false,none),none), pstore [] input [] [] [] [] []⟩ =
      some ⟨some (.flip 0), ((false,none),none),
        pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
          (List.replicate (fieldOf input).length true) []
          (((natBitsSplit input).2.take (binaryValue (fieldOf input))
            ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
              false).reverse) []⟩ := by
    rw [Stacks.run_add, h23, Option.bind_some]
    simpa only [List.append_nil] using! h4
  have h2345 : Stacks.stackRun parseProgram (((t2+t3)+t4)+t5)
      ⟨some (.nat 0), ((false,none),none), pstore [] input [] [] [] [] []⟩ =
      some ⟨some .pdone, ((false,none),none),
        pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
          (List.replicate (fieldOf input).length true) [] []
          (((natBitsSplit input).2.take (binaryValue (fieldOf input))
            ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
              false).reverse).reverse⟩ := by
    rw [Stacks.run_add, h234, Option.bind_some]
    exact h5
  have hfull : Stacks.stackRun parseProgram ((((t2+t3)+t4)+t5)+1)
      ⟨some (.nat 0), ((false,none),none), pstore [] input [] [] [] [] []⟩ =
      some ⟨none, ((false,none),none),
        pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
          (List.replicate (fieldOf input).length true) [] []
          (((natBitsSplit input).2.take (binaryValue (fieldOf input))
            ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
              false).reverse).reverse⟩ := by
    rw [Stacks.run_add, h2345, Option.bind_some]
    exact pdone_run _
  refine ⟨((((t2+t3)+t4)+t5)+1), ?_, ?_⟩
  · simpa only [binaryValue_fieldOf, length_fieldOf, List.reverse_reverse, frameSplit_take,
      frameSplit_drop] using! hfull
  · have hs23 := Stacks.clock_add parseProgram t2 t3 _ _ h2
    have hs34 := Stacks.clock_add parseProgram (t2+t3) t4 _ _ h23
    have hs45 := Stacks.clock_add parseProgram ((t2+t3)+t4) t5 _ _ h234
    have hsf := Stacks.clock_add parseProgram (((t2+t3)+t4)+t5) 1 _ _ h2345
    have hpc : Stacks.stackRunClock parseProgram 1
        ⟨some .pdone, ((false,none),none),
          pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input)))
            [] (List.replicate (fieldOf input).length true) [] []
            (((natBitsSplit input).2.take (binaryValue (fieldOf input))
              ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
                false).reverse).reverse⟩ ≤ 1 :=
      pdone_clock _
    have h3c' : Stacks.stackRunClock parseProgram t3
        ⟨some (.nflip 0), ((false,none),none),
          pstore [] (natBitsSplit input).2 (fieldOf input).reverse [] [] [] []⟩ ≤
        9*(1+countTrues input)^2 := by
      simpa only [List.length_reverse, length_fieldOf] using! h3c
    have h4c' : Stacks.stackRunClock parseProgram t4
        ⟨some (.tk .borrow), ((false,none),none),
          pstore [] (natBitsSplit input).2 [] (fieldOf input) [] [] []⟩ ≤
        (2*(natBitsSplit input).1+4)*(10*(1+countTrues input)^2
          +50*(1+(natBitsSplit input).2.length+(natBitsSplit input).1)^2+10) := by
      simpa only [List.length_nil, Nat.add_zero, binaryValue_fieldOf, length_fieldOf] using! h4c
    have h5c' : Stacks.stackRunClock parseProgram t5
        ⟨some (.flip 0), ((false,none),none),
          pstore [] ((natBitsSplit input).2.drop (binaryValue (fieldOf input))) []
            (List.replicate (fieldOf input).length true) []
            (((natBitsSplit input).2.take (binaryValue (fieldOf input))
              ++ List.replicate (binaryValue (fieldOf input) - (natBitsSplit input).2.length)
                false).reverse) []⟩ ≤
        9*(1+(frameSplit input).1.length)^2 := by
      simpa only [List.length_reverse, binaryValue_fieldOf, ← frameSplit_take] using! h5c
    simp only [parseCostFrom]
    linarith only [hs23, hs34, hs45, hsf, h2c, h3c', h4c', h5c', hpc]

end ParseFramed

end TotalParse

section PairAssembly

open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordCompiler TM
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM (Symbol)
open Turing

namespace PairAssembly

/-- The pair-assembly local state, consisting of a counter state and an optional saved bit. -/
abbrev Local := Counter.Local × Option Bool

instance : Fintype ParseFramed.PLabel where
  elems := {ParseFramed.PLabel.read 0, ParseFramed.PLabel.nat 0, ParseFramed.PLabel.nat 1,
    ParseFramed.PLabel.nat 2, ParseFramed.PLabel.nflip 0, ParseFramed.PLabel.tk .borrow,
    ParseFramed.PLabel.tk .restore, ParseFramed.PLabel.pbranch, ParseFramed.PLabel.tkBody,
    ParseFramed.PLabel.clear, ParseFramed.PLabel.flip 0, ParseFramed.PLabel.pdone}
  complete := by
    intro x
    cases x with
    | read l => fin_cases l <;> simp
    | nat l => fin_cases l <;> simp
    | nflip l => fin_cases l <;> simp
    | tk l => cases l <;> simp
    | pbranch => simp
    | tkBody => simp
    | clear => simp
    | flip l => fin_cases l <;> simp
    | pdone => simp

instance : Fintype AddLoop.Label where
  elems := {AddLoop.Label.dec .borrow, AddLoop.Label.dec .restore, AddLoop.Label.branch,
    AddLoop.Label.inc .carry, AddLoop.Label.inc .restore, AddLoop.Label.done}
  complete := by
    intro x
    cases x with
    | dec l => cases l <;> simp
    | branch => simp
    | inc l => cases l <;> simp
    | done => simp

instance : Fintype PairCopy.Label where
  elems := {PairCopy.Label.mv 0, PairCopy.Label.cp, PairCopy.Label.done}
  complete := by
    intro x
    cases x with
    | mv l => fin_cases l <;> simp
    | cp => simp
    | done => simp

instance : Fintype LengthCount.Label where
  elems := {LengthCount.Label.check, LengthCount.Label.inc .carry,
    LengthCount.Label.inc .restore, LengthCount.Label.done}
  complete := by
    intro x
    cases x with
    | check => simp
    | inc l => cases l <;> simp
    | done => simp

/-- The thirteen stack slots used for pair parsing, arithmetic, copying, length counting, and
output assembly. -/
inductive Slot
  | raw | parse | num | num2 | spare | acc1
  | acc | live | keep | tmp | work | lout | out
  deriving DecidableEq, Fintype
instance : Inhabited Slot := ⟨.tmp⟩

/-- The control labels for the two parsers, copying and addition calls, length counting, output
emission, cleanup, and completion. -/
inductive Label
  | p1 : ParseFramed.PLabel → Label
  | p2 : ParseFramed.PLabel → Label
  | clNum2a
  | clNum2b
  | c1 : PairCopy.Label → Label
  | add : AddLoop.Label → Label
  | c2 : PairCopy.Label → Label
  | lc1 : LengthCount.Label → Label
  | eA : NatEmit.Label → Label
  | clLoutA
  | eB : NatEmit.Label → Label
  | clRaw
  | lc2 : LengthCount.Label → Label
  | eC : NatEmit.Label → Label
  | clLoutC
  | eD : NatEmit.Label → Label
  | clKeep
  | finish
  deriving DecidableEq, Fintype
instance : Inhabited Label := ⟨.p1 (.read 0)⟩

/-- The pair-assembly store assigning the supplied bit words to its thirteen named stacks. -/
def astore (raw parse num num2 spare acc1 acc live keep tmp work lout out : Bits) : Slot → Bits
  | .raw => raw | .parse => parse | .num => num | .num2 => num2 | .spare => spare | .acc1 => acc1
  | .acc => acc | .live => live | .keep => keep | .tmp => tmp | .work => work
  | .lout => lout | .out => out

/-- Embeds the first framed parser's stack slots into the pair-assembly slots, with its output
in `acc`. -/
def pCode1 : ParseFramed.PSlot → Slot
  | .raw => .raw | .parse => .parse | .num => .num | .num2 => .num2
  | .spare => .spare | .acc1 => .acc1 | .acc => .acc

/-- Embeds the second framed parser's stack slots into the pair-assembly slots, with its output
in `work`. -/
def pCode2 : ParseFramed.PSlot → Slot
  | .raw => .raw | .parse => .parse | .num => .num | .num2 => .num2
  | .spare => .spare | .acc1 => .acc1 | .acc => .work

/-- Maps the first copying call from `work` through `tmp` to destinations `live` and `keep`. -/
def cCode1 : PairCopy.Slot → Slot
  | .src => .work | .tmp => .tmp | .d1 => .live | .d2 => .keep

/-- Maps the second copying call from `acc` through `tmp` to destinations `work` and `raw`. -/
def cCode2 : PairCopy.Slot → Slot
  | .src => .acc | .tmp => .tmp | .d1 => .work | .d2 => .raw

/-- Maps addition-loop slots to the pair-assembly accumulator, live counter, and temporary
stacks. -/
def aCode : AddLoop.Slot → Slot
  | .acc => .acc | .cnt => .live | .tmp => .tmp

/-- Maps the first length-counting call to source `work`, counter `lout`, and temporary stack
`tmp`. -/
def lCode1 : LengthCount.Slot → Slot
  | .src => .work | .cnt => .lout | .tmp => .tmp

/-- Maps the second length-counting call to source `live`, counter `lout`, and temporary stack
`tmp`. -/
def lCode2 : LengthCount.Slot → Slot
  | .src => .live | .cnt => .lout | .tmp => .tmp

/-- Maps natural-number emission slots to the length-output, number-work, and output stacks. -/
def nCodeL (k : Fin 3) : Slot := if k = 0 then .lout else if k = 1 then .num else .out

/-- Maps emission slots to the raw-word, number-work, and output stacks. -/
def nCodeR (k : Fin 3) : Slot := if k = 0 then .raw else if k = 1 then .num else .out

/-- Maps emission slots to the preserved-word, number-work, and output stacks. -/
def nCodeK (k : Fin 3) : Slot := if k = 0 then .keep else if k = 1 then .num else .out

/-- The pair-assembly stack program combining framed parsing, copying, repeated-increment
addition, length counting, emission, and stack cleanup. -/
def program : Label → TM2.Stmt (fun _ : Slot => Bool) Label Local
  | .p1 l => StackCall.stmt pCode1 Label.p1 (.clNum2a) id (fun _ v => v) (ParseFramed.parseProgram l)
  | .p2 l => StackCall.stmt pCode2 Label.p2 (.clNum2b) id (fun _ v => v) (ParseFramed.parseProgram l)
  | .clNum2a => .pop .num2 (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome) (.goto (fun _ => .clNum2a)) (.goto (fun _ => .p2 (.nat 0))))
  | .clNum2b => .pop .num2 (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome) (.goto (fun _ => .clNum2b)) (.goto (fun _ => .c1 (.mv 0))))
  | .c1 l => StackCall.stmt cCode1 Label.c1 (.add (.dec .borrow))
      Prod.snd (fun v b => (v.1, b)) (PairCopy.program l)
  | .add l => StackCall.stmt aCode Label.add (.c2 (.mv 0))
      Prod.fst (fun v s => (s, v.2)) (AddLoop.addProgram l)
  | .c2 l => StackCall.stmt cCode2 Label.c2 (.lc1 .check)
      Prod.snd (fun v b => (v.1, b)) (PairCopy.program l)
  | .lc1 l => StackCall.stmt lCode1 Label.lc1 (.eA .count)
      Prod.snd (fun v b => (v.1, b)) (LengthCount.program l)
  | .eA l => StackCall.stmt nCodeL Label.eA (.clLoutA)
      Prod.snd (fun v b => (v.1, b)) (NatEmit.program l)
  | .clLoutA => .pop .lout (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome) (.goto (fun _ => .clLoutA)) (.goto (fun _ => .eB .emit)))
  | .eB l => StackCall.stmt nCodeR Label.eB (.clRaw)
      Prod.snd (fun v b => (v.1, b)) (NatEmit.program l)
  | .clRaw => .pop .raw (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome) (.goto (fun _ => .clRaw)) (.goto (fun _ => .lc2 .check)))
  | .lc2 l => StackCall.stmt lCode2 Label.lc2 (.eC .count)
      Prod.snd (fun v b => (v.1, b)) (LengthCount.program l)
  | .eC l => StackCall.stmt nCodeL Label.eC (.clLoutC)
      Prod.snd (fun v b => (v.1, b)) (NatEmit.program l)
  | .clLoutC => .pop .lout (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome) (.goto (fun _ => .clLoutC)) (.goto (fun _ => .eD .emit)))
  | .eD l => StackCall.stmt nCodeK Label.eD (.clKeep)
      Prod.snd (fun v b => (v.1, b)) (NatEmit.program l)
  | .clKeep => .pop .keep (fun v b => (v.1, b))
      (.branch (fun v => v.2.isSome) (.goto (fun _ => .clKeep)) (.goto (fun _ => .finish)))
  | .finish => .halt

/-- Embeds the first parser's store into the pair-assembly store with the specified background
stacks. -/
def pFrame1 (live keep tmp work lout out : Bits) (S : ParseFramed.PSlot → Bits) : Slot → Bits :=
  astore (S .raw) (S .parse) (S .num) (S .num2) (S .spare) (S .acc1) (S .acc)
    live keep tmp work lout out

/-- Evaluating `pFrame1` at a slot selected by `pCode1` recovers the corresponding first-parser
stack. -/
theorem pFrame1_at (live keep tmp work lout out : Bits) (S : ParseFramed.PSlot → Bits)
    (k : ParseFramed.PSlot) : pFrame1 live keep tmp work lout out S (pCode1 k) = S k := by
  cases k <;> rfl

/-- Updating a first-parser stack commutes with embedding it through `pFrame1`. -/
theorem pFrame1_update (live keep tmp work lout out : Bits) (S : ParseFramed.PSlot → Bits)
    (k : ParseFramed.PSlot) (bits : Bits) :
    pFrame1 live keep tmp work lout out (Function.update S k bits)
      = Function.update (pFrame1 live keep tmp work lout out S) (pCode1 k) bits := by
  funext j
  cases k <;> cases j <;> simp [pFrame1, astore, pCode1, Function.update_apply]

/-- Embeds the second parser's store into the pair-assembly store with the specified background
stacks. -/
def pFrame2 (acc live keep tmp lout out : Bits) (S : ParseFramed.PSlot → Bits) : Slot → Bits :=
  astore (S .raw) (S .parse) (S .num) (S .num2) (S .spare) (S .acc1) acc
    live keep tmp (S .acc) lout out

/-- Evaluating `pFrame2` at a slot selected by `pCode2` recovers the corresponding second-parser
stack. -/
theorem pFrame2_at (acc live keep tmp lout out : Bits) (S : ParseFramed.PSlot → Bits)
    (k : ParseFramed.PSlot) : pFrame2 acc live keep tmp lout out S (pCode2 k) = S k := by
  cases k <;> rfl

/-- Updating a second-parser stack commutes with embedding it through `pFrame2`. -/
theorem pFrame2_update (acc live keep tmp lout out : Bits) (S : ParseFramed.PSlot → Bits)
    (k : ParseFramed.PSlot) (bits : Bits) :
    pFrame2 acc live keep tmp lout out (Function.update S k bits)
      = Function.update (pFrame2 acc live keep tmp lout out S) (pCode2 k) bits := by
  funext j
  cases k <;> cases j <;> simp [pFrame2, astore, pCode2, Function.update_apply]

/-- Embeds the first copying subroutine's store into the pair-assembly store with the specified
background stacks. -/
def cFrame1 (raw parse num num2 spare acc1 acc lout out : Bits)
    (S : PairCopy.Slot → Bits) : Slot → Bits :=
  astore raw parse num num2 spare acc1 acc (S .d1) (S .d2) (S .tmp) (S .src) lout out

/-- Evaluating `cFrame1` at a slot selected by `cCode1` recovers the corresponding first-copy
stack. -/
theorem cFrame1_at (raw parse num num2 spare acc1 acc lout out : Bits)
    (S : PairCopy.Slot → Bits) (k : PairCopy.Slot) :
    cFrame1 raw parse num num2 spare acc1 acc lout out S (cCode1 k) = S k := by
  cases k <;> rfl

/-- Updating a first-copy stack commutes with embedding it through `cFrame1`. -/
theorem cFrame1_update (raw parse num num2 spare acc1 acc lout out : Bits)
    (S : PairCopy.Slot → Bits) (k : PairCopy.Slot) (bits : Bits) :
    cFrame1 raw parse num num2 spare acc1 acc lout out (Function.update S k bits)
      = Function.update (cFrame1 raw parse num num2 spare acc1 acc lout out S)
          (cCode1 k) bits := by
  funext j
  cases k <;> cases j <;> simp [cFrame1, astore, cCode1, Function.update_apply]

/-- Embeds the second copying subroutine's store into the pair-assembly store with the specified
background stacks. -/
def cFrame2 (parse num num2 spare acc1 live keep lout out : Bits)
    (S : PairCopy.Slot → Bits) : Slot → Bits :=
  astore (S .d2) parse num num2 spare acc1 (S .src) live keep (S .tmp) (S .d1) lout out

/-- Evaluating `cFrame2` at a slot selected by `cCode2` recovers the corresponding second-copy
stack. -/
theorem cFrame2_at (parse num num2 spare acc1 live keep lout out : Bits)
    (S : PairCopy.Slot → Bits) (k : PairCopy.Slot) :
    cFrame2 parse num num2 spare acc1 live keep lout out S (cCode2 k) = S k := by
  cases k <;> rfl

/-- Updating a second-copy stack commutes with embedding it through `cFrame2`. -/
theorem cFrame2_update (parse num num2 spare acc1 live keep lout out : Bits)
    (S : PairCopy.Slot → Bits) (k : PairCopy.Slot) (bits : Bits) :
    cFrame2 parse num num2 spare acc1 live keep lout out (Function.update S k bits)
      = Function.update (cFrame2 parse num num2 spare acc1 live keep lout out S)
          (cCode2 k) bits := by
  funext j
  cases k <;> cases j <;> simp [cFrame2, astore, cCode2, Function.update_apply]

/-- Embeds the addition-loop store into the pair-assembly store with the specified background
stacks. -/
def aFrame (raw parse num num2 spare acc1 keep work lout out : Bits)
    (S : AddLoop.Slot → Bits) : Slot → Bits :=
  astore raw parse num num2 spare acc1 (S .acc) (S .cnt) keep (S .tmp) work lout out

/-- Evaluating `aFrame` at a slot selected by `aCode` recovers the corresponding addition-loop
stack. -/
theorem aFrame_at (raw parse num num2 spare acc1 keep work lout out : Bits)
    (S : AddLoop.Slot → Bits) (k : AddLoop.Slot) :
    aFrame raw parse num num2 spare acc1 keep work lout out S (aCode k) = S k := by
  cases k <;> rfl

/-- Updating an addition-loop stack commutes with embedding it through `aFrame`. -/
theorem aFrame_update (raw parse num num2 spare acc1 keep work lout out : Bits)
    (S : AddLoop.Slot → Bits) (k : AddLoop.Slot) (bits : Bits) :
    aFrame raw parse num num2 spare acc1 keep work lout out (Function.update S k bits)
      = Function.update (aFrame raw parse num num2 spare acc1 keep work lout out S)
          (aCode k) bits := by
  funext j
  cases k <;> cases j <;> simp [aFrame, astore, aCode, Function.update_apply]

/-- Embeds the first length-counting store into the pair-assembly store with the specified
background stacks. -/
def lFrame1 (raw parse num num2 spare acc1 acc live keep out : Bits)
    (S : LengthCount.Slot → Bits) : Slot → Bits :=
  astore raw parse num num2 spare acc1 acc live keep (S .tmp) (S .src) (S .cnt) out

/-- Evaluating `lFrame1` at a slot selected by `lCode1` recovers the corresponding first
length-counting stack. -/
theorem lFrame1_at (raw parse num num2 spare acc1 acc live keep out : Bits)
    (S : LengthCount.Slot → Bits) (k : LengthCount.Slot) :
    lFrame1 raw parse num num2 spare acc1 acc live keep out S (lCode1 k) = S k := by
  cases k <;> rfl

/-- Updating a first length-counting stack commutes with embedding it through `lFrame1`. -/
theorem lFrame1_update (raw parse num num2 spare acc1 acc live keep out : Bits)
    (S : LengthCount.Slot → Bits) (k : LengthCount.Slot) (bits : Bits) :
    lFrame1 raw parse num num2 spare acc1 acc live keep out (Function.update S k bits)
      = Function.update (lFrame1 raw parse num num2 spare acc1 acc live keep out S)
          (lCode1 k) bits := by
  funext j
  cases k <;> cases j <;> simp [lFrame1, astore, lCode1, Function.update_apply]

/-- Embeds the second length-counting store into the pair-assembly store with the specified
background stacks. -/
def lFrame2 (raw parse num num2 spare acc1 acc keep work out : Bits)
    (S : LengthCount.Slot → Bits) : Slot → Bits :=
  astore raw parse num num2 spare acc1 acc (S .src) keep (S .tmp) work (S .cnt) out

/-- Evaluating `lFrame2` at a slot selected by `lCode2` recovers the corresponding second
length-counting stack. -/
theorem lFrame2_at (raw parse num num2 spare acc1 acc keep work out : Bits)
    (S : LengthCount.Slot → Bits) (k : LengthCount.Slot) :
    lFrame2 raw parse num num2 spare acc1 acc keep work out S (lCode2 k) = S k := by
  cases k <;> rfl

/-- Updating a second length-counting stack commutes with embedding it through `lFrame2`. -/
theorem lFrame2_update (raw parse num num2 spare acc1 acc keep work out : Bits)
    (S : LengthCount.Slot → Bits) (k : LengthCount.Slot) (bits : Bits) :
    lFrame2 raw parse num num2 spare acc1 acc keep work out (Function.update S k bits)
      = Function.update (lFrame2 raw parse num num2 spare acc1 acc keep work out S)
          (lCode2 k) bits := by
  funext j
  cases k <;> cases j <;> simp [lFrame2, astore, lCode2, Function.update_apply]

/-- Embeds the length-prefix emission store into the pair-assembly store with the specified
background stacks. -/
def nFrameL (raw parse num2 spare acc1 acc live keep tmp work : Bits)
    (S : Fin 3 → Bits) : Slot → Bits :=
  astore raw parse (S 1) num2 spare acc1 acc live keep tmp work (S 0) (S 2)

/-- Evaluating `nFrameL` at a slot selected by `nCodeL` recovers the corresponding length-prefix
emission stack. -/
theorem nFrameL_at (raw parse num2 spare acc1 acc live keep tmp work : Bits)
    (S : Fin 3 → Bits) (k : Fin 3) :
    nFrameL raw parse num2 spare acc1 acc live keep tmp work S (nCodeL k) = S k := by
  fin_cases k <;> rfl

/-- Updating a length-prefix emission stack commutes with embedding it through `nFrameL`. -/
theorem nFrameL_update (raw parse num2 spare acc1 acc live keep tmp work : Bits)
    (S : Fin 3 → Bits) (k : Fin 3) (bits : Bits) :
    nFrameL raw parse num2 spare acc1 acc live keep tmp work (Function.update S k bits)
      = Function.update (nFrameL raw parse num2 spare acc1 acc live keep tmp work S)
          (nCodeL k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [nFrameL, astore, nCodeL, Function.update_apply]

/-- Embeds the raw-word emission store into the pair-assembly store with the specified
background stacks. -/
def nFrameR (parse num2 spare acc1 acc live keep tmp work lout : Bits)
    (S : Fin 3 → Bits) : Slot → Bits :=
  astore (S 0) parse (S 1) num2 spare acc1 acc live keep tmp work lout (S 2)

/-- Evaluating `nFrameR` at a slot selected by `nCodeR` recovers the corresponding raw-word
emission stack. -/
theorem nFrameR_at (parse num2 spare acc1 acc live keep tmp work lout : Bits)
    (S : Fin 3 → Bits) (k : Fin 3) :
    nFrameR parse num2 spare acc1 acc live keep tmp work lout S (nCodeR k) = S k := by
  fin_cases k <;> rfl

/-- Updating a raw-word emission stack commutes with embedding it through `nFrameR`. -/
theorem nFrameR_update (parse num2 spare acc1 acc live keep tmp work lout : Bits)
    (S : Fin 3 → Bits) (k : Fin 3) (bits : Bits) :
    nFrameR parse num2 spare acc1 acc live keep tmp work lout (Function.update S k bits)
      = Function.update (nFrameR parse num2 spare acc1 acc live keep tmp work lout S)
          (nCodeR k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [nFrameR, astore, nCodeR, Function.update_apply]

/-- Embeds the preserved-word emission store into the pair-assembly store with the specified
background stacks. -/
def nFrameK (raw parse num2 spare acc1 acc live tmp work lout : Bits)
    (S : Fin 3 → Bits) : Slot → Bits :=
  astore raw parse (S 1) num2 spare acc1 acc live (S 0) tmp work lout (S 2)

/-- Evaluating `nFrameK` at a slot selected by `nCodeK` recovers the corresponding
preserved-word emission stack. -/
theorem nFrameK_at (raw parse num2 spare acc1 acc live tmp work lout : Bits)
    (S : Fin 3 → Bits) (k : Fin 3) :
    nFrameK raw parse num2 spare acc1 acc live tmp work lout S (nCodeK k) = S k := by
  fin_cases k <;> rfl

/-- Updating a preserved-word emission stack commutes with embedding it through `nFrameK`. -/
theorem nFrameK_update (raw parse num2 spare acc1 acc live tmp work lout : Bits)
    (S : Fin 3 → Bits) (k : Fin 3) (bits : Bits) :
    nFrameK raw parse num2 spare acc1 acc live tmp work lout (Function.update S k bits)
      = Function.update (nFrameK raw parse num2 spare acc1 acc live tmp work lout S)
          (nCodeK k) bits := by
  funext j
  fin_cases k <;> cases j <;> simp [nFrameK, astore, nCodeK, Function.update_apply]

/-- The first embedded parser extracts `w` from the reversed raw encoding of `framed w ++ rest`,
stores it in `acc`, and reaches counter cleanup with the displayed clock bound. -/
theorem parse1_call (w rest : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.p1 (.read 0)), ((false,none),none),
          astore (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse [] [] [] [] [] [] [] [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some .clNum2a, ((false,none),none),
        astore [] rest [] (List.replicate w.length.bits.length true) [] [] w
          [] [] [] [] [] []⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.p1 (.read 0)), ((false,none),none),
          astore (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse [] [] [] [] [] [] [] [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤
        9*(1+((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest).reverse).length)^2
          +40*(1+(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)).length)^2
          +9*(1+w.length.bits.length)^2
          +(2*w.length+4)*(10*(1+w.length.bits.length)^2
            +50*(1+(w ++ rest).length+0+w.length)^2+10)
          +9*(1+w.length)^2+1 := by
  obtain ⟨t, h, hc⟩ := ParseFramed.parseFramed_run w rest
  obtain ⟨hr, hrc⟩ := StackCall.execution pCode1 Label.p1 (.clNum2a) id (fun _ v => v)
    (pFrame1 [] [] [] [] [] []) (pFrame1_at [] [] [] [] [] []) (pFrame1_update [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    ParseFramed.parseProgram program (fun _ => rfl) (((false,none),none) : Local) t _ _ h
  exact ⟨t, hr, (le_of_eq hrc).trans hc⟩

/-- The second embedded parser extracts `w` into `work` while preserving `acc` and the residual
suffix, and reaches counter cleanup with the displayed clock bound. -/
theorem parse2_call (acc w rest : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.p2 (.nat 0)), ((false,none),none),
          astore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest) [] [] [] [] acc [] [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some .clNum2b, ((false,none),none),
        astore [] rest [] (List.replicate w.length.bits.length true) [] [] acc
          [] [] [] w [] []⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.p2 (.nat 0)), ((false,none),none),
          astore [] (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.framed w ++ rest) [] [] [] [] acc [] [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤
        40*(1+(Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits w.length ++ (w ++ rest)).length)^2
          +9*(1+w.length.bits.length)^2
          +(2*w.length+4)*(10*(1+w.length.bits.length)^2
            +50*(1+(w ++ rest).length+0+w.length)^2+10)
          +9*(1+w.length)^2+1 := by
  obtain ⟨t, h, hc⟩ := ParseFramed.parseFramed_run_from w rest
  obtain ⟨hr, hrc⟩ := StackCall.execution pCode2 Label.p2 (.clNum2b) id (fun _ v => v)
    (pFrame2 acc [] [] [] [] []) (pFrame2_at acc [] [] [] [] []) (pFrame2_update acc [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    ParseFramed.parseProgram program (fun _ => rfl) (((false,none),none) : Local) t _ _ h
  exact ⟨t, hr, (le_of_eq hrc).trans hc⟩

/-- The first copying call duplicates `work` into `live` and `keep`, empties `work`, and enters
addition with clock at most `30 * (1 + w.length) ^ 2`. -/
theorem copy1_call (w : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.c1 (.mv 0)), ((false,none),none),
          astore [] [] [] [] [] [] [] [] [] [] w [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some (.add (.dec .borrow)), ((false, none), none),
        astore [] [] [] [] [] [] [] w w [] [] [] []⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.c1 (.mv 0)), ((false,none),none),
          astore [] [] [] [] [] [] [] [] [] [] w [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤ 30*(1+w.length)^2 := by
  obtain ⟨t, h, hc⟩ := PairCopy.copyTwo_run w none
  obtain ⟨hr, hrc⟩ := StackCall.execution cCode1 Label.c1 (.add (.dec .borrow))
    Prod.snd (fun v b => (v.1, b))
    (cFrame1 [] [] [] [] [] [] [] [] []) (cFrame1_at [] [] [] [] [] [] [] [] [])
    (cFrame1_update [] [] [] [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    PairCopy.program program (fun _ => rfl) (((false,none),none) : Local) t _ _ h
  exact ⟨t, hr, (le_of_eq hrc).trans hc⟩

/-- The embedded addition call increments `acc` exactly `binaryValue cnt` times, replaces the
live counter by an all-ones word, and enters the second copying call with the displayed
clock bound. -/
theorem add_call (acc cnt : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.add (.dec .borrow)), ((false,none),none),
          astore [] [] [] [] [] [] acc cnt [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some (.c2 (.mv 0)), ((false, none), none),
        astore [] [] [] [] [] []
          (Increment.word^[binaryValue cnt] acc) (List.replicate cnt.length true)
          [] [] [] [] []⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.add (.dec .borrow)), ((false,none),none),
          astore [] [] [] [] [] [] acc cnt [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤
        (2*binaryValue cnt+4)*(10*(1+cnt.length)^2
          +50*(1+acc.length+binaryValue cnt+1)^2+10) := by
  obtain ⟨t, h, hc, _⟩ := AddLoop.addLoop_complete (binaryValue cnt) acc cnt rfl ((false,none))
  obtain ⟨hr, hrc⟩ := StackCall.execution aCode Label.add (.c2 (.mv 0))
    Prod.fst (fun v s => (s, v.2))
    (aFrame [] [] [] [] [] [] [] [] [] []) (aFrame_at [] [] [] [] [] [] [] [] [] [])
    (aFrame_update [] [] [] [] [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    AddLoop.addProgram program (fun _ => rfl) (((false,none),none) : Local) t _ _ h
  exact ⟨t, hr, (le_of_eq hrc).trans hc⟩

/-- The second copying call duplicates `acc` into `raw` and `work`, empties `acc`, and enters
the first length-counting phase with clock at most `30 * (1 + w.length) ^ 2`. -/
theorem copy2_call (w : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.c2 (.mv 0)), ((false,none),none),
          astore [] [] [] [] [] [] w [] [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some (.lc1 .check), ((false, none), none),
        astore w [] [] [] [] [] [] [] [] [] w [] []⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.c2 (.mv 0)), ((false,none),none),
          astore [] [] [] [] [] [] w [] [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤ 30*(1+w.length)^2 := by
  obtain ⟨t, h, hc⟩ := PairCopy.copyTwo_run w none
  obtain ⟨hr, hrc⟩ := StackCall.execution cCode2 Label.c2 (.lc1 .check)
    Prod.snd (fun v b => (v.1, b))
    (cFrame2 [] [] [] [] [] [] [] [] []) (cFrame2_at [] [] [] [] [] [] [] [] [])
    (cFrame2_update [] [] [] [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    PairCopy.program program (fun _ => rfl) (((false,none),none) : Local) t _ _ h
  exact ⟨t, hr, (le_of_eq hrc).trans hc⟩

/-- The first length-counting call consumes `work`, writes the canonical binary word for its
length to `lout`, and enters the first prefix-emission phase with the displayed clock bound. -/
theorem count1_call (w : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.lc1 .check), ((false,none),none),
          astore [] [] [] [] [] [] [] [] [] [] w [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some (.eA .count), ((false, none), none),
        astore [] [] [] [] [] [] [] [] [] [] [] w.length.bits []⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.lc1 .check), ((false,none),none),
          astore [] [] [] [] [] [] [] [] [] [] w [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤
        (w.length+1)*(20+50*(2+w.length)^2)+1 := by
  obtain ⟨t, h, hc⟩ := LengthCount.count_run w none
  obtain ⟨hr, hrc⟩ := StackCall.execution lCode1 Label.lc1 (.eA .count)
    Prod.snd (fun v b => (v.1, b))
    (lFrame1 [] [] [] [] [] [] [] [] [] []) (lFrame1_at [] [] [] [] [] [] [] [] [] [])
    (lFrame1_update [] [] [] [] [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    LengthCount.program program (fun _ => rfl) (((false,none),none) : Local) t _ _ h
  exact ⟨t, hr, (le_of_eq hrc).trans hc⟩

/-- The second length-counting call consumes `live`, writes the canonical binary word for its
length to `lout`, and enters the second prefix-emission phase with the displayed clock
bound. -/
theorem count2_call (w : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.lc2 .check), ((false,none),none),
          astore [] [] [] [] [] [] [] w [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some (.eC .count), ((false, none), none),
        astore [] [] [] [] [] [] [] [] [] [] [] w.length.bits []⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.lc2 .check), ((false,none),none),
          astore [] [] [] [] [] [] [] w [] [] [] [] []⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤
        (w.length+1)*(20+50*(2+w.length)^2)+1 := by
  obtain ⟨t, h, hc⟩ := LengthCount.count_run w none
  obtain ⟨hr, hrc⟩ := StackCall.execution lCode2 Label.lc2 (.eC .count)
    Prod.snd (fun v b => (v.1, b))
    (lFrame2 [] [] [] [] [] [] [] [] [] []) (lFrame2_at [] [] [] [] [] [] [] [] [] [])
    (lFrame2_update [] [] [] [] [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    LengthCount.program program (fun _ => rfl) (((false,none),none) : Local) t _ _ h
  exact ⟨t, hr, (le_of_eq hrc).trans hc⟩

/-- The first prefix-emission call prefixes `(natBits n).reverse` to output, preserves `n.bits`
in `lout`, and reaches length-stack cleanup with clock at most `100 * (1 + n.bits.length +
out.length) ^ 2`. -/
theorem emitA_call (n : ℕ) (out : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.eA .count), ((false,none),none),
          astore [] [] [] [] [] [] [] [] [] [] [] n.bits out⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some .clLoutA, ((false, none), none),
        astore [] [] [] [] [] [] [] [] [] [] [] n.bits ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse++out)⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.eA .count), ((false,none),none),
          astore [] [] [] [] [] [] [] [] [] [] [] n.bits out⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤
        100*(1+n.bits.length+out.length)^2 := by
  obtain ⟨h, hc⟩ := NatEmit.complete n out none
  obtain ⟨hr, hrc⟩ := StackCall.execution nCodeL Label.eA (.clLoutA)
    Prod.snd (fun v b => (v.1, b))
    (nFrameL [] [] [] [] [] [] [] [] [] []) (nFrameL_at [] [] [] [] [] [] [] [] [] [])
    (nFrameL_update [] [] [] [] [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    NatEmit.program program (fun _ => rfl) (((false,none),none) : Local)
    (4*n.bits.length+5) _ _ h
  have hcb := NatEmit.clock_bound n out none
  exact ⟨_, hr, (le_of_eq hrc).trans hcb⟩

/-- The first payload-emission call prefixes `bits.reverse` to output, preserves the raw word,
and reaches raw-stack cleanup with clock at most `25 * (1 + bits.length + out.length) ^ 2`. -/
theorem emitB_call (bits out : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.eB .emit), ((false,none),none),
          astore bits [] [] [] [] [] [] [] [] [] [] [] out⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some .clRaw, ((false, none), none),
        astore bits [] [] [] [] [] [] [] [] [] [] [] (bits.reverse++out)⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.eB .emit), ((false,none),none),
          astore bits [] [] [] [] [] [] [] [] [] [] [] out⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤
        25*(1+bits.length+out.length)^2 := by
  obtain ⟨h, hc⟩ := NatEmit.copy_complete bits out none
  obtain ⟨hr, hrc⟩ := StackCall.execution nCodeR Label.eB (.clRaw)
    Prod.snd (fun v b => (v.1, b))
    (nFrameR [] [] [] [] [] [] [] [] [] []) (nFrameR_at [] [] [] [] [] [] [] [] [] [])
    (nFrameR_update [] [] [] [] [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    NatEmit.program program (fun _ => rfl) (((false,none),none) : Local)
    (2*bits.length+3) _ _ h
  have hcb := NatEmit.copy_clock_bound bits out none
  exact ⟨_, hr, (le_of_eq hrc).trans hcb⟩

/-- The second prefix-emission call prefixes `(natBits n).reverse` to output, preserves `n.bits`
in `lout`, and reaches length-stack cleanup with clock at most `100 * (1 + n.bits.length +
out.length) ^ 2`. -/
theorem emitC_call (n : ℕ) (out : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.eC .count), ((false,none),none),
          astore [] [] [] [] [] [] [] [] [] [] [] n.bits out⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some .clLoutC, ((false, none), none),
        astore [] [] [] [] [] [] [] [] [] [] [] n.bits ((Qatlib.Concepts.BitWordCompiler.CanonicalCodec.natBits n).reverse++out)⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.eC .count), ((false,none),none),
          astore [] [] [] [] [] [] [] [] [] [] [] n.bits out⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤
        100*(1+n.bits.length+out.length)^2 := by
  obtain ⟨h, hc⟩ := NatEmit.complete n out none
  obtain ⟨hr, hrc⟩ := StackCall.execution nCodeL Label.eC (.clLoutC)
    Prod.snd (fun v b => (v.1, b))
    (nFrameL [] [] [] [] [] [] [] [] [] []) (nFrameL_at [] [] [] [] [] [] [] [] [] [])
    (nFrameL_update [] [] [] [] [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    NatEmit.program program (fun _ => rfl) (((false,none),none) : Local)
    (4*n.bits.length+5) _ _ h
  have hcb := NatEmit.clock_bound n out none
  exact ⟨_, hr, (le_of_eq hrc).trans hcb⟩

/-- The second payload-emission call prefixes `bits.reverse` to output, preserves the kept word,
and reaches kept-stack cleanup with clock at most `25 * (1 + bits.length + out.length) ^ 2`. -/
theorem emitD_call (bits out : Bits) :
    ∃ ticks, Stacks.stackRun program ticks
        (⟨some (.eD .emit), ((false,none),none),
          astore [] [] [] [] [] [] [] [] bits [] [] [] out⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) =
      some ⟨some .clKeep, ((false, none), none),
        astore [] [] [] [] [] [] [] [] bits [] [] [] (bits.reverse++out)⟩ ∧
      Stacks.stackRunClock program ticks
        (⟨some (.eD .emit), ((false,none),none),
          astore [] [] [] [] [] [] [] [] bits [] [] [] out⟩ :
          TM2.Cfg (fun _ : Slot => Bool) Label Local) ≤
        25*(1+bits.length+out.length)^2 := by
  obtain ⟨h, hc⟩ := NatEmit.copy_complete bits out none
  obtain ⟨hr, hrc⟩ := StackCall.execution nCodeK Label.eD (.clKeep)
    Prod.snd (fun v b => (v.1, b))
    (nFrameK [] [] [] [] [] [] [] [] [] []) (nFrameK_at [] [] [] [] [] [] [] [] [] [])
    (nFrameK_update [] [] [] [] [] [] [] [] [] [])
    (fun _ _ => rfl) (fun _ _ _ => rfl)
    NatEmit.program program (fun _ => rfl) (((false,none),none) : Local)
    (2*bits.length+3) _ _ h
  have hcb := NatEmit.copy_clock_bound bits out none
  exact ⟨_, hr, (le_of_eq hrc).trans hcb⟩

end PairAssembly

end PairAssembly

end Clause3BinaryAddition

end Qatlib.Concepts.QueryComplexity.DegreeMethod
