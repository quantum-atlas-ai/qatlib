/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription

/-!
# Native dyadic coefficients for history operators

The module computes integer rounding numerators for the coefficients zero, ±1, and ±1/√2 using
natural square roots. `Atom`, `atomNumerator`, and `dyadicValue` connect these computations to
real and complex values, including the half-scaled coefficient arithmetic used in propagation
operators. The background is described in [KitaevShenVyalyi2002].

## Main statements

* `floor_atom`: native numerators agree with shifted-floor rounding.
* `atomNumerator_bounds`: numerators remain within the precision range.
* `dyadic_half`: exact dyadic arithmetic for half-scaled propagation coefficients.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.UniformBqp.FiniteGateWord
set_option autoImplicit false

/-- The integer ceiling of the square root of a natural number, computed using `Nat.sqrt` and a
perfect-square test. -/
def ceilSqrtNative (B : ℕ) : ℕ :=
  Nat.sqrt B + if Nat.sqrt B * Nat.sqrt B = B then 0 else 1

/-- The integer numerator for nearest-integer rounding of `2^b / sqrt 2`, computed from the
natural square root of `2^(2*b + 1)`. -/
def rootPosNumerator (b : ℕ) : ℤ :=
  ((Nat.sqrt (2 ^ (2 * b + 1)) : ℤ) + 1) / 2

/-- The integer numerator for nearest-integer rounding of `-2^b / sqrt 2`, computed from the
native square-root ceiling of `2^(2*b + 1)`. -/
def rootNegNumerator (b : ℕ) : ℤ :=
  (1 - (ceilSqrtNative (2 ^ (2 * b + 1)) : ℤ)) / 2

/-- The integer ceiling of the real square root of a natural number equals `ceilSqrtNative` cast
to an integer. -/
theorem ceil_real_sqrt_eq_native (B : ℕ) :
    ⌈Real.sqrt (B : ℝ)⌉ = (ceilSqrtNative B : ℤ) := by
  by_cases h : Nat.sqrt B * Nat.sqrt B = B
  · have hr : Real.sqrt (B : ℝ) = (Nat.sqrt B : ℝ) := by
      apply (Real.sqrt_eq_iff_mul_self_eq
        (Nat.cast_nonneg B) (Nat.cast_nonneg (Nat.sqrt B))).2
      exact_mod_cast h.symm
    simp [ceilSqrtNative, h, hr]
  · have hne : (Nat.sqrt B : ℝ) ≠ Real.sqrt (B : ℝ) := by
      intro he
      apply h
      have heq : (Nat.sqrt B : ℝ) * (Nat.sqrt B : ℝ) = (B : ℝ) := by
        rw [he]
        exact Real.mul_self_sqrt (Nat.cast_nonneg B)
      exact_mod_cast heq
    have hlo : (Nat.sqrt B : ℝ) < Real.sqrt (B : ℝ) :=
      lt_of_le_of_ne Real.nat_sqrt_le_real_sqrt hne
    have hhi : Real.sqrt (B : ℝ) < (Nat.sqrt B : ℝ) + 1 :=
      Real.real_sqrt_lt_nat_sqrt_succ
    apply Int.ceil_eq_iff.mpr
    constructor
    · simpa [ceilSqrtNative, h] using hlo
    · simpa [ceilSqrtNative, h] using hhi.le

/-- The square root of `2^(2*b + 1)` equals twice `2^b / sqrt 2`. -/
theorem sqrt_radicand_eq_twice (b : ℕ) :
    Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ) =
      2 * ((Real.sqrt 2)⁻¹ * (2 : ℝ) ^ b) := by
  have hcast : ((2 ^ (2 * b + 1) : ℕ) : ℝ) =
      (2 : ℝ) * ((2 : ℝ) ^ b) ^ 2 := by
    push_cast
    rw [show 2 * b + 1 = b + b + 1 by omega, pow_add, pow_add]
    ring
  have hroot : Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ) =
      Real.sqrt 2 * (2 : ℝ) ^ b := by
    apply (Real.sqrt_eq_iff_eq_sq (Nat.cast_nonneg _)
      (mul_nonneg (Real.sqrt_nonneg 2) (by positivity))).2
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    exact hcast
  have hs0 : Real.sqrt (2 : ℝ) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
  have hsinv : Real.sqrt (2 : ℝ) = 2 * (Real.sqrt 2)⁻¹ := by
    calc
      Real.sqrt (2 : ℝ) =
          (Real.sqrt 2 * Real.sqrt 2) * (Real.sqrt 2)⁻¹ := by
            rw [mul_assoc, mul_inv_cancel₀ hs0, mul_one]
      _ = 2 * (Real.sqrt 2)⁻¹ := by
            rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  calc
    Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ) =
        Real.sqrt 2 * (2 : ℝ) ^ b := hroot
    _ = (2 * (Real.sqrt 2)⁻¹) * (2 : ℝ) ^ b :=
        congrArg (fun z : ℝ => z * (2 : ℝ) ^ b) hsinv
    _ = 2 * ((Real.sqrt 2)⁻¹ * (2 : ℝ) ^ b) := by ring

/-- The floor of `2^b / sqrt 2 + 1/2` equals the native positive-root numerator. -/
theorem floor_root_pos (b : ℕ) :
    ⌊(Real.sqrt 2)⁻¹ * (2 : ℝ) ^ b + (1 : ℝ) / 2⌋ =
      rootPosNumerator b := by
  calc
    ⌊(Real.sqrt 2)⁻¹ * (2 : ℝ) ^ b + (1 : ℝ) / 2⌋ =
        ⌊(Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ) + 1) / (2 : ℝ)⌋ := by
          congr 1
          rw [sqrt_radicand_eq_twice]
          ring
    _ = (⌊Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ)⌋ + 1) / (2 : ℤ) := by
          have h := Int.floor_div_natCast
            (Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ) + 1) 2
          rw [Int.floor_add_one] at h
          exact h
    _ = rootPosNumerator b := by
          rw [Real.floor_real_sqrt_eq_nat_sqrt]
          rfl

/-- The floor of `-2^b / sqrt 2 + 1/2` equals the native negative-root numerator. -/
theorem floor_root_neg (b : ℕ) :
    ⌊-((Real.sqrt 2)⁻¹ * (2 : ℝ) ^ b) + (1 : ℝ) / 2⌋ =
      rootNegNumerator b := by
  have hfloor :
      ⌊(1 : ℝ) - Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ)⌋ =
        (1 : ℤ) + ⌊-Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ)⌋ := by
    simpa only [Int.cast_one, sub_eq_add_neg] using
      (Int.floor_intCast_add (1 : ℤ)
        (-Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ)))
  calc
    ⌊-((Real.sqrt 2)⁻¹ * (2 : ℝ) ^ b) + (1 : ℝ) / 2⌋ =
        ⌊((1 : ℝ) - Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ)) / (2 : ℝ)⌋ := by
          congr 1
          rw [sqrt_radicand_eq_twice]
          ring
    _ = ⌊(1 : ℝ) - Real.sqrt ((2 ^ (2 * b + 1) : ℕ) : ℝ)⌋ / (2 : ℤ) := by
          exact Int.floor_div_natCast _ 2
    _ = rootNegNumerator b := by
          rw [hfloor, Int.floor_neg, ceil_real_sqrt_eq_native]
          simp only [rootNegNumerator, sub_eq_add_neg]

/-- The five real coefficient symbols representing zero, one, minus one, and the positive and
negative inverse square root of two. -/
inductive Atom where
  | zero | one | negOne | root | negRoot
  deriving DecidableEq, Repr

/-- The real value represented by a coefficient atom. -/
noncomputable def atomVal : Atom→ℝ
  | .zero => 0
  | .one => 1
  | .negOne => -1
  | .root => (Real.sqrt 2)⁻¹
  | .negRoot => -(Real.sqrt 2)⁻¹

/-- The integer dyadic numerator at precision `b` associated with a coefficient atom. -/
def atomNumerator (b : ℕ) : Atom→ℤ
  | .zero => 0
  | .one => (2:ℤ)^b
  | .negOne => -((2:ℤ)^b)
  | .root => rootPosNumerator b
  | .negRoot => rootNegNumerator b

/-- The complex number whose real and imaginary parts are the values of the two coefficient
atoms. -/
noncomputable def cartesian (a c : Atom) : ℂ :=
  (atomVal a:ℂ)+Complex.I*(atomVal c:ℂ)

/-- The complex dyadic number with integer real and imaginary numerators and denominator `2^b`. -/
noncomputable def dyadicValue (b : ℕ) (r i : ℤ) : ℂ :=
  ((r:ℂ)+Complex.I*(i:ℂ))/(2:ℂ)^b

/-- For an integer `k`, the floor of `k + 1/2` is `k`. -/
theorem floor_int_half (k : ℤ) : ⌊(k:ℝ)+(1:ℝ)/2⌋=k := by
  norm_num

/-- The native numerator of an atom equals the floor of its value scaled by `2^b` and shifted by
`1/2`. -/
theorem floor_atom (b : ℕ) (a : Atom) :
    ⌊atomVal a*(2:ℝ)^b+(1:ℝ)/2⌋=atomNumerator b a := by
  cases a with
  | zero => norm_num [atomVal,atomNumerator]
  | one => simpa [atomVal,atomNumerator] using floor_int_half ((2:ℤ)^b)
  | negOne => simpa [atomVal,atomNumerator] using floor_int_half (-((2:ℤ)^b))
  | root => exact floor_root_pos b
  | negRoot => simpa [atomVal,atomNumerator,neg_mul] using floor_root_neg b

/-- Every real coefficient atom has value between minus one and one. -/
theorem atomVal_bounds (a : Atom) : -1≤atomVal a ∧ atomVal a≤1 := by
  have hp : 0 < Real.sqrt (2:ℝ) := Real.sqrt_pos.mpr (by norm_num)
  have hsq := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  have hone : 1≤Real.sqrt (2:ℝ) := by nlinarith
  have hi : 0≤(Real.sqrt (2:ℝ))⁻¹ := inv_nonneg.mpr hp.le
  have hh := mul_nonneg (sub_nonneg.mpr hone) hi
  have he := mul_inv_cancel₀ hp.ne'
  have hu : (Real.sqrt (2:ℝ))⁻¹≤1 := by nlinarith
  cases a <;> simp only [atomVal] <;> constructor <;> linarith

/-- Every atom numerator at precision `b` lies between `-2^b` and `2^b`. -/
theorem atomNumerator_bounds (b : ℕ) (a : Atom) :
    -((2:ℤ)^b)≤atomNumerator b a ∧ atomNumerator b a≤(2:ℤ)^b := by
  have hp : 0≤(2:ℝ)^b := by positivity
  have hlo : ((-((2:ℤ)^b):ℤ):ℝ)+(1:ℝ)/2≤atomVal a*(2:ℝ)^b+(1:ℝ)/2 := by
    push_cast
    nlinarith [(mul_le_mul_of_nonneg_right (atomVal_bounds a).1 hp)]
  have hhi : atomVal a*(2:ℝ)^b+(1:ℝ)/2≤(((2:ℤ)^b:ℤ):ℝ)+(1:ℝ)/2 := by
    push_cast
    nlinarith [(mul_le_mul_of_nonneg_right (atomVal_bounds a).2 hp)]
  exact ⟨by simpa only [floor_int_half,floor_atom] using Int.floor_mono hlo,
    by simpa only [floor_int_half,floor_atom] using Int.floor_mono hhi⟩

/-- A half-scaled difference of three dyadic coefficients, with the last conjugated, is
represented at precision `b + 1` by numerators `d - r - s` and `-i + j`. -/
theorem dyadic_half (b : ℕ) (d r s i j : ℤ) :
    dyadicValue (b+1) (d-r-s) (-i+j)=
      ((1:ℂ)/2)*(dyadicValue b d 0-dyadicValue b r i-star (dyadicValue b s j)) := by
  simp only [dyadicValue,pow_succ,star_div₀,star_add,star_mul,star_pow,
    star_intCast,star_ofNat,Complex.star_def,Complex.conj_I]
  push_cast
  field_simp
  ring

/-- The dyadic value with both numerators zero is zero. -/
theorem dyadic_zero (b : ℕ) : dyadicValue b 0 0=0 := by simp [dyadicValue]

/-- The dyadic value with real numerator `2^b` and imaginary numerator zero is one. -/
theorem dyadic_one (b : ℕ) : dyadicValue b ((2:ℤ)^b) 0=1 := by
  simp [dyadicValue]

end Qatlib.Concepts.UniformBqp.FiniteGateWord
