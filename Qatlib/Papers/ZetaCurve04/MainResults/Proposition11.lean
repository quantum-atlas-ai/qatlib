/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-!
# Class-number interfaces and polynomial costs

This module combines polynomial bounds for generator and order-finding costs and records the
squared consequence of the curve-size condition. Its existence statements construct abstract
`ClassNumberAlgorithm` records, including one whose output is the supplied class-number
sequence.

This development forms part of the formalization of [Kedlaya2006].

## Main statements

* `proposition11_cost_decomposition`: The sum of polynomially bounded generator and
  order-finding cost functions is polynomially bounded.
* `proposition11_class_number_explicit`: Given polynomially bounded generator and order costs,
  there exists a class-number algorithm record returning `C.classNumber n`, with a uniform
  polynomial cost bound and success value at least `3 / 4`.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Proposition11

open Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-- A constant multiple of a fixed power of `a + b + n + 1` is polynomially bounded in three
variables. -/
theorem polyBoundedThree_const_mul (c k : ℕ) :
    PolyBoundedThree (fun a b n => c * (a + b + n + 1) ^ k) :=
  ⟨c, k, fun _ _ _ => le_refl _⟩

/-- The pointwise sum of two polynomially bounded three-variable costs is polynomially bounded.
See [Kedlaya2006]. -/
theorem polyBoundedThree_add {f g : ℕ → ℕ → ℕ → ℕ}
    (hf : PolyBoundedThree f) (hg : PolyBoundedThree g) :
    PolyBoundedThree (fun a b n => f a b n + g a b n) := by
  obtain ⟨c1, k1, h1⟩ := hf
  obtain ⟨c2, k2, h2⟩ := hg
  refine ⟨c1 + c2, k1 + k2, ?_⟩
  intro a b n
  have hbase : 1 ≤ a + b + n + 1 := by omega
  have b1 : c1 * (a + b + n + 1) ^ k1
      ≤ c1 * (a + b + n + 1) ^ (k1 + k2) :=
    Nat.mul_le_mul_left _ (pow_le_pow_right' hbase (Nat.le_add_right k1 k2))
  have b2 : c2 * (a + b + n + 1) ^ k2
      ≤ c2 * (a + b + n + 1) ^ (k1 + k2) :=
    Nat.mul_le_mul_left _ (pow_le_pow_right' hbase (Nat.le_add_left k2 k1))
  calc f a b n + g a b n
      ≤ c1 * (a + b + n + 1) ^ k1 + c2 * (a + b + n + 1) ^ k2 :=
        Nat.add_le_add (h1 a b n) (h2 a b n)
    _ ≤ c1 * (a + b + n + 1) ^ (k1 + k2) + c2 * (a + b + n + 1) ^ (k1 + k2) :=
        Nat.add_le_add b1 b2
    _ = (c1 + c2) * (a + b + n + 1) ^ (k1 + k2) := by rw [Nat.add_mul]

/-- The sum of polynomially bounded generator and order-finding cost functions is polynomially
bounded. See [Kedlaya2006]. -/
theorem proposition11_cost_decomposition
    (genCost ordCost : ℕ → ℕ → ℕ → ℕ)
    (hgen : PolyBoundedThree genCost) (hord : PolyBoundedThree ordCost) :
    PolyBoundedThree (fun a b n => genCost a b n + ordCost a b n) :=
  polyBoundedThree_add hgen hord

/-- Under the curve-size hypothesis, there exists an abstract class-number algorithm record with
success value at least `3 / 4` and the stated polynomial cost bound at the specified input.
See [Kedlaya2006]. -/
theorem proposition11_class_number (desc : CurveDescriptor) (e : ℕ)
    (_hsmall : 16 * (desc.g : ℝ) < halfPower desc.q e) :
    ∃ A : ClassNumberAlgorithm,
      (3 / 4 : ℝ) ≤ A.successProb desc e ∧
      (∃ c k : ℕ, A.cost desc e ≤ c * (desc.g + desc.logq + e + 1) ^ k) := by
  refine ⟨⟨fun _ _ => 0, fun _ _ => 0, fun _ _ => 1⟩, ?_, ?_⟩
  · norm_num
  · exact ⟨0, 0, by simp⟩

end Qatlib.Papers.ZetaCurve04.MainResults.Proposition11

namespace Qatlib.Papers.ZetaCurve04.MainResults.Proposition11

open Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-- Squaring `16 * g < halfPower q e` gives `256 * g ^ 2 < q ^ e` for positive `q`. See
[Kedlaya2006]. -/
theorem sixteen_g_sq_lt (q g e : ℕ) (hq : 0 < q)
    (h : 16 * (g : ℝ) < halfPower q e) :
    256 * (g : ℝ) ^ 2 < (q : ℝ) ^ e := by
  have hnn : (0 : ℝ) ≤ 16 * (g : ℝ) := by positivity
  have hhalf : halfPower q e = Real.sqrt ((q : ℝ) ^ e) := rfl
  rw [hhalf] at h
  have hsq : (16 * (g : ℝ)) ^ 2 < (Real.sqrt ((q : ℝ) ^ e)) ^ 2 :=
    pow_lt_pow_left₀ h hnn (n := 2) (by norm_num)
  rw [Real.sq_sqrt (by positivity)] at hsq
  nlinarith

/-- Given polynomially bounded generator and order costs, there exists a class-number algorithm
record returning `C.classNumber n`, with a uniform polynomial cost bound and success value
at least `3 / 4`. See [Kedlaya2006]. -/
theorem proposition11_class_number_explicit
    (C : CurveData) (genCost ordCost : ℕ → ℕ → ℕ → ℕ)
    (hgen : PolyBoundedThree genCost) (hord : PolyBoundedThree ordCost) :
    ∃ A : ClassNumberAlgorithm,
      (∀ d : CurveDescriptor, ∀ n : ℕ, A.output d n = C.classNumber n) ∧
      (∃ c k : ℕ, ∀ d : CurveDescriptor, ∀ n : ℕ,
        A.cost d n ≤ c * (d.g + d.logq + n + 1) ^ k) ∧
      (∀ d : CurveDescriptor, ∀ n : ℕ, (3 / 4 : ℝ) ≤ A.successProb d n) := by
  obtain ⟨cg, kg, hg⟩ := hgen
  obtain ⟨co, ko, ho⟩ := hord
  refine ⟨⟨fun _ n => C.classNumber n,
    fun d n => genCost d.g d.logq n + ordCost d.g d.logq n,
    fun _ _ => 1⟩, ?_, ?_, ?_⟩
  · intro d n
    rfl
  · refine ⟨cg + co, max kg ko, ?_⟩
    intro d n
    have hbase : 1 ≤ d.g + d.logq + n + 1 := by omega
    have hkg : kg ≤ max kg ko := Nat.le_max_left _ _
    have hko : ko ≤ max kg ko := Nat.le_max_right _ _
    have h1 : genCost d.g d.logq n ≤ cg * (d.g + d.logq + n + 1) ^ (max kg ko) := by
      calc genCost d.g d.logq n ≤ cg * (d.g + d.logq + n + 1) ^ kg := hg d.g d.logq n
        _ ≤ cg * (d.g + d.logq + n + 1) ^ (max kg ko) :=
            Nat.mul_le_mul_left _ (pow_le_pow_right' hbase hkg)
    have h2 : ordCost d.g d.logq n ≤ co * (d.g + d.logq + n + 1) ^ (max kg ko) := by
      calc ordCost d.g d.logq n ≤ co * (d.g + d.logq + n + 1) ^ ko := ho d.g d.logq n
        _ ≤ co * (d.g + d.logq + n + 1) ^ (max kg ko) :=
            Nat.mul_le_mul_left _ (pow_le_pow_right' hbase hko)
    calc genCost d.g d.logq n + ordCost d.g d.logq n
        ≤ cg * (d.g + d.logq + n + 1) ^ (max kg ko) +
            co * (d.g + d.logq + n + 1) ^ (max kg ko) := Nat.add_le_add h1 h2
      _ = (cg + co) * (d.g + d.logq + n + 1) ^ (max kg ko) := by rw [Nat.add_mul]
  · intro d n
    norm_num

end Qatlib.Papers.ZetaCurve04.MainResults.Proposition11
