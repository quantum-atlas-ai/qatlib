/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.Divisors
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Curve counting data and sampling interfaces

This module provides abstract curve counts in `CurveData`, point-count and orbit-count
hypotheses, and the square-root expression `halfPower`. It also defines finite near-uniform
samplers, polynomial cost predicates, and output, cost, and success fields for the algorithm
records used by the zeta-curve development.

This development forms part of the formalization of [Kedlaya2006].

## Main statements

* `CurveData`: A record of field-size, genus, and degree parameters together with point,
  class-number, and prime-divisor count sequences.
* `UniformSampler`: A normalized nonnegative distribution with a factor `b ≥ 1` comparing all
  point masses and a recorded success value in the unit interval.
* `PolyBoundedTwo`: A two-variable natural cost is bounded by a constant multiple of a fixed
  power of the sum of its arguments plus one.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurve04.MainResults.Defs

/-- The nonnegative square root of `(q : ℝ) ^ n`. -/
def halfPower (q n : ℕ) : ℝ := Real.sqrt ((q : ℝ) ^ n)

/-- The half-power expression at exponent zero equals one. -/
@[simp] theorem halfPower_zero (q : ℕ) : halfPower q 0 = 1 := by
  simp [halfPower]

/-- The half-power expression is nonnegative. -/
theorem halfPower_nonneg (q n : ℕ) : 0 ≤ halfPower q n := Real.sqrt_nonneg _

/-- Squaring the half-power expression gives `(q : ℝ) ^ n`. -/
theorem halfPower_sq (q n : ℕ) : halfPower q n ^ 2 = (q : ℝ) ^ n :=
  Real.sq_sqrt (by positivity)

/-- The half-power expression equals the `n`th power of the square root of `q`. -/
theorem halfPower_eq_sqrt_pow (q n : ℕ) :
    halfPower q n = (Real.sqrt (q : ℝ)) ^ n := by
  induction n with
  | zero => simp [halfPower]
  | succ n ih =>
      unfold halfPower
      rw [pow_succ, Real.sqrt_mul (by positivity)]
      rw [show Real.sqrt ((q : ℝ) ^ n) = (Real.sqrt (q : ℝ)) ^ n from ih]
      rw [pow_succ]

/-- For `q ≥ 1`, the half-power expression is monotone in its natural exponent. -/
theorem halfPower_mono_exp {q : ℕ} (hq : 1 ≤ q) :
    Monotone (halfPower q) := by
  intro m n hmn
  unfold halfPower
  apply Real.sqrt_le_sqrt
  exact pow_le_pow_right₀ (by exact_mod_cast hq) hmn

/-- A record of field-size, genus, and degree parameters together with point, class-number, and
prime-divisor count sequences. -/
structure CurveData where
  q : ℕ
  g : ℕ
  d : ℕ
  pointCount : ℕ → ℕ
  classNumber : ℕ → ℕ
  primeDivisorCount : ℕ → ℕ

/-- For every positive `n`, the recorded point count lies between `q ^ n - 2 * g * halfPower q
n` and `q ^ n + 2 * g * halfPower q n`. -/
def PointCountWeil (C : CurveData) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ((C.q : ℝ) ^ n - 2 * (C.g : ℝ) * halfPower C.q n ≤ (C.pointCount n : ℝ)) ∧
    ((C.pointCount n : ℝ) ≤ (C.q : ℝ) ^ n + 2 * (C.g : ℝ) * halfPower C.q n)

/-- For every positive `n`, the recorded point count is the sum of `i * primeDivisorCount i`
over divisors `i` of `n`. -/
def OrbitCountIdentity (C : CurveData) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (C.pointCount n : ℝ) = ∑ i ∈ n.divisors, (i : ℝ) * (C.primeDivisorCount i : ℝ)

/-- The recorded genus satisfies the natural-number bound `g ≤ (d - 1) * (d - 2) / 2`. -/
def PluckerBound (C : CurveData) : Prop :=
  C.g ≤ (C.d - 1) * (C.d - 2) / 2

/-- A normalized nonnegative distribution with a factor `b ≥ 1` comparing all point masses and a
recorded success value in the unit interval. -/
structure UniformSampler (V : Type) [Fintype V] where
  b : ℝ
  hb : 1 ≤ b
  dist : V → ℝ
  dist_nonneg : ∀ x, 0 ≤ dist x
  dist_sum : ∑ x, dist x = 1
  success : ℝ
  success_nonneg : 0 ≤ success
  success_le_one : success ≤ 1
  uniform : ∀ x y, dist x ≤ b * dist y

/-- The sampler has uniformity factor at most one. -/
def IsOneUniform {V : Type} [Fintype V] (O : UniformSampler V) : Prop :=
  O.b ≤ 1

/-- The minimum value of a real-valued function on a nonempty finite type. -/
noncomputable def minProb {V : Type} [Fintype V] [Nonempty V] (p : V → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty p

/-- The minimum value is at most the value at any specified element. -/
theorem minProb_le {V : Type} [Fintype V] [Nonempty V] (p : V → ℝ) (x : V) :
    minProb p ≤ p x :=
  Finset.inf'_le _ (Finset.mem_univ x)

/-- The minimum value is attained at some element of the finite type. -/
theorem exists_minProb_eq {V : Type} [Fintype V] [Nonempty V] (p : V → ℝ) :
    ∃ x : V, minProb p = p x := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset V))
    Finset.univ_nonempty p
  exact ⟨x, hx⟩

/-- A two-variable natural cost is bounded by a constant multiple of a fixed power of the sum of
its arguments plus one. -/
def PolyBoundedTwo (cost : ℕ → ℕ → ℕ) : Prop :=
  ∃ c e : ℕ, ∀ a b : ℕ, cost a b ≤ c * (a + b + 1) ^ e

/-- A three-variable natural cost is bounded by a constant multiple of a fixed power of the sum
of its arguments plus one. -/
def PolyBoundedThree (cost : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ c e : ℕ, ∀ a b n : ℕ, cost a b n ≤ c * (a + b + n + 1) ^ e

/-- A record of field size, genus, degree, and a logarithmic field-size parameter. -/
structure CurveDescriptor where
  q : ℕ
  g : ℕ
  d : ℕ
  logq : ℕ

/-- A record assigning a rational polynomial output, a natural cost, and a real success value to
each curve descriptor. -/
structure ZetaNumeratorAlgorithm where
  output : CurveDescriptor → Polynomial ℚ
  cost : CurveDescriptor → ℕ
  successProb : CurveDescriptor → ℝ

/-- A record assigning a natural output, a natural cost, and a real success value to a curve
descriptor and extension degree. -/
structure ClassNumberAlgorithm where
  output : CurveDescriptor → ℕ → ℕ
  cost : CurveDescriptor → ℕ → ℕ
  successProb : CurveDescriptor → ℕ → ℝ

/-- A record of a finite subset of an additive commutative group, a natural cost function, and a
real success value. -/
structure ClassGroupGeneratorAlgorithm (G : Type) [AddCommGroup G] where
  output : Finset G
  cost : ℕ → ℕ
  successProb : ℝ

/-- At extension degree one, the orbit-count identity equates the point count and the
prime-divisor count. -/
theorem OrbitCountIdentity.one {C : CurveData} (h : OrbitCountIdentity C) :
    (C.pointCount 1 : ℝ) = (C.primeDivisorCount 1 : ℝ) := by
  have h1 := h 1 (le_refl 1)
  simpa [Nat.divisors_one] using h1

/-- At exponent `2 * n`, the half-power expression is `(q : ℝ) ^ n`. -/
theorem halfPower_even (q n : ℕ) :
    halfPower q (2 * n) = (q : ℝ) ^ n := by
  unfold halfPower
  rw [mul_comm 2 n, pow_mul]
  exact Real.sqrt_sq (by positivity)

end Qatlib.Papers.ZetaCurve04.MainResults.Defs
