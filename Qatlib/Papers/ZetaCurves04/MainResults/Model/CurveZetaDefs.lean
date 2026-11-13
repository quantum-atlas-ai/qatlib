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
# Curve zeta data and algorithm records

This module defines abstract data for the curve zeta computations of [Kedlaya2006]. `CurveData`
records numerical curve parameters and counting functions, while `PointCountWeil`,
`OrbitCountIdentity`, and `PluckerBound` express conditions on these data. The function
`halfPower` represents the square root of a natural power and satisfies elementary power
identities.

`UniformSampler` records a finite probability distribution with a multiplicative uniformity
bound and a separate success parameter. `PolyBoundedTwo` and `PolyBoundedThree` express uniform
polynomial cost bounds, and the algorithm structures store outputs, costs, and success fields.
These legacy structures are specifications only: their success scalars are not
probabilities of correct execution and their cost fields are not certified runtimes.
Algorithm existence headlines are statement-only declarations in the result modules.

## Main statements

* `halfPower_sq`, `halfPower_even`: identities for the square root of a natural power.
* `OrbitCountIdentity.one`: the orbit-count identity equates the degree-one point and prime
  divisor counts.
* `minProb_le`, `exists_minProb_eq`: the minimum of a real function on a nonempty finite type is
  a lower bound and is attained.

## References

* [Kedlaya, 2006][Kedlaya2006]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.ZetaCurves04.MainResults.Model

/-- The nonnegative real square root of `(q : ℝ) ^ n`, representing q^(n/2). -/
def halfPower (q n : ℕ) : ℝ := Real.sqrt ((q : ℝ) ^ n)

/-- The half power with exponent zero equals one for every natural base. -/
@[simp] theorem halfPower_zero (q : ℕ) : halfPower q 0 = 1 := by
  simp [halfPower]

/-- Every value of `halfPower` is nonnegative. -/
theorem halfPower_nonneg (q n : ℕ) : 0 ≤ halfPower q n := Real.sqrt_nonneg _

/-- Squaring `halfPower q n` recovers `(q : ℝ) ^ n`. -/
theorem halfPower_sq (q n : ℕ) : halfPower q n ^ 2 = (q : ℝ) ^ n :=
  Real.sq_sqrt (by positivity)

/-- The square root of `(q : ℝ) ^ n` equals the nth power of `Real.sqrt (q : ℝ)`. -/
theorem halfPower_eq_sqrt_pow (q n : ℕ) :
    halfPower q n = (Real.sqrt (q : ℝ)) ^ n := by
  induction n with
  | zero => simp [halfPower]
  | succ n ih =>
      unfold halfPower
      rw [pow_succ, Real.sqrt_mul (by positivity)]
      rw [show Real.sqrt ((q : ℝ) ^ n) = (Real.sqrt (q : ℝ)) ^ n from ih]
      rw [pow_succ]

/-- For a natural base `q` at least one, `halfPower q` is monotone in its exponent. -/
theorem halfPower_mono_exp {q : ℕ} (hq : 1 ≤ q) :
    Monotone (halfPower q) := by
  intro m n hmn
  unfold halfPower
  apply Real.sqrt_le_sqrt
  exact pow_le_pow_right₀ (by exact_mod_cast hq) hmn

/-- Numerical curve data consisting of field-size, genus, and degree parameters together with
point-count, class-number, and prime-divisor-count functions indexed by natural numbers. -/
structure CurveData where
  q : ℕ
  g : ℕ
  d : ℕ
  pointCount : ℕ → ℕ
  classNumber : ℕ → ℕ
  primeDivisorCount : ℕ → ℕ

/-- The condition that, for every positive `n`, `C.pointCount n` lies between q^n - 2g q^(n/2)
and q^n + 2g q^(n/2), with q^(n/2) represented by `halfPower C.q n`. -/
def PointCountWeil (C : CurveData) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    ((C.q : ℝ) ^ n - 2 * (C.g : ℝ) * halfPower C.q n ≤ (C.pointCount n : ℝ)) ∧
    ((C.pointCount n : ℝ) ≤ (C.q : ℝ) ^ n + 2 * (C.g : ℝ) * halfPower C.q n)

/-- The condition that, for every positive `n`, `C.pointCount n` equals the sum of i times
`C.primeDivisorCount i` over positive divisors i of n, viewed in the real numbers. -/
def OrbitCountIdentity (C : CurveData) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    (C.pointCount n : ℝ) = ∑ i ∈ n.divisors, (i : ℝ) * (C.primeDivisorCount i : ℝ)

/-- The genus-degree inequality `C.g ≤ (C.d - 1) * (C.d - 2) / 2`, with subtraction and division
taken in the natural numbers. -/
def PluckerBound (C : CurveData) : Prop :=
  C.g ≤ (C.d - 1) * (C.d - 2) / 2

/-- A normalized nonnegative distribution on a finite type with a parameter b ≥ 1 satisfying
`dist x ≤ b * dist y` for all x and y, together with a separate success parameter in [0, 1]. -/
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

/-- The condition `O.b ≤ 1` on a sampler's uniformity parameter, which together with `O.hb`
forces that parameter to equal one. -/
def IsOneUniform {V : Type} [Fintype V] (O : UniformSampler V) : Prop :=
  O.b ≤ 1

/-- The minimum value of a real-valued function on a nonempty finite type. -/
noncomputable def minProb {V : Type} [Fintype V] [Nonempty V] (p : V → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty p

/-- The finite minimum `minProb p` is at most the value of `p` at any point. -/
theorem minProb_le {V : Type} [Fintype V] [Nonempty V] (p : V → ℝ) (x : V) :
    minProb p ≤ p x :=
  Finset.inf'_le _ (Finset.mem_univ x)

/-- A real-valued function on a nonempty finite type attains `minProb p` at some point. -/
theorem exists_minProb_eq {V : Type} [Fintype V] [Nonempty V] (p : V → ℝ) :
    ∃ x : V, minProb p = p x := by
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_eq_inf' (s := (Finset.univ : Finset V))
    Finset.univ_nonempty p
  exact ⟨x, hx⟩

/-- The condition that a cost function in two natural parameters is bounded uniformly by c(a + b
+ 1)^e for some natural constants c and e. -/
def PolyBoundedTwo (cost : ℕ → ℕ → ℕ) : Prop :=
  ∃ c e : ℕ, ∀ a b : ℕ, cost a b ≤ c * (a + b + 1) ^ e

/-- The condition that a cost function in three natural parameters is bounded uniformly by c(a +
b + n + 1)^e for some natural constants c and e. -/
def PolyBoundedThree (cost : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∃ c e : ℕ, ∀ a b n : ℕ, cost a b n ≤ c * (a + b + n + 1) ^ e

/-- A curve descriptor storing natural field-size, genus, and degree parameters together with a
separate logarithmic size parameter `logq`. -/
structure CurveDescriptor where
  q : ℕ
  g : ℕ
  d : ℕ
  logq : ℕ

/-- Legacy specification of polynomial output and independent cost/success labels;
this record alone carries no algorithm correctness or execution guarantee. -/
structure ZetaNumeratorAlgorithm where
  output : CurveDescriptor → Polynomial ℤ
  cost : CurveDescriptor → ℕ
  successProb : CurveDescriptor → ℝ

/-- Legacy natural-output specification with independent cost/success labels. -/
structure ClassNumberAlgorithm where
  output : CurveDescriptor → ℕ → ℕ
  cost : CurveDescriptor → ℕ → ℕ
  successProb : CurveDescriptor → ℕ → ℝ

/-- Legacy finite-subset specification with independent cost/success labels. -/
structure ClassGroupGeneratorAlgorithm (G : Type) [AddCommGroup G] where
  output : Finset G
  cost : ℕ → ℕ
  successProb : ℝ

/-- The orbit-count identity at degree one equates the point count and the prime divisor count,
viewed in the real numbers. -/
theorem OrbitCountIdentity.one {C : CurveData} (h : OrbitCountIdentity C) :
    (C.pointCount 1 : ℝ) = (C.primeDivisorCount 1 : ℝ) := by
  have h1 := h 1 (le_refl 1)
  simpa [Nat.divisors_one] using h1

/-- The half power at exponent `2 * n` equals `(q : ℝ) ^ n`. -/
theorem halfPower_even (q n : ℕ) :
    halfPower q (2 * n) = (q : ℝ) ^ n := by
  unfold halfPower
  rw [mul_comm 2 n, pow_mul]
  exact Real.sqrt_sq (by positivity)

end Qatlib.Papers.ZetaCurves04.MainResults.Model
