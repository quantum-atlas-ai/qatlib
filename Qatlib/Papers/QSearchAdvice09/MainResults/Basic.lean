/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Qatlib.Papers.QSearchAdvice09.MainResults.PowSums
import Qatlib.Papers.QSearchAdvice09.MainResults.Zalka
import Qatlib.Papers.FixedPtSearch14.FixedPoint.SearchCore

/-!
# Search with advice and power-law costs

This module defines probability-weighted classical and quantum search cost expressions,
amplitude-amplification probabilities, and power-law advice distributions. It proves analytic
upper and lower bounds, power-sum asymptotics, and conditional reductions for the cost model of
Algorithm 3, including the exact prepared-circuit amplification law.

The source paper is [Montanaro2011].

## Main statements

* `prop_2_1`: For a probability distribution on a nonempty `Fin n`, the weighted
  geometric-search bound is at most πe times the advice-weighted square-root sum.
* `prop_2_5`: For k < 0, under the stated eventual bounds on Q, gives the ten Theta
  classifications of `powerLawD` and `powerLawQ`, with power, logarithmic, and constant regimes
  at the thresholds −2, −3/2, and −1.
* `lemma_3_1`: For a unitary preparation whose marked probability is p in (0, 1), k iterations
  of the prepared amplification circuit have marked probability sin²((2k + 1)arcsin(√p)).

## References

* [Montanaro, 2011][Montanaro2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QSearchAdvice09.MainResults

open scoped BigOperators

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.FixedPtSearch14.FixedPoint
set_option warningAsError false

/-- The function p is nonnegative on `Fin n` and sums to one. -/
def IsProbDist (n : ℕ) (p : Fin n → ℝ) : Prop :=
  (∀ x, 0 ≤ p x) ∧ ∑ x : Fin n, p x = 1

/-- The advice-weighted sum of √(x + 1) over x in `Fin n`. -/
def adviceSqrtSum {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ x : Fin n, p x * Real.sqrt ((x : ℕ) + 1 : ℝ)

/-- The advice-weighted average of the ordered search positions x + 1. -/
def classicalAverageQueries {n : ℕ} (p : Fin n → ℝ) : ℝ :=
  ∑ x : Fin n, p x * ((x : ℕ) + 1 : ℝ)

/-- The geometric-search upper-bound expression 2 log x + 4 + (πe/2)√x. -/
def geometricSearchQueryUpper (x : ℝ) : ℝ :=
  2 * Real.log x + 4 + (Real.pi * Real.exp 1 / 2) * Real.sqrt x

/-- The amplification success expression sin²((2k + 1)θ). -/
def amplSuccessProb (θ : ℝ) (k : ℕ) : ℝ :=
  (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2

/-- The sum of yᵏ over the natural-number interval 1 ≤ y ≤ n. -/
def powerLawMass (k : ℝ) (n : ℕ) : ℝ :=
  ∑ y ∈ Finset.Icc 1 n, (y : ℝ) ^ k

/-- The power-law weight (x + 1)ᵏ divided by `powerLawMass k n`. -/
def powerLawProb (k : ℝ) (n : ℕ) (x : Fin n) : ℝ :=
  (((x : ℕ) + 1 : ℝ) ^ k) / powerLawMass k n

/-- The ratio of the power sum with exponent k + 1 to the normalizing power sum with exponent k. -/
def powerLawD (k : ℝ) (n : ℕ) : ℝ :=
  (∑ x ∈ Finset.Icc 1 n, (x : ℝ) ^ (k + 1)) / powerLawMass k n

/-- The ratio of the power sum with exponent k + 1/2 to the normalizing power sum with exponent
k. -/
def powerLawQ (k : ℝ) (n : ℕ) : ℝ :=
  (∑ x ∈ Finset.Icc 1 n, (x : ℝ) ^ (k + 1 / 2)) / powerLawMass k n

/-- The average-amplification expression 1/2 − sin(4m arcsin(√p))/(8m√(p(1 − p))). -/
def ampAvgSuccessProb (p : ℝ) (m : ℕ) : ℝ :=
  1 / 2 - Real.sin (4 * (m : ℝ) * Real.arcsin (Real.sqrt p)) /
    (8 * (m : ℝ) * Real.sqrt (p * (1 - p)))

/-- The natural floor of kⁱ, viewed as a real number. -/
def iterCount (k : ℝ) (i : ℕ) : ℝ := ((Nat.floor (k ^ i) : ℕ) : ℝ)

/-- The sum of (iterCount k i + 3)/2 over i < j. -/
def alg3IterationCost (k : ℝ) (j : ℕ) : ℝ :=
  ∑ i ∈ Finset.range j, (iterCount k i + 3) / 2

/-- The finite first-success cost sum for the geometric amplification schedule, together with
the residual worst-case search cost. -/
def alg3QueryModel (k px : ℝ) (n : ℕ) : ℝ :=
  let J := Nat.floor (Real.logb k (Real.sqrt (n : ℝ)))
  (∑ j ∈ Finset.range (J + 1),
      (∏ i ∈ Finset.range j, (1 - ampAvgSuccessProb px (Nat.floor (k ^ i)))) *
        ampAvgSuccessProb px (Nat.floor (k ^ j)) * alg3IterationCost k (j + 1))
    + (∏ i ∈ Finset.range (J + 1), (1 - ampAvgSuccessProb px (Nat.floor (k ^ i)))) *
        (alg3IterationCost k (J + 1) + (Real.pi / 4) * Real.sqrt (n : ℝ))

/-- The power-law advice cost bound combining 83 times the square-root probability sum above
density 1/n with 53√n times the remaining probability mass and the additive constant 4/3. -/
def powerLawTstarBound (k : ℝ) (n : ℕ) : ℝ :=
  83 * (∑ x : Fin n,
        if (1 : ℝ) / (n : ℝ) < powerLawProb k n x then Real.sqrt (powerLawProb k n x) else 0)
    + 53 * Real.sqrt (n : ℝ) *
        (∑ x : Fin n,
          if powerLawProb k n x ≤ (1 : ℝ) / (n : ℝ) then powerLawProb k n x else 0)
    + 4 / 3

/-- For positive x, log x + 2 ≤ 2√x. -/
theorem log_add_two_le_two_sqrt (x : ℝ) (hx : 0 < x) : Real.log x + 2 ≤ 2 * Real.sqrt x := by
  have hx' : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hlog : Real.log x = 2 * Real.log (Real.sqrt x) := by
    rw [Real.log_sqrt hx.le]; ring
  have hbound : Real.log (Real.sqrt x) ≤ Real.sqrt x - 1 := Real.log_le_sub_one_of_pos hx'
  linarith

/-- The product πe is at least 8. -/
theorem eight_le_pi_mul_exp_one : (8 : ℝ) ≤ Real.pi * Real.exp 1 := by
  have hp : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  nlinarith

/-- For positive x, the geometric-search upper-bound expression is at most πe√x [Montanaro2011]. -/
theorem geometricSearchQueryUpper_le (x : ℝ) (hx : 0 < x) :
    geometricSearchQueryUpper x ≤ Real.pi * Real.exp 1 * Real.sqrt x := by
  have hlog := log_add_two_le_two_sqrt x hx
  have hs : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hconst := eight_le_pi_mul_exp_one
  have h2 : (2 : ℝ) * Real.log x + 4 ≤ 4 * Real.sqrt x := by linarith
  calc
    geometricSearchQueryUpper x
        = 2 * Real.log x + 4 + (Real.pi * Real.exp 1 / 2) * Real.sqrt x := rfl
    _ ≤ 4 * Real.sqrt x + (Real.pi * Real.exp 1 / 2) * Real.sqrt x := by gcongr
    _ = (4 + Real.pi * Real.exp 1 / 2) * Real.sqrt x := by ring
    _ ≤ (Real.pi * Real.exp 1) * Real.sqrt x := by
          apply mul_le_mul_of_nonneg_right _ hs
          linarith

/-- For positive p, p/√p equals √p. -/
theorem div_sqrt_self (p : ℝ) (hp : 0 < p) : p / Real.sqrt p = Real.sqrt p := by
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  rw [div_eq_iff hs.ne']
  calc p = (Real.sqrt p) ^ 2 := (Real.sq_sqrt hp.le).symm
    _ = Real.sqrt p * Real.sqrt p := by ring

/-- For a probability distribution on a nonempty `Fin n`, the weighted geometric-search bound is
at most πe times the advice-weighted square-root sum [Montanaro2011]. -/
theorem prop_2_1 (n : ℕ) (hn : 0 < n) (p : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x : Fin n, p x = 1) :
    (∑ x : Fin n, p x * geometricSearchQueryUpper (((x : ℕ) + 1 : ℝ)))
      ≤ Real.pi * Real.exp 1 * ∑ x : Fin n, p x * Real.sqrt (((x : ℕ) + 1 : ℝ)) := by
  have hterm : ∀ x : Fin n,
      p x * geometricSearchQueryUpper (((x : ℕ) + 1 : ℝ))
        ≤ p x * (Real.pi * Real.exp 1 * Real.sqrt (((x : ℕ) + 1 : ℝ))) := by
    intro x
    have hx : (0 : ℝ) < ((x : ℕ) + 1 : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (geometricSearchQueryUpper_le _ hx) (hp x)
  calc
    (∑ x : Fin n, p x * geometricSearchQueryUpper (((x : ℕ) + 1 : ℝ)))
        ≤ ∑ x : Fin n, p x * (Real.pi * Real.exp 1 * Real.sqrt (((x : ℕ) + 1 : ℝ))) :=
          Finset.sum_le_sum (fun x _ => hterm x)
    _ = Real.pi * Real.exp 1 * ∑ x : Fin n, p x * Real.sqrt (((x : ℕ) + 1 : ℝ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _
          ring

/-- For n ≥ 2, 1/√n is at most sin(1/√(n − 1)). -/
theorem one_sub_div_sqrt_le_sin (n : ℕ) (hn : 2 ≤ n) :
    1 / Real.sqrt (n : ℝ) ≤ Real.sin (1 / Real.sqrt ((n : ℝ) - 1)) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) - 1 with hm
  have hm1 : 1 ≤ m := by rw [hm]; linarith
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm1
  set u : ℝ := Real.sqrt m with hu
  have hu1 : 1 ≤ u := by
    rw [hu]
    exact Real.one_le_sqrt.2 hm1
  have hu0 : 0 < u := lt_of_lt_of_le zero_lt_one hu1
  have hu2 : u ^ 2 = m := by rw [hu]; exact Real.sq_sqrt hm0.le
  have hnm : (n : ℝ) = m + 1 := by rw [hm]; ring
  have hsqn : (Real.sqrt (n : ℝ)) ^ 2 = (n : ℝ) := Real.sq_sqrt (by positivity)
  have hsin_gt : 1 / u - (1 / u) ^ 3 / 4 < Real.sin (1 / u) := by
    have hpos : (0 : ℝ) < 1 / u := by positivity
    linarith [Real.sin_gt_sub_cube hpos, pow_nonneg hpos.le 3]
  have hfrac : 1 / u - (1 / u) ^ 3 / 4 = (4 * u ^ 2 - 1) / (4 * u ^ 3) := by
    field_simp [hu0.ne']
  have hclaim2 : (4 * u ^ 2 - 1) / (4 * u ^ 3) ≤ Real.sin (1 / u) := by
    rw [← hfrac]; linarith
  have hu3pos : (0 : ℝ) < 4 * u ^ 3 := by positivity
  have hsqrtn : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hnonneg1 : (0 : ℝ) ≤ 4 * u ^ 3 := hu3pos.le
  have hnonneg2 : (0 : ℝ) ≤ (4 * u ^ 2 - 1) * Real.sqrt (n : ℝ) := by
    have h41 : (0 : ℝ) ≤ 4 * u ^ 2 - 1 := by nlinarith [hu2, hm1]
    positivity
  have hpoly : 16 * m ^ 3 ≤ (4 * m - 1) ^ 2 * (m + 1) := by
    nlinarith [sq_nonneg (m - 1), hm1]
  have hsq : (4 * u ^ 3) ^ 2 ≤ ((4 * u ^ 2 - 1) * Real.sqrt (n : ℝ)) ^ 2 := by
    have e1 : (4 * u ^ 3) ^ 2 = 16 * m ^ 3 := by
      have h6 : (4 * u ^ 3) ^ 2 = 16 * (u ^ 2) ^ 3 := by ring
      rw [h6, hu2]
    have e2 : ((4 * u ^ 2 - 1) * Real.sqrt (n : ℝ)) ^ 2 = (4 * m - 1) ^ 2 * (m + 1) := by
      rw [mul_pow, hsqn, hu2, hnm]
    rw [e1, e2]
    exact hpoly
  have hlin : 4 * u ^ 3 ≤ (4 * u ^ 2 - 1) * Real.sqrt (n : ℝ) :=
    (sq_le_sq₀ hnonneg1 hnonneg2).1 hsq
  have hclaim1 : 1 / Real.sqrt (n : ℝ) ≤ (4 * u ^ 2 - 1) / (4 * u ^ 3) := by
    rw [div_le_div_iff₀ hsqrtn hu3pos]
    simpa using! hlin
  exact le_trans hclaim1 hclaim2

/-- For n ≥ 2, arcsin(1/√n) is at most 1/√(n − 1) [Montanaro2011]. -/
theorem arcsin_inv_sqrt_le (n : ℕ) (hn : 2 ≤ n) :
    Real.arcsin (1 / Real.sqrt (n : ℝ)) ≤ 1 / Real.sqrt ((n : ℝ) - 1) := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  have hx : (1 / Real.sqrt (n : ℝ)) ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have : (0 : ℝ) < 1 / Real.sqrt (n : ℝ) := by positivity
      linarith
    · rw [div_le_one (Real.sqrt_pos.2 hnpos)]
      exact Real.one_le_sqrt.2 (by linarith)
  have hpred : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have hy : (1 / Real.sqrt ((n : ℝ) - 1)) ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor
    · have : (0 : ℝ) < 1 / Real.sqrt ((n : ℝ) - 1) := by positivity
      have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
      linarith
    · have hle1 : 1 / Real.sqrt ((n : ℝ) - 1) ≤ 1 := by
        rw [div_le_one (Real.sqrt_pos.2 hpred)]
        exact Real.one_le_sqrt.2 (by linarith)
      have hpi : (1 : ℝ) ≤ Real.pi / 2 := by nlinarith [Real.pi_gt_three]
      linarith
  exact (Real.arcsin_le_iff_le_sin hx hy).2 (one_sub_div_sqrt_le_sin n hn)

/-- For n ≥ 2, the assumed lower bound 0.206/arcsin(1/√n) − 0.316 ≤ T implies 0.206√n − 1 ≤ T
[Montanaro2011]. -/
theorem prop_2_3 (n : ℕ) (hn : 2 ≤ n) (T : ℝ)
    (hZalka : 0.206 / Real.arcsin (1 / Real.sqrt (n : ℝ)) - 0.316 ≤ T) :
    0.206 * Real.sqrt (n : ℝ) - 1 ≤ T := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set a : ℝ := Real.arcsin (1 / Real.sqrt (n : ℝ)) with ha
  have hs : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hargpos : (0 : ℝ) < 1 / Real.sqrt (n : ℝ) := by positivity
  have ha_pos : 0 < a := by rw [ha]; exact Real.arcsin_pos.2 hargpos
  have haA := arcsin_inv_sqrt_le n hn
  have h1 : 1 / (1 / Real.sqrt ((n : ℝ) - 1)) ≤ 1 / a := by
    apply one_div_le_one_div_of_le ha_pos
    simpa [ha] using! haA
  have h1' : Real.sqrt ((n : ℝ) - 1) ≤ 1 / a := by
    simpa [one_div] using! h1
  have hsqrt : Real.sqrt (n : ℝ) - 1 ≤ Real.sqrt ((n : ℝ) - 1) := by
    have hpred : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hsq : (Real.sqrt ((n : ℝ) - 1)) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt hpred.le
    have hlt : Real.sqrt (n : ℝ) < Real.sqrt ((n : ℝ) - 1) + 1 := by
      rw [Real.sqrt_lt' (by positivity : (0 : ℝ) < Real.sqrt ((n : ℝ) - 1) + 1)]
      nlinarith [hsq, Real.sqrt_nonneg ((n : ℝ) - 1)]
    linarith
  have hrec : Real.sqrt (n : ℝ) - 1 ≤ 1 / a := le_trans hsqrt h1'
  have hmul := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 0.206)
  have hstep : 0.206 * Real.sqrt (n : ℝ) - 0.206 ≤ 0.206 / a := by
    calc 0.206 * Real.sqrt (n : ℝ) - 0.206 = 0.206 * (Real.sqrt (n : ℝ) - 1) := by ring
      _ ≤ 0.206 * (1 / a) := hmul
      _ = 0.206 / a := by ring
  have hZalka' : 0.206 / a - 0.316 ≤ T := by simpa [ha] using! hZalka
  linarith

/-- For n ≥ 2, the assumed lower bound with coefficient 0.2059 and offset 0.316 implies T ≥
0.2059√n − 1 [Montanaro2011]. -/
theorem prop_2_3_sqrt_sharp (n : ℕ) (hn : 2 ≤ n) (T : ℝ)
    (h : 0.2059 / Real.arcsin (1 / Real.sqrt (n : ℝ)) - 0.316 ≤ T) :
    0.2059 * Real.sqrt (n : ℝ) - 1 ≤ T := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
  set a : ℝ := Real.arcsin (1 / Real.sqrt (n : ℝ)) with ha
  have hs : (0 : ℝ) < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnpos
  have hargpos : (0 : ℝ) < 1 / Real.sqrt (n : ℝ) := by positivity
  have ha_pos : 0 < a := by rw [ha]; exact Real.arcsin_pos.2 hargpos
  have haA := arcsin_inv_sqrt_le n hn
  have h1 : 1 / (1 / Real.sqrt ((n : ℝ) - 1)) ≤ 1 / a := by
    apply one_div_le_one_div_of_le ha_pos
    simpa [ha] using! haA
  have h1' : Real.sqrt ((n : ℝ) - 1) ≤ 1 / a := by
    simpa [one_div] using! h1
  have hsqrt : Real.sqrt (n : ℝ) - 1 ≤ Real.sqrt ((n : ℝ) - 1) := by
    have hpred : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hsq : (Real.sqrt ((n : ℝ) - 1)) ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt hpred.le
    have hlt : Real.sqrt (n : ℝ) < Real.sqrt ((n : ℝ) - 1) + 1 := by
      rw [Real.sqrt_lt' (by positivity : (0 : ℝ) < Real.sqrt ((n : ℝ) - 1) + 1)]
      nlinarith [hsq, Real.sqrt_nonneg ((n : ℝ) - 1)]
    linarith
  have hrec : Real.sqrt (n : ℝ) - 1 ≤ 1 / a := le_trans hsqrt h1'
  have hmul := mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 0.2059)
  have hstep : 0.2059 * Real.sqrt (n : ℝ) - 0.2059 ≤ 0.2059 / a := by
    calc 0.2059 * Real.sqrt (n : ℝ) - 0.2059
        = 0.2059 * (Real.sqrt (n : ℝ) - 1) := by ring
      _ ≤ 0.2059 * (1 / a) := hmul
      _ = 0.2059 / a := by ring
  have h' : 0.2059 / a - 0.316 ≤ T := by simpa [ha] using! h
  nlinarith

/-- A probability-weighted average of pointwise bounds T x ≥ 0.206√(x + 1) − 1 is at least 0.206
times the weighted square-root sum minus one [Montanaro2011]. -/
theorem prop_2_4 (n : ℕ) (p T : Fin n → ℝ) (hp : ∀ x, 0 ≤ p x)
    (hsum : ∑ x : Fin n, p x = 1)
    (hT : ∀ x : Fin n, 0.206 * Real.sqrt (((x : ℕ) + 1 : ℝ)) - 1 ≤ T x) :
    0.206 * (∑ x : Fin n, p x * Real.sqrt (((x : ℕ) + 1 : ℝ))) - 1
      ≤ ∑ x : Fin n, p x * T x := by
  have hterm : ∀ x : Fin n,
      p x * (0.206 * Real.sqrt (((x : ℕ) + 1 : ℝ)) - 1) ≤ p x * T x := by
    intro x
    exact mul_le_mul_of_nonneg_left (hT x) (hp x)
  calc
    0.206 * (∑ x : Fin n, p x * Real.sqrt (((x : ℕ) + 1 : ℝ))) - 1
        = 0.206 * (∑ x : Fin n, p x * Real.sqrt (((x : ℕ) + 1 : ℝ))) - ∑ x : Fin n, p x := by
          rw [hsum]
    _ = ∑ x : Fin n, (0.206 * (p x * Real.sqrt (((x : ℕ) + 1 : ℝ))) - p x) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    _ = ∑ x : Fin n, p x * (0.206 * Real.sqrt (((x : ℕ) + 1 : ℝ)) - 1) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
    _ ≤ ∑ x : Fin n, p x * T x := Finset.sum_le_sum (fun x _ => hterm x)

/-- The classical power-law cost ratio equals sumPow(k + 1, n)/sumPow(k, n). -/
theorem powerLawD_eq (k : ℝ) (n : ℕ) :
    powerLawD k n = sumPow (k + 1) n / sumPow k n := by
  unfold powerLawD powerLawMass
  rw [sum_Icc_one_eq_sumPow (k + 1) n, sum_Icc_one_eq_sumPow k n]

/-- The quantum power-law cost ratio equals sumPow(k + 1/2, n)/sumPow(k, n). -/
theorem powerLawQ_eq (k : ℝ) (n : ℕ) :
    powerLawQ k n = sumPow (k + 1 / 2) n / sumPow k n := by
  unfold powerLawQ powerLawMass
  rw [sum_Icc_one_eq_sumPow (k + 1 / 2) n, sum_Icc_one_eq_sumPow k n]

/-- Theta estimates for the numerator and denominator power sums give a Theta estimate for
`powerLawD` by their ratio. -/
theorem isTheta_powerLawD {k : ℝ} {gA gB : ℕ → ℝ}
    (hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (k + 1) n) gA)
    (hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow k n) gB) :
    Asymptotics.IsTheta Filter.atTop (fun n => powerLawD k n) (fun n => gA n / gB n) := by
  have hdiv : Asymptotics.IsTheta Filter.atTop
      (fun n => sumPow (k + 1) n / sumPow k n) (fun n => gA n / gB n) :=
    Asymptotics.IsTheta.div hA hB
  refine isTheta_congr (f₁ := fun n => sumPow (k + 1) n / sumPow k n)
    (g₁ := fun n => gA n / gB n) (f₂ := fun n => powerLawD k n)
    (g₂ := fun n => gA n / gB n) hdiv ?_ ?_
  · filter_upwards with n
    exact (powerLawD_eq k n).symm
  · filter_upwards with n
    rfl

/-- Theta estimates for the numerator and denominator power sums give a Theta estimate for
`powerLawQ` by their ratio. -/
theorem isTheta_powerLawQ {k : ℝ} {gA gB : ℕ → ℝ}
    (hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (k + 1 / 2) n) gA)
    (hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow k n) gB) :
    Asymptotics.IsTheta Filter.atTop (fun n => powerLawQ k n) (fun n => gA n / gB n) := by
  have hdiv : Asymptotics.IsTheta Filter.atTop
      (fun n => sumPow (k + 1 / 2) n / sumPow k n) (fun n => gA n / gB n) :=
    Asymptotics.IsTheta.div hA hB
  refine isTheta_congr (f₁ := fun n => sumPow (k + 1 / 2) n / sumPow k n)
    (g₁ := fun n => gA n / gB n) (f₂ := fun n => powerLawQ k n)
    (g₂ := fun n => gA n / gB n) hdiv ?_ ?_
  · filter_upwards with n
    exact (powerLawQ_eq k n).symm
  · filter_upwards with n
    rfl

/-- A Theta estimate by nᵃ/nᵇ becomes a Theta estimate by nᶜ when a − b = c. -/
theorem isTheta_trans_rpow {f : ℕ → ℝ} {a b c : ℝ}
    (h : Asymptotics.IsTheta Filter.atTop f (fun n : ℕ => (n : ℝ) ^ a / (n : ℝ) ^ b))
    (hc : a - b = c) :
    Asymptotics.IsTheta Filter.atTop f (fun n : ℕ => (n : ℝ) ^ c) :=
  h.trans (isTheta_rpow_div hc)

/-- A Theta estimate at infinity is preserved when both functions are replaced by eventually
equal functions. -/
theorem isTheta_of_eventuallyEq {f₁ f₂ g₁ g₂ : ℕ → ℝ}
    (hf : f₁ =ᶠ[Filter.atTop] f₂) (hg : g₁ =ᶠ[Filter.atTop] g₂)
    (h : Asymptotics.IsTheta Filter.atTop f₁ g₁) :
    Asymptotics.IsTheta Filter.atTop f₂ g₂ :=
  isTheta_congr h hf hg

/-- For k < 0, under the stated eventual bounds on Q, gives the ten Theta classifications of
`powerLawD` and `powerLawQ`, with power, logarithmic, and constant regimes at the thresholds
−2, −3/2, and −1 [Montanaro2011]. -/
theorem prop_2_5 (k : ℝ) (hk : k < 0) (Q : ℕ → ℝ)
    (hQ_pos : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ Q n)
    (hQ_lo : ∀ᶠ n : ℕ in Filter.atTop, 0.206 * powerLawQ k n - 1 ≤ Q n)
    (hQ_hi : ∀ᶠ n : ℕ in Filter.atTop, Q n ≤ Real.pi * Real.exp 1 * powerLawQ k n) :
    ((-1 < k ∧ k < 0) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawD k n) (fun n => (n : ℝ)))
  ∧ ((-1 < k ∧ k < 0) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawQ k n) (fun n => Real.sqrt (n : ℝ)))
  ∧ ((k = -1) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawD k n)
          (fun n => (n : ℝ) / Real.log (n : ℝ)))
  ∧ ((k = -1) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawQ k n)
          (fun n => Real.sqrt (n : ℝ) / Real.log (n : ℝ)))
  ∧ ((-2 < k ∧ k < -1) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawD k n)
          (fun n => (n : ℝ) ^ (k + 2)))
  ∧ ((-(3 : ℝ) / 2 < k ∧ k < -1) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawQ k n)
          (fun n => (n : ℝ) ^ (k + 3 / 2)))
  ∧ ((k = -2) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawD k n) (fun n => Real.log (n : ℝ)))
  ∧ ((k = -(3 : ℝ) / 2) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawQ k n) (fun n => Real.log (n : ℝ)))
  ∧ ((k < -2) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawD k n) (fun _ => (1 : ℝ)))
  ∧ ((k < -(3 : ℝ) / 2) →
        Asymptotics.IsTheta Filter.atTop (fun n => powerLawQ k n) (fun _ => (1 : ℝ))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hk'
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (k + 1) n)
        (fun n : ℕ => (n : ℝ) ^ ((k + 1) + 1)) :=
      sumPow_isTheta_pos (r := k + 1) (by linarith [hk'.1])
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow k n)
        (fun n : ℕ => (n : ℝ) ^ (k + 1)) :=
      sumPow_isTheta_pos (r := k) (by linarith [hk'.1])
    have hD := isTheta_powerLawD hA hB
    have h1 := isTheta_trans_rpow hD (a := (k + 1) + 1) (b := k + 1) (c := 1) (by ring)
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n; rw [Real.rpow_one]) h1
  · intro hk'
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (k + 1 / 2) n)
        (fun n : ℕ => (n : ℝ) ^ ((k + 1 / 2) + 1)) :=
      sumPow_isTheta_pos (r := k + 1 / 2) (by linarith [hk'.1])
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow k n)
        (fun n : ℕ => (n : ℝ) ^ (k + 1)) :=
      sumPow_isTheta_pos (r := k) (by linarith [hk'.1])
    have hQ := isTheta_powerLawQ hA hB
    have h1 := isTheta_trans_rpow hQ (a := (k + 1 / 2) + 1) (b := k + 1) (c := 1 / 2) (by ring)
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n
          rw [← Real.sqrt_eq_rpow])
      h1
  · intro hk'
    rw [hk']
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow ((-1 : ℝ) + 1) n)
        (fun n : ℕ => (n : ℝ) ^ (((-1 : ℝ) + 1) + 1)) :=
      sumPow_isTheta_pos (r := (-1 : ℝ) + 1) (by norm_num)
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (-1 : ℝ) n)
        (fun n : ℕ => Real.log (n : ℝ)) :=
      sumPow_isTheta_neg_one
    have hD := isTheta_powerLawD hA hB
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n
          rw [show ((-1 : ℝ) + 1) + 1 = 1 by norm_num, Real.rpow_one])
      hD
  · intro hk'
    rw [hk']
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow ((-1 : ℝ) + 1 / 2) n)
        (fun n : ℕ => (n : ℝ) ^ (((-1 : ℝ) + 1 / 2) + 1)) :=
      sumPow_isTheta_pos (r := (-1 : ℝ) + 1 / 2) (by norm_num)
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (-1 : ℝ) n)
        (fun n : ℕ => Real.log (n : ℝ)) :=
      sumPow_isTheta_neg_one
    have hQ := isTheta_powerLawQ hA hB
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n
          rw [show ((-1 : ℝ) + 1 / 2) + 1 = 1 / 2 by norm_num, ← Real.sqrt_eq_rpow])
      hQ
  · intro hk'
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (k + 1) n)
        (fun n : ℕ => (n : ℝ) ^ ((k + 1) + 1)) :=
      sumPow_isTheta_pos (r := k + 1) (by linarith [hk'.1])
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow k n)
        (fun _ : ℕ => (1 : ℝ)) :=
      sumPow_isTheta_lt (r := k) (by linarith [hk'.2])
    have hD := isTheta_powerLawD hA hB
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n
          rw [div_one, show (k + 1) + 1 = k + 2 by ring])
      hD
  · intro hk'
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (k + 1 / 2) n)
        (fun n : ℕ => (n : ℝ) ^ ((k + 1 / 2) + 1)) :=
      sumPow_isTheta_pos (r := k + 1 / 2) (by linarith [hk'.1])
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow k n)
        (fun _ : ℕ => (1 : ℝ)) :=
      sumPow_isTheta_lt (r := k) (by linarith [hk'.2])
    have hQ := isTheta_powerLawQ hA hB
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n
          rw [div_one, show (k + 1 / 2) + 1 = k + 3 / 2 by ring])
      hQ
  · intro hk'
    rw [hk']
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow ((-2 : ℝ) + 1) n)
        (fun n : ℕ => Real.log (n : ℝ)) := by
      simpa [show ((-2 : ℝ) + 1) = -1 by norm_num] using! sumPow_isTheta_neg_one
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (-2 : ℝ) n)
        (fun _ : ℕ => (1 : ℝ)) :=
      sumPow_isTheta_lt (r := -2) (by norm_num)
    have hD := isTheta_powerLawD hA hB
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n; rw [div_one]) hD
  · intro hk'
    rw [hk']
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow ((-(3:ℝ)/2) + 1 / 2) n)
        (fun n : ℕ => Real.log (n : ℝ)) := by
      have h : ((-(3:ℝ)/2) + 1 / 2) = -1 := by norm_num
      rw [h]
      exact sumPow_isTheta_neg_one
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (-(3:ℝ)/2) n)
        (fun _ : ℕ => (1 : ℝ)) :=
      sumPow_isTheta_lt (r := -(3:ℝ)/2) (by norm_num)
    have hQ := isTheta_powerLawQ hA hB
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n; rw [div_one]) hQ
  · intro hk'
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (k + 1) n)
        (fun _ : ℕ => (1 : ℝ)) :=
      sumPow_isTheta_lt (r := k + 1) (by linarith)
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow k n)
        (fun _ : ℕ => (1 : ℝ)) :=
      sumPow_isTheta_lt (r := k) (by linarith)
    have hD := isTheta_powerLawD hA hB
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n; norm_num) hD
  · intro hk'
    have hA : Asymptotics.IsTheta Filter.atTop (fun n => sumPow (k + 1 / 2) n)
        (fun _ : ℕ => (1 : ℝ)) :=
      sumPow_isTheta_lt (r := k + 1 / 2) (by linarith)
    have hB : Asymptotics.IsTheta Filter.atTop (fun n => sumPow k n)
        (fun _ : ℕ => (1 : ℝ)) :=
      sumPow_isTheta_lt (r := k) (by linarith)
    have hQ := isTheta_powerLawQ hA hB
    exact isTheta_of_eventuallyEq (by filter_upwards with n; rfl)
      (by filter_upwards with n; norm_num) hQ

/-- The power-law normalizing mass is positive for n ≥ 1. -/
theorem powerLawMass_pos (k : ℝ) (n : ℕ) (hn : 1 ≤ n) : 0 < powerLawMass k n := by
  unfold powerLawMass
  apply Finset.sum_pos
  · intro x hx
    have hx1 : 1 ≤ x := (Finset.mem_Icc.mp hx).1
    have hx0 : (0 : ℝ) < (x : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num : (0 : ℕ) < 1) hx1)
    exact Real.rpow_pos_of_pos hx0 k
  · exact ⟨1, by simp [hn]⟩

/-- For k < 0 and n ≥ 1, the quantum power-law cost ratio is at least one. -/
theorem powerLawQ_ge_one (k : ℝ) (hk : k < 0) (n : ℕ) (hn : 1 ≤ n) :
    1 ≤ powerLawQ k n := by
  unfold powerLawQ
  have hpos := powerLawMass_pos k n hn
  rw [le_div_iff₀ hpos]
  have hle : powerLawMass k n ≤ ∑ x ∈ Finset.Icc 1 n, (x : ℝ) ^ (k + 1 / 2) := by
    unfold powerLawMass
    apply Finset.sum_le_sum
    intro x hx
    have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hx).1
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith : k ≤ k + 1 / 2)
  simpa using! hle

/-- For k < 0 and n ≥ 1, the quantum power-law ratio satisfies its stated lower comparison with
coefficient 0.206 and upper comparison with factor πe. -/
theorem powerLawQ_sandwich (k : ℝ) (hk : k < 0) (n : ℕ) (hn : 1 ≤ n) :
    0.206 * powerLawQ k n - 1 ≤ powerLawQ k n ∧
      powerLawQ k n ≤ Real.pi * Real.exp 1 * powerLawQ k n := by
  have h1 := powerLawQ_ge_one k hk n hn
  have hpe : (1 : ℝ) ≤ Real.pi * Real.exp 1 := by
    nlinarith [Real.pi_gt_three, Real.exp_one_gt_d9]
  constructor <;> nlinarith

/-- For 0 < ε < 1/2, some exponent between −2 and −3/2 gives a bounded quantum power-law ratio
while n^(1/2 − ε) is bounded above in big-O by the classical ratio [Montanaro2011]. -/
theorem cor_2_6 (ε : ℝ) (hε0 : 0 < ε) (hε : ε < 1 / 2) :
    ∃ k : ℝ, -2 < k ∧ k < -(3 : ℝ) / 2 ∧
      Asymptotics.IsBigO Filter.atTop (fun n : ℕ => (n : ℝ) ^ (1 / 2 - ε))
        (fun n : ℕ => powerLawD k n) ∧
      Asymptotics.IsBigO Filter.atTop (fun n : ℕ => powerLawQ k n)
        (fun _ : ℕ => (1 : ℝ)) := by
  have hkneg : (-(3 : ℝ) / 2 - ε) < 0 := by linarith
  have hev_pos : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ powerLawQ (-(3 : ℝ) / 2 - ε) n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => powerLawQ_ge_one _ hkneg n hn⟩
  have hev_lo : ∀ᶠ n : ℕ in Filter.atTop,
      0.206 * powerLawQ (-(3 : ℝ) / 2 - ε) n - 1 ≤ powerLawQ (-(3 : ℝ) / 2 - ε) n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => (powerLawQ_sandwich _ hkneg n hn).1⟩
  have hev_hi : ∀ᶠ n : ℕ in Filter.atTop,
      powerLawQ (-(3 : ℝ) / 2 - ε) n ≤
        Real.pi * Real.exp 1 * powerLawQ (-(3 : ℝ) / 2 - ε) n :=
    Filter.eventually_atTop.2 ⟨1, fun n hn => (powerLawQ_sandwich _ hkneg n hn).2⟩
  obtain ⟨-, -, -, -, hD3, -, -, -, -, hQ5⟩ :=
    prop_2_5 (-(3 : ℝ) / 2 - ε) hkneg (powerLawQ (-(3 : ℝ) / 2 - ε)) hev_pos hev_lo hev_hi
  refine ⟨-(3 : ℝ) / 2 - ε, by linarith, by linarith, ?_, ?_⟩
  · have hth := hD3 ⟨by linarith, by linarith⟩
    have hexp : (-(3 : ℝ) / 2 - ε) + 2 = 1 / 2 - ε := by ring
    simpa [hexp] using! hth.isBigO_symm
  · exact (hQ5 (by linarith)).isBigO

/-- For a unitary preparation whose marked probability is p in (0, 1), k iterations of the
prepared amplification circuit have marked probability sin²((2k + 1)arcsin(√p))
[Montanaro2011]. -/
theorem lemma_3_1 {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (j : I) (S : Finset I) (p : ℝ) (k : ℕ)
    (hA : A ∈ Matrix.unitaryGroup I ℂ)
    (hp0 : 0 < p) (hp1 : p < 1)
    (hp : MeasureProb (preparedAAState A j) S = p) :
    MeasureProb (Run (preparedMark S) (preparedAACircuit A j k) (Ket j)) S
      = (Real.sin ((2 * (k : ℝ) + 1) * Real.arcsin (Real.sqrt p))) ^ 2 := by
  have hspos : 0 < Real.sqrt p := Real.sqrt_pos.2 hp0
  have hslt : Real.sqrt p < 1 := by
    rw [Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)]
    norm_num
    exact hp1
  have hθ0 : 0 < Real.arcsin (Real.sqrt p) := Real.arcsin_pos.2 hspos
  have hθ1 : Real.arcsin (Real.sqrt p) < Real.pi / 2 :=
    Real.arcsin_lt_pi_div_two.2 hslt
  have hsin : Real.sin (Real.arcsin (Real.sqrt p)) = Real.sqrt p :=
    Real.sin_arcsin (by linarith [Real.sqrt_nonneg p]) hslt.le
  have hp' : MeasureProb (preparedAAState A j) S =
      (Real.sin (Real.arcsin (Real.sqrt p))) ^ 2 := by
    rw [hsin, Real.sq_sqrt hp0.le]; exact hp
  exact phase_mark_success_exact A j S (Real.arcsin (Real.sqrt p)) k hA hθ0 hθ1 hp'

/-- The triple (k + 1, k, k + 1) recording the amplification access counts. -/
def amplQueryLedger (k : ℕ) : ℕ × ℕ × ℕ := (k + 1, k, k + 1)

/-- The three components of the amplification query ledger are k + 1, k, and k + 1
[Montanaro2011]. -/
theorem lemma_3_1_query_ledger (k : ℕ) :
    (amplQueryLedger k).1 = k + 1 ∧ (amplQueryLedger k).2.1 = k ∧
      (amplQueryLedger k).2.2 = k + 1 := by
  simp [amplQueryLedger]

/-- Returns the assumed analytic bound for the Algorithm 3 query model with growth factor 1.162,
bounded by the minimum of 83/√px + 4/3 and 53√n. -/
theorem prop_3_2_reduction (n : ℕ) (hn : 0 < n) (px : ℝ) (hpx0 : 0 < px) (hpx1 : px < 1)
    (h_analytic : alg3QueryModel 1.162 px n ≤
      min (83 / Real.sqrt px + 4 / 3) (53 * Real.sqrt (n : ℝ))) :
    alg3QueryModel 1.162 px n ≤ min (83 / Real.sqrt px + 4 / 3) (53 * Real.sqrt (n : ℝ)) :=
  h_analytic

/-- Pointwise Algorithm 3 cost bounds imply the advice-averaged bound obtained by splitting
probabilities at 1/n, with coefficients 83 and 53 and additive constant 4/3 [Montanaro2011]. -/
theorem cor_3_3 (n : ℕ) (hn : 0 < n) (prob : Fin n → ℝ) (T : Fin n → ℝ) (Tstar : ℝ)
    (hp : ∀ x, 0 ≤ prob x) (hsum : ∑ x : Fin n, prob x = 1)
    (hT : ∀ x, T x ≤ min (83 / Real.sqrt (prob x) + 4 / 3) (53 * Real.sqrt (n : ℝ)))
    (hTstar : Tstar ≤ ∑ x : Fin n, prob x * T x) :
    Tstar ≤ 83 * (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i),
            Real.sqrt (prob x))
      + 53 * Real.sqrt (n : ℝ) *
          (∑ x ∈ Finset.univ.filter (fun i => prob i ≤ (1 : ℝ) / (n : ℝ)), prob x)
      + 4 / 3 := by
  have hsplit : ∑ x : Fin n, prob x * T x
      = (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i), prob x * T x)
        + (∑ x ∈ Finset.univ.filter (fun i => prob i ≤ (1 : ℝ) / (n : ℝ)), prob x * T x) := by
    have h :
        (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i), prob x * T x)
          + (∑ x ∈ Finset.univ.filter (fun i => ¬ ((1 : ℝ) / (n : ℝ) < prob i)),
              prob x * T x)
          = ∑ x ∈ (Finset.univ : Finset (Fin n)), prob x * T x :=
      Finset.sum_filter_add_sum_filter_not _ _ _
    have hB : (Finset.univ.filter (fun i => ¬ ((1 : ℝ) / (n : ℝ) < prob i)))
        = Finset.univ.filter (fun i => prob i ≤ (1 : ℝ) / (n : ℝ)) := by
      apply Finset.filter_congr
      intro x _
      exact ⟨fun h => le_of_not_gt h, fun h => not_lt.mpr h⟩
    rw [hB] at h
    simpa using! h.symm
  have hA_bound :
      (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i), prob x * T x)
        ≤ 83 * (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i),
            Real.sqrt (prob x))
          + (4 / 3) * (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i),
              prob x) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x hx
    have hmem : (1 : ℝ) / (n : ℝ) < prob x := (Finset.mem_filter.mp hx).2
    have hp0 : 0 < prob x := lt_trans (by positivity) hmem
    have hTle : T x ≤ 83 / Real.sqrt (prob x) + 4 / 3 := le_trans (hT x) (min_le_left _ _)
    have hmul := mul_le_mul_of_nonneg_left hTle hp0.le
    have h1 : prob x * (83 / Real.sqrt (prob x)) = 83 * Real.sqrt (prob x) := by
      have h2 : prob x * (83 / Real.sqrt (prob x)) = 83 * (prob x / Real.sqrt (prob x)) := by
        ring
      rw [h2, div_sqrt_self (prob x) hp0]
    have heq : prob x * (83 / Real.sqrt (prob x) + 4 / 3)
        = 83 * Real.sqrt (prob x) + (4 / 3) * prob x := by
      calc prob x * (83 / Real.sqrt (prob x) + 4 / 3)
          = prob x * (83 / Real.sqrt (prob x)) + prob x * (4 / 3) := by ring
        _ = 83 * Real.sqrt (prob x) + (4 / 3) * prob x := by rw [h1]; ring
    linarith
  have hA_sum_le :
      (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i), prob x) ≤ 1 := by
    have h : (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i), prob x)
        ≤ ∑ x ∈ (Finset.univ : Finset (Fin n)), prob x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun i _ _ => hp i)
    simpa [hsum] using! h
  have hB_bound :
      (∑ x ∈ Finset.univ.filter (fun i => prob i ≤ (1 : ℝ) / (n : ℝ)), prob x * T x)
        ≤ 53 * Real.sqrt (n : ℝ) *
            (∑ x ∈ Finset.univ.filter (fun i => prob i ≤ (1 : ℝ) / (n : ℝ)), prob x) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro x hx
    have hTle : T x ≤ 53 * Real.sqrt (n : ℝ) := le_trans (hT x) (min_le_right _ _)
    have hmul := mul_le_mul_of_nonneg_left hTle (hp x)
    calc prob x * T x ≤ prob x * (53 * Real.sqrt (n : ℝ)) := hmul
      _ = 53 * Real.sqrt (n : ℝ) * prob x := by ring
  have h4 : (4 / 3) *
      (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i), prob x) ≤ 4 / 3 := by
    calc (4 / 3) * (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i), prob x)
          ≤ (4 / 3) * 1 := mul_le_mul_of_nonneg_left hA_sum_le (by norm_num)
      _ = 4 / 3 := by ring
  have hA' :
      (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i), prob x * T x)
        ≤ 83 * (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i),
            Real.sqrt (prob x)) + 4 / 3 := by
    linarith
  have hfinal : ∑ x : Fin n, prob x * T x
      ≤ 83 * (∑ x ∈ Finset.univ.filter (fun i => (1 : ℝ) / (n : ℝ) < prob i),
            Real.sqrt (prob x))
        + 53 * Real.sqrt (n : ℝ) *
            (∑ x ∈ Finset.univ.filter (fun i => prob i ≤ (1 : ℝ) / (n : ℝ)), prob x)
        + 4 / 3 := by
    rw [hsplit]
    linarith
  linarith

/-- Eventually nonnegative functions with f ≤ g eventually satisfy f = O(g) at infinity. -/
theorem isBigO_of_eventually_le {f g : ℕ → ℝ}
    (hf : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ f n)
    (hg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ g n)
    (h : ∀ᶠ n : ℕ in Filter.atTop, f n ≤ g n) :
    Asymptotics.IsBigO Filter.atTop f g := by
  refine Asymptotics.IsBigO.of_bound 1 ?_
  filter_upwards [hf, hg, h] with n hf' hg' hle
  rw [Real.norm_of_nonneg hf', Real.norm_of_nonneg hg', one_mul]
  exact hle

/-- Transfers the assumed power-law cost-bound estimates to an eventually nonnegative function
Tstar dominated by that bound, yielding the stated square-root, power, logarithmic, and
constant big-O implications [Montanaro2011]. -/
theorem prop_3_4 (k : ℝ) (hk : k < 0) (Tstar : ℕ → ℝ)
    (h_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ Tstar n)
    (h_bound_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ powerLawTstarBound k n)
    (h_bound : ∀ᶠ n : ℕ in Filter.atTop, Tstar n ≤ powerLawTstarBound k n)
    (h_sqrt : Asymptotics.IsBigO Filter.atTop (fun n => powerLawTstarBound k n)
      (fun n => Real.sqrt (n : ℝ)))
    (h_pow : Asymptotics.IsBigO Filter.atTop (fun n => powerLawTstarBound k n)
      (fun n => (n : ℝ) ^ (-(1 / 2 + 1 / k))))
    (h_log : Asymptotics.IsBigO Filter.atTop (fun n => powerLawTstarBound k n)
      (fun n => Real.log (n : ℝ)))
    (h_const : Asymptotics.IsBigO Filter.atTop (fun n => powerLawTstarBound k n)
      (fun _ => (1 : ℝ))) :
    ((-1 ≤ k ∧ k < 0) →
        Asymptotics.IsBigO Filter.atTop Tstar (fun n => Real.sqrt (n : ℝ)))
  ∧ ((-2 < k ∧ k < -1) →
        Asymptotics.IsBigO Filter.atTop Tstar (fun n => (n : ℝ) ^ (-(1 / 2 + 1 / k))))
  ∧ ((k = -2) →
        Asymptotics.IsBigO Filter.atTop Tstar (fun n => Real.log (n : ℝ)))
  ∧ ((k < -2) →
        Asymptotics.IsBigO Filter.atTop Tstar (fun _ => (1 : ℝ))) := by
  have hbase : Asymptotics.IsBigO Filter.atTop Tstar (fun n => powerLawTstarBound k n) :=
    isBigO_of_eventually_le h_nonneg h_bound_nonneg h_bound
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro _
    exact hbase.trans h_sqrt
  · intro _
    exact hbase.trans h_pow
  · intro _
    exact hbase.trans h_log
  · intro _
    exact hbase.trans h_const

end Qatlib.Papers.QSearchAdvice09.MainResults
