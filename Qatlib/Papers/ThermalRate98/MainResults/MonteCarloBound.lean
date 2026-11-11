/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Basic.IsEmpty.Defs
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Finite probability and Monte Carlo bounds

This module defines finite probability weights, expectation, variance, product weights, and the
sample mean for the sampling analysis of [LidarWang1999]. It proves elementary expectation
identities, the variance bound of `1 / 4` for variables in the unit interval, and a finite
Chebyshev inequality.

The product construction is normalized by `prodProb_isProb`, and `sampleMean_expect` establishes
unbiasedness for a positive number of samples.

## Main statements

* `variance_le_quarter`: bounds the variance of a variable taking values in the unit interval.
* `chebyshev_finite`: bounds the weighted mass of deviations from the expectation.
* `sampleMean_expect`: identifies the expected sample mean with the original expectation.

## References

* [Lidar and Wang, 1999][LidarWang1999]
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.ThermalRate98.MainResults

section Single

variable {α : Type*} [Fintype α]

/-- A finite real weight function is a probability distribution when its weights are nonnegative
and sum to one. -/
def IsProb (p : α → ℝ) : Prop := (∀ a, 0 ≤ p a) ∧ (∑ a, p a = 1)

/-- The finite weighted expectation of `X` with weights `p`. -/
def expect (p X : α → ℝ) : ℝ := ∑ a, p a * X a

/-- The finite weighted sum of squared deviations of `X` from `expect p X`. -/
def variance (p X : α → ℝ) : ℝ := ∑ a, p a * (X a - expect p X) ^ 2

/-- A constant has its own value as expectation when the weights sum to one. -/
theorem expect_const (p : α → ℝ) (hsum : ∑ a, p a = 1) (c : ℝ) :
    expect p (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, hsum, one_mul]

/-- Finite weighted expectation preserves pointwise addition. -/
theorem expect_add (p X Y : α → ℝ) :
    expect p (fun a => X a + Y a) = expect p X + expect p Y := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Finite weighted expectation preserves pointwise subtraction. -/
theorem expect_sub (p X Y : α → ℝ) :
    expect p (fun a => X a - Y a) = expect p X - expect p Y := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A real constant factor can be pulled out of finite weighted expectation. -/
theorem expect_mul_const (p X : α → ℝ) (c : ℝ) :
    expect p (fun a => c * X a) = c * expect p X := by
  unfold expect
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The expectation is nonnegative when both the weights and the values are nonnegative. -/
theorem expect_nonneg (p X : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hX : ∀ a, 0 ≤ X a) :
    0 ≤ expect p X := by
  unfold expect
  exact Finset.sum_nonneg (fun a _ => mul_nonneg (hp a) (hX a))

/-- With nonnegative weights summing to one, the expectation of a function bounded above by one
is at most one. -/
theorem expect_le_one (p X : α → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    (hX : ∀ a, X a ≤ 1) :
    expect p X ≤ 1 := by
  unfold expect
  calc (∑ a, p a * X a) ≤ ∑ a, p a * 1 := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (hX a) (hp a)
    _ = 1 := by simpa using hsum

/-- When the weights sum to one, variance equals the second moment minus the square of the
expectation. -/
theorem variance_eq (p X : α → ℝ) (hsum : ∑ a, p a = 1) :
    variance p X = expect p (fun a => X a ^ 2) - (expect p X) ^ 2 := by
  have hpt : ∀ a, p a * (X a - expect p X) ^ 2 =
      p a * X a ^ 2 - 2 * (expect p X) * (p a * X a) + (expect p X) ^ 2 * p a := by
    intro a
    ring
  calc variance p X
      = ∑ a, (p a * X a ^ 2 - 2 * (expect p X) * (p a * X a)
          + (expect p X) ^ 2 * p a) := by
        unfold variance
        apply Finset.sum_congr rfl
        intro a _
        exact hpt a
    _ = (∑ a, p a * X a ^ 2) - 2 * (expect p X) * (∑ a, p a * X a)
          + (expect p X) ^ 2 * (∑ a, p a) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [show (∑ a, 2 * (expect p X) * (p a * X a))
            = 2 * (expect p X) * (∑ a, p a * X a) by
              rw [Finset.mul_sum]]
        rw [show (∑ a, (expect p X) ^ 2 * p a)
            = (expect p X) ^ 2 * (∑ a, p a) by
              rw [Finset.mul_sum]]
    _ = expect p (fun a => X a ^ 2) - (expect p X) ^ 2 := by
        unfold expect
        rw [hsum, mul_one]
        ring

/-- For nonnegative weights and values in the unit interval, the second moment is at most the
first moment. -/
theorem expect_sq_le_expect (p X : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hX0 : ∀ a, 0 ≤ X a) (hX1 : ∀ a, X a ≤ 1) :
    expect p (fun a => X a ^ 2) ≤ expect p X := by
  unfold expect
  apply Finset.sum_le_sum
  intro a _
  apply mul_le_mul_of_nonneg_left _ (hp a)
  nlinarith [hX0 a, hX1 a]

/-- A finite probability distribution assigns variance at most `1 / 4` to every real function
taking values in the unit interval. See [LidarWang1999]. -/
theorem variance_le_quarter (p X : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    (hsum : ∑ a, p a = 1) (hX0 : ∀ a, 0 ≤ X a) (hX1 : ∀ a, X a ≤ 1) :
    variance p X ≤ 1 / 4 := by
  have hμ0 : 0 ≤ expect p X := expect_nonneg p X hp hX0
  have hμ1 : expect p X ≤ 1 := expect_le_one p X hp hsum hX1
  rw [variance_eq p X hsum]
  have hsq := expect_sq_le_expect p X hp hX0 hX1
  nlinarith [sq_nonneg (expect p X - 1 / 2)]

/-- For nonnegative finite weights and positive `ε`, the weight of deviations of size at least
`ε` is at most the variance divided by `ε²`. See [LidarWang1999]. -/
theorem chebyshev_finite (p X : α → ℝ) (hp : ∀ a, 0 ≤ p a)
    {ε : ℝ} (hε : 0 < ε) :
    (∑ a ∈ Finset.univ.filter (fun a => ε ≤ |X a - expect p X|), p a)
      ≤ variance p X / ε ^ 2 := by
  classical
  have hpoint : ∀ a, ε ≤ |X a - expect p X| →
      p a ≤ p a * (X a - expect p X) ^ 2 / ε ^ 2 := by
    intro a ha
    have hs : ε ^ 2 ≤ (X a - expect p X) ^ 2 := by
      rw [sq_le_sq]
      rwa [abs_of_pos hε]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < ε ^ 2)]
    nlinarith [hp a, hs]
  calc (∑ a ∈ Finset.univ.filter (fun a => ε ≤ |X a - expect p X|), p a)
      ≤ ∑ a ∈ Finset.univ.filter (fun a => ε ≤ |X a - expect p X|),
          p a * (X a - expect p X) ^ 2 / ε ^ 2 := by
        apply Finset.sum_le_sum
        intro a ha
        exact hpoint a (Finset.mem_filter.mp ha).2
    _ = (ε ^ 2)⁻¹ * ∑ a ∈ Finset.univ.filter (fun a => ε ≤ |X a - expect p X|),
          p a * (X a - expect p X) ^ 2 := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [div_eq_inv_mul]
    _ ≤ (ε ^ 2)⁻¹ * ∑ a, p a * (X a - expect p X) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        intro a _ _
        exact mul_nonneg (hp a) (sq_nonneg _)
    _ = variance p X / ε ^ 2 := by
        unfold variance
        rw [div_eq_inv_mul]

end Single

section Product

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The product weight of a sequence of `n` outcomes, with one factor of `p` for each
coordinate. -/
def prodProb (p : α → ℝ) (n : ℕ) (ω : Fin n → α) : ℝ := ∏ i, p (ω i)

/-- The arithmetic mean of the sampled values, expressed as the inverse of `n` times their sum
and equal to zero when `n = 0`. -/
def sampleMean (X : α → ℝ) (n : ℕ) (ω : Fin n → α) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i, X (ω i)

/-- The product weights of a finite probability distribution form a probability distribution on
sequences of `n` outcomes. See [LidarWang1999]. -/
theorem prodProb_isProb (p : α → ℝ) (hp : IsProb p) (n : ℕ) :
    IsProb (prodProb p n) := by
  refine ⟨fun ω => Finset.prod_nonneg (fun i _ => hp.1 _), ?_⟩
  unfold prodProb
  rw [← Fintype.piFinset_univ]
  rw [Finset.sum_prod_piFinset]
  simp [hp.2]

/-- Summing a product of coordinate functions over all finite sequences factors into the product
of their coordinate sums. See [LidarWang1999]. -/
theorem sum_prod_factor {n : ℕ} (g : Fin n → α → ℝ) :
    (∑ ω : Fin n → α, ∏ i, g i (ω i)) = ∏ i, ∑ x, g i x := by
  rw [← Fintype.piFinset_univ]
  simpa using Finset.sum_prod_piFinset (Finset.univ : Finset α) g

/-- For a positive number of independent samples from a finite probability distribution, the
sample mean has expectation `expect p X`. See [LidarWang1999]. -/
theorem sampleMean_expect (p X : α → ℝ) (hp : IsProb p) {n : ℕ} (hn : 0 < n) :
    expect (prodProb p n) (sampleMean X n) = expect p X := by
  classical
  have hfac : ∀ ω : Fin n → α,
      prodProb p n ω * sampleMean X n ω =
        (n : ℝ)⁻¹ * (prodProb p n ω * ∑ i, X (ω i)) := by
    intro ω
    unfold prodProb sampleMean
    ring
  have hinner : (∑ ω : Fin n → α, prodProb p n ω * ∑ i, X (ω i))
      = (n : ℝ) * expect p X := by
    have h1 : ∀ ω : Fin n → α, prodProb p n ω * (∑ i, X (ω i))
        = ∑ i, prodProb p n ω * X (ω i) := by
      intro ω
      unfold prodProb
      rw [Finset.mul_sum]
    simp only [h1]
    rw [Finset.sum_comm]
    have hi : ∀ i : Fin n, (∑ ω : Fin n → α, prodProb p n ω * X (ω i)) = expect p X := by
      intro i
      have hrewrite : ∀ ω : Fin n → α,
          prodProb p n ω * X (ω i) =
            ∏ k, (if k = i then p (ω k) * X (ω k) else p (ω k)) := by
        intro ω
        unfold prodProb
        rw [Finset.prod_eq_mul_prod_diff_singleton i (fun k => p (ω k)) (by simp)]
        rw [Finset.prod_eq_mul_prod_diff_singleton i
          (fun k => if k = i then p (ω k) * X (ω k) else p (ω k)) (by simp)]
        have hdiff :
            (∏ k ∈ Finset.univ \ {i},
                (if k = i then p (ω k) * X (ω k) else p (ω k)))
              = ∏ k ∈ Finset.univ \ {i}, p (ω k) := by
          apply Finset.prod_congr rfl
          intro k hk
          have hki : k ≠ i := by simpa using hk
          simp [hki]
        rw [hdiff]
        rw [if_pos rfl]
        ring
      calc (∑ ω : Fin n → α, prodProb p n ω * X (ω i))
          = ∑ ω : Fin n → α,
              ∏ k, (if k = i then p (ω k) * X (ω k) else p (ω k)) := by
            apply Finset.sum_congr rfl
            intro ω _
            exact hrewrite ω
        _ = ∏ k, ∑ x, (if k = i then p x * X x else p x) :=
            sum_prod_factor (fun k => fun x => if k = i then p x * X x else p x)
        _ = expect p X := by
            have hk : ∀ k : Fin n,
                (∑ x, (if k = i then p x * X x else p x)) =
                  if k = i then expect p X else 1 := by
              intro k
              by_cases h : k = i
              · simp [h, expect]
              · simp [h, hp.2]
            simp only [hk]
            rw [Finset.prod_ite_eq']
            simp
    calc (∑ i : Fin n, ∑ ω : Fin n → α, prodProb p n ω * X (ω i))
        = ∑ i : Fin n, expect p X := by
          apply Finset.sum_congr rfl
          intro i _
          exact hi i
      _ = (n : ℝ) * expect p X := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold expect
  simp only [hfac]
  rw [← Finset.mul_sum, hinner]
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  field_simp
  rfl

end Product

end Qatlib.Papers.ThermalRate98.MainResults
