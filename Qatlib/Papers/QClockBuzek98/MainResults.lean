/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Module.Defs
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.LinearCombination.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Clock amplitude costs and entropy estimates

The module defines a finite nearest-neighbor cost operator and evaluates its quadratic form on
binomial, constant, and half-shifted sine amplitude families. The sine-family calculations give
explicit norm and cost formulas, a boundary correction, and two-sided cost and inverse-size
resolution bounds.

The entropy part defines finite Shannon entropy using natural logarithms, conditional entropy,
and mutual information. `holevoBound` proves the finite-distribution entropy bound, and
`clockConstraintBounds` combines it with the sine-family resolution estimate. See
[BuzekDerkaMassar1999].

## Main statements

* `costForm_sine`: evaluates the cost of the half-shifted sine family.
* `optimalCost_two_sided`: bounds its normalized cost above and below.
* `holevoBound`: bounds entropy on N + 1 outcomes by log(N + 1).
* `clockConstraintBounds`: collects the resolution and entropy estimates.

## References

* [Bužek et al., 1999][BuzekDerkaMassar1999]
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped BigOperators

namespace Qatlib.Papers.QClockBuzek98.MainResults

/-- The angular parameter `Real.pi / (N + 1)`. -/
def theta (N : ℕ) : ℝ := Real.pi / (N + 1)

/-- The angular parameter `theta N` is positive for every natural `N`. -/
lemma theta_pos (N : ℕ) : 0 < theta N := by
  unfold theta; positivity

/-- For `N ≥ 1`, the angular parameter `theta N` is strictly less than π. -/
lemma theta_lt_pi {N : ℕ} (hN : 1 ≤ N) : theta N < Real.pi := by
  unfold theta
  rw [div_lt_iff₀ (by positivity)]
  have h1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  nlinarith [Real.pi_pos]

/-- The half-shifted sine amplitude `Real.sin (theta N * ((m : ℝ) + 1 / 2))`. -/
def sineAmplitude (N : ℕ) (m : ℕ) : ℝ := Real.sin (theta N * ((m:ℝ) + 1/2))

/-- The nearest-neighbor operator with diagonal coefficient two and adjacent coefficients minus
one, omitting neighbors outside the index interval from zero to `N`. -/
def costOp (N : ℕ) (a : ℕ → ℝ) (m : ℕ) : ℝ :=
  2 * a m
    - (if m + 1 ≤ N then a (m + 1) else 0)
    - (if 1 ≤ m then a (m - 1) else 0)

/-- The quadratic form obtained by summing `a m * costOp N a m` over indices from zero to `N`. -/
def costForm (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range (N + 1), a m * costOp N a m

/-- The sum of squared real amplitudes over indices from zero to `N`. -/
def normSq (N : ℕ) (a : ℕ → ℝ) : ℝ :=
  ∑ m ∈ range (N + 1), (a m) ^ 2

/-- For `N ≥ 1`, the sum of `Real.cos (theta N * (2 * (m : ℝ) + 1))` over indices from zero to
`N` is zero. -/
lemma sum_cos_odd {N : ℕ} (hN : 1 ≤ N) :
    (∑ m ∈ range (N + 1), Real.cos (theta N * (2 * (m:ℝ) + 1))) = 0 := by
  have hpos := theta_pos N
  have hlt := theta_lt_pi hN
  have hsinpos : 0 < Real.sin (theta N) := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  have hterm : ∀ m : ℕ, 2 * Real.sin (theta N) * Real.cos (theta N * (2*(m:ℝ)+1))
      = Real.sin (theta N * (2*((m:ℝ)+1))) - Real.sin (theta N * (2*(m:ℝ))) := by
    intro m
    rw [Real.sin_sub_sin]
    have e1 : (theta N * (2*((m:ℝ)+1)) - theta N * (2*(m:ℝ))) / 2 = theta N := by ring
    have e2 : (theta N * (2*((m:ℝ)+1)) + theta N * (2*(m:ℝ))) / 2 =
        theta N * (2*(m:ℝ)+1) := by ring
    rw [e1, e2]
  have key : 2 * Real.sin (theta N) * (∑ m ∈ range (N+1), Real.cos (theta N * (2*(m:ℝ)+1)))
      = Real.sin (theta N * (2*((N:ℝ)+1))) - Real.sin (0:ℝ) := by
    rw [Finset.mul_sum]
    rw [show (∑ m ∈ range (N+1), 2 * Real.sin (theta N) * Real.cos (theta N * (2*(m:ℝ)+1)))
         = ∑ m ∈ range (N+1),
             (Real.sin (theta N * (2*((m:ℝ)+1))) - Real.sin (theta N * (2*(m:ℝ)))) from by
           apply Finset.sum_congr rfl; intro m _; exact hterm m]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, Real.sin_zero] using
      Finset.sum_range_sub (fun m => Real.sin (theta N * (2*(m:ℝ)))) (N+1)
  have hlast : theta N * (2*((N:ℝ)+1)) = 2*Real.pi := by
    unfold theta
    have hne : ((N:ℝ)+1) ≠ 0 := by positivity
    field_simp
  simp only [hlast, Real.sin_two_pi, Real.sin_zero, sub_zero] at key
  exact (mul_eq_zero.mp key).resolve_left (by positivity)

/-- For `N ≥ 1`, the sum of `Real.cos (2 * theta N * ((m : ℝ) + 1))` over indices below `N` is
minus one. -/
lemma sum_cos_even {N : ℕ} (hN : 1 ≤ N) :
    (∑ m ∈ range N, Real.cos (2 * theta N * ((m:ℝ) + 1))) = -1 := by
  have hpos := theta_pos N
  have hlt := theta_lt_pi hN
  have hsinpos : 0 < Real.sin (theta N) := Real.sin_pos_of_pos_of_lt_pi hpos hlt
  have hterm : ∀ m : ℕ, 2 * Real.sin (theta N) * Real.cos (2 * theta N * ((m:ℝ)+1))
      = Real.sin (theta N * (2*((m:ℝ)+1)+1)) - Real.sin (theta N * (2*(m:ℝ)+1)) := by
    intro m
    rw [Real.sin_sub_sin]
    have e1 : (theta N * (2*((m:ℝ)+1)+1) - theta N * (2*(m:ℝ)+1)) / 2 = theta N := by ring
    have e2 : (theta N * (2*((m:ℝ)+1)+1) + theta N * (2*(m:ℝ)+1)) / 2 =
        2 * theta N * ((m:ℝ)+1) := by ring
    rw [e1, e2]
  have key : 2 * Real.sin (theta N) * (∑ m ∈ range N, Real.cos (2 * theta N * ((m:ℝ)+1)))
      = Real.sin (theta N * (2*(N:ℝ)+1)) - Real.sin (theta N * (2*((0:ℕ):ℝ)+1)) := by
    rw [Finset.mul_sum]
    rw [show (∑ m ∈ range N, 2 * Real.sin (theta N) * Real.cos (2 * theta N * ((m:ℝ)+1)))
         = ∑ m ∈ range N,
             (Real.sin (theta N * (2*((m:ℝ)+1)+1)) - Real.sin (theta N * (2*(m:ℝ)+1))) from by
           apply Finset.sum_congr rfl; intro m _; exact hterm m]
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero] using
      Finset.sum_range_sub (fun m => Real.sin (theta N * (2*(m:ℝ)+1))) N
  have hlast : theta N * (2*(N:ℝ)+1) = 2*Real.pi - theta N := by
    unfold theta
    have hne : ((N:ℝ)+1) ≠ 0 := by positivity
    field_simp
    ring
  have h0 : theta N * (2*((0:ℕ):ℝ)+1) = theta N := by push_cast; ring
  rw [hlast, h0, Real.sin_two_pi_sub] at key

  have key2 : 2 * Real.sin (theta N) * (∑ m ∈ range N, Real.cos (2 * theta N * ((m:ℝ)+1)))
      = -2 * Real.sin (theta N) := by
    rw [key]; ring
  have : 2 * Real.sin (theta N) * (∑ m ∈ range N, Real.cos (2 * theta N * ((m:ℝ)+1)))
      + 2 * Real.sin (theta N) = 0 := by rw [key2]; ring
  have hfac : (2 * Real.sin (theta N)) * ((∑ m ∈ range N, Real.cos (2 * theta N * ((m:ℝ)+1))) + 1) = 0 := by
    linear_combination this
  rcases mul_eq_zero.mp hfac with h | h
  · exact absurd h (by positivity)
  · linarith

/-- For `N ≥ 1`, the sum of the squared half-shifted sine amplitudes over indices from zero to
`N` is `((N : ℝ) + 1) / 2`. -/
lemma sum_sq_sin {N : ℕ} (hN : 1 ≤ N) :
    (∑ m ∈ range (N + 1), (Real.sin (theta N * ((m:ℝ) + 1/2)))^2) = ((N:ℝ)+1)/2 := by
  have hcos : ∑ m ∈ range (N+1), Real.cos (2*(theta N * ((m:ℝ)+1/2))) = 0 := by
    have heq : ∀ m : ℕ, 2*(theta N * ((m:ℝ)+1/2)) = theta N * (2*(m:ℝ)+1) := by
      intro m; ring
    simp_rw [heq]
    exact sum_cos_odd hN
  have hstep : (∑ m ∈ range (N+1), (Real.sin (theta N * ((m:ℝ) + 1/2)))^2)
      = (∑ m ∈ range (N+1), (1/2:ℝ))
        - (∑ m ∈ range (N+1), Real.cos (2*(theta N*((m:ℝ)+1/2)))/2) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro m _; rw [Real.sin_sq_eq_half_sub]
  rw [hstep, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← Finset.sum_div, hcos]
  push_cast; ring

/-- For `N ≥ 1`, the squared norm of `sineAmplitude N` is `((N : ℝ) + 1) / 2`. This evaluates
the sine family used in the clock-state analysis of [BuzekDerkaMassar1999]. -/
theorem sine_normSq {N : ℕ} (hN : 1 ≤ N) :
    normSq N (sineAmplitude N) = ((N:ℝ)+1)/2 := by
  unfold normSq sineAmplitude
  exact sum_sq_sin hN

/-- The product `Real.sin A * Real.sin B` equals `(Real.cos (A - B) - Real.cos (A + B)) / 2`. -/
lemma sin_mul_sin_eq (A B : ℝ) :
    Real.sin A * Real.sin B = (Real.cos (A - B) - Real.cos (A + B)) / 2 := by
  rw [Real.cos_sub, Real.cos_add]; ring

/-- The sine at `3 * theta N / 2` equals `(1 + 2 * Real.cos (theta N)) * Real.sin (theta N /
2)`. -/
lemma sin_three_half (N : ℕ) :
    Real.sin (3 * theta N / 2) = (1 + 2 * Real.cos (theta N)) * Real.sin (theta N / 2) := by
  have h := Real.sin_sub_sin (3 * theta N / 2) (theta N / 2)
  have e1 : (3 * theta N / 2 - theta N / 2) / 2 = theta N / 2 := by ring
  have e2 : (3 * theta N / 2 + theta N / 2) / 2 = theta N := by ring
  rw [e1, e2] at h
  have key : Real.sin (3 * theta N / 2) =
      Real.sin (theta N / 2) + 2 * Real.sin (theta N / 2) * Real.cos (theta N) := by
    linarith [h]
  rw [key]; ring

/-- Adjacent half-shifted sine values sum to twice the central value multiplied by `Real.cos
(theta N)`. -/
lemma sine_step_relation (N : ℕ) (m : ℕ) :
    Real.sin (theta N * ((m:ℝ) + 3/2)) + Real.sin (theta N * ((m:ℝ) - 1/2))
      = 2 * Real.cos (theta N) * Real.sin (theta N * ((m:ℝ) + 1/2)) := by
  have h := Real.sin_add_sin (theta N * ((m:ℝ) + 3/2)) (theta N * ((m:ℝ) - 1/2))
  have e1 : (theta N * ((m:ℝ) + 3/2) + theta N * ((m:ℝ) - 1/2)) / 2 =
      theta N * ((m:ℝ) + 1/2) := by ring
  have e2 : (theta N * ((m:ℝ) + 3/2) - theta N * ((m:ℝ) - 1/2)) / 2 = theta N := by ring
  rw [e1, e2] at h
  rw [h]; ring

/-- The scalar expression `2 - 2 * Real.cos (theta N)` equals `4 * (Real.sin (theta N / 2)) ^
2`. This is the trigonometric identity used in the sine-family estimates related to
[BuzekDerkaMassar1999]. -/
theorem sine_eigenvalue_eq (N : ℕ) :
    2 - 2 * Real.cos (theta N) = 4 * (Real.sin (theta N / 2))^2 := by
  have h := Real.sin_sq_eq_half_sub (theta N / 2)
  have e : 2 * (theta N / 2) = theta N := by ring
  rw [e] at h
  linarith [h]

/-- The scalar expression `2 - 2 * Real.cos (theta N)` is at most `(theta N) ^ 2`. This bounds
the interior spectral parameter used in the clock estimates of [BuzekDerkaMassar1999]. -/
theorem sine_eigenvalue_le_theta_sq (N : ℕ) :
    2 - 2 * Real.cos (theta N) ≤ (theta N)^2 := by
  rw [sine_eigenvalue_eq]
  have hs : (Real.sin (theta N / 2))^2 ≤ (theta N / 2)^2 := Real.sin_sq_le_sq
  nlinarith [hs]

/-- At indices strictly between zero and `N`, `costOp` acts on the sine family by multiplication
by `2 - 2 * Real.cos (theta N)`. This is the interior recurrence used in the clock-state
calculations related to [BuzekDerkaMassar1999]. -/
theorem sine_interior_eigen (N : ℕ) {m : ℕ} (hm0 : 0 < m) (hmN : m < N) :
    costOp N (sineAmplitude N) m = (2 - 2 * Real.cos (theta N)) * sineAmplitude N m := by
  have hm1 : m + 1 ≤ N := by omega
  have hmle : 1 ≤ m := hm0
  unfold costOp sineAmplitude
  rw [if_pos hm1, if_pos hmle]

  have hsub : (((m - 1 : ℕ)) : ℝ) = (m:ℝ) - 1 := by
    rw [Nat.cast_pred hm0]
  simp only [Nat.cast_add, Nat.cast_one, hsub]
  have e1 : (↑m + 1 + 1/2 : ℝ) = ↑m + 3/2 := by ring
  have e2 : (↑m - 1 + 1/2 : ℝ) = ↑m - 1/2 := by ring
  rw [e1, e2]
  have hstep := sine_step_relation N m
  linarith [hstep]

/-- For `N ≥ 1`, the left boundary value of `costOp` on the sine family equals the interior
eigenvalue expression minus `sineAmplitude N 0`. This records the boundary correction in the
sine-family calculation related to [BuzekDerkaMassar1999]. -/
theorem sine_left_boundary (N : ℕ) (hN : 1 ≤ N) :
    costOp N (sineAmplitude N) 0 =
      (2 - 2 * Real.cos (theta N)) * sineAmplitude N 0 - sineAmplitude N 0 := by
  have h1N : 0 + 1 ≤ N := by simpa using hN
  unfold costOp sineAmplitude
  rw [if_pos h1N, if_neg (by norm_num : ¬ (1:ℕ) ≤ 0)]

  have hv0 : theta N * ((0:ℕ) + 1/2) = theta N / 2 := by push_cast; ring
  have hv1 : theta N * (((1:ℕ)) + 1/2) = 3 * theta N / 2 := by push_cast; ring
  rw [hv0, hv1]
  have hbound := sin_three_half N
  have : (2:ℝ) * Real.sin (theta N / 2) - Real.sin (3 * theta N / 2)
      = (2 - 2 * Real.cos (theta N)) * Real.sin (theta N / 2) - Real.sin (theta N / 2) := by
    rw [hbound]; ring
  simpa using this

/-- The cost form equals twice the squared norm minus twice the sum of adjacent amplitude
products. -/
theorem costForm_offdiag (N : ℕ) (a : ℕ → ℝ) :
    costForm N a = 2 * normSq N a - 2 * (∑ m ∈ range N, a m * a (m+1)) := by
  unfold costForm normSq
  have hsplit : (∑ m ∈ range (N+1), a m * costOp N a m)
      = (∑ m ∈ range (N+1), a m * (2 * a m))
        - (∑ m ∈ range (N+1), a m * (if m+1 ≤ N then a (m+1) else 0))
        - (∑ m ∈ range (N+1), a m * (if 1 ≤ m then a (m-1) else 0)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro m _
    unfold costOp; ring
  rw [hsplit]
  have hA : (∑ m ∈ range (N+1), a m * (2 * a m)) = 2 * (∑ m ∈ range (N+1), (a m)^2) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro m _; ring
  have hB : (∑ m ∈ range (N+1), a m * (if m+1 ≤ N then a (m+1) else 0))
      = ∑ m ∈ range N, a m * a (m+1) := by
    rw [Finset.sum_range_succ]
    have hz : a N * (if N + 1 ≤ N then a (N + 1) else 0) = 0 := by
      rw [if_neg (by omega)]; ring
    rw [show (∑ m ∈ range N, a m * (if m + 1 ≤ N then a (m + 1) else 0))
          = ∑ m ∈ range N, a m * a (m+1) from by
          apply Finset.sum_congr rfl; intro m hm
          rw [if_pos (Nat.succ_le_of_lt (Finset.mem_range.mp hm))], hz]
    ring
  have hC : (∑ m ∈ range (N+1), a m * (if 1 ≤ m then a (m-1) else 0))
      = ∑ m ∈ range N, a m * a (m+1) := by
    rw [Finset.sum_range_succ']
    rw [show (a 0 * (if 1 ≤ (0:ℕ) then a (0-1) else 0)) = 0 from by
          rw [if_neg (by norm_num)]; ring]
    rw [show (∑ m ∈ range N, a (m+1) * (if 1 ≤ m+1 then a (m+1-1) else 0))
          = ∑ m ∈ range N, a m * a (m+1) from by
          apply Finset.sum_congr rfl; intro m _
          rw [if_pos (by omega)]
          have h : m + 1 - 1 = m := by omega
          rw [h]; ring]
    ring
  rw [hA, hB, hC]
  ring

/-- The square root of the binomial probability `(Nat.choose N m : ℝ) / (2 : ℝ) ^ N`. -/
def prodAmplitude (N m : ℕ) : ℝ := Real.sqrt ((Nat.choose N m : ℝ) / (2:ℝ)^N)

/-- The binomial amplitude family `prodAmplitude N` has squared norm one. -/
theorem prod_normSq (N : ℕ) : normSq N (prodAmplitude N) = 1 := by
  unfold normSq prodAmplitude
  have hterm : ∀ m, (Real.sqrt ((Nat.choose N m : ℝ) / (2:ℝ)^N))^2 =
      (Nat.choose N m : ℝ)/(2:ℝ)^N := by
    intro m
    rw [Real.sq_sqrt]
    positivity
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [← Finset.sum_div, ← Nat.cast_sum, Nat.sum_range_choose]
  have h2 : (0:ℝ) < (2:ℝ)^N := by positivity
  rw [Nat.cast_pow, Nat.cast_ofNat]
  field_simp

/-- The binomial family's cost equals twice one minus the adjacent-binomial square-root sum
divided by `2 ^ N`. This is the product-family cost expression associated with
[BuzekDerkaMassar1999]. -/
theorem costForm_prod (N : ℕ) :
    costForm N (prodAmplitude N) =
      2 * (1 - (∑ m ∈ range N,
        Real.sqrt ((Nat.choose N m : ℝ) * (Nat.choose N (m+1) : ℝ))) / (2:ℝ)^N) := by
  rw [costForm_offdiag, prod_normSq]
  have hterm : ∀ m, prodAmplitude N m * prodAmplitude N (m+1)
      = Real.sqrt ((Nat.choose N m : ℝ) * (Nat.choose N (m+1) : ℝ)) / (2:ℝ)^N := by
    intro m
    unfold prodAmplitude
    have hx : (0:ℝ) ≤ (Nat.choose N m : ℝ)/(2:ℝ)^N := by positivity
    rw [← Real.sqrt_mul hx]
    have h2 : (0:ℝ) < (2:ℝ)^N := by positivity
    rw [show (Nat.choose N m : ℝ)/(2:ℝ)^N * ((Nat.choose N (m+1) : ℝ)/(2:ℝ)^N)
        = ((Nat.choose N m : ℝ) * (Nat.choose N (m+1) : ℝ)) / ((2:ℝ)^N)^2 by
      field_simp]
    rw [Real.sqrt_div (by positivity)]
    congr 1
    rw [Real.sqrt_sq (le_of_lt h2)]
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [Finset.sum_div]
  ring

/-- The constant amplitude `1 / Real.sqrt ((N : ℝ) + 1)`. -/
def phaseAmplitude (N : ℕ) (_m : ℕ) : ℝ := 1 / Real.sqrt ((N:ℝ)+1)

/-- The constant amplitude family `phaseAmplitude N` has squared norm one. -/
theorem phase_normSq (N : ℕ) : normSq N (phaseAmplitude N) = 1 := by
  unfold normSq phaseAmplitude
  have hpos : (0:ℝ) < (N:ℝ)+1 := by positivity
  have hsq : (Real.sqrt ((N:ℝ)+1))^2 = (N:ℝ)+1 := Real.sq_sqrt (le_of_lt hpos)
  have hterm : ∀ m : ℕ, (1 / Real.sqrt ((N:ℝ)+1))^2 = 1/((N:ℝ)+1) := by
    intro m
    rw [div_pow, one_pow, hsq]
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  push_cast
  field_simp

/-- The constant amplitude family has cost `2 / ((N : ℝ) + 1)`. This evaluates the phase-family
cost associated with [BuzekDerkaMassar1999]. -/
theorem costForm_phase (N : ℕ) :
    costForm N (phaseAmplitude N) = 2/((N:ℝ)+1) := by
  rw [costForm_offdiag, phase_normSq]
  have hpos : (0:ℝ) < (N:ℝ)+1 := by positivity
  have hsq : (Real.sqrt ((N:ℝ)+1))^2 = (N:ℝ)+1 := Real.sq_sqrt (le_of_lt hpos)
  have hne : Real.sqrt ((N:ℝ)+1) ≠ 0 := by positivity
  have hterm : ∀ m, phaseAmplitude N m * phaseAmplitude N (m+1) = 1/((N:ℝ)+1) := by
    intro m
    unfold phaseAmplitude
    rw [show (1 / Real.sqrt ((N:ℝ)+1)) * (1 / Real.sqrt ((N:ℝ)+1))
        = 1 / (Real.sqrt ((N:ℝ)+1))^2 by field_simp]
    rw [hsq]
  rw [Finset.sum_congr rfl (fun m _ => hterm m)]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  field_simp
  ring

/-- The square root of the constant family's normalized cost equals `Real.sqrt (2 / ((N : ℝ) +
1))`. -/
theorem phaseResolution (N : ℕ) :
    Real.sqrt (costForm N (phaseAmplitude N) / normSq N (phaseAmplitude N))
      = Real.sqrt (2/((N:ℝ)+1)) := by
  rw [costForm_phase, phase_normSq, div_one]

/-- For `N ≥ 1`, the sum of adjacent sine-amplitude products equals `((N : ℝ) * Real.cos (theta
N) + 1) / 2`. -/
theorem sine_offdiag (N : ℕ) (hN : 1 ≤ N) :
    (∑ m ∈ range N, sineAmplitude N m * sineAmplitude N (m+1)) =
      ((N:ℝ) * Real.cos (theta N) + 1) / 2 := by
  unfold sineAmplitude
  push_cast
  have hterm : ∀ m : ℕ,
      Real.sin (theta N * ((m:ℝ)+1/2)) * Real.sin (theta N * ((m:ℝ)+1+1/2))
      = (Real.cos (theta N) - Real.cos (2 * theta N * ((m:ℝ)+1))) / 2 := by
    intro m
    rw [sin_mul_sin_eq]
    have e1 : theta N * ((m:ℝ)+1/2) - theta N * ((m:ℝ)+1+1/2) = - theta N := by ring
    have e2 : theta N * ((m:ℝ)+1/2) + theta N * ((m:ℝ)+1+1/2)
        = 2 * theta N * ((m:ℝ)+1) := by ring
    rw [e1, e2, Real.cos_neg]
  rw [Finset.sum_congr rfl (fun m (_ : m ∈ range N) => hterm m)]
  rw [← Finset.sum_div, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul, sum_cos_even hN]
  ring

/-- For `N ≥ 1`, the sine-family cost equals `2 * (N : ℝ) * (Real.sin (theta N / 2)) ^ 2`. -/
theorem costForm_sine (N : ℕ) (hN : 1 ≤ N) :
    costForm N (sineAmplitude N) = 2 * (N:ℝ) * (Real.sin (theta N / 2))^2 := by
  rw [costForm_offdiag, sine_normSq hN, sine_offdiag N hN]
  have hs : (Real.sin (theta N / 2))^2 = (1 - Real.cos (theta N)) / 2 := by
    have h := Real.sin_sq_eq_half_sub (theta N / 2)
    have e : 2 * (theta N / 2) = theta N := by ring
    rw [e] at h
    linarith [h]
  rw [hs]; ring

/-- For `N ≥ 1`, the sine family's cost divided by its squared norm is at most `(theta N) ^ 2`. -/
theorem optimalCost_rayleigh (N : ℕ) (hN : 1 ≤ N) :
    costForm N (sineAmplitude N) / normSq N (sineAmplitude N) ≤ (theta N)^2 := by
  rw [costForm_sine N hN, sine_normSq hN]
  have hs : (Real.sin (theta N / 2))^2 ≤ (theta N / 2)^2 := Real.sin_sq_le_sq
  have hN0 : (0:ℝ) ≤ (N:ℝ) := Nat.cast_nonneg N
  have hth : (0:ℝ) ≤ (theta N)^2 := sq_nonneg _
  rw [div_le_iff₀ (by positivity : (0:ℝ) < ((N:ℝ)+1)/2)]
  nlinarith [hs, hN0, hth]

/-- For `N ≥ 1`, the square root of the sine family's normalized cost is at most `theta N`. -/
theorem optimalTimeResolution (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (costForm N (sineAmplitude N) / normSq N (sineAmplitude N)) ≤ theta N := by
  have hray := optimalCost_rayleigh N hN
  calc Real.sqrt (costForm N (sineAmplitude N) / normSq N (sineAmplitude N))
      ≤ Real.sqrt ((theta N)^2) := Real.sqrt_le_sqrt hray
    _ = theta N := Real.sqrt_sq (le_of_lt (theta_pos N))

/-- For `N ≥ 1`, the sine family's normalized cost lies between `4 * (N : ℝ) / ((N : ℝ) + 1) ^
3` and `(theta N) ^ 2`. This gives two-sided scalar cost estimates related to the clock
analysis of [BuzekDerkaMassar1999]. -/
theorem optimalCost_two_sided (N : ℕ) (hN : 1 ≤ N) :
    (4*(N:ℝ)/((N:ℝ)+1)^3)
        ≤ costForm N (sineAmplitude N) / normSq N (sineAmplitude N) ∧
    costForm N (sineAmplitude N) / normSq N (sineAmplitude N) ≤ (theta N)^2 := by
  refine ⟨?_, optimalCost_rayleigh N hN⟩
  rw [costForm_sine N hN, sine_normSq hN]
  have hpos : (0:ℝ) < (N:ℝ)+1 := by positivity
  have hspos : (0:ℝ) ≤ theta N / 2 := by
    have := theta_pos N; positivity
  have hhalf : theta N / 2 ≤ Real.pi / 2 := by
    have htheta_le : theta N ≤ Real.pi := by
      unfold theta
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Real.pi_pos]
    linarith
  have hsin_lb : 1/((N:ℝ)+1) ≤ Real.sin (theta N / 2) := by
    have hj := Real.mul_le_sin hspos hhalf
    have he : 2/Real.pi * (theta N/2) = 1/((N:ℝ)+1) := by
      unfold theta
      field_simp
    rwa [he] at hj
  have hsin2 : 1/((N:ℝ)+1)^2 ≤ (Real.sin (theta N / 2))^2 := by
    have h0 : (0:ℝ) ≤ 1/((N:ℝ)+1) := by positivity
    have h := pow_le_pow_left₀ h0 hsin_lb 2
    have he : (1/((N:ℝ)+1))^2 = 1/((N:ℝ)+1)^2 := by
      rw [div_pow, one_pow]
    rwa [he] at h
  rw [le_div_iff₀ (by positivity : (0:ℝ) < ((N:ℝ)+1)/2)]
  have hL : 4*(N:ℝ)/((N:ℝ)+1)^3 * (((N:ℝ)+1)/2) = 2*(N:ℝ)/((N:ℝ)+1)^2 := by
    field_simp
    ring
  rw [hL]
  have hmul : 2*(N:ℝ) * (1/((N:ℝ)+1)^2)
      ≤ 2*(N:ℝ) * (Real.sin (theta N / 2))^2 :=
    mul_le_mul_of_nonneg_left hsin2 (by positivity)
  have hrew : 2*(N:ℝ) * (1/((N:ℝ)+1)^2) = 2*(N:ℝ)/((N:ℝ)+1)^2 := by ring
  rw [hrew] at hmul
  exact hmul

/-- For `N ≥ 1`, the square root of the sine family's normalized cost is at most `Real.pi / (N :
ℝ)`. This gives an inverse-size resolution bound associated with [BuzekDerkaMassar1999]. -/
theorem optimalTimeResolution_le_pi_div_N (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (costForm N (sineAmplitude N) / normSq N (sineAmplitude N))
      ≤ Real.pi / (N:ℝ) := by
  have h := optimalTimeResolution N hN
  have hN0 : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hth : theta N ≤ Real.pi / (N:ℝ) := by
    unfold theta
    have hN1 : (0:ℝ) < (N:ℝ)+1 := by positivity
    rw [div_le_div_iff₀ hN1 hN0]
    nlinarith [Real.pi_pos]
  linarith

/-- For `N ≥ 1`, the sine family has the stated exact cost and normalized square-root cost at
most `theta N`. These are scalar sine-family estimates related to [BuzekDerkaMassar1999]. -/
theorem optimalState_scaling (N : ℕ) (hN : 1 ≤ N) :
    costForm N (sineAmplitude N) = 2 * (N:ℝ) * (Real.sin (theta N / 2))^2 ∧
    Real.sqrt (costForm N (sineAmplitude N) / normSq N (sineAmplitude N)) ≤ theta N :=
  ⟨costForm_sine N hN, optimalTimeResolution N hN⟩

/-- Finite Shannon entropy `∑ i, Real.negMulLog (p i)`, using natural logarithms. -/
def shannonEntropy {n : ℕ} (p : Fin n → ℝ) : ℝ := ∑ i, Real.negMulLog (p i)

/-- The constant function on `Fin n` with value `(1 : ℝ) / n`. -/
def uniformDist (n : ℕ) : Fin n → ℝ := fun _ => (1:ℝ)/n

/-- For `n ≥ 1`, the Shannon entropy of `uniformDist n` is `Real.log (n : ℝ)`. This is the
uniform-distribution entropy used in the information-content discussion of
[BuzekDerkaMassar1999]. -/
theorem uniformEntropy {n : ℕ} (hn : 1 ≤ n) :
    shannonEntropy (uniformDist n) = Real.log (n:ℝ) := by
  unfold shannonEntropy uniformDist
  have hn0 : (n:ℝ) ≠ 0 := by
    have hpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    exact ne_of_gt hpos
  have hterm : Real.negMulLog (1/(n:ℝ)) = Real.log (n:ℝ) / (n:ℝ) := by
    unfold Real.negMulLog
    rw [one_div, Real.log_inv]
    ring
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hterm]
  field_simp

/-- A nonnegative probability distribution on `Fin (N + 1)` has Shannon entropy at most
`Real.log ((N : ℝ) + 1)` for `N ≥ 1`. This finite entropy estimate supports the
information-content bound discussed in [BuzekDerkaMassar1999]. -/
theorem holevoBound (N : ℕ) (hN : 1 ≤ N) {p : Fin (N+1) → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1) :
    shannonEntropy p ≤ Real.log ((N:ℝ) + 1) := by
  have hsum_w : (∑ _i ∈ (Finset.univ : Finset (Fin (N+1))),
      (1:ℝ) / ((N:ℝ)+1)) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    field_simp
  have hj := Real.concaveOn_negMulLog.le_map_sum
    (t := (Finset.univ : Finset (Fin (N+1))))
    (w := fun _ => (1:ℝ) / ((N:ℝ)+1))
    (p := p) (fun _ _ => by positivity) hsum_w (fun i _ => hp0 i)
  have hL : (∑ i ∈ (Finset.univ : Finset (Fin (N+1))),
        ((1:ℝ)/((N:ℝ)+1)) • Real.negMulLog (p i))
      = (1/((N:ℝ)+1)) * shannonEntropy p := by
    unfold shannonEntropy
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [smul_eq_mul]
  have hR : (∑ i ∈ (Finset.univ : Finset (Fin (N+1))),
        ((1:ℝ)/((N:ℝ)+1)) • p i) = 1/((N:ℝ)+1) := by
    simp only [smul_eq_mul]
    rw [← Finset.mul_sum, hp1, mul_one]
  rw [hL, hR] at hj
  have hrhs : Real.negMulLog (1/((N:ℝ)+1))
      = (1/((N:ℝ)+1)) * Real.log ((N:ℝ)+1) := by
    unfold Real.negMulLog
    rw [one_div, Real.log_inv]
    ring
  rw [hrhs] at hj
  have hc : 0 < (1:ℝ)/((N:ℝ)+1) := by positivity
  exact le_of_mul_le_mul_left hj hc

/-- The first marginal obtained by summing `P (x, y)` over the second coordinate. -/
def margFst {n : ℕ} (P : Fin n × Fin n → ℝ) (x : Fin n) : ℝ := ∑ y, P (x, y)

/-- The second marginal obtained by summing `P (x, y)` over the first coordinate. -/
def margSnd {n : ℕ} (P : Fin n × Fin n → ℝ) (y : Fin n) : ℝ := ∑ x, P (x, y)

/-- The conditional first-coordinate function at `y`, given by `P (x, y) / margSnd P y`, with
value zero when that marginal is zero. -/
def condDist {n : ℕ} (P : Fin n × Fin n → ℝ) (y : Fin n) : Fin n → ℝ :=
  fun x => if margSnd P y = 0 then 0 else P (x, y) / margSnd P y

/-- The sum of the entropies of `condDist P y`, weighted by `margSnd P y`. -/
def condEntropy {n : ℕ} (P : Fin n × Fin n → ℝ) : ℝ :=
  ∑ y, margSnd P y * shannonEntropy (condDist P y)

/-- The entropy of the first marginal minus the conditional entropy. -/
def mutualInfo {n : ℕ} (P : Fin n × Fin n → ℝ) : ℝ :=
  shannonEntropy (margFst P) - condEntropy P

/-- A finite function with values in `[0, 1]` has nonnegative Shannon entropy. -/
lemma shannonEntropy_nonneg {n : ℕ} {p : Fin n → ℝ}
    (h0 : ∀ i, 0 ≤ p i) (h1 : ∀ i, p i ≤ 1) : 0 ≤ shannonEntropy p := by
  unfold shannonEntropy
  apply Finset.sum_nonneg
  intro i _
  exact Real.negMulLog_nonneg (h0 i) (h1 i)

/-- If all entries of `P` are nonnegative, every conditional value `condDist P y x` is
nonnegative. -/
lemma condDist_nonneg {n : ℕ} {P : Fin n × Fin n → ℝ}
    (hP : ∀ x y, 0 ≤ P (x, y)) (y : Fin n) (x : Fin n) :
    0 ≤ condDist P y x := by
  unfold condDist
  split_ifs with h
  · norm_num
  · exact div_nonneg (hP x y) (le_of_lt (lt_of_le_of_ne (by
      unfold margSnd
      exact Finset.sum_nonneg (fun i _ => hP i y)) (Ne.symm h)))

/-- If all entries of `P` are nonnegative, every conditional value `condDist P y x` is at most
one. -/
lemma condDist_le_one {n : ℕ} {P : Fin n × Fin n → ℝ}
    (hP : ∀ x y, 0 ≤ P (x, y)) (y : Fin n) (x : Fin n) :
    condDist P y x ≤ 1 := by
  unfold condDist
  split_ifs with h
  · norm_num
  · have hq : 0 < margSnd P y := lt_of_le_of_ne (by
      unfold margSnd
      exact Finset.sum_nonneg (fun i _ => hP i y)) (Ne.symm h)
    have hle : P (x, y) ≤ margSnd P y := by
      unfold margSnd
      exact Finset.single_le_sum (f := fun i => P (i, y)) (fun i _ => hP i y)
        (Finset.mem_univ x)
    rw [div_le_one hq]
    exact hle

/-- A nonnegative joint function has nonnegative conditional entropy. -/
lemma condEntropy_nonneg {n : ℕ} {P : Fin n × Fin n → ℝ}
    (hP : ∀ x y, 0 ≤ P (x, y)) : 0 ≤ condEntropy P := by
  unfold condEntropy
  apply Finset.sum_nonneg
  intro y _
  apply mul_nonneg
  · unfold margSnd
    exact Finset.sum_nonneg (fun i _ => hP i y)
  · exact shannonEntropy_nonneg (fun x => condDist_nonneg hP y x)
      (fun x => condDist_le_one hP y x)

/-- For a nonnegative joint function, mutual information is at most the entropy of the first
marginal. -/
lemma mutualInfo_le_entropy {n : ℕ} {P : Fin n × Fin n → ℝ}
    (hP : ∀ x y, 0 ≤ P (x, y)) :
    mutualInfo P ≤ shannonEntropy (margFst P) := by
  unfold mutualInfo
  linarith [condEntropy_nonneg hP]

/-- The sum of the first marginal equals the total sum of the joint function. -/
lemma sum_margFst {n : ℕ} (P : Fin n × Fin n → ℝ) :
    ∑ x, margFst P x = ∑ p, P p := by
  unfold margFst
  rw [Fintype.sum_prod_type]

/-- The first marginal of a nonnegative joint function is nonnegative. -/
lemma margFst_nonneg {n : ℕ} {P : Fin n × Fin n → ℝ}
    (hP : ∀ x y, 0 ≤ P (x, y)) (x : Fin n) : 0 ≤ margFst P x := by
  unfold margFst
  exact Finset.sum_nonneg (fun i _ => hP x i)

/-- A nonnegative joint distribution of total mass one on `Fin n × Fin n` has mutual information
at most `Real.log (n : ℝ)` when `n ≥ 1`. This is the finite information bound used in the
discussion related to [BuzekDerkaMassar1999]. -/
lemma mutualInfo_le_log {n : ℕ} (hn : 1 ≤ n) {P : Fin n × Fin n → ℝ}
    (hP : ∀ x y, 0 ≤ P (x, y)) (hsum : ∑ p, P p = 1) :
    mutualInfo P ≤ Real.log (n:ℝ) := by
  have hbound : shannonEntropy (margFst P) ≤ Real.log (n:ℝ) := by
    have hsum' : ∑ x, margFst P x = 1 := by rw [sum_margFst, hsum]
    have hsum_w : (∑ _i ∈ (Finset.univ : Finset (Fin n)), (1:ℝ)/n) = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      field_simp
    have hj := Real.concaveOn_negMulLog.le_map_sum
      (t := (Finset.univ : Finset (Fin n)))
      (w := fun _ => (1:ℝ)/n) (p := margFst P)
      (fun _ _ => by positivity) hsum_w (fun i _ => margFst_nonneg hP i)
    have hL : (∑ i ∈ (Finset.univ : Finset (Fin n)),
          ((1:ℝ)/n) • Real.negMulLog (margFst P i))
        = (1/n) * shannonEntropy (margFst P) := by
      unfold shannonEntropy
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro i _; rw [smul_eq_mul]
    have hR : (∑ i ∈ (Finset.univ : Finset (Fin n)),
          ((1:ℝ)/n) • margFst P i) = 1/n := by
      simp only [smul_eq_mul]
      rw [← Finset.mul_sum, hsum', mul_one]
    rw [hL, hR] at hj
    have hrhs : Real.negMulLog (1/(n:ℝ)) = (1/(n:ℝ)) * Real.log (n:ℝ) := by
      unfold Real.negMulLog
      rw [one_div, Real.log_inv]
      ring
    rw [hrhs] at hj
    have hc : 0 < (1:ℝ)/n := by positivity
    exact le_of_mul_le_mul_left hj hc
  exact (mutualInfo_le_entropy hP).trans hbound

/-- For `N ≥ 1`, the uniform distribution on `N + 1` outcomes has entropy `Real.log ((N : ℝ) +
1)`, and every nonnegative probability distribution on those outcomes has entropy at most
that value. This records the finite entropy bounds associated with [BuzekDerkaMassar1999]. -/
theorem informationContent (N : ℕ) (hN : 1 ≤ N) :
    shannonEntropy (uniformDist (N+1)) = Real.log ((N:ℝ)+1) ∧
    (∀ (p : Fin (N+1) → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
      shannonEntropy p ≤ Real.log ((N:ℝ)+1)) :=
  ⟨by simpa using uniformEntropy (n := N+1) (by omega),
   fun p a b => holevoBound N hN a b⟩

/-- For `N ≥ 1`, the sine family's normalized square-root cost is at most `Real.pi / (N + 1)`,
and the uniform distribution on `N + 1` outcomes has entropy `Real.log ((N : ℝ) + 1)`. -/
theorem sineResolution_entropy (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (costForm N (sineAmplitude N) / normSq N (sineAmplitude N))
        ≤ Real.pi / (N+1)
    ∧ shannonEntropy (uniformDist (N+1)) = Real.log ((N:ℝ)+1) := by
  refine ⟨?_, ?_⟩
  · exact optimalTimeResolution N hN
  · simpa using uniformEntropy (n := N+1) (by omega)

/-- For `N ≥ 1`, the sine family's normalized square-root cost is at most `Real.pi / (N : ℝ)`,
while entropy on `N + 1` outcomes is bounded by and attains `Real.log ((N : ℝ) + 1)`. These
combine the scalar resolution and entropy estimates associated with [BuzekDerkaMassar1999]. -/
theorem clockConstraintBounds (N : ℕ) (hN : 1 ≤ N) :
    Real.sqrt (costForm N (sineAmplitude N) / normSq N (sineAmplitude N))
        ≤ Real.pi / (N:ℝ)
    ∧ (∀ (p : Fin (N+1) → ℝ), (∀ i, 0 ≤ p i) → (∑ i, p i = 1) →
        shannonEntropy p ≤ Real.log ((N:ℝ)+1))
    ∧ shannonEntropy (uniformDist (N+1)) = Real.log ((N:ℝ)+1) :=
  ⟨optimalTimeResolution_le_pi_div_N N hN,
   fun p a b => holevoBound N hN a b,
   by simpa using uniformEntropy (n := N+1) (by omega)⟩

end Qatlib.Papers.QClockBuzek98.MainResults
