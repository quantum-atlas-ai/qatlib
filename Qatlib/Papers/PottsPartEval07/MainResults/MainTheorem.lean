/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Function.Defs
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Numerical parameters for exact Potts evaluation

The module defines Boltzmann weights and the finite Potts partition sum with edge-dependent real
couplings, and proves their positivity. It also records the numerical predicate `IsIccc`, the
precision parameter `delta`, and the output specification `PottsScheme`, together with a bound
on the parameter counting weight classes [GeraciLidar2008].

## Main statements

* `pottsPartition_pos`: A positive number of spin values gives a positive partition sum.
* `weight_count_bound`: The assumed length formula bounds the quotient parameter N.

## References

* [Geraci and Lidar, 2008][GeraciLidar2008]
-/

set_option autoImplicit false

namespace Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem

open scoped BigOperators

/-- The product of `exp (J e)` over monochromatic edges, with factor one on every other edge. -/
noncomputable def pottsBoltzmann {V E : Type*} [Fintype E]
    (q : ℕ) (ends : E → V × V) (J : E → ℝ) (σ : V → Fin q) : ℝ :=
  ∏ e : E, if σ (ends e).1 = σ (ends e).2 then Real.exp (J e) else 1

/-- The Potts partition sum over all assignments of `q` spin values to vertices. -/
noncomputable def pottsPartition {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (q : ℕ) (ends : E → V × V) (J : E → ℝ) : ℝ :=
  ∑ σ : V → Fin q, pottsBoltzmann q ends J σ

/-- Every Potts Boltzmann weight is strictly positive. -/
theorem pottsBoltzmann_pos {V E : Type*} [Fintype E]
    (q : ℕ) (ends : E → V × V) (J : E → ℝ) (σ : V → Fin q) :
    0 < pottsBoltzmann q ends J σ := by
  unfold pottsBoltzmann
  apply Finset.prod_pos
  intro e _
  split_ifs
  · exact Real.exp_pos _
  · exact one_pos

/-- The Potts partition sum is strictly positive when there is at least one spin value
[GeraciLidar2008]. -/
theorem pottsPartition_pos {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (q : ℕ) (hq : 0 < q) (ends : E → V × V) (J : E → ℝ) :
    0 < pottsPartition q ends J := by
  classical
  haveI : Nonempty (V → Fin q) := ⟨fun (_ : V) => (⟨0, hq⟩ : Fin q)⟩
  unfold pottsPartition
  apply Finset.sum_pos
  · intro σ _; exact pottsBoltzmann_pos q ends J σ
  · exact Finset.univ_nonempty

/-- The precision parameter `ε ^ 2 / (2 * (q ^ k - 1) ^ 2)`. -/
noncomputable def delta (q k : ℕ) (ε : ℝ) : ℝ :=
  ε ^ 2 / (2 * ((q : ℝ) ^ k - 1) ^ 2)

/-- For `q ≥ 2` and `k ≥ 1`, the real number `q ^ k` is strictly greater than one. -/
private lemma one_lt_q_pow {q k : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k) : (1 : ℝ) < (q : ℝ) ^ k := by
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by linarith
  calc (1 : ℝ) < (q : ℝ) := by linarith
    _ = (q : ℝ) ^ 1 := (pow_one _).symm
    _ ≤ (q : ℝ) ^ k := pow_le_pow_right₀ hq1 hk

/-- The precision parameter `delta q k ε` is positive for `q ≥ 2`, `k ≥ 1`, and positive `ε`. -/
theorem delta_pos {q k : ℕ} {ε : ℝ} (hq : 2 ≤ q) (hk : 1 ≤ k) (hε : 0 < ε) :
    0 < delta q k ε := by
  unfold delta
  have h1 : (1 : ℝ) < (q : ℝ) ^ k := one_lt_q_pow hq hk
  have hx : 0 < (q : ℝ) ^ k - 1 := by linarith
  have hden : 0 < 2 * ((q : ℝ) ^ k - 1) ^ 2 := by nlinarith [sq_pos_of_pos hx]
  exact div_pos (pow_pos hε 2) hden

/-- The precision parameter is less than one half when `q ≥ 2`, `k ≥ 1`, and `0 < ε < 1`
[GeraciLidar2008]. -/
theorem delta_lt_half {q k : ℕ} {ε : ℝ} (hq : 2 ≤ q) (hk : 1 ≤ k)
    (hε0 : 0 < ε) (hε1 : ε < 1) : delta q k ε < 1 / 2 := by
  unfold delta
  have h1 : (1 : ℝ) < (q : ℝ) ^ k := one_lt_q_pow hq hk
  have hq2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by linarith
  have h2 : (2 : ℝ) ≤ (q : ℝ) ^ k := by
    calc (2 : ℝ) ≤ (q : ℝ) := hq2
      _ = (q : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (q : ℝ) ^ k := pow_le_pow_right₀ hq1 hk
  have hx : 0 < (q : ℝ) ^ k - 1 := by linarith
  have hden : 0 < 2 * ((q : ℝ) ^ k - 1) ^ 2 := by nlinarith [sq_pos_of_pos hx]
  rw [div_lt_iff₀ hden]
  have hQ : ε < (q : ℝ) ^ k - 1 := by linarith
  have hsq : ε ^ 2 < ((q : ℝ) ^ k - 1) ^ 2 := by nlinarith [hε0, hQ]
  nlinarith

/-- The numerical ICCC condition asserting a length formula with positive coefficient and the
stated precision inequality for some exponent function and real parameter `θ`. -/
def IsIccc (q n k : ℕ) (ε : ℝ) : Prop :=
  ∃ (α : ℝ) (s : ℕ → ℕ) (θ : ℝ), 0 < α ∧
    (n : ℝ) = ((q : ℝ) ^ k - 1) / (α * (k : ℝ) ^ (s k)) ∧
    ε ≤ (q : ℝ) ^ (θ - 1) / (4 * Real.sqrt ((q : ℝ) ^ k))

/-- A record of cost, success-probability value, and an output equal to the specified Potts
partition sum. -/
structure PottsScheme {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    (q : ℕ) (ends : E → V × V) (J : E → ℝ) where

  cost : ℕ

  successProb : ℝ

  output : ℝ

  exactOutput : output = pottsPartition q ends J

/-- The assumed formula for `n` and the quotient relation for `N` imply `N ≤ α * k ^ s k` over
the reals [GeraciLidar2008]. -/
theorem weight_count_bound {q k n N : ℕ} {α : ℝ} {s : ℕ → ℕ}
    (hq : 2 ≤ q) (hk : 1 ≤ k) (hα : 0 < α)
    (hn : (n : ℝ) = ((q : ℝ) ^ k - 1) / (α * (k : ℝ) ^ s k))
    (hN : (N : ℝ) = ((q : ℝ) ^ k - 1) / (n : ℝ)) :
    (N : ℝ) ≤ α * (k : ℝ) ^ s k := by
  have h1 : (1 : ℝ) < (q : ℝ) ^ k := one_lt_q_pow hq hk
  have hA : 0 < (q : ℝ) ^ k - 1 := by linarith
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hden : 0 < α * (k : ℝ) ^ s k := mul_pos hα (pow_pos hkR _)
  have hneA : ((q : ℝ) ^ k - 1) ≠ 0 := ne_of_gt hA
  have hnec : α * (k : ℝ) ^ s k ≠ 0 := ne_of_gt hden
  rw [hN, hn]
  have heq : ((q : ℝ) ^ k - 1) / (((q : ℝ) ^ k - 1) / (α * (k : ℝ) ^ s k))
      = α * (k : ℝ) ^ s k := by
    rw [div_eq_iff (div_ne_zero hneA hnec)]
    exact (mul_div_cancel₀ ((q : ℝ) ^ k - 1) hnec).symm
  rw [heq]

end Qatlib.Papers.PottsPartEval07.MainResults.MainTheorem
