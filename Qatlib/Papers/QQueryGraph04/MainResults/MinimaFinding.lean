/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.GeomSum
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Nat.Defs
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Qatlib.Papers.QQueryGraph04.MainResults.Model.Basic
public import Qatlib.Papers.QQueryGraph04.MainResults.Model.SupportBounds
public import Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs

@[expose] public section

/-!
# Cost bounds for greedy minima finding

This module proves the numerical contraction and phase-sum estimates used in greedy selection of
minima of different types. The expressions `phaseGeomSum` and `greedyPhaseCost` yield explicit
√(dN) cost bounds, while `theorem6_solution` extracts the cardinality and replacement property
of a supplied solution.

The source paper is [DurrEtAl2006].

## Main statements

* `lemma4`: For positive d, the contraction factor after 32d steps is at most 3/4 and the
  corresponding iteration expression equals 1024d.
* `corollary5_cost`: For positive d, the total greedy phase cost is at most 128√(dN).
* `theorem6_query_cost`: For positive d, three times the greedy phase cost is at most 384√(dN).

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.MinimaFinding

open Finset
open Qatlib.Papers.QQueryGraph04.MainResults.Model

/-- For positive d, 32d repetitions of the factor 1 − 1/(32d) give a value at most 3/4
[DurrEtAl2006]. -/
theorem lemma4_decay (d : ℕ) (hd : 0 < d) :
    (1 - 1 / (32 * (d : ℝ))) ^ (32 * d) ≤ 3 / 4 := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hn : (1 : ℝ) ≤ 32 * (d : ℝ) := by nlinarith
  have hcast : (1 : ℝ) ≤ ((32 * d : ℕ) : ℝ) := by push_cast; linarith
  have hexp := Real.one_sub_div_pow_le_exp_neg (n := 32 * d) (t := 1) hcast
  push_cast at hexp
  have hquarter : Real.exp (-1) ≤ 3 / 4 := by
    rw [Real.exp_neg]
    rw [inv_le_iff_one_le_mul₀ (Real.exp_pos 1)]
    nlinarith [Real.exp_one_gt_two]
  exact hexp.trans hquarter

/-- For positive d, the iteration expression (1/(1/32))·32d equals 1024d, which is positive
[DurrEtAl2006]. -/
theorem lemma4_expected_iterations (d : ℕ) (hd : 0 < d) :
    (1 / (1 / 32 : ℝ)) * (32 * (d : ℝ)) = 1024 * (d : ℝ) ∧
      0 < (1024 : ℝ) * (d : ℝ) := by
  constructor
  · ring
  · have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
    positivity

/-- For positive d, the contraction factor after 32d steps is at most 3/4 and the corresponding
iteration expression equals 1024d [DurrEtAl2006]. -/
theorem lemma4 (d : ℕ) (hd : 0 < d) :
    (1 - 1 / (32 * (d : ℝ))) ^ (32 * d) ≤ 3 / 4 ∧
      (1 / (1 / 32 : ℝ)) * (32 * (d : ℝ)) = 1024 * (d : ℝ) :=
  ⟨lemma4_decay d hd, (lemma4_expected_iterations d hd).1⟩

/-- The finite geometric sum of powers of 1/√2 over the first K phases. -/
noncomputable def phaseGeomSum (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, (1 / Real.sqrt 2 : ℝ) ^ k

/-- The finite phase geometric sum is at most 4 [DurrEtAl2006]. -/
theorem phaseGeomSum_le (K : ℕ) : phaseGeomSum K ≤ 4 := by
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hlt : (1 / Real.sqrt 2 : ℝ) < 1 := by
    rw [div_lt_one h2]
    exact Real.one_lt_sqrt_two
  have hr0 : (0 : ℝ) ≤ 1 / Real.sqrt 2 := by positivity
  have hden : (0 : ℝ) < 1 - 1 / Real.sqrt 2 := by linarith
  have hgeom : phaseGeomSum K = ((1 / Real.sqrt 2 : ℝ) ^ K - 1) /
      (1 / Real.sqrt 2 - 1) := by
    rw [phaseGeomSum, geom_sum_eq (ne_of_lt hlt)]
  have hquot : ((1 / Real.sqrt 2 : ℝ) ^ K - 1) / (1 / Real.sqrt 2 - 1) =
      (1 - (1 / Real.sqrt 2 : ℝ) ^ K) / (1 - 1 / Real.sqrt 2) := by
    rw [div_eq_div_iff (by linarith) (by linarith)]
    ring
  rw [hgeom, hquot]
  have hle1 : (1 - (1 / Real.sqrt 2 : ℝ) ^ K) / (1 - 1 / Real.sqrt 2) ≤
      1 / (1 - 1 / Real.sqrt 2) := by
    rw [div_le_div_iff_of_pos_right hden]
    nlinarith [pow_nonneg hr0 K]
  have hle4 : 1 / (1 - 1 / Real.sqrt 2) ≤ (4 : ℝ) := by
    rw [div_le_iff₀ hden]
    have hr : (1 / Real.sqrt 2 : ℝ) ≤ 3 / 4 := by
      rw [div_le_iff₀ h2]
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    linarith
  exact hle1.trans hle4

/-- The sum of the phase costs 32d√(N/(d·2ᵏ)) over k < K. -/
noncomputable def greedyPhaseCost (d N K : ℕ) : ℝ :=
  ∑ k ∈ Finset.range K, 32 * (d : ℝ) * Real.sqrt ((N : ℝ) / ((d : ℝ) * 2 ^ k))

/-- For positive d, each greedy phase cost factors as 32d√(N/d) times (1/√2)ᵏ [DurrEtAl2006]. -/
theorem greedyPhaseCost_term (d N : ℕ) (hd : 0 < d) (k : ℕ) :
    32 * (d : ℝ) * Real.sqrt ((N : ℝ) / ((d : ℝ) * 2 ^ k)) =
      32 * (d : ℝ) * Real.sqrt ((N : ℝ) / (d : ℝ)) * (1 / Real.sqrt 2 : ℝ) ^ k := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hsplit : (N : ℝ) / ((d : ℝ) * 2 ^ k) = ((N : ℝ) / (d : ℝ)) * (1 / 2) ^ k := by
    rw [div_mul_eq_div_div, one_div_pow]
    field_simp
  rw [hsplit, Real.sqrt_mul (by positivity)]
  have hroot : ∀ k : ℕ, Real.sqrt ((1 / 2 : ℝ) ^ k) = (1 / Real.sqrt 2 : ℝ) ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]
      congr 1
      rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1), Real.sqrt_one, one_div]
  rw [hroot k]
  ring

/-- For positive d, the total greedy phase cost is at most 128√(dN) [DurrEtAl2006]. -/
theorem corollary5_cost (d N K : ℕ) (hd : 0 < d) :
    greedyPhaseCost d N K ≤ 128 * Real.sqrt ((d : ℝ) * (N : ℝ)) := by
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hsum : greedyPhaseCost d N K =
      ∑ k ∈ Finset.range K, 32 * (d : ℝ) * Real.sqrt ((N : ℝ) / (d : ℝ)) *
        (1 / Real.sqrt 2 : ℝ) ^ k := by
    unfold greedyPhaseCost
    exact Finset.sum_congr rfl fun k _ => greedyPhaseCost_term d N hd k
  rw [hsum, ← Finset.mul_sum]
  have hgeo := phaseGeomSum_le K
  unfold phaseGeomSum at hgeo
  have hfac : (0 : ℝ) ≤ 32 * (d : ℝ) * Real.sqrt ((N : ℝ) / (d : ℝ)) := by positivity
  have hstep : 32 * (d : ℝ) * Real.sqrt ((N : ℝ) / (d : ℝ)) *
      (∑ k ∈ Finset.range K, (1 / Real.sqrt 2 : ℝ) ^ k) ≤
      32 * (d : ℝ) * Real.sqrt ((N : ℝ) / (d : ℝ)) * 4 := by
    exact mul_le_mul_of_nonneg_left hgeo hfac
  have heq : 32 * (d : ℝ) * Real.sqrt ((N : ℝ) / (d : ℝ)) * 4 =
      128 * Real.sqrt ((d : ℝ) * (N : ℝ)) := by
    have hspos : (0 : ℝ) < Real.sqrt (d : ℝ) := Real.sqrt_pos.mpr hdR
    have h1 : (d : ℝ) / Real.sqrt (d : ℝ) = Real.sqrt (d : ℝ) := by
      rw [div_eq_iff hspos.ne']
      exact (Real.mul_self_sqrt hdR.le).symm
    rw [Real.sqrt_div (by positivity : (0 : ℝ) ≤ (N : ℝ))]
    rw [Real.sqrt_mul hdR.le]
    calc 32 * (d : ℝ) * (Real.sqrt (N : ℝ) / Real.sqrt (d : ℝ)) * 4
        = 128 * ((d : ℝ) / Real.sqrt (d : ℝ) * Real.sqrt (N : ℝ)) := by
          field_simp
          ring
      _ = 128 * (Real.sqrt (d : ℝ) * Real.sqrt (N : ℝ)) := by rw [h1]
  exact hstep.trans (le_of_eq heq)

/-- For positive d, three times the greedy phase cost is at most 384√(dN) [DurrEtAl2006]. -/
theorem theorem6_query_cost (d N K : ℕ) (hd : 0 < d) :
    3 * greedyPhaseCost d N K ≤ 384 * Real.sqrt ((d : ℝ) * (N : ℝ)) := by
  have h := corollary5_cost d N K hd
  linarith

/-- A supplied minimum different-type solution has cardinality d, and every smaller unselected
value is represented by a selected element of the same type with no larger value
[DurrEtAl2006]. -/
theorem theorem6_solution {N : ℕ} (f g : Fin N → ℕ) (d : ℕ) (I : Finset (Fin N))
    (h : Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs.IsMinDifferentTypeSolution
      f g d I) :
    I.card = d ∧ ∀ j ∉ I, ∀ i ∈ I, f j < f i → ∃ i' ∈ I, g i' = g j ∧ f i' ≤ f j := by
  obtain ⟨hcard, _, hgood⟩ := h
  exact ⟨hcard, hgood⟩

end Qatlib.Papers.QQueryGraph04.MainResults.MinimaFinding
