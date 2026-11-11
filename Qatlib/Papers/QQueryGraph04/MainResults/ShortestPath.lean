/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Qatlib.Papers.QQueryGraph04.MainResults.Model.Basic
import Qatlib.Papers.QQueryGraph04.MainResults.Model.SupportBounds
import Qatlib.Papers.QQueryGraph04.MainResults.ProblemDefs

/-!
# Single-source shortest-path cost estimates

This module bounds the level cost `ssspLevelCost` using aggregate cardinality and edge-count
hypotheses. It then bounds the finite sum `ssspCost` and gives an existential multiplicative
bound at the √(nm)(log n)^(3/2) scale under a level-count hypothesis.

The source paper is [DurrEtAl2006].

## Main statements

* `sssp_level_cost_le`: For positive s, at most n/s summands and total edge count at most m give
  a level cost at most √(nm).
* `theorem18_query_cost`: If n ≥ 1 and the number of levels is at most log n/log 2 + 2, there
  exists a positive constant bounding `ssspCost` by that constant times √(nm)(log n)^(3/2).

## References

* [Dürr et al., 2006][DurrEtAl2006]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.QQueryGraph04.MainResults.ShortestPath

open Finset
open Qatlib.Papers.QQueryGraph04.MainResults.Model

/-- The sum of √(s·m j) over the index type at a single shortest-path level. -/
noncomputable def ssspLevelCost {ι : Type*} [Fintype ι] (s : ℕ) (m_ : ι → ℕ) : ℝ :=
  ∑ j, Real.sqrt ((s : ℝ) * (m_ j : ℝ))

/-- For positive s, at most n/s summands and total edge count at most m give a level cost at
most √(nm) [DurrEtAl2006]. -/
theorem sssp_level_cost_le {ι : Type*} [Fintype ι] (s n m : ℕ) (m_ : ι → ℕ)
    (hs : 0 < s) (hcard : Fintype.card ι ≤ n / s) (hm : (∑ j, m_ j) ≤ m) :
    ssspLevelCost s m_ ≤ Real.sqrt ((n : ℝ) * (m : ℝ)) := by
  unfold ssspLevelCost
  have hterm : ∀ j, Real.sqrt ((s : ℝ) * (m_ j : ℝ)) =
      Real.sqrt (s : ℝ) * Real.sqrt (m_ j : ℝ) := fun j =>
    Real.sqrt_mul (Nat.cast_nonneg s) (m_ j : ℝ)
  simp only [hterm]
  have hCS := sum_sqrt_mul_le (Finset.univ : Finset ι) (fun _ => 1) m_
  have h1 : (∑ j, Real.sqrt (m_ j : ℝ)) ≤
      Real.sqrt ((Fintype.card ι : ℝ)) * Real.sqrt (∑ j, (m_ j : ℝ)) := by
    simpa using hCS
  calc (∑ j, Real.sqrt (s : ℝ) * Real.sqrt (m_ j : ℝ))
      = Real.sqrt (s : ℝ) * ∑ j, Real.sqrt (m_ j : ℝ) := by rw [Finset.mul_sum]
    _ ≤ Real.sqrt (s : ℝ) *
          (Real.sqrt ((Fintype.card ι : ℝ)) * Real.sqrt (∑ j, (m_ j : ℝ))) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = Real.sqrt ((s : ℝ) * (Fintype.card ι : ℝ)) * Real.sqrt (∑ j, (m_ j : ℝ)) := by
        rw [← mul_assoc, ← Real.sqrt_mul (Nat.cast_nonneg s)]
    _ ≤ Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) := by
        apply mul_le_mul
        · apply Real.sqrt_le_sqrt
          have hcs : Fintype.card ι * s ≤ n := (Nat.le_div_iff_mul_le hs).mp hcard
          have hcast : ((Fintype.card ι * s : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hcs
          rw [Nat.cast_mul] at hcast
          linarith
        · apply Real.sqrt_le_sqrt
          have hcast : ((∑ j, m_ j : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
          simpa using hcast
        · exact Real.sqrt_nonneg _
        · exact Real.sqrt_nonneg _
    _ = Real.sqrt ((n : ℝ) * (m : ℝ)) := by rw [Real.sqrt_mul (Nat.cast_nonneg n)]

/-- The sum of `len` identical shortest-path level budgets √(nm)√(log n). -/
noncomputable def ssspCost (n m len : ℕ) : ℝ :=
  ∑ _l ∈ Finset.range len,
    Real.sqrt ((n : ℝ) * (m : ℝ)) * Real.sqrt (Real.log (n : ℝ))

/-- The total shortest-path cost is at most `len` times √(nm)√(log n) [DurrEtAl2006]. -/
theorem ssspCost_le (n m len : ℕ) :
    ssspCost n m len ≤
      (len : ℝ) * (Real.sqrt ((n : ℝ) * (m : ℝ)) * Real.sqrt (Real.log (n : ℝ))) := by
  unfold ssspCost
  have h : (∑ _l ∈ Finset.range len,
      Real.sqrt ((n : ℝ) * (m : ℝ)) * Real.sqrt (Real.log (n : ℝ))) =
      (len : ℝ) * (Real.sqrt ((n : ℝ) * (m : ℝ)) * Real.sqrt (Real.log (n : ℝ))) := by
    simp [Finset.sum_const, nsmul_eq_mul]
  rw [h]

/-- If n ≥ 1 and the number of levels is at most log n/log 2 + 2, there exists a positive
constant bounding `ssspCost` by that constant times √(nm)(log n)^(3/2) [DurrEtAl2006]. -/
theorem theorem18_query_cost (n m len : ℕ) (hn : 1 ≤ n)
    (hlen : (len : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 2) :
    ∃ C : ℝ, 0 < C ∧ ssspCost n m len ≤
      C * Real.sqrt ((n : ℝ) * (m : ℝ)) * Real.rpow (Real.log (n : ℝ)) (3 / 2) := by
  refine ⟨8, by norm_num, ?_⟩
  have hlog2pos : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
  rcases Nat.lt_or_ge n 2 with hn1 | hn2
  · have hn1' : n = 1 := by omega
    subst hn1'
    have hzero : Real.rpow (Real.log ((1 : ℕ) : ℝ)) (3 / 2) = 0 := by
      rw [Nat.cast_one, Real.log_one, Real.rpow_eq_pow]
      exact Real.zero_rpow (by norm_num)
    simp [ssspCost]
  · have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
    have hlogmono : Real.log 2 ≤ Real.log (n : ℝ) := Real.log_le_log (by norm_num) hn2'
    have hLpos : 0 < Real.log (n : ℝ) := lt_of_lt_of_le hlog2pos hlogmono
    have hratio : 1 ≤ Real.log (n : ℝ) / Real.log 2 :=
      (one_le_div hlog2pos).mpr hlogmono
    have hlen' : (len : ℝ) ≤ 3 * Real.log (n : ℝ) / Real.log 2 := by
      have h2 : (2 : ℝ) ≤ 2 * (Real.log (n : ℝ) / Real.log 2) := by linarith
      calc (len : ℝ) ≤ Real.log (n : ℝ) / Real.log 2 + 2 := hlen
        _ ≤ Real.log (n : ℝ) / Real.log 2 + 2 * (Real.log (n : ℝ) / Real.log 2) := by
            linarith
        _ = 3 * Real.log (n : ℝ) / Real.log 2 := by ring

    have hLrpow : Real.rpow (Real.log (n : ℝ)) (3 / 2) =
        Real.log (n : ℝ) * Real.sqrt (Real.log (n : ℝ)) := by
      rw [Real.rpow_eq_pow]
      have h : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
      rw [h, Real.rpow_add hLpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
    have hconst : 3 / Real.log 2 ≤ 8 := by
      rw [div_le_iff₀ hlog2pos]
      nlinarith [Real.log_two_gt_d9]
    calc ssspCost n m len
        ≤ (len : ℝ) *
            (Real.sqrt ((n : ℝ) * (m : ℝ)) * Real.sqrt (Real.log (n : ℝ))) :=
          ssspCost_le n m len
      _ ≤ (3 * Real.log (n : ℝ) / Real.log 2) *
            (Real.sqrt ((n : ℝ) * (m : ℝ)) * Real.sqrt (Real.log (n : ℝ))) := by
          apply mul_le_mul_of_nonneg_right hlen'
          positivity
      _ = (3 / Real.log 2) * Real.sqrt ((n : ℝ) * (m : ℝ)) *
            (Real.log (n : ℝ) * Real.sqrt (Real.log (n : ℝ))) := by ring
      _ = (3 / Real.log 2) * Real.sqrt ((n : ℝ) * (m : ℝ)) *
            Real.rpow (Real.log (n : ℝ)) (3 / 2) := by rw [hLrpow]
      _ ≤ 8 * Real.sqrt ((n : ℝ) * (m : ℝ)) *
            Real.rpow (Real.log (n : ℝ)) (3 / 2) := by
          apply mul_le_mul_of_nonneg_right
          · exact mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _)
          · exact Real.rpow_nonneg hLpos.le _

end Qatlib.Papers.QQueryGraph04.MainResults.ShortestPath
