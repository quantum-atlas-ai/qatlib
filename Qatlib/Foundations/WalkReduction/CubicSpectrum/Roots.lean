/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Hom.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.FunLike.Basic
import Mathlib.Basic.FunLike.Equiv
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Real.Star
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Data.ZMod.Defs
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Logic.Equiv.Defs
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Constructions.SumProd
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Foundations.WalkReduction.CubicSpectrum

def gammaC (n : ℝ) : ℝ := 1 / (3 * n) + 7 / (6 * n ^ 2)

def Er (γ n : ℝ) : ℝ := -γ * (3 * n - 9)

theorem Er_at_critical {n : ℝ} (hn : n ≠ 0) :
    Er (gammaC n) n = -1 - 1 / (2 * n) + 21 / (2 * n ^ 2) := by
  unfold Er gammaC
  field_simp [hn]
  ring

theorem gammaC_100 : gammaC 100 = 69 / 20000 := by
  unfold gammaC
  norm_num

def Hred0 (γ n : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![ -1, 0, -(γ * Real.sqrt (3 * n));
      0, -(γ * (2 * n - 17)), -(γ * (-2 * Real.sqrt (2 * n)));
      -(γ * Real.sqrt (3 * n)), -(γ * (-2 * Real.sqrt (2 * n))), -(γ * (n - 2)) ]

def charPoly (γ lam n : ℝ) : ℝ :=
  -lam ^ 3 - (3 * γ * n - 19 * γ + 1) * lam ^ 2
    + γ * (19 - 34 * γ - 2 * γ * n ^ 2 + n * (32 * γ - 3)) * lam
    + γ ^ 2 * (-34 + n * (29 - 51 * γ) + n ^ 2 * (-2 + 6 * γ))

theorem charPoly_eq_det {γ lam n : ℝ} (hn : 0 ≤ n) :
    (Matrix.scalar (Fin 3) lam - Hred0 γ n).det = -charPoly γ lam n := by
  rw [Matrix.det_fin_three]
  simp [Matrix.scalar_apply, Hred0]
  unfold charPoly
  ring_nf
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hn]
  ring

theorem charPoly_at_critical_closed {n : ℝ} (hn : 0 < n) :
    charPoly (gammaC n) (-1 - 1 / (2 * n)) n =
      -(4729798656 * n ^ 3 + 50415353856 * n ^ 2 + 243423387648 * n + 223859220480)
        / (3869835264 * n ^ 5) := by
  unfold charPoly gammaC
  field_simp [hn.ne']
  ring

theorem residual_bound {n : ℝ} (hn : 6 ≤ n) :
    |charPoly (gammaC n) (-1 - 1 / (2 * n)) n| ≤ 135 / n ^ 2 := by
  have hn0 : 0 < n := by linarith
  have hnp : (0 : ℝ) < n ^ 2 := by positivity
  rw [charPoly_at_critical_closed hn0]
  have hQ : 0 < 4729798656 * n ^ 3 + 50415353856 * n ^ 2 + 243423387648 * n + 223859220480 := by
    positivity
  have hden : 0 < 3869835264 * n ^ 5 := by positivity
  rw [show -(4729798656 * n ^ 3 + 50415353856 * n ^ 2 + 243423387648 * n + 223859220480) /
         (3869835264 * n ^ 5) =
       -((4729798656 * n ^ 3 + 50415353856 * n ^ 2 + 243423387648 * n + 223859220480) /
         (3869835264 * n ^ 5)) by ring,
    abs_neg, abs_of_pos (div_pos hQ hden), div_le_div_iff₀ hden hnp]
  have hmain : 4729798656 * n ^ 3 + 50415353856 * n ^ 2 + 243423387648 * n + 223859220480
      ≤ 522427760640 * n ^ 3 := by
    nlinarith [hn, sq_nonneg n, sq_nonneg (n - 6),
      mul_nonneg (sq_nonneg (n - 6)) (by linarith : (0 : ℝ) ≤ n - 6)]
  have hstep : (4729798656 * n ^ 3 + 50415353856 * n ^ 2 + 243423387648 * n + 223859220480)
        * n ^ 2 ≤ 522427760640 * n ^ 5 := by
    have := mul_le_mul_of_nonneg_right hmain (le_of_lt hnp)
    nlinarith [this]
  nlinarith [hstep]

lemma charPoly_at_minus_ten_closed {n : ℝ} (hn : 0 < n) :
    charPoly (gammaC n) (-1 - 1 / (2 * n) - 10 / n ^ 2) n =
      (72 * n ^ 4 + 382 * n ^ 3 + 7971 * n ^ 2 + 30675 * n + 264920) / (72 * n ^ 6) := by
  unfold charPoly gammaC
  field_simp [hn.ne']
  ring

lemma charPoly_at_plus_ten_closed {n : ℝ} (hn : 0 < n) :
    charPoly (gammaC n) (-1 - 1 / (2 * n) + 10 / n ^ 2) n =
      -(248 * n ^ 4 + 2258 * n ^ 3 + 2629 * n ^ 2 - 23395 * n - 54280) / (72 * n ^ 6) := by
  unfold charPoly gammaC
  field_simp [hn.ne']
  ring

lemma quartic_ten_pos {n : ℝ} (hn : 6 ≤ n) :
    0 < 248 * n ^ 4 + 2258 * n ^ 3 + 2629 * n ^ 2 - 23395 * n - 54280 := by
  nlinarith [hn, sq_nonneg (n - 6),
    mul_nonneg (sq_nonneg (n - 6)) (by linarith : (0 : ℝ) ≤ n - 6),
    mul_nonneg (mul_nonneg (sq_nonneg (n - 6)) (by linarith : (0 : ℝ) ≤ n - 6))
      (by linarith : (0 : ℝ) ≤ n - 6)]

theorem lambda_u_exists {n : ℝ} (hn : 6 ≤ n) :
    ∃ lam : ℝ, charPoly (gammaC n) lam n = 0 ∧ |lam - (-1 - 1 / (2 * n))| ≤ 54 / n ^ 2 := by
  have hn0 : 0 < n := by linarith
  set x0 : ℝ := -1 - 1 / (2 * n) with hx0
  have hden : 0 < 72 * n ^ 6 := by positivity
  have hleft_pos : 0 < charPoly (gammaC n) (x0 - 10 / n ^ 2) n := by
    rw [show x0 - 10 / n ^ 2 = -1 - 1 / (2 * n) - 10 / n ^ 2 by rw [hx0]]
    rw [charPoly_at_minus_ten_closed hn0]
    apply div_pos _ hden
    positivity
  have hright_neg : charPoly (gammaC n) (x0 + 10 / n ^ 2) n < 0 := by
    rw [show x0 + 10 / n ^ 2 = -1 - 1 / (2 * n) + 10 / n ^ 2 by rw [hx0]]
    rw [charPoly_at_plus_ten_closed hn0]
    have hq : 0 < 248 * n ^ 4 + 2258 * n ^ 3 + 2629 * n ^ 2 - 23395 * n - 54280 :=
      quartic_ten_pos hn
    have : -(248 * n ^ 4 + 2258 * n ^ 3 + 2629 * n ^ 2 - 23395 * n - 54280) / (72 * n ^ 6) < 0 :=
      div_neg_of_neg_of_pos (neg_neg_of_pos hq) hden
    exact this
  have hcont : ContinuousOn (fun lam => charPoly (gammaC n) lam n)
      (Set.Icc (x0 - 10 / n ^ 2) (x0 + 10 / n ^ 2)) := by
    apply Continuous.continuousOn
    unfold charPoly
    fun_prop
  have hle : x0 - 10 / n ^ 2 ≤ x0 + 10 / n ^ 2 := by
    have hpos : 0 < 10 / n ^ 2 := by positivity
    linarith
  have hzero_mem : (0 : ℝ) ∈ Set.Icc (charPoly (gammaC n) (x0 + 10 / n ^ 2) n)
      (charPoly (gammaC n) (x0 - 10 / n ^ 2) n) :=
    ⟨le_of_lt hright_neg, le_of_lt hleft_pos⟩
  obtain ⟨lam, hlam_mem, hlam_zero⟩ :=
    intermediate_value_Icc' hle hcont hzero_mem
  refine ⟨lam, hlam_zero, ?_⟩
  have hdist : |lam - x0| ≤ 10 / n ^ 2 := by
    rw [abs_le]
    constructor <;> linarith [hlam_mem.1, hlam_mem.2]
  have hten : 10 / n ^ 2 ≤ 54 / n ^ 2 := by
    apply div_le_div_of_nonneg_right (by norm_num : (10 : ℝ) ≤ 54) (by positivity)
  exact le_trans hdist hten

theorem critical_degeneracy {n : ℝ} (hn : 6 ≤ n) :
    Er (gammaC n) n = -1 - 1 / (2 * n) + 21 / (2 * n ^ 2) ∧
      ∃ lam : ℝ, charPoly (gammaC n) lam n = 0 ∧ |lam - (-1 - 1 / (2 * n))| ≤ 54 / n ^ 2 :=
  ⟨Er_at_critical (by linarith), lambda_u_exists hn⟩

end Qatlib.Foundations.WalkReduction.CubicSpectrum
