/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Data.Real.StarOrdered
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMomentStat
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductCoeffClosedFormStat
import Qatlib.Papers.HamLCUSim12.Multiproduct.MultiproductMassStructureStat
set_option warningAsError false

set_option autoImplicit false

open scoped BigOperators Classical

namespace Qatlib.Papers.HamLCUSim12.Multiproduct

def MultiproductMomentLegacy : Prop :=
  ∀ k : ℕ, ∀ N : ℝ, NodesDistinct k N →
    (∑ q : Fin (k+1), mCoeff k N q = 1) ∧
    (∀ m : ℕ, 1 ≤ m → m ≤ k →
      (∑ q : Fin (k+1), mCoeff k N q / mNode k N q ^ (2 * m)) = 0)

def MultiproductCoeffClosedFormLegacy : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ N : ℝ, NodesDistinct k N →
    ∀ q : Fin (k+1), (q : ℕ) < k →
      mCoeff k N q * (((q : ℕ) + 1 : ℝ) ^ 2 - N ^ 2)
        * (((k + (q : ℕ) + 1).factorial : ℝ) * (((k : ℕ) - (q : ℕ) - 1).factorial : ℝ))
        = (-(1 : ℝ)) ^ ((k - (q : ℕ) - 1 : ℕ)) * 2 * (((q : ℕ) + 1 : ℝ) ^ (2 * (k + 1)))

theorem multiproduct_squared_collision_distinct : NodesDistinct 1 (-1) := by
  intro j hj
  have hv : j.val=0 := by omega
  norm_num [hv]

theorem multiproductMoment_obstruction : ¬MultiproductMomentLegacy := by
  intro h
  have hs := (h 1 (-1) multiproduct_squared_collision_distinct).1
  norm_num [mCoeff, mNode, Fin.sum_univ_succ, Fin.prod_univ_succ] at hs

theorem multiproductMoment_zero_obstruction : ¬MultiproductMomentLegacy := by
  intro h
  have hd : NodesDistinct 1 0 := by
    intro j hj
    have hv : j.val=0 := by omega
    norm_num [hv]
  have hs := (h 1 0 hd).2 1 (by omega) (by omega)
  norm_num [mCoeff, mNode, Fin.sum_univ_succ, Fin.prod_univ_succ] at hs

theorem multiproductCoeffClosedForm_obstruction : ¬MultiproductCoeffClosedFormLegacy := by
  intro h
  have hs := h 1 (by omega) (-1) multiproduct_squared_collision_distinct
    (0 : Fin 2) (by decide)
  norm_num [mCoeff, mNode, Fin.prod_univ_succ] at hs
end Qatlib.Papers.HamLCUSim12.Multiproduct
