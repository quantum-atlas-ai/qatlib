/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.Star.Int
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Int.Order.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Lattice
import Mathlib.Order.Max
import Mathlib.Order.Nat
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Tactic.Zify
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Basic
import Mathlib.Topology.Continuous
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.UniformSpace.Defs
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace Qatlib.Papers.HamOracle06.MainResults

theorem queryTime_lowerBound_power (j : ℕ) (hj : 1 ≤ j) (T a : ℝ) (hT : 0 ≤ T)
    (ha0 : 0 ≤ a)
    (h : a ≤ (1 / (Nat.factorial j : ℝ)) * (Real.pi * T / 2) ^ j) :
    (2 / Real.pi) * (Nat.factorial j : ℝ) ^ (1 / (j : ℝ)) * a ^ (1 / (j : ℝ)) ≤ T := by
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj
  have hfact_pos : 0 < (Nat.factorial j : ℝ) := by exact_mod_cast Nat.factorial_pos j
  have hpiT : 0 ≤ Real.pi * T / 2 := by positivity
  have h1 : a * (Nat.factorial j : ℝ) ≤ (Real.pi * T / 2) ^ j := by
    have hmul := mul_le_mul_of_nonneg_right h hfact_pos.le
    have heq :
        (1 / (Nat.factorial j : ℝ)) * (Real.pi * T / 2) ^ j * (Nat.factorial j : ℝ)
          = (Real.pi * T / 2) ^ j := by
      have hc : (Nat.factorial j : ℝ)⁻¹ * (Nat.factorial j : ℝ) = 1 :=
        inv_mul_cancel₀ hfact_pos.ne'
      calc
        (1 / (Nat.factorial j : ℝ)) * (Real.pi * T / 2) ^ j * (Nat.factorial j : ℝ)
            = (Real.pi * T / 2) ^ j *
                ((Nat.factorial j : ℝ)⁻¹ * (Nat.factorial j : ℝ)) := by
              rw [one_div]; ring
        _ = (Real.pi * T / 2) ^ j := by rw [hc, mul_one]
    rwa [heq] at hmul
  have h2 : (a * (Nat.factorial j : ℝ)) ^ (1 / (j : ℝ))
      ≤ ((Real.pi * T / 2) ^ j) ^ (1 / (j : ℝ)) :=
    Real.rpow_le_rpow (mul_nonneg ha0 hfact_pos.le) h1 (by positivity)
  have h3 : (a * (Nat.factorial j : ℝ)) ^ (1 / (j : ℝ))
      = a ^ (1 / (j : ℝ)) * (Nat.factorial j : ℝ) ^ (1 / (j : ℝ)) :=
    Real.mul_rpow ha0 hfact_pos.le
  have h4 : ((Real.pi * T / 2) ^ j) ^ (1 / (j : ℝ)) = Real.pi * T / 2 := by
    rw [← Real.rpow_natCast (Real.pi * T / 2) j, ← Real.rpow_mul hpiT]
    have hjj : (j : ℝ) * (1 / (j : ℝ)) = 1 := by field_simp
    rw [hjj, Real.rpow_one]
  rw [h3, h4] at h2
  have h5 : a ^ (1 / (j : ℝ)) * (Nat.factorial j : ℝ) ^ (1 / (j : ℝ))
      ≤ Real.pi * T / 2 := h2
  have hfin : (2 / Real.pi) *
      (a ^ (1 / (j : ℝ)) * (Nat.factorial j : ℝ) ^ (1 / (j : ℝ)))
      ≤ (2 / Real.pi) * (Real.pi * T / 2) :=
    mul_le_mul_of_nonneg_left h5 (by positivity)
  have hsimp : (2 / Real.pi) * (Real.pi * T / 2) = T := by
    field_simp
  rw [hsimp] at hfin
  calc
    (2 / Real.pi) * (Nat.factorial j : ℝ) ^ (1 / (j : ℝ)) * a ^ (1 / (j : ℝ))
        = (2 / Real.pi) *
            (a ^ (1 / (j : ℝ)) * (Nat.factorial j : ℝ) ^ (1 / (j : ℝ))) := by ring
    _ ≤ T := hfin

theorem factorial_rpow_ge (j : ℕ) (hj : 1 ≤ j) :
    (j : ℝ) / Real.exp 1 ≤ (Nat.factorial j : ℝ) ^ (1 / (j : ℝ)) := by
  have hj0 : 0 < (j : ℝ) := by exact_mod_cast hj
  have hje0 : 0 ≤ (j : ℝ) / Real.exp 1 := by positivity
  have hst := Stirling.le_factorial_stirling j
  have hsq : 1 ≤ Real.sqrt (2 * Real.pi * (j : ℝ)) := by
    rw [Real.one_le_sqrt]
    have hpi1 : (1 : ℝ) ≤ Real.pi := by linarith [Real.pi_gt_three]
    have hj1 : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    have hprod : (1 : ℝ) * 1 ≤ Real.pi * (j : ℝ) :=
      mul_le_mul hpi1 hj1 zero_le_one (by linarith)
    nlinarith [hprod]
  have hpow : ((j : ℝ) / Real.exp 1) ^ j ≤ (Nat.factorial j : ℝ) := by
    have h1 : ((j : ℝ) / Real.exp 1) ^ j
        ≤ Real.sqrt (2 * Real.pi * (j : ℝ)) * ((j : ℝ) / Real.exp 1) ^ j :=
      le_mul_of_one_le_left (pow_nonneg hje0 j) hsq
    exact h1.trans hst
  have h2 : (((j : ℝ) / Real.exp 1) ^ j) ^ (1 / (j : ℝ))
      ≤ (Nat.factorial j : ℝ) ^ (1 / (j : ℝ)) :=
    Real.rpow_le_rpow (pow_nonneg hje0 j) hpow (by positivity)
  have h3 : (((j : ℝ) / Real.exp 1) ^ j) ^ (1 / (j : ℝ)) = (j : ℝ) / Real.exp 1 := by
    rw [← Real.rpow_natCast ((j : ℝ) / Real.exp 1) j, ← Real.rpow_mul hje0]
    have hjj : (j : ℝ) * (1 / (j : ℝ)) = 1 := by field_simp
    rw [hjj, Real.rpow_one]
  rwa [h3] at h2

theorem queryTime_lowerBound_combined (j : ℕ) (hj : 1 ≤ j) (T δ : ℝ) (hT : 0 ≤ T)
    (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1)
    (h : δ ≤ (1 / (Nat.factorial j : ℝ)) * (Real.pi * T / 2) ^ j) :
    (2 / Real.pi) * ((j : ℝ) / Real.exp 1) * δ ^ (1 / (j : ℝ)) ≤ T := by
  have hpow := queryTime_lowerBound_power j hj T δ hT hδ0.le h
  have hfac := factorial_rpow_ge j hj
  have hδp : 0 ≤ δ ^ (1 / (j : ℝ)) := Real.rpow_nonneg hδ0.le _
  have hcoef : 0 ≤ 2 / Real.pi := by positivity
  have hm : (2 / Real.pi) * ((j : ℝ) / Real.exp 1) * δ ^ (1 / (j : ℝ))
      ≤ (2 / Real.pi) * (Nat.factorial j : ℝ) ^ (1 / (j : ℝ)) * δ ^ (1 / (j : ℝ)) := by
    apply mul_le_mul_of_nonneg_right _ hδp
    exact mul_le_mul_of_nonneg_left hfac hcoef
  exact hm.trans hpow

theorem queryTime_asymptotic_linear (δ : ℝ) (hδ0 : 0 < δ) (_hδ1 : δ ≤ 1) (c : ℝ)
    (hc : c < 1 / (Real.pi * Real.exp 1)) :
    ∀ᶠ n : ℕ in atTop,
      c * (n : ℝ) ≤
        (2 / Real.pi) * (((n / 2 : ℕ) : ℝ) / Real.exp 1) *
          δ ^ (1 / ((n / 2 : ℕ) : ℝ)) := by

  have hjn : Tendsto (fun n : ℕ => ((n / 2 : ℕ) : ℝ) / (n : ℝ)) atTop (𝓝 (1 / 2)) := by
    have hfloor :=
      (tendsto_nat_floor_mul_div_atTop (R := ℝ) (a := (1 / 2 : ℝ))
        (by norm_num)).comp tendsto_natCast_atTop_atTop
    refine hfloor.congr' ?_
    filter_upwards with n
    simp only [Function.comp_apply]
    have harg : (1 / 2 : ℝ) * (n : ℝ) = (n : ℝ) / 2 := by ring
    rw [harg]
    have hfl : ⌊(n : ℝ) / 2⌋₊ = n / 2 := by
      have hcast : ((2 : ℕ) : ℝ) = 2 := by norm_num
      rw [← hcast, Nat.floor_div_natCast, Nat.floor_natCast]
    rw [hfl]

  have hJtop : Tendsto (fun n : ℕ => (n / 2 : ℕ)) atTop atTop := by
    rw [Filter.tendsto_atTop_atTop]
    intro b
    refine ⟨2 * b, fun a ha => ?_⟩
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
    linarith
  have hJtopR : Tendsto (fun n : ℕ => ((n / 2 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hJtop

  have hinv : Tendsto (fun n : ℕ => 1 / ((n / 2 : ℕ) : ℝ)) atTop (𝓝 0) :=
    hJtopR.const_div_atTop 1
  have hrpow : Tendsto (fun n : ℕ => δ ^ (1 / ((n / 2 : ℕ) : ℝ))) atTop (𝓝 1) := by
    have hcont := (Real.continuous_const_rpow (ne_of_gt hδ0)).tendsto (0 : ℝ)
    simpa [Real.rpow_zero] using! hcont.comp hinv

  have hratio : Tendsto (fun n : ℕ =>
      (2 / Real.pi) * (1 / Real.exp 1) * (((n / 2 : ℕ) : ℝ) / (n : ℝ)) *
        δ ^ (1 / ((n / 2 : ℕ) : ℝ))) atTop (𝓝 (1 / (Real.pi * Real.exp 1))) := by
    have hconst : Tendsto (fun n : ℕ => (2 / Real.pi) * (1 / Real.exp 1) *
        (((n / 2 : ℕ) : ℝ) / (n : ℝ))) atTop
        (𝓝 ((2 / Real.pi) * (1 / Real.exp 1) * (1 / 2))) :=
      (tendsto_const_nhds (x := (2 / Real.pi) * (1 / Real.exp 1))).mul hjn
    have h := hconst.mul hrpow
    have hval : (2 / Real.pi) * (1 / Real.exp 1) * (1 / 2) * 1
        = 1 / (Real.pi * Real.exp 1) := by
      field_simp
    rw [← hval]
    simpa only [mul_assoc] using h
  have hcf : ∀ᶠ n : ℕ in atTop,
      c < (2 / Real.pi) * (1 / Real.exp 1) * (((n / 2 : ℕ) : ℝ) / (n : ℝ)) *
        δ ^ (1 / ((n / 2 : ℕ) : ℝ)) :=
    (tendsto_order.1 hratio).1 c hc
  filter_upwards [hcf, Filter.eventually_gt_atTop (0 : ℕ)] with n hlt hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hEq : (2 / Real.pi) * (1 / Real.exp 1) * (((n / 2 : ℕ) : ℝ) / (n : ℝ)) *
        δ ^ (1 / ((n / 2 : ℕ) : ℝ))
      = ((2 / Real.pi) * (((n / 2 : ℕ) : ℝ) / Real.exp 1) *
          δ ^ (1 / ((n / 2 : ℕ) : ℝ))) / (n : ℝ) := by
    field_simp
  rw [hEq] at hlt
  have hgoal : c * (n : ℝ) <
      (2 / Real.pi) * (((n / 2 : ℕ) : ℝ) / Real.exp 1) *
        δ ^ (1 / ((n / 2 : ℕ) : ℝ)) := by
    have hmul := mul_lt_mul_of_pos_right hlt hnR
    rwa [div_mul_cancel₀ _ hnR.ne'] at hmul
  exact hgoal.le

end Qatlib.Papers.HamOracle06.MainResults
