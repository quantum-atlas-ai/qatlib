/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

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
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Normed.Group.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Rat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Defs
import Mathlib.Order.ConditionallyCompletePartialOrder.Defs
import Mathlib.Order.Defs.Lattice
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Lattice
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.FieldSimp.Lemmas
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.Linarith.Preprocessing
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Eq
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Defs.Filter
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.UniformSpace.Defs

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.HamOracle06.MainResults

def hamMetricSpeed (θ θdot φdot : ℝ) : ℝ :=
  (4 / Real.pi ^ 2) * (θdot ^ 2 + Real.tan θ ^ 2 * φdot ^ 2)

theorem hamMetricSpeed_nonneg (θ θdot φdot : ℝ) : 0 ≤ hamMetricSpeed θ θdot φdot := by
  unfold hamMetricSpeed
  have hpi : 0 ≤ 4 / Real.pi ^ 2 := by positivity
  have hq : 0 ≤ θdot ^ 2 + Real.tan θ ^ 2 * φdot ^ 2 := by positivity
  exact mul_nonneg hpi hq

theorem hamMetricSpeed_control (θ wθ wφ : ℝ) (h : Real.tan θ ≠ 0) :
    hamMetricSpeed θ (Real.pi / 2 * wθ) (Real.pi / 2 * (wφ / Real.tan θ))
      = wθ ^ 2 + wφ ^ 2 := by
  unfold hamMetricSpeed
  field_simp
  ring

def apexClimbTime (θ0 : ℝ) : ℝ := Real.cos θ0

def apexTurnAngle (θ0 : ℝ) : ℝ := Real.pi / 2 * (1 - Real.sin θ0)

def twoBitExcursionTime (cθ0 cθ : ℝ) : ℝ :=
  2 * cθ0 * (1 - (1 / Real.pi) * Real.arcsin (cθ / cθ0))

def twoBitDescentTime (cθ0 cθ : ℝ) : ℝ := twoBitExcursionTime cθ0 cθ - cθ0

theorem twoBitExcursionTime_decomposition (cθ0 cθ : ℝ) :
    twoBitExcursionTime cθ0 cθ = cθ0 + twoBitDescentTime cθ0 cθ := by
  unfold twoBitDescentTime
  ring

theorem twoBitExcursionTime_eq_arccos (cθ0 cθ : ℝ) :
    twoBitExcursionTime cθ0 cθ =
      cθ0 + (2 * cθ0 / Real.pi) * Real.arccos (cθ / cθ0) := by
  set a : ℝ := Real.arccos (cθ / cθ0) with ha
  have harc : Real.arcsin (cθ / cθ0) = Real.pi / 2 - a := by
    rw [Real.arcsin_eq_pi_div_two_sub_arccos, ← ha]
  unfold twoBitExcursionTime
  rw [harc]
  field_simp
  ring

theorem apexRoundTrip_ge (θ0 : ℝ) (h0 : 0 ≤ θ0) (h : θ0 ≤ Real.pi / 4) :
    Real.sqrt 2 ≤ 2 * apexClimbTime θ0 := by
  have hpi4 : Real.pi / 4 ≤ Real.pi := by nlinarith [Real.pi_pos]
  have hcos : Real.cos (Real.pi / 4) ≤ Real.cos θ0 :=
    Real.cos_le_cos_of_nonneg_of_le_pi h0 hpi4 h
  unfold apexClimbTime
  rw [Real.cos_pi_div_four] at hcos
  nlinarith

theorem twoBitExcursionTime_strictMonoOn (cθ : ℝ) (hcθ : 0 < cθ) :
    StrictMonoOn (fun cθ0 => twoBitExcursionTime cθ0 cθ) (Set.Ici cθ) := by
  intro c1 hc1 c2 hc2 hlt
  have hc1pos : 0 < c1 := lt_of_lt_of_le hcθ hc1
  have hc2pos : 0 < c2 := lt_trans hc1pos hlt
  simp only [twoBitExcursionTime_eq_arccos]
  have hrec : 1 / c2 < 1 / c1 := one_div_lt_one_div_of_lt hc1pos hlt
  have hr1 : cθ / c2 < cθ / c1 := by
    have := mul_lt_mul_of_pos_left hrec hcθ
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have ha2 : Real.arccos (cθ / c1) < Real.arccos (cθ / c2) := by
    refine Real.arccos_lt_arccos (x := cθ / c2) (y := cθ / c1) ?_ hr1 ?_
    · have : 0 ≤ cθ / c2 := by positivity
      linarith
    · rw [div_le_one hc1pos]
      exact hc1
  have ha2pos : 0 < Real.arccos (cθ / c2) := by
    apply Real.arccos_pos.mpr
    rw [div_lt_one hc2pos]
    exact lt_of_le_of_lt hc1 hlt
  have hπc : 0 < Real.pi * (c2 - c1) := mul_pos Real.pi_pos (by linarith)
  have hterm : 0 < 2 * (c2 * Real.arccos (cθ / c2) - c1 * Real.arccos (cθ / c1)) := by
    have hpos :
        0 < (c2 - c1) * Real.arccos (cθ / c2) +
          c1 * (Real.arccos (cθ / c2) - Real.arccos (cθ / c1)) := by
      apply add_pos
      · exact mul_pos (by linarith) ha2pos
      · exact mul_pos hc1pos (by linarith)
    nlinarith [hpos]
  field_simp
  nlinarith [hπc, hterm]

theorem twoBitQueryTime_numeric :
    ∃ cθ0 : ℝ, |cθ0 - 0.7477| < 0.01 ∧
      |twoBitExcursionTime cθ0 (Real.sqrt 2 / 2) - 0.9052| < 0.001 := by

  have hcos2 : Real.cos (2 * Real.pi / 5) = (Real.sqrt 5 - 1) / 4 := by
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [show 2 * Real.pi / 5 = 2 * (Real.pi / 5) by ring, Real.cos_two_mul,
      Real.cos_pi_div_five]
    nlinarith [h5]
  have hsin_sq : Real.sin (2 * Real.pi / 5) ^ 2 = (10 + 2 * Real.sqrt 5) / 16 := by
    have h5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)
    rw [Real.sin_sq, hcos2]
    nlinarith [h5]
  have hsin_pos : 0 < Real.sin (2 * Real.pi / 5) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos])
      (by linarith [Real.pi_pos])
  have hsin_eq : Real.sin (2 * Real.pi / 5) = Real.sqrt ((10 + 2 * Real.sqrt 5) / 16) := by
    rw [← hsin_sq]
    exact (Real.sqrt_sq hsin_pos.le).symm
  have hsqrt2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt5_gt : 2 < Real.sqrt 5 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hsqrt5_lt : Real.sqrt 5 < 9 / 4 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hsqrt2_lt : Real.sqrt 2 < 14754 / 10000 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)

  have hS1 : 5000 * Real.sqrt 2 / 7577 < Real.sin (2 * Real.pi / 5) := by
    rw [hsin_eq]
    refine Real.lt_sqrt_of_sq_lt ?_
    nlinarith [hsqrt2, hsqrt5_gt]
  have hS2 : Real.sin (2 * Real.pi / 5) < 5000 * Real.sqrt 2 / 7377 := by
    rw [hsin_eq]
    have hx0 : (0 : ℝ) ≤ (10 + 2 * Real.sqrt 5) / 16 := by positivity
    have hy0 : (0 : ℝ) ≤ 5000 * Real.sqrt 2 / 7377 := by positivity
    rw [Real.sqrt_lt hx0 hy0]
    nlinarith [hsqrt2, hsqrt5_lt]

  have harcA : 2 * Real.pi / 5 < Real.arcsin (5000 * Real.sqrt 2 / 7377) := by
    have h1 : -1 ≤ Real.sin (2 * Real.pi / 5) := Real.neg_one_le_sin _
    have h2 : 5000 * Real.sqrt 2 / 7377 ≤ 1 := by nlinarith [hsqrt2_lt]
    have h := Real.arcsin_lt_arcsin h1 hS2 h2
    rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at h
  have harcB : Real.arcsin (5000 * Real.sqrt 2 / 7577) < 2 * Real.pi / 5 := by
    have h1 : -1 ≤ 5000 * Real.sqrt 2 / 7577 := by
      have hpos : (0 : ℝ) ≤ 5000 * Real.sqrt 2 / 7577 := by positivity
      linarith
    have h2 : 5000 * Real.sqrt 2 / 7577 ≤ 1 := by nlinarith [hsqrt2_lt]
    have h := Real.arcsin_lt_arcsin h1 hS1 (Real.sin_le_one _)
    rwa [Real.arcsin_sin (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])] at h

  have hfa : twoBitExcursionTime (7377 / 10000) (Real.sqrt 2 / 2) < 0.9052 := by
    have hratio : Real.sqrt 2 / 2 / (7377 / 10000) = 5000 * Real.sqrt 2 / 7377 := by
      field_simp
      norm_num
    have hinner : 1 - (1 / Real.pi) *
        Real.arcsin (Real.sqrt 2 / 2 / (7377 / 10000)) < 3 / 5 := by
      rw [hratio]
      have hmul : (1 / Real.pi) * (2 * Real.pi / 5) <
          (1 / Real.pi) * Real.arcsin (5000 * Real.sqrt 2 / 7377) :=
        mul_lt_mul_of_pos_left harcA (by positivity)
      have hval : 1 - (1 / Real.pi) * (2 * Real.pi / 5) = 3 / 5 := by
        field_simp
        norm_num
      linarith [hmul, hval]
    unfold twoBitExcursionTime
    calc
      2 * (7377 / 10000) * (1 - (1 / Real.pi) *
          Real.arcsin (Real.sqrt 2 / 2 / (7377 / 10000)))
          < 2 * (7377 / 10000) * (3 / 5) :=
            mul_lt_mul_of_pos_left hinner (by norm_num)
      _ < 0.9052 := by norm_num
  have hfb : 0.9052 < twoBitExcursionTime (7577 / 10000) (Real.sqrt 2 / 2) := by
    have hratio : Real.sqrt 2 / 2 / (7577 / 10000) = 5000 * Real.sqrt 2 / 7577 := by
      field_simp
      norm_num
    have hinner : 3 / 5 < 1 - (1 / Real.pi) *
        Real.arcsin (Real.sqrt 2 / 2 / (7577 / 10000)) := by
      rw [hratio]
      have hmul : (1 / Real.pi) * Real.arcsin (5000 * Real.sqrt 2 / 7577) <
          (1 / Real.pi) * (2 * Real.pi / 5) :=
        mul_lt_mul_of_pos_left harcB (by positivity)
      have hval : 1 - (1 / Real.pi) * (2 * Real.pi / 5) = 3 / 5 := by
        field_simp
        norm_num
      linarith [hmul, hval]
    unfold twoBitExcursionTime
    calc
      0.9052 < 2 * (7577 / 10000) * (3 / 5) := by norm_num
      _ < 2 * (7577 / 10000) * (1 - (1 / Real.pi) *
          Real.arcsin (Real.sqrt 2 / 2 / (7577 / 10000))) :=
            mul_lt_mul_of_pos_left hinner (by norm_num)

  have hcont : ContinuousOn (fun x : ℝ => twoBitExcursionTime x (Real.sqrt 2 / 2))
      (Set.Icc (7377 / 10000) (7577 / 10000)) := by
    unfold twoBitExcursionTime
    refine ContinuousOn.mul (continuousOn_const.mul continuousOn_id) ?_
    refine ContinuousOn.sub continuousOn_const ?_
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.arcsin ?_
    refine ContinuousOn.div continuousOn_const continuousOn_id ?_
    intro x hx
    exact ne_of_gt (by linarith [hx.1])
  have hmem : (0.9052 : ℝ) ∈
      Set.Ioo (twoBitExcursionTime (7377 / 10000) (Real.sqrt 2 / 2))
        (twoBitExcursionTime (7577 / 10000) (Real.sqrt 2 / 2)) := ⟨hfa, hfb⟩
  obtain ⟨x, hxmem, hxeq⟩ :=
    intermediate_value_Ioo (a := (7377 / 10000 : ℝ)) (b := (7577 / 10000 : ℝ))
      (by norm_num) hcont hmem
  refine ⟨x, ?_, ?_⟩
  · rw [abs_lt]
    constructor <;> linarith [hxmem.1, hxmem.2]
  · have hxeq' : twoBitExcursionTime x (Real.sqrt 2 / 2) = 0.9052 := hxeq
    rw [hxeq', sub_self, abs_zero]
    norm_num

end Qatlib.Papers.HamOracle06.MainResults
