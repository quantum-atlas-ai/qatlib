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
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.NeZero
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Algebra.NeZero
import Mathlib.Algebra.Notation.Pi.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.Group.Unbundled.Basic
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.Basic.Real.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Data.Set.Defs
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Order.Filter.Defs
import Mathlib.Order.Filter.Tendsto
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Order.Max
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
import Mathlib.Topology.Algebra.Field
import Mathlib.Topology.Algebra.Group.Defs
import Mathlib.Topology.Algebra.GroupWithZero
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
import Mathlib.Topology.UniformSpace.Defs

/-!
# Continuous Grover query-time formulas

This module defines `continuousGroverTime` and the squared-cosine parameterization
`continuousGroverTimeAt`. It verifies the target identity at the designated zero-error time,
simplifies the half-error time expression, and proves that the zero-error time divided by √N
tends to 1/2. See [Mochon2007] for the Hamiltonian oracle formulation.

## Main statements

* `continuousGrover_zeroError_time`: For N > 1, evaluating the squared cosine of the Grover
  rotation angle at `continuousGroverTime N` gives 1 / N.
* `continuousGrover_halfError_time`: For N > 1, the continuous Grover time expression with
  target √(1 / 2) simplifies to N / (4√(N − 1)).
* `continuousGroverTime_asymptotic`: As real N tends to infinity, `continuousGroverTime N /
  Real.sqrt N` tends to 1 / 2.

## References

* [Mochon, 2007][Mochon2007]
-/

set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology

namespace Qatlib.Papers.HamOracle06.MainResults

/-- The continuous Grover time N arccos(1 / √N) / (π√(N − 1)). -/
def continuousGroverTime (N : ℝ) : ℝ :=
  (1 / Real.pi) * (N / Real.sqrt (N - 1)) * Real.arccos (1 / Real.sqrt N)

/-- The continuous Grover time parameter N arccos(√x) / (π√(N − 1)) for a squared-cosine target
x. -/
def continuousGroverTimeAt (N x : ℝ) : ℝ :=
  (1 / Real.pi) * (N / Real.sqrt (N - 1)) * Real.arccos (Real.sqrt x)

/-- For N > 1, evaluating the squared cosine of the Grover rotation angle at
`continuousGroverTime N` gives 1 / N. See [Mochon2007]. -/
theorem continuousGrover_zeroError_time (N : ℝ) (hN : 1 < N) :
    Real.cos (Real.pi * Real.sqrt (N - 1) / N * continuousGroverTime N) ^ 2 = 1 / N := by
  have hN0 : 0 < N := by linarith
  have hs : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr (by linarith)
  have hsqrtN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have harg : Real.pi * Real.sqrt (N - 1) / N * continuousGroverTime N
      = Real.arccos (1 / Real.sqrt N) := by
    unfold continuousGroverTime
    field_simp
  rw [harg]
  have hle : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN.le
  have hmem : 1 / Real.sqrt N ∈ Set.Icc (-1 : ℝ) 1 := by
    constructor
    · have hnn : 0 ≤ 1 / Real.sqrt N := by positivity
      linarith
    · rw [div_le_iff₀ hsqrtN]
      simpa using hle
  rw [Real.cos_arccos hmem.1 hmem.2, div_pow, one_pow, Real.sq_sqrt hN0.le]

/-- For N > 1, the continuous Grover time expression with target √(1 / 2) simplifies to N /
(4√(N − 1)). See [Mochon2007]. -/
theorem continuousGrover_halfError_time (N : ℝ) (hN : 1 < N) :
    (1 / Real.pi) * (N / Real.sqrt (N - 1)) * Real.arccos (Real.sqrt (1 / 2))
      = N / (4 * Real.sqrt (N - 1)) := by
  have hcos : Real.sqrt (1 / 2) = Real.cos (Real.pi / 4) := by
    rw [Real.cos_pi_div_four]
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num : (0 : ℝ) ≤ 1 / 2) (by positivity)]
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have harccos : Real.arccos (Real.sqrt (1 / 2)) = Real.pi / 4 := by
    exact Real.arccos_eq_of_eq_cos (by positivity) (by linarith [Real.pi_pos]) hcos
  have hs : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr (by linarith)
  rw [harccos]
  field_simp

/-- As real N tends to infinity, `continuousGroverTime N / Real.sqrt N` tends to 1 / 2. See
[Mochon2007]. -/
theorem continuousGroverTime_asymptotic :
    Tendsto (fun N : ℝ => continuousGroverTime N / Real.sqrt N) atTop (𝓝 (1 / 2)) := by
  have harc : Tendsto (fun N : ℝ => Real.arccos (1 / Real.sqrt N)) atTop
      (𝓝 (Real.pi / 2)) := by
    have hinv : Tendsto (fun N : ℝ => 1 / Real.sqrt N) atTop (𝓝 0) := by
      have h := Real.tendsto_sqrt_atTop.inv_tendsto_atTop
      simpa [one_div] using! h
    have h := (Real.continuous_arccos.tendsto 0).comp hinv
    simpa [Real.arccos_zero] using! h
  have hratio : Tendsto (fun N : ℝ => N / (N - 1)) atTop (𝓝 1) := by
    have hinv : Tendsto (fun N : ℝ => N⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
    have hsub : Tendsto (fun N : ℝ => (1 : ℝ) - N⁻¹) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub hinv :
        Tendsto (fun N : ℝ => (1 : ℝ) - N⁻¹) atTop (𝓝 ((1 : ℝ) - 0)))
    have hinvsub := hsub.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using hinvsub.congr' (by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
      have hN0 : N ≠ 0 := ne_of_gt (by linarith)
      have hNm : N - 1 ≠ 0 := ne_of_gt (by linarith)
      field_simp)
  have hfac : Tendsto (fun N : ℝ => Real.sqrt N / Real.sqrt (N - 1)) atTop (𝓝 1) := by
    have h := Real.continuous_sqrt.tendsto 1 |>.comp hratio
    rw [Real.sqrt_one] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
    have hN0 : 0 ≤ N := by linarith
    exact Real.sqrt_div hN0 (N - 1)
  have hlimit : Tendsto (fun N : ℝ =>
      (1 / Real.pi) * (Real.sqrt N / Real.sqrt (N - 1)) *
        Real.arccos (1 / Real.sqrt N)) atTop (𝓝 (1 / 2)) := by
    have h := (tendsto_const_nhds (x := (1 / Real.pi))).mul (hfac.mul harc)
    have hval : (1 / Real.pi) * (1 * (Real.pi / 2)) = 1 / 2 := by
      field_simp
    rw [hval] at h
    simpa [mul_assoc] using h
  refine hlimit.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with N hN
  have hN0 : 0 < N := by linarith
  have hs : 0 < Real.sqrt (N - 1) := Real.sqrt_pos.mpr (by linarith)
  have hsN : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hsq : Real.sqrt N * Real.sqrt N = N := by
    simpa [sq] using Real.sq_sqrt hN0.le
  have hkey : Real.sqrt N = N / Real.sqrt N := by
    rw [eq_div_iff hsN.ne']
    exact hsq
  unfold continuousGroverTime
  rw [hkey]
  field_simp
  rw [sq, hsq]

end Qatlib.Papers.HamOracle06.MainResults
