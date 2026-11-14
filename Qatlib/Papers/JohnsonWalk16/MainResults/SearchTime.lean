/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Algebra.Rat
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.Group.Action.Pi
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.Module.Defs
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Rat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.InnerProductSpace.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.FunLike.Basic
public import Mathlib.Basic.FunLike.Equiv
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Matrix.Diagonal
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.NNRat.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Rat.Defs
public import Mathlib.Data.Rat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.GroupTheory.GroupAction.Ring
public import Mathlib.LinearAlgebra.Matrix.Defs
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Tactic
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Algebra.Group.Defs
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Monoid.Defs
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Basic
public import Mathlib.Topology.Continuous
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.Instances.Rat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.Neighborhoods
public import Mathlib.Topology.UniformSpace.Defs

@[expose] public section

/-!
# Reported search time and ideal two-level transfer

`vertexCount` and `reportedGap` encode the scalar vertex-count polynomial and reported splitting
for Johnson graph search. The module proves the exact transfer-time formula and its asymptotic
ratio to π√N/2, and independently evaluates the closed-form evolution `idealTwoLevel` at time
π/gap. See [Wong2016].

## Main statements

* `search_time_asymptotic`: The reported transfer time is asymptotic to (π/2)√(`vertexCount n`)
  as natural n tends to infinity.
* `ideal_dynamics_at_reported_gap`: For positive n, the ideal evolution with `reportedGap n`
  transfers the first coordinate vector to the second at time π/`reportedGap n`, up to the
  displayed complex phase.

## References

* [Wong, 2016][Wong2016]
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Matrix
open Filter
open scoped BigOperators Topology

namespace Qatlib.Papers.JohnsonWalk16.MainResults.SearchTime

/-- The polynomial n(n − 1)(n − 2)/6, viewed as a real-valued function. -/
def vertexCount (n : ℝ) : ℝ := n * (n - 1) * (n - 2) / 6

/-- The reported energy splitting 2√6/(n√n) for the Johnson graph search approximation. -/
def reportedGap (n : ℝ) : ℝ := 2 * Real.sqrt 6 / (n * Real.sqrt n)

/-- The reported splitting is positive when n is positive. -/
theorem reportedGap_pos {n : ℝ} (hn : 0 < n) : 0 < reportedGap n := by
  unfold reportedGap
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hden : 0 < n * Real.sqrt n := mul_pos hn (Real.sqrt_pos.2 hn)
  exact div_pos (mul_pos (by norm_num) h6) hden

/-- The reported splitting is nonzero when n is positive. -/
theorem reportedGap_ne_zero {n : ℝ} (hn : 0 < n) : reportedGap n ≠ 0 :=
  ne_of_gt (reportedGap_pos hn)

/-- For positive n, the time π/`reportedGap n` equals (π/2)√(n³/6); see [Wong2016]. -/
theorem search_time_exact {n : ℝ} (hn : 0 < n) :
    Real.pi / reportedGap n = Real.pi / 2 * Real.sqrt (n ^ 3 / 6) := by
  have hn0 : 0 ≤ n := le_of_lt hn
  have h6 : (0 : ℝ) < Real.sqrt 6 := Real.sqrt_pos.2 (by norm_num)
  have hs : Real.sqrt (n ^ 3 / 6) = n * Real.sqrt n / Real.sqrt 6 := by
    have hsq : (n * Real.sqrt n / Real.sqrt 6) ^ 2 = n ^ 3 / 6 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hn0, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 6)]
      ring
    rw [← hsq, Real.sqrt_sq (by positivity)]
  unfold reportedGap
  rw [hs]
  have hden : n * Real.sqrt n ≠ 0 := (mul_pos hn (Real.sqrt_pos.2 hn)).ne'
  field_simp [h6.ne', hden]

/-- The ratio of `vertexCount n` to n³/6 tends to one as natural n tends to infinity. -/
theorem vertexCount_ratio_tendsto :
    Tendsto (fun n : ℕ => vertexCount (n : ℝ) / ((n : ℝ) ^ 3 / 6)) atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ => ((1 : ℝ) - 1 / (n : ℝ)) * ((1 : ℝ) - 2 / (n : ℝ)))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => (1 : ℝ) - 1 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
        (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
    have h2 : Tendsto (fun n : ℕ => (1 : ℝ) - 2 / (n : ℝ)) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
        (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
    simpa using h1.mul h2
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold vertexCount
  field_simp

/-- The ratio of n³/6 to `vertexCount n` tends to one as natural n tends to infinity. -/
theorem n_cube_over_six_ratio_tendsto :
    Tendsto (fun n : ℕ => ((n : ℝ) ^ 3 / 6) / vertexCount (n : ℝ)) atTop (𝓝 1) := by
  have hbase : Tendsto (fun n : ℕ => (1 / ((1 : ℝ) - 1 / (n : ℝ))) * (1 / ((1 : ℝ) - 2 / (n : ℝ))))
      atTop (𝓝 1) := by
    have h1 : Tendsto (fun n : ℕ => 1 / ((1 : ℝ) - 1 / (n : ℝ))) atTop (𝓝 1) := by
      have hc : Tendsto (fun n : ℕ => ((1 : ℝ) - 1 / (n : ℝ))) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
          (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ))
      simpa using hc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    have h2 : Tendsto (fun n : ℕ => 1 / ((1 : ℝ) - 2 / (n : ℝ))) atTop (𝓝 1) := by
      have hc : Tendsto (fun n : ℕ => ((1 : ℝ) - 2 / (n : ℝ))) atTop (𝓝 1) := by
        simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop)).sub
          (tendsto_const_div_atTop_nhds_zero_nat (2 : ℝ))
      simpa using hc.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h1.mul h2
  refine Tendsto.congr' ?_ hbase
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  unfold vertexCount
  field_simp

/-- The reported transfer time is asymptotic to (π/2)√(`vertexCount n`) as natural n tends to
infinity; see [Wong2016]. -/
theorem search_time_asymptotic :
    Tendsto (fun n : ℕ =>
        (Real.pi / reportedGap (n : ℝ)) / (Real.pi / 2 * Real.sqrt (vertexCount (n : ℝ))))
      atTop (𝓝 1) := by
  have hsq : Tendsto (fun n : ℕ =>
        Real.sqrt ((((n : ℝ) ^ 3 / 6) / vertexCount (n : ℝ)))) atTop (𝓝 1) := by
    have := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp n_cube_over_six_ratio_tendsto
    simpa [Real.sqrt_one] using! this
  refine Tendsto.congr' ?_ hsq
  filter_upwards [eventually_ge_atTop 3] with n hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hnR : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have h1 : (0 : ℝ) < n - 1 := by linarith
  have h2 : (0 : ℝ) < n - 2 := by linarith
  have hNpos : 0 < vertexCount (n : ℝ) := by
    unfold vertexCount
    have : 0 < (n : ℝ) * ((n : ℝ) - 1) * ((n : ℝ) - 2) :=
      mul_pos (mul_pos hn0 h1) h2
    exact div_pos this (by norm_num)
  have hnum : (0 : ℝ) ≤ (n : ℝ) ^ 3 / 6 := by positivity
  rw [Real.sqrt_div hnum (vertexCount (n : ℝ)), search_time_exact hn0]
  field_simp [hNpos.ne', (Real.sqrt_pos.2 hNpos).ne', Real.pi_ne_zero]

/-- The two-dimensional Pauli X matrix, which exchanges the two coordinate vectors. -/
def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

/-- The closed-form two-level evolution with common energy E, splitting gap, and time t. -/
def idealTwoLevel (E gap t : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Complex.exp (-(Complex.I) * (E : ℂ) * (t : ℂ)) •
    (Real.cos (gap * t / 2) • (1 : Matrix (Fin 2) (Fin 2) ℂ)
      - (Complex.I * (Real.sin (gap * t / 2) : ℂ)) • sigmaX)

/-- For nonzero gap, the ideal evolution at π/gap is `sigmaX` multiplied by the phase −i
exp(−iEπ/gap). -/
theorem idealTwoLevel_at_pi_gap {E gap : ℝ} (hgap : gap ≠ 0) :
    idealTwoLevel E gap (Real.pi / gap) =
      (Complex.exp (-(Complex.I) * (E : ℂ) * ((Real.pi / gap : ℝ) : ℂ)) * (-Complex.I)) •
        sigmaX := by
  unfold idealTwoLevel
  have ht : gap * (Real.pi / gap) / 2 = Real.pi / 2 := by
    field_simp
  rw [ht, Real.cos_pi_div_two, Real.sin_pi_div_two]
  rw [zero_smul, zero_sub, Complex.ofReal_one, mul_one]
  rw [smul_neg, smul_smul, ← neg_smul]
  congr 1
  ring

/-- The Pauli X matrix maps the first coordinate vector to the second. -/
theorem sigmaX_mulVec_r :
    sigmaX *ᵥ (![1, 0] : Fin 2 → ℂ) = ![0, 1] := by
  ext i
  fin_cases i <;> simp [sigmaX, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

/-- For nonzero gap, the ideal evolution at π/gap transfers the first coordinate vector to the
second with phase −i exp(−iEπ/gap). -/
theorem r_maps_to_u {E gap : ℝ} (hgap : gap ≠ 0) :
    (idealTwoLevel E gap (Real.pi / gap)) *ᵥ (![1, 0] : Fin 2 → ℂ) =
      (Complex.exp (-(Complex.I) * (E : ℂ) * ((Real.pi / gap : ℝ) : ℂ)) * (-Complex.I)) •
        (![0, 1] : Fin 2 → ℂ) := by
  rw [idealTwoLevel_at_pi_gap hgap, Matrix.smul_mulVec, sigmaX_mulVec_r]

/-- For positive n, the ideal evolution with `reportedGap n` transfers the first coordinate
vector to the second at time π/`reportedGap n`, up to the displayed complex phase; see
[Wong2016]. -/
theorem ideal_dynamics_at_reported_gap {E n : ℝ} (hn : 0 < n) :
    (idealTwoLevel E (reportedGap n) (Real.pi / reportedGap n)) *ᵥ (![1, 0] : Fin 2 → ℂ) =
      (Complex.exp (-(Complex.I) * (E : ℂ) * ((Real.pi / reportedGap n : ℝ) : ℂ)) *
        (-Complex.I)) • (![0, 1] : Fin 2 → ℂ) :=
  r_maps_to_u (reportedGap_ne_zero hn)

end Qatlib.Papers.JohnsonWalk16.MainResults.SearchTime
