/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QLinearODE17.TaylorAnalysis.Theorem7Aux
import Qatlib.Papers.QLinearODE17.Structure.TaylorReadoutCorrected

/-!
# Stability and guards for Taylor readout probabilities

This module proves positivity and the trace identity for `taylorMeasuredDensityV2`, together
with norm estimates for collapse and stability of success-set mass. It derives a squared
probability lower bound under the guard δ ≤ a and gives explicit examples showing why an
unguarded square can fail.

The zero-generator example verifies the V2 solution, its final blocks, and the measured density
in the readout setting of [BerryEtAl2017ODE].

## Main statements

* `taylor_measure_sqrt_sub_le`: Stability of the square root of success-set mass.
* `taylor_measure_probability_of_guard`: A squared lower bound under a nonnegative-amplitude
  guard.
* `taylor_unguarded_probability_square_counterexample`: An explicit failure of squaring an
  unguarded lower bound.

## References

* [Berry et al., 2017][BerryEtAl2017ODE]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution Qatlib.Papers.QLinearODE17.TaylorAnalysis
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.Measurement

namespace Qatlib.Papers.QLinearODE17.StructureCore

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

variable {N : Type} [Fintype N] [DecidableEq N]

/-- The V2 measured output density is positive semidefinite. -/
theorem taylorMeasuredDensityV2_posSemidef (m k p : ℕ)
    (φ : QState (Fin (m * (k + 1) + p + 1) × N)) :
    (taylorMeasuredDensityV2 m k p φ).PosSemidef :=
  taylorMeasuredDensity_posSemidef m k p φ

/-- The trace of the V2 measured output density equals the complex embedding of the success-set
mass. -/
theorem taylorMeasuredDensityV2_trace (m k p : ℕ)
    (φ : QState (Fin (m * (k + 1) + p + 1) × N)) :
    Matrix.trace (taylorMeasuredDensityV2 m k p φ) =
      (MeasureProb φ (taylorSuccessSet m k p) : ℂ) :=
  taylorMeasuredDensity_trace m k p φ

/-- The norm of a state collapsed to a finite set is the square root of its mass on that set. -/
theorem taylor_collapse_norm (ψ : QState N) (S : Finset N) :
    ‖stateVector (Collapse ψ S)‖ = Real.sqrt (MeasureProb ψ S) := by
  have hs : ‖stateVector (Collapse ψ S)‖ ^ 2 = MeasureProb ψ S := by
    rw [stateVector_norm_sq]
    exact sum_normSq_collapse ψ S
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

/-- Collapsing a state to a finite set cannot increase its norm. -/
theorem taylor_collapse_norm_le (ψ : QState N) (S : Finset N) :
    ‖stateVector (Collapse ψ S)‖ ≤ ‖stateVector ψ‖ := by
  apply taylor_stateVector_norm_mono
  intro n
  rw [collapse_apply]
  split_ifs
  · rfl
  · simp

/-- If two state vectors are within δ, the square root of the second state's mass on `S` is at
least that of the first minus δ. -/
theorem taylor_measure_sqrt_sub_le (ψ φ : QState N) (S : Finset N) (δ : ℝ)
    (herr : ‖stateVector φ - stateVector ψ‖ ≤ δ) :
    Real.sqrt (MeasureProb ψ S) - δ ≤ Real.sqrt (MeasureProb φ S) := by
  have heq : Collapse φ S - Collapse ψ S = Collapse (φ - ψ) S := by
    ext n
    simp only [Pi.sub_apply, collapse_apply]
    split_ifs <;> simp
  have hnorm : ‖stateVector (Collapse φ S) - stateVector (Collapse ψ S)‖ ≤ δ := by
    change ‖stateVector (Collapse φ S - Collapse ψ S)‖ ≤ δ
    rw [heq]
    exact (taylor_collapse_norm_le (φ - ψ) S).trans herr
  have htri := norm_le_norm_add_norm_sub (stateVector (Collapse φ S)) (stateVector (Collapse ψ S))
  rw [taylor_collapse_norm, taylor_collapse_norm] at htri
  linarith

/-- If a ≤ √`MeasureProb ψ S`, δ ≤ a, and the states are within δ, then the mass of `φ` on `S`
is at least (a - δ)². -/
theorem taylor_measure_probability_of_guard (ψ φ : QState N) (S : Finset N) (a δ : ℝ)
    (ha : a ≤ Real.sqrt (MeasureProb ψ S)) (hguard : δ ≤ a)
    (herr : ‖stateVector φ - stateVector ψ‖ ≤ δ) :
    (a - δ) ^ 2 ≤ MeasureProb φ S := by
  have hle := taylor_measure_sqrt_sub_le ψ φ S δ herr
  have hs := Real.sq_sqrt (measureProb_nonneg φ S)
  have hnn := Real.sqrt_nonneg (MeasureProb φ S)
  nlinarith

/-- At the stated parameters, the square-root success-mass estimate minus the inverse-solver
error is negative. -/
theorem taylor_joint_mass_lower_bound_negative :
    Real.sqrt (((1 + 1 : ℕ) : ℝ) / ((1 : ℝ) + 77 * (1 : ℝ) * (10 : ℝ) ^ 2)) -
      (1 : ℝ) / 2 ^ (1 : ℕ) < 0 := by
  have he : (((1 + 1 : ℕ) : ℝ) / ((1 : ℝ) + 77 * (1 : ℝ) * (10 : ℝ) ^ 2)) =
      (2 / 7701 : ℝ) := by norm_num
  rw [he]
  simp only [pow_one]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2 / 7701)
  have hn := Real.sqrt_nonneg (2 / 7701 : ℝ)
  nlinarith

/-- The scalar state supported only at label zero in the eight-label Taylor system. -/
def taylorOutsideSuccess : QState (Fin 8 × Unit) :=
  fun r => if r.1.val = 0 then 1 else 0

/-- The normalized state `taylorOutsideSuccess` is within 1/2 of itself, but squaring its
square-root success mass minus 1/2 does not give a valid lower bound on its success mass. -/
theorem taylor_unguarded_probability_square_counterexample :
    Normalized taylorOutsideSuccess ∧
    ‖stateVector taylorOutsideSuccess - stateVector taylorOutsideSuccess‖ ≤ (1 / 2 : ℝ) ∧
    ¬((Real.sqrt (MeasureProb taylorOutsideSuccess (taylorSuccessSet 1 5 1)) -
        (1 / 2 : ℝ)) ^ 2 ≤ MeasureProb taylorOutsideSuccess (taylorSuccessSet 1 5 1)) := by
  norm_num [Normalized, MeasureProb, BornProb, taylorOutsideSuccess,
    taylorSuccessSet, Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]

/-- The explicit corrected zero-generator state solves the V2 system, has unit final blocks and
measured trace 2, and agrees with the constant scalar ODE solution. -/
theorem taylorV2_zero_generator_consumer :
    taylorStepMatrixV2 1 5 1 (0 : Matrix Unit Unit ℂ) *ᵥ correctedZeroSolution =
      taylorRHS 1 5 1 1 (fun _ : Unit => 1) 0 ∧
    taylorBlock correctedZeroSolution (taylorFinalLabel 1 5 1 0 (by omega)) =
      (fun _ : Unit => 1) ∧
    taylorBlock correctedZeroSolution (taylorFinalLabel 1 5 1 1 (by omega)) =
      (fun _ : Unit => 1) ∧
    Matrix.trace (taylorMeasuredDensityV2 1 5 1 correctedZeroSolution) = 2 ∧
    taylorODESolution (0 : Matrix Unit Unit ℂ) 0 (fun _ => 1) 1 = (fun _ => 1) := by
  refine ⟨correctedZeroSolution_solves, ?_, ?_, ?_, taylorODESolution_zero_signal 1⟩
  · ext n
    norm_num [taylorBlock, correctedZeroSolution, taylorFinalLabel]
  · ext n
    norm_num [taylorBlock, correctedZeroSolution, taylorFinalLabel]
  · rw [taylorMeasuredDensityV2_trace]
    norm_num [MeasureProb, BornProb, taylorSuccessSet, correctedZeroSolution,
      Finset.sum_filter, Fintype.sum_prod_type, Fin.sum_univ_succ]

end Qatlib.Papers.QLinearODE17.StructureCore
