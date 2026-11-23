/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QCounting98.MainResults.Boundary

@[expose] public section

/-!
# A quantitative Euclidean boundary for Lemma 1

In [BrassardHoyerTapp1998Counting], Lemma 1 compares a phase change on the
first-register-zero subspace with a rank-one expression. Set the preparation to the identity
and fix the phase of the first-register-zero gate at `-1`. On the normalized two-qubit ancilla
supported by that subspace, the gate's output has complex Euclidean distance at least
`sqrt 2` from the rank-one output for every choice of the rank-one phase coefficient.

## Main statements

* `firstZero_literal_Euclidean_separation_sqrt_two`: the direct quantitative lower bound.
* `firstZero_literal_Euclidean_separation`: a positive constant chosen before quantifying
  over the rank-one phase.

## References

* [Brassard et al., 1998, §2](https://arxiv.org/abs/quant-ph/9805082v1)
-/

set_option autoImplicit false

noncomputable section

namespace Qatlib.Papers.QCounting98.MainResults.BoundaryEuclidean

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Papers.QCounting98.MainResults.Boundary
open Qatlib.Concepts.LchsSimulation.StaticLchs
open Qatlib.Foundations.QueryWordCore.Circuit

/-- The first-register-zero sign reflection and the literal rank-one formula are separated by
at least `sqrt 2` in Euclidean state norm for every rank-one phase coefficient. -/
theorem firstZero_literal_Euclidean_separation_sqrt_two (phase : ℂ) :
    Real.sqrt 2 ≤
      ‖toEuclidean_fromVec
        (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
          [Step.gate (preparedMark firstZeroSet)] ancillaInput -
        literalRankOne phase ancillaInput)‖ := by
  have hactual :
      Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
        [Step.gate (preparedMark firstZeroSet)] ancillaInput = -ancillaInput :=
    firstZero_actual_run
  have hsq :
      ‖toEuclidean_fromVec
        (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
          [Step.gate (preparedMark firstZeroSet)] ancillaInput -
          literalRankOne phase ancillaInput)‖ ^ 2 =
        2 + Complex.normSq (1 + phase) / 2 := by
    have hpoint :
        ∀ p : Bool × Bool,
          (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
            [Step.gate (preparedMark firstZeroSet)] ancillaInput -
            literalRankOne phase ancillaInput) p =
          if p = (false, false) then -((1 + phase) / Real.sqrt 2) else
            if p = (false, true) then -(Real.sqrt 2) else 0 := by
      intro p
      rw [hactual]
      match p with
      | (false, false) =>
          simp [literalRankOne, ancillaInput, TensorState, Plus, Ket, Hadamard,
            Qatlib.Foundations.PureStateMath.Inner, dotProduct,
            Fintype.sum_prod_type]
          field_simp
          ring
      | (false, true) =>
          simp [literalRankOne, ancillaInput, TensorState, Plus, Ket, Hadamard,
            Qatlib.Foundations.PureStateMath.Inner, dotProduct,
            Fintype.sum_prod_type]
          field_simp
          rw [sqrt2_sq]
          norm_num
      | (true, false) =>
          simp [literalRankOne, ancillaInput, TensorState, Plus, Ket, Hadamard,
            Qatlib.Foundations.PureStateMath.Inner, dotProduct,
            Fintype.sum_prod_type]
      | (true, true) =>
          simp [literalRankOne, ancillaInput, TensorState, Plus, Ket, Hadamard,
            Qatlib.Foundations.PureStateMath.Inner, dotProduct,
            Fintype.sum_prod_type]
    rw [norm_toEuclidean_fromVec_sq]
    simp only [hpoint, Fintype.sum_prod_type, Fintype.sum_bool]
    norm_num
    rw [div_pow, Complex.normSq_eq_norm_sq,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ Real.sqrt 2),
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have h2 : (Real.sqrt 2 : ℝ) ^ 2 ≤
      ‖toEuclidean_fromVec
        (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
          [Step.gate (preparedMark firstZeroSet)] ancillaInput -
          literalRankOne phase ancillaInput)‖ ^ 2 := by
    rw [hsq]
    have hnn : 0 ≤ Complex.normSq (1 + phase) / 2 :=
      div_nonneg (Complex.normSq_nonneg _) (by norm_num)
    rw [Real.sq_sqrt (by norm_num)]
    linarith
  exact (sq_le_sq₀ (by norm_num) (norm_nonneg _)).mp h2

/-- A positive separation constant for the fixed first-register-zero sign reflection can be
chosen before quantifying over the rank-one phase coefficient. -/
theorem firstZero_literal_Euclidean_separation :
    ∃ C > 0, ∀ phase : ℂ,
      C ≤ ‖toEuclidean_fromVec
        (Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
          [Step.gate (preparedMark firstZeroSet)] ancillaInput -
          literalRankOne phase ancillaInput)‖ := by
  refine ⟨Real.sqrt 2, by norm_num, fun phase => ?_⟩
  exact firstZero_literal_Euclidean_separation_sqrt_two phase

end Qatlib.Papers.QCounting98.MainResults.BoundaryEuclidean
