/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Basic.Real.Star
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.QGradient17.GradientAlgo

/-- Idempotence alone does not supply the orthogonal-projection hypothesis of Lemma 26. -/
theorem idempotent_not_hermitian :
    ∃ P : Matrix (Fin 2) (Fin 2) ℝ, P * P = P ∧ ¬ P.IsHermitian := by
  refine ⟨!![1, 2; 0, 0], ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> norm_num [Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 1) h.eq
    norm_num [Matrix.conjTranspose_apply] at h01

end Qatlib.Papers.QGradient17.GradientAlgo
