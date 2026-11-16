/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PureStateMath.Qubit
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ext
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

@[expose] public section


set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.QGradient17.GradientAlgo

open Qatlib.Foundations.PureStateMath

/-- The legacy unsigned product of the two reflections has the wrong global sign at zero angle. -/
theorem zero_angle_counterexample :
    let ψ : QState (Fin 2) := ![1, 0]
    let φ : QState (Fin 2) := ![0, 1]
    let P₁ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 0]
    let P₂ : Matrix (Fin 2) (Fin 2) ℂ := !![0, 0; 0, 1]
    (1 : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    Normalized ψ ∧ Normalized φ ∧ Normalized ψ ∧
    ApplyGate (1 : Matrix (Fin 2) (Fin 2) ℂ) ψ =
      (Real.sin 0 : ℂ) • φ + (Real.cos 0 : ℂ) • ψ ∧
    (∑ i : Fin 2, star (φ i) * ψ i) = 0 ∧
    P₁ * P₁ = P₁ ∧ P₁.conjTranspose = P₁ ∧
    P₂ * P₂ = P₂ ∧ P₂.conjTranspose = P₂ ∧
    ApplyGate P₂ φ = φ ∧ ApplyGate P₂ ψ = 0 ∧ ApplyGate P₁ ψ = ψ ∧
    ApplyGate P₁ (ApplyGate (1 : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose
      ((Real.cos 0 : ℂ) • φ - (Real.sin 0 : ℂ) • ψ)) = 0 ∧
    ApplyGate
      (((1 : Matrix (Fin 2) (Fin 2) ℂ) * ((2 : ℂ) • P₁ - 1) *
        (1 : Matrix (Fin 2) (Fin 2) ℂ).conjTranspose * ((2 : ℂ) • P₂ - 1)) ^ 1)
      (ApplyGate (1 : Matrix (Fin 2) (Fin 2) ℂ) ψ) ≠
        (Real.sin ((2 * (1 : ℝ) + 1) * 0) : ℂ) • φ +
          (Real.cos ((2 * (1 : ℝ) + 1) * 0) : ℂ) • ψ := by
  norm_num [Normalized, ApplyGate, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Fin.sum_univ_two, funext_iff, Fin.forall_fin_two, Matrix.conjTranspose_apply,
    Matrix.smul_apply]
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [Matrix.conjTranspose_apply]

end Qatlib.Papers.QGradient17.GradientAlgo
