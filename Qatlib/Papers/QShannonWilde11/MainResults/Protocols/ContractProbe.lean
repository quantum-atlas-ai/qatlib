/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QShannonWilde11.MainResults.Model.ClassicalAux

@[expose] public section


/-! # Matrix-tail counterexamples with every literal old hypothesis checked

The old Markov statement omits positive definiteness of its threshold; the old
Bernstein statement replaces an exponential moment by a freely zero sandwich.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Qatlib.Papers.QShannonWilde11.MainResults.Protocols.ContractProbe

open Qatlib.Papers.QShannonWilde11.MainResults.Model
open Classical
open scoped BigOperators ComplexOrder MatrixOrder

/-- The identity on a one-dimensional register is not at most zero. -/
theorem identity_not_le_zero : ¬ (1 : Matrix (Fin 1) (Fin 1) ℂ) ≤ 0 := by
  intro h
  have hd := (Matrix.le_iff.mp h).diag_nonneg (i := (0 : Fin 1))
  norm_num at hd

/-- A zero threshold refutes the old operator Markov contract . -/
theorem markov_failure :
    let Pr : Unit → ℝ := fun _ => 1
    let X : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
    let A : Matrix (Fin 1) (Fin 1) ℂ := 0
    let EX : Matrix (Fin 1) (Fin 1) ℂ := 1
    IsProb Pr ∧ EX = ∑ ω, Pr ω • X ω ∧
      ¬ (∑ ω, if X ω ≤ A then 0 else Pr ω) ≤ (Matrix.trace (EX * A⁻¹)).re := by
  dsimp
  simp [IsProb, identity_not_le_zero]

/-- The zero sandwich refutes the old Bernstein expression at K=1 . -/
theorem bernstein_failure :
    let Pr : Unit → ℝ := fun _ => 1
    let X : Unit → Matrix (Fin 1) (Fin 1) ℂ := fun _ => 1
    let A : Matrix (Fin 1) (Fin 1) ℂ := 0
    let T : Matrix (Fin 1) (Fin 1) ℂ := 0
    IsProb Pr ∧ A.IsHermitian ∧ T.IsHermitian ∧
      ¬ (∑ ω, if X ω ≤ A then 0 else Pr ω) ≤
        (Fintype.card (Fin 1) : ℝ) *
          (Matrix.traceNorm (∑ ω, Pr ω • (T * X ω * T.conjTranspose))) ^ 1 := by
  dsimp
  simp [IsProb, identity_not_le_zero, Matrix.isHermitian_zero]

/-- A singular projection, hence a valid effect, on a two-dimensional register. -/
def singularEffect : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]

/-- A singular effect refutes the old ordinary-inverse Hayashi--Nagaoka contract .
The source uses a support inverse; the total nonsingular matrix inverse is zero here. -/
theorem hayashi_failure :
    singularEffect.PosSemidef ∧
      (1 - singularEffect).PosSemidef ∧
      ¬ (1 : Matrix (Fin 2) (Fin 2) ℂ) -
          (CFC.sqrt (singularEffect + 0))⁻¹ * singularEffect *
            (CFC.sqrt (singularEffect + 0))⁻¹ ≤
        ((1 : ℝ) + 1) • (1 - singularEffect) +
          ((2 : ℝ) + 1 + (1 : ℝ)⁻¹) • (0 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hS : singularEffect.PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  have hI : (1 - singularEffect).PosSemidef := by
    have heq : (1 : Matrix (Fin 2) (Fin 2) ℂ) - singularEffect = Matrix.diagonal ![0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> norm_num [singularEffect, Matrix.one_apply]
    rw [heq]
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro i
    fin_cases i <;> norm_num
  have hsquare : singularEffect * singularEffect = singularEffect := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [singularEffect, Matrix.mul_apply, Fin.sum_univ_two]
  have hsqrt : CFC.sqrt singularEffect = singularEffect := by
    simpa only [hsquare] using CFC.sqrt_mul_self singularEffect hS.nonneg
  have hinv : singularEffect⁻¹ = 0 := by
    apply Matrix.nonsing_inv_apply_not_isUnit
    norm_num [singularEffect, Matrix.det_fin_two]
  refine ⟨hS, hI, ?_⟩
  simp only [add_zero, hsqrt, hinv, zero_mul, mul_zero, sub_zero, smul_zero]
  intro h
  have hd := (Matrix.le_iff.mp h).diag_nonneg (i := (0 : Fin 2))
  norm_num [singularEffect, Matrix.one_apply] at hd

end Qatlib.Papers.QShannonWilde11.MainResults.Protocols.ContractProbe
