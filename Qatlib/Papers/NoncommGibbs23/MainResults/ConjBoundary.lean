/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.ConjTranspose
public import Mathlib.LinearAlgebra.Matrix.Notation
public import Mathlib.Tactic

@[expose] public section


set_option autoImplicit false

namespace Qatlib.Papers.NoncommGibbs23.MainResults

open Matrix
open scoped Matrix

/-- A nonreal scalar coefficient distinguishes adjointing the same jump from
adjointing a jump with the conjugate coefficient, as in the legacy Gram expansion. -/
theorem conjugate_jump :
    ∃ A X : Matrix (Fin 2) (Fin 2) ℂ,
      ((-Complex.I) • A) * X * (Complex.I • A)ᴴ -
          (1 / 2 : ℂ) • ((Complex.I • A)ᴴ * ((-Complex.I) • A) * X +
            X * (Complex.I • A)ᴴ * ((-Complex.I) • A)) ≠
        (A * X * Aᴴ - (1 / 2 : ℂ) • (Aᴴ * A * X + X * Aᴴ * A)) := by
  refine ⟨!![1, 0; 0, 0], !![0, 1; 0, 0], ?_⟩
  intro h
  have h01 := congrFun (congrFun h 0) 1
  norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_two,
    Matrix.vecMul, dotProduct, Complex.I_sq] at h01

/-- Singleton jump and coefficient indices refute the full legacy finite-sum identity. -/
theorem gram_sum_false :
    ∃ (c : Fin 1 → Fin 1 → ℂ) (A : Fin 1 → Matrix (Fin 2) (Fin 2) ℂ)
      (X : Matrix (Fin 2) (Fin 2) ℂ),
      (∑ k, ((∑ i, star (c k i) • A i) * X * (∑ j, c k j • A j)ᴴ -
        (1 / 2 : ℂ) • ((∑ j, c k j • A j)ᴴ * (∑ i, star (c k i) • A i) * X +
          X * (∑ j, c k j • A j)ᴴ * (∑ i, star (c k i) • A i)))) ≠
        ∑ i, ∑ j, (∑ k, star (c k i) * c k j) •
          (A i * X * (A j)ᴴ - (1 / 2 : ℂ) •
            ((A j)ᴴ * A i * X + X * (A j)ᴴ * A i)) := by
  obtain ⟨A, X, h⟩ := conjugate_jump
  refine ⟨fun _ _ => Complex.I, fun _ => A, X, ?_⟩
  simpa using h

end Qatlib.Papers.NoncommGibbs23.MainResults
