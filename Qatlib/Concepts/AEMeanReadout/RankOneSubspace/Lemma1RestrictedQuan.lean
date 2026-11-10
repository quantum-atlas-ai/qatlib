/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma1RestrictedStat

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

lemma zoo_counting_conjugate_basis_projector
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (k : κ) :
    A * Matrix.single k k (1 : ℂ) * A.conjTranspose =
      Matrix.vecMulVec (fun i => A i k) (fun j => star (A j k)) := by
  rw [Matrix.single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.mulVec_single_one, Matrix.single_one_vecMul]
  rfl

theorem zoo_counting_rankone_phase_conjugation :
    ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (φ : ℂ),
      A * A.conjTranspose = 1 →
      A * (1 + (φ - 1) • Matrix.single 0 0 (1 : ℂ)) * A.conjTranspose =
        1 + (φ - 1) • Matrix.vecMulVec (fun i => A i 0) (fun j => star (A j 0)) := by
  intro n A φ hA
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hA,
    Matrix.mul_smul, Matrix.smul_mul, zoo_counting_conjugate_basis_projector]

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
