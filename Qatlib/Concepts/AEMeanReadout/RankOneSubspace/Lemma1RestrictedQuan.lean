/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Qatlib.Concepts.AEMeanReadout.RankOneSubspace.Lemma1RestrictedStat

/-!
# Conjugation of rank-one phase operators

This module proves that conjugating a coordinate projector by a matrix gives the outer product
of the corresponding column. Under `A * A.conjTranspose = 1`,
`zoo_counting_rankone_phase_conjugation` applies this identity to the rank-one phase operator of
[BrassardHoyerTapp1998Counting].

## Main statements

* `zoo_counting_conjugate_basis_projector`: the column outer-product identity.
* `zoo_counting_rankone_phase_conjugation`: the conjugation formula for a rank-one phase
  operator.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

/-- Conjugating the coordinate projector at `k` by `A` gives the outer product of column `k`
with its complex conjugate. -/
lemma zoo_counting_conjugate_basis_projector
    {ι κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (k : κ) :
    A * Matrix.single k k (1 : ℂ) * A.conjTranspose =
      Matrix.vecMulVec (fun i => A i k) (fun j => star (A j k)) := by
  rw [Matrix.single_eq_single_vecMulVec_single, Matrix.mul_vecMulVec,
    Matrix.vecMulVec_mul, Matrix.mulVec_single_one, Matrix.single_one_vecMul]
  rfl

/-- If `A * A.conjTranspose = 1`, conjugating a phase update at coordinate zero gives the
identity plus that update on the outer product of the first column [Brassard et al., Lemma
1][BrassardHoyerTapp1998Counting]. -/
theorem zoo_counting_rankone_phase_conjugation :
    ∀ (n : ℕ) (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (φ : ℂ),
      A * A.conjTranspose = 1 →
      A * (1 + (φ - 1) • Matrix.single 0 0 (1 : ℂ)) * A.conjTranspose =
        1 + (φ - 1) • Matrix.vecMulVec (fun i => A i 0) (fun j => star (A j 0)) := by
  intro n A φ hA
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, hA,
    Matrix.mul_smul, Matrix.smul_mul, zoo_counting_conjugate_basis_projector]

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
