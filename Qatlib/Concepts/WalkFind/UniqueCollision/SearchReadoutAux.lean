/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.UniqueCollision.JohnsonWalk

/-!
# Marked flips and initial search readout

This module records identities for the full marked phase flip and for Johnson-walk search with
zero outer iterations. In particular, `jwFlipBig` negates the good vector, while the
zero-iteration state and marked amplitude reduce to the starting state and its overlap
[Ambainis2007ElementDistinctness].

## Main statements

* `jwFlipBig_unitary`: the marked flip has identity Gram matrix.
* `jwFlipBig_goodVec`: the good vector has phase-flip eigenvalue `-1`.
* `jwMarkedAmplitude_zero`: the initial marked-overlap formula.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

open Qatlib.Concepts.WalkFind.UniqueCollision

namespace Qatlib.Concepts.WalkFind.UniqueCollision

open Matrix Qatlib.Concepts.WalkFind.UniqueCollision

/-- With zero outer search iterations, the full evolution matrix is the identity. -/
theorem jwRunMat_zero_iterations (k N r t2 : ℕ) (I : Finset (Fin N)) :
    jwRunMat k N r 0 t2 I = 1 := by
  simp [jwRunMat]

/-- At zero outer iterations, the diagonal readout sum equals the sum of the good-vector
amplitudes. -/
theorem jwDiagonalReadout_zero (k N r t2 : ℕ) (I : Finset (Fin N)) :
    (∑ p, star ((jwRunMat k N r 0 t2 I) p p) * jwGoodVec k N r I p) =
      ∑ p, jwGoodVec k N r I p := by
  simp [jwRunMat_zero_iterations]

/-- The overlap of the good vector with the uniform starting vector equals the uniform amplitude
times the sum of the good-vector entries. -/
theorem jwInitialMarkedOverlap (k N r : ℕ) (I : Finset (Fin N)) :
    (∑ p, star (jwGoodVec k N r I p) * jwStartBig N r p) =
      ((1 / Real.sqrt (Fintype.card (JRState N r) : ℝ) : ℝ) : ℂ) *
        ∑ p, jwGoodVec k N r I p := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _hp
  by_cases h : I ⊆ p.1.1 <;> simp [jwStartBig, jwGoodVec, h, mul_comm]

/-- The full marked flip multiplies each amplitude by `-1` on subsets containing `I` and by `1`
elsewhere. -/
theorem jwFlipBig_mulVec (k N r : ℕ) (I : Finset (Fin N)) (v : JRState N r → ℂ) :
    jwFlipBig k N r I *ᵥ v = fun p => (if I ⊆ p.1.1 then -1 else 1) * v p := by
  ext p
  exact Matrix.mulVec_diagonal _ _ _

/-- The conjugate transpose of the full marked flip times the flip is the identity. -/
theorem jwFlipBig_unitary (k N r : ℕ) (I : Finset (Fin N)) :
    star (jwFlipBig k N r I) * jwFlipBig k N r I = 1 := by
  simp only [jwFlipBig, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  ext p q
  by_cases hp : I ⊆ p.1.1 <;> simp [hp, Matrix.diagonal_apply, Matrix.one_apply]

/-- The good vector is an eigenvector of the full marked flip with eigenvalue `-1`. -/
theorem jwFlipBig_goodVec (k N r : ℕ) (I : Finset (Fin N)) :
    jwFlipBig k N r I *ᵥ jwGoodVec k N r I = -jwGoodVec k N r I := by
  rw [jwFlipBig_mulVec]
  ext p
  by_cases hp : I ⊆ p.1.1 <;> simp [jwGoodVec, hp]

/-- With zero outer search iterations, the evolved state is `jwStartBig`. -/
theorem jwRunState_zero (k N r t2 : ℕ) (I : Finset (Fin N)) :
    jwRunState k N r 0 t2 I = jwStartBig N r := by
  simp [jwRunState, jwRunMat_zero_iterations]

/-- With zero outer search iterations, the marked amplitude is the inner product of `jwGoodVec`
with `jwStartBig`. -/
theorem jwMarkedAmplitude_zero (k N r t2 : ℕ) (I : Finset (Fin N)) :
    jwMarkedAmplitude k N r 0 t2 I =
      ∑ p, star (jwGoodVec k N r I p) * jwStartBig N r p := by
  simp [jwMarkedAmplitude, jwRunState_zero]

end Qatlib.Concepts.WalkFind.UniqueCollision
