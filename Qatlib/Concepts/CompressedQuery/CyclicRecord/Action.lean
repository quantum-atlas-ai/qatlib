/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import Qatlib.Concepts.CompressedQuery.CyclicRecord.PhaseQuery

/-!
# Unitary actions of recording matrices

This module turns finite unitary matrices into unitary continuous linear operators and linear
isometry equivalences of Euclidean spaces. The construction `recordingAction` applies this
correspondence to the recording matrix with unit modulus phases.

The mathematical context is discussed in [MagniezZur2026].

## Main statements

* `matrixAction`: The Euclidean linear isometry equivalence induced by a unitary matrix.
* `recordingAction`: The isometric action of the recording query matrix.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical Matrix
namespace Qatlib.Concepts.CompressedQuery.CyclicRecord
variable {B : Type*} [Fintype B]

/-- The unitary continuous linear operator on Euclidean space induced by a matrix satisfying `Uᴴ
* U = 1`. -/
def matrixUnitary (U : Matrix B B ℂ) (hU : Uᴴ*U=1) :
    unitary (EuclideanSpace ℂ B →L[ℂ] EuclideanSpace ℂ B) := by
  let F := Matrix.toEuclideanCLM (n := B) (𝕜 := ℂ)
  have hs : F Uᴴ=star (F U) := by simpa only [Matrix.star_eq_conjTranspose] using (map_star F U)
  refine ⟨F U,?_⟩
  constructor
  · simpa only [map_mul,hs,map_one] using congrArg F hU
  · have hV : U*Uᴴ=1 := mul_eq_one_comm.mp hU
    simpa only [map_mul,hs,map_one] using congrArg F hV

/-- The complex linear isometry equivalence of Euclidean space induced by a matrix satisfying
`Uᴴ * U = 1`. -/
def matrixAction (U : Matrix B B ℂ) (hU : Uᴴ*U=1) : EuclideanSpace ℂ B ≃ₗᵢ[ℂ] EuclideanSpace ℂ B :=
  Unitary.linearIsometryEquiv (matrixUnitary U hU)

/-- The action of `matrixAction` is ordinary matrix-vector multiplication after passing between
Euclidean space and coordinate functions. -/
theorem matrixAction_apply (U : Matrix B B ℂ) (hU : Uᴴ*U=1) (v : EuclideanSpace ℂ B) :
    matrixAction U hU v=WithLp.toLp 2 (U*ᵥ (WithLp.ofLp v)) := rfl

/-- The linear isometry equivalence induced by the recording matrix when each phase has
conjugate product one. -/
def recordingAction {L : Type*} [Fintype L] [Nonempty L] (phase : L → ℂ)
    (hp : ∀ y, star (phase y)*phase y=1) : EuclideanSpace ℂ (Option L) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (Option L) :=
  matrixAction (recording phase) (by
    ext i j
    have h :=
        congrArg (fun M : Matrix (Option L) (Option L) ℂ => M i j) (recording_unitary phase hp)
    by_cases hij : i=j <;> simpa [Matrix.one_apply,hij] using h)
end Qatlib.Concepts.CompressedQuery.CyclicRecord
