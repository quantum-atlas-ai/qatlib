/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Reflection.ReflectionLaws

/-!
# Projected unitary encodings

The predicate `ProjectedUnitaryEncoding` expresses a matrix as the compression `Lᴴ * U * R` of a
unitary between two isometries. The module develops the associated range projectors and the
elementary linearity and adjoint laws for `compress`.

These constructions provide the matrix formulation of projected unitary encodings used in
quantum singular value transformation [GilyenSuLowWiebe2019].

## Main statements

* `rangeProjector_isOrthogonalProjector`: the range matrix of an isometry is an orthogonal
  projector.
* `ProjectedUnitaryEncoding.adjoint`: taking adjoints swaps the two encoding isometries.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement

namespace Qatlib.Concepts.Execution.WorkspaceCP

open Matrix

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

/-- The matrix `V` is an isometry when `Vᴴ * V = 1`. -/
def IsIsometry (V : Matrix H I ℂ) : Prop := Vᴴ * V = 1

/-- The compression `Lᴴ * U * R` of an ambient operator between two rectangular matrices. -/
noncomputable def compress (L : Matrix H O ℂ) (U : Matrix H H ℂ)
    (R : Matrix H I ℂ) : Matrix O I ℂ := Lᴴ * U * R

/-- A unitary `U` encodes `A` through isometries `L` and `R` when `compress L U R = A`. -/
structure ProjectedUnitaryEncoding (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) : Prop where
  unitary : U ∈ Matrix.unitaryGroup H ℂ
  left_isometry : IsIsometry L
  right_isometry : IsIsometry R
  encoded : compress L U R = A

/-- The matrix `V * Vᴴ`, which projects onto the range of `V` when `V` is an isometry. -/
noncomputable def rangeProjector (V : Matrix H I ℂ) : Matrix H H ℂ := V * Vᴴ

omit [DecidableEq H] in

/-- The range matrix of an isometry is an orthogonal projector. -/
theorem rangeProjector_isOrthogonalProjector {V : Matrix H I ℂ}
    (hV : IsIsometry V) : IsOrthogonalProjector (rangeProjector V) := by
  have h : Vᴴ * V = 1 := hV
  constructor
  · change (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ
    calc
      (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * V) * Vᴴ := by simp only [Matrix.mul_assoc]
      _ = V * Vᴴ := by rw [h]; simp
  · change (V * Vᴴ)ᴴ = V * Vᴴ
    simp

omit [DecidableEq H] in

/-- The range projector of an isometry acts as the identity on that isometry. -/
theorem rangeProjector_mul {V : Matrix H I ℂ} (hV : IsIsometry V) :
    rangeProjector V * V = V := by
  have h : Vᴴ * V = 1 := hV
  simp [rangeProjector, Matrix.mul_assoc, h]

omit [Fintype I] [Fintype O] [DecidableEq H] [DecidableEq I] [DecidableEq O] in

/-- Taking the adjoint of a compression swaps its outer matrices and takes the adjoint of the
ambient operator. -/
theorem compress_adjoint (L : Matrix H O ℂ) (U : Matrix H H ℂ)
    (R : Matrix H I ℂ) : (compress L U R)ᴴ = compress R Uᴴ L := by
  simp [compress, Matrix.mul_assoc]

omit [Fintype I] [Fintype O] [DecidableEq H] [DecidableEq I] [DecidableEq O] in

/-- Compression is additive in the ambient operator. -/
theorem compress_add (L : Matrix H O ℂ) (U V : Matrix H H ℂ)
    (R : Matrix H I ℂ) : compress L (U + V) R = compress L U R + compress L V R := by
  simp [compress, Matrix.mul_add, Matrix.add_mul]

omit [Fintype I] [Fintype O] [DecidableEq H] [DecidableEq I] [DecidableEq O] in

/-- Compression commutes with complex scalar multiplication of the ambient operator. -/
theorem compress_smul (L : Matrix H O ℂ) (U : Matrix H H ℂ)
    (R : Matrix H I ℂ) (c : ℂ) : compress L (c • U) R = c • compress L U R := by
  simp [compress, Matrix.mul_smul, Matrix.smul_mul]

/-- The adjoint of a unitary matrix is unitary. -/
theorem adjoint_unitary {U : Matrix H H ℂ} (hU : U ∈ Matrix.unitaryGroup H ℂ) :
    Uᴴ ∈ Matrix.unitaryGroup H ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  simpa only [Matrix.star_eq_conjTranspose] using hU.2

omit [Fintype I] [Fintype O] in

/-- Taking adjoints of a projected unitary encoding yields an encoding of `Aᴴ` with the left and
right isometries exchanged. -/
theorem ProjectedUnitaryEncoding.adjoint {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ} (h : ProjectedUnitaryEncoding A U L R) :
    ProjectedUnitaryEncoding Aᴴ Uᴴ R L := by
  refine ⟨adjoint_unitary h.unitary, h.right_isometry, h.left_isometry, ?_⟩
  rw [← compress_adjoint, h.encoded]

end Qatlib.Concepts.Execution.WorkspaceCP
