/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GrpJuntaTest15.MainResults.SourceModel
public import Mathlib.Data.Matrix.Block

@[expose] public section

/-!
# The block oracle in Definition 5.1

The source oracle in arXiv:1507.03126v1 is the direct sum of its
workspace actions. Reindexing the library's block-diagonal matrix
matches the source's input-register-first convention.
-/

set_option autoImplicit false

open Matrix
open scoped Matrix
open Qatlib.Papers.GrpJuntaTest15.MainResults.SourceModel

namespace Qatlib.Papers.GrpJuntaTest15.MainResults

variable {ι W : Type} [DecidableEq ι]

/-- Swapping register order identifies the source oracle with a block
diagonal matrix in Mathlib. -/
private theorem blockOracle_eq_submatrix (O : ι → Matrix W W ℂ) :
    blockOracle O = (blockDiagonal O).submatrix (Equiv.prodComm ι W) (Equiv.prodComm ι W) := by
  ext ⟨i, x⟩ ⟨j, y⟩
  rfl

/-- The direct sum in Definition 5.1 preserves the workspace unitary
identity `Oᴴ O = 1`. -/
theorem blockOracle_unitary [Fintype ι] [Fintype W] [DecidableEq W]
    (O : ι → Matrix W W ℂ) (hO : ∀ i, (O i)ᴴ * O i = 1) :
    (blockOracle O)ᴴ * blockOracle O = 1 := by
  rw [blockOracle_eq_submatrix, conjTranspose_submatrix,
    submatrix_mul_equiv _ _ _ (Equiv.prodComm ι W), blockDiagonal_conjTranspose,
    ← blockDiagonal_mul]
  simp_rw [hO]
  rw [← Pi.one_def, blockDiagonal_one, submatrix_one_equiv]

/-- The assembled oracle is an allowed unitary for the source query
circuit whenever each workspace action is unitary. -/
theorem blockOracle_mem_unitaryGroup [Fintype ι] [Fintype W] [DecidableEq W]
    (O : ι → Matrix W W ℂ) (hO : ∀ i, O i ∈ Matrix.unitaryGroup W ℂ) :
    blockOracle O ∈ Matrix.unitaryGroup (ι × W) ℂ :=
  Matrix.mem_unitaryGroup_iff'.mpr (blockOracle_unitary O
    (fun i => Matrix.mem_unitaryGroup_iff'.mp (hO i)))

/-- Block assembly preserves self-adjointness when the workspace
actions have already been made self-adjoint. -/
theorem blockOracle_selfAdjoint (O : ι → Matrix W W ℂ) (hO : ∀ i, (O i)ᴴ = O i) :
    (blockOracle O)ᴴ = blockOracle O := by
  rw [blockOracle_eq_submatrix, conjTranspose_submatrix, blockDiagonal_conjTranspose]
  simp_rw [hO]

end Qatlib.Papers.GrpJuntaTest15.MainResults
