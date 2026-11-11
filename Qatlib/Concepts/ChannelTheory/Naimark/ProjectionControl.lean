/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic

/-!
# Projector corners from controlled reflections

`program` conjugates a controlled reflection by a balanced Hadamard matrix. Its diagonal blocks
are `P` and its off-diagonal blocks are `1 - P`; it is unitary for an orthogonal projector `P`.
The specialization `removeZero` realizes deletion of one coordinate in the successful block.

The mathematical background is described in [NielsenChuang2010].

## Main statements

* `program_blocks`: the explicit four-block program matrix.
* `program_unitary`: unitarity for Hermitian idempotent `P`.
* `program_removeZero_action`: coordinate removal in the successful output block.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
noncomputable section
open Matrix
open scoped Classical ComplexOrder Matrix.Norms.L2Operator

namespace Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The real complex amplitude `1 / sqrt 2` used in the balanced Hadamard matrix. -/
def amplitude : ℂ := (Real.sqrt 2 : ℂ)⁻¹

/-- The balanced Hadamard amplitude is fixed by complex conjugation. -/
theorem amplitude_star : star amplitude=amplitude := by simp [amplitude]

/-- The square of the balanced Hadamard amplitude is one half. -/
theorem amplitude_square : amplitude*amplitude=(1/2:ℂ) := by
  have hs : (Real.sqrt 2 : ℂ)^2=2 := by exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
  unfold amplitude
  rw [← mul_inv,← pow_two,hs]
  norm_num

/-- The Hadamard block matrix on two copies of the system, with identity blocks scaled by `1 /
sqrt 2` and a negative lower-right block. -/
def balancedHadamard (I : Type) [DecidableEq I] : Matrix (I⊕I) (I⊕I) ℂ :=
  fromBlocks (amplitude•1) (amplitude•1) (amplitude•1) ((-amplitude)•1)

omit [Fintype I] in

/-- The balanced Hadamard block matrix is Hermitian. -/
theorem balancedHadamard_star : (balancedHadamard I)ᴴ=balancedHadamard I := by
  simp [balancedHadamard,Matrix.fromBlocks_conjTranspose,amplitude_star]

/-- The balanced Hadamard block matrix squares to the identity. -/
theorem balancedHadamard_square : balancedHadamard I*balancedHadamard I=1 := by
  norm_num [balancedHadamard,Matrix.fromBlocks_multiply,smul_smul,mul_neg,amplitude_square,← add_smul]

/-- The balanced Hadamard block matrix is unitary. -/
theorem balancedHadamard_unitary : balancedHadamard I∈Matrix.unitaryGroup (I⊕I) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,balancedHadamard_star]
  exact balancedHadamard_square

/-- The matrix `2P - 1` associated with `P`. -/
def reflection (P : Matrix I I ℂ) : Matrix I I ℂ := (2:ℂ)•P-1

/-- The block diagonal matrix acting as the identity on the first summand and `reflection P` on
the second. -/
def controlledReflection (P : Matrix I I ℂ) : Matrix (I⊕I) (I⊕I) ℂ :=
    fromBlocks 1 0 0 (reflection P)

/-- The product of a balanced Hadamard, a controlled reflection, and a balanced Hadamard. -/
def program (P : Matrix I I ℂ) : Matrix (I⊕I) (I⊕I) ℂ :=
  balancedHadamard I*controlledReflection P*balancedHadamard I

/-- The controlled-reflection program has diagonal blocks `P` and off-diagonal blocks `1 - P`. -/
theorem program_blocks (P : Matrix I I ℂ) : program P=fromBlocks P (1-P) (1-P) P := by
  simp only [program,balancedHadamard,controlledReflection,Matrix.fromBlocks_multiply,
    mul_zero,add_zero,zero_add,Matrix.smul_mul,Matrix.mul_smul,Matrix.one_mul,
    Matrix.mul_one,smul_smul,neg_mul,mul_neg,neg_neg,amplitude_square]
  congr 1 <;> simp only [reflection,smul_sub,smul_smul] <;> module

/-- The matrix `2P - 1` is unitary when `P` is Hermitian and idempotent. -/
theorem reflection_unitary (P : Matrix I I ℂ) (hstar : Pᴴ=P) (hid : P*P=P) :
    reflection P∈Matrix.unitaryGroup I ℂ := by
  have hs : (reflection P)ᴴ=reflection P := by simp [reflection,hstar]
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose,hs]
  simp only [reflection,Matrix.sub_mul,Matrix.mul_sub,Matrix.smul_mul,Matrix.mul_smul,
    Matrix.one_mul,Matrix.mul_one,hid]
  module

/-- The controlled reflection is unitary when `P` is Hermitian and idempotent. -/
theorem controlledReflection_unitary (P : Matrix I I ℂ) (hstar : Pᴴ=P) (hid : P*P=P) :
    controlledReflection P∈Matrix.unitaryGroup (I⊕I) ℂ := by
  have h : (reflection P)ᴴ*reflection P=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff'.mp (reflection_unitary P hstar hid)
  rw [Matrix.mem_unitaryGroup_iff',Matrix.star_eq_conjTranspose]
  simp [controlledReflection,Matrix.fromBlocks_conjTranspose,Matrix.fromBlocks_multiply,h]

/-- The Hadamard-controlled-reflection program is unitary when `P` is Hermitian and idempotent. -/
theorem program_unitary (P : Matrix I I ℂ) (hstar : Pᴴ=P) (hid : P*P=P) :
    program P∈Matrix.unitaryGroup (I⊕I) ℂ :=
  mul_mem (mul_mem balancedHadamard_unitary (controlledReflection_unitary P hstar hid)) balancedHadamard_unitary

/-- The upper-left corner of the controlled-reflection program equals `P`. -/
theorem program_success_corner (P : Matrix I I ℂ) (i j : I) : program P (Sum.inl i) (Sum.inl j)=P i j := by
  rw [program_blocks]
  rfl

/-- The diagonal matrix setting coordinate `zero` to zero and retaining every other coordinate. -/
def removeZero (zero : I) : Matrix I I ℂ := diagonal (fun i => if i=zero then 0 else 1)

omit [Fintype I] in

/-- The coordinate-removal matrix is Hermitian. -/
theorem removeZero_star (zero : I) : (removeZero zero)ᴴ=removeZero zero := by
  simp [removeZero,Matrix.diagonal_conjTranspose]

/-- The coordinate-removal matrix is idempotent. -/
theorem removeZero_square (zero : I) : removeZero zero*removeZero zero=removeZero zero := by
  rw [removeZero,Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  split_ifs <;> simp

/-- The controlled-reflection program for coordinate removal is unitary. -/
theorem removeZero_program_unitary (zero : I) : program (removeZero zero)∈Matrix.unitaryGroup (I⊕I) ℂ :=
  program_unitary _ (removeZero_star zero) (removeZero_square zero)

/-- On input supported in the first summand, the successful block of the coordinate-removal
program sets coordinate `zero` to zero and retains all other amplitudes. -/
theorem program_removeZero_action (zero : I) (x : I→ℂ) (i : I) :
    (program (removeZero zero)*ᵥSum.elim x 0) (Sum.inl i)=if i=zero then 0 else x i := by
  rw [program_blocks,Matrix.fromBlocks_mulVec]
  simp [removeZero,Matrix.mulVec_diagonal]

end Qatlib.Concepts.ChannelTheory.Naimark.ProjectionControl
