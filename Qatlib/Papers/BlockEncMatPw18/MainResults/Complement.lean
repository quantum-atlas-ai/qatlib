/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.BlockEncoding.EncodingCore.CoordinateFiber
public import Qatlib.Concepts.CoherentSim.CoherentOAA.BlockRobustness
public import Qatlib.Foundations.MatrixGeometry.BranchUnitary.Defs
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-!
# Complementing block-encoded matrices

Lemma 6 of arXiv:1804.01973v2 uses the new control bit as part of the
Hermitian dilation's data register. The same old ancilla value is fixed
in both control sectors.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.MatrixGeometry.BranchUnitary

namespace Qatlib.Papers.BlockEncMatPw18.MainResults

variable {S J I : Type*}

/-- The two control sectors of the controlled unitary, ordered zero then one. -/
def complementControl [DecidableEq S] (U : Matrix S S ℂ) : Matrix (S ⊕ S) (S ⊕ S) ℂ :=
  Matrix.fromBlocks 1 0 0 U

/-- The Pauli-X gate on the new bit exchanges the two system sectors. -/
def complementFlip [DecidableEq S] : Matrix (S ⊕ S) (S ⊕ S) ℂ :=
  Matrix.fromBlocks 0 1 1 0

/-- The source circuit is controlled-U, then a bit flip, then controlled-U adjoint. -/
def complementCircuit [Fintype S] [DecidableEq S] (U : Matrix S S ℂ) :
    Matrix (S ⊕ S) (S ⊕ S) ℂ :=
  (complementControl U)ᴴ * complementFlip * complementControl U

/-- Evaluating the three-gate matrix product gives the Hermitian dilation. -/
theorem complementCircuit_eq_dilation [Fintype S] [DecidableEq S] (U : Matrix S S ℂ) :
    complementCircuit U = hermitianDilation U := by
  simp [complementCircuit, complementControl, complementFlip, hermitianDilation,
    Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]

/-- In product coordinates the source circuit is the branch-controlled operation
conjugating the Pauli-X on the Boolean register. -/
theorem complementCircuit_product [Fintype S] [DecidableEq S] (U : Matrix S S ℂ) :
    let e := (Equiv.prodComm S Bool).trans (Equiv.boolProdEquivSum S)
    let cU := controlled (fun b : Bool => if b then U else 1)
    let X : Matrix (S × Bool) (S × Bool) ℂ :=
      fun p q => if p.1 = q.1 ∧ p.2 ≠ q.2 then 1 else 0
    (complementCircuit U).submatrix e e = cUᴴ * X * cU := by
  dsimp only
  let e := (Equiv.prodComm S Bool).trans (Equiv.boolProdEquivSum S)
  let cU := controlled (fun b : Bool => if b then U else 1)
  let X : Matrix (S × Bool) (S × Bool) ℂ :=
    fun p q => if p.1 = q.1 ∧ p.2 ≠ q.2 then 1 else 0
  change (complementCircuit U).submatrix e e = cUᴴ * X * cU
  have hc : (complementControl U).submatrix e e = cU := by
    ext ⟨s, b⟩ ⟨t, c⟩
    cases b <;> cases c <;>
      simp [e, Equiv.boolProdEquivSum, cU, complementControl, controlled,
        Matrix.blockDiagonal_apply]
  have hx : (complementFlip (S := S)).submatrix e e = X := by
    ext ⟨s, b⟩ ⟨t, c⟩
    cases b <;> cases c <;> simp [e, Equiv.boolProdEquivSum, complementFlip, X, Matrix.one_apply]
  unfold complementCircuit
  rw [← Matrix.submatrix_mul_equiv _ _ _ e, ← Matrix.submatrix_mul_equiv _ _ _ e,
    ← Matrix.conjTranspose_submatrix, hc, hx]

/-- Fix the old ancilla coordinate on both data sectors of the dilation. -/
def complementFiber [DecidableEq J] [DecidableEq I] (j₀ : J) :
    Matrix ((J × I) ⊕ (J × I)) (I ⊕ I) ℂ :=
  Matrix.fromBlocks (encodingFiber j₀) 0 0 (encodingFiber j₀)

/-- The doubled coordinate frame is an isometry. -/
theorem complementFiber_isIsometry [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I] (j₀ : J) :
    IsIsometry (complementFiber (I := I) j₀) := by
  have hl : (encodingFiber (I := I) j₀)ᴴ * encodingFiber (I := I) j₀ = 1 :=
    by simpa only [IsIsometry] using encodingFiber_isIsometry (I := I) j₀
  simp [IsIsometry, complementFiber, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, hl]

/-- Compression in the doubled frame gives exactly the dilation of the old compressed block. -/
theorem compress_complementCircuit [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (j₀ : J) (U : Matrix (J × I) (J × I) ℂ) :
    compress (complementFiber j₀) (complementCircuit U) (complementFiber j₀) =
      hermitianDilation (compress (encodingFiber j₀) U (encodingFiber j₀)) := by
  rw [complementCircuit_eq_dilation]
  simp [compress, complementFiber, hermitianDilation, Matrix.fromBlocks_conjTranspose,
    Matrix.fromBlocks_multiply, Matrix.conjTranspose_mul, Matrix.mul_assoc]

/-- The dilation is compatible with multiplication by a real scale. -/
private theorem hermitianDilation_real_smul (α : ℝ) (A : Matrix I I ℂ) :
    hermitianDilation (α • A) = α • hermitianDilation A := by
  simp [hermitianDilation, Matrix.conjTranspose_smul, Matrix.fromBlocks_smul]

/-- Lemma 6. The source circuit is a block encoding of the Hermitian dilation
with the original scale and error, using one more system qubit. -/
theorem lemma6_complement_block_encoding [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]
    (j₀ : J) (A : Matrix I I ℂ) (U : Matrix (J × I) (J × I) ℂ) (α δ : ℝ)
    (hU : BlockEncoding A U (encodingFiber j₀) (encodingFiber j₀) α δ) :
    BlockEncoding (hermitianDilation A) (complementCircuit U)
      (complementFiber j₀) (complementFiber j₀) α δ := by
  refine ⟨?_, complementFiber_isIsometry (I := I) j₀, complementFiber_isIsometry (I := I) j₀,
    hU.normalization_pos, hU.error_nonneg, ?_⟩
  · rw [complementCircuit_eq_dilation]
    apply Matrix.mem_unitaryGroup_iff'.2
    have hleft := Matrix.mem_unitaryGroup_iff'.1 hU.unitary
    have hright := Matrix.mem_unitaryGroup_iff.1 hU.unitary
    rw [Matrix.star_eq_conjTranspose] at hleft hright ⊢
    rw [hermitianDilation_adjoint]
    simp [hermitianDilation, Matrix.fromBlocks_multiply, hleft, hright]
  · rw [compress_complementCircuit, ← hermitianDilation_real_smul,
      hermitianDilation_sub_norm]
    exact hU.error_le

/-- The sector bit doubles the data dimension and leaves the ancilla dimension unchanged. -/
theorem complementRegister_card [Fintype J] [Fintype I] (a s : ℕ)
    (hJ : Fintype.card J = 2 ^ a) (hI : Fintype.card I = 2 ^ s) :
    Fintype.card ((J × I) ⊕ (J × I)) = 2 ^ (a + (s + 1)) ∧
      Fintype.card (I ⊕ I) = 2 ^ (s + 1) := by
  simp [Fintype.card_sum, Fintype.card_prod, hJ, hI, pow_add, Nat.mul_add, Nat.mul_two]

end Qatlib.Papers.BlockEncMatPw18.MainResults
