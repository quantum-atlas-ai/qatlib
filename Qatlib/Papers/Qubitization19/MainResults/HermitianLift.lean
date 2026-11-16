/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.Qubitization19.MainResults.SourceQubitization
public import Mathlib.Data.Matrix.Block

@[expose] public section


open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding
open Qatlib.Papers.Qubitization19.MainResults

set_option autoImplicit false

namespace Qatlib.Papers.Qubitization19.MainResults

noncomputable section

variable {N J I : Type*} [Fintype N] [DecidableEq N]
  [Fintype J] [DecidableEq J] [Fintype I] [DecidableEq I]

/-- A rotated Hermitian dilation preserves the Hermitian part of a matrix in its first block. -/
def rotatedDilation (V : Matrix N N ℂ) : Matrix (N ⊕ N) (N ⊕ N) ℂ :=
  (1 / 2 : ℂ) • Matrix.fromBlocks (V + Vᴴ) (Vᴴ - V) (V - Vᴴ) (-(V + Vᴴ))

omit [Fintype N] [DecidableEq N] in
/-- A rotated dilation is self-adjoint. -/
theorem rotatedDilation_adjoint (V : Matrix N N ℂ) :
    (rotatedDilation V)ᴴ = rotatedDilation V := by
  simp [rotatedDilation, Matrix.conjTranspose_smul, Matrix.fromBlocks_conjTranspose,
    add_comm]

/-- A unitary matrix has a rotated Hermitian dilation that squares to the identity. -/
theorem rotatedDilation_square (V : Matrix N N ℂ)
    (hV : V ∈ Matrix.unitaryGroup N ℂ) :
    rotatedDilation V * rotatedDilation V = 1 := by
  have hv : V * Vᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hV)
  have hv' : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff'.mp hV)
  have hb : Matrix.fromBlocks (V + Vᴴ) (Vᴴ - V) (V - Vᴴ) (-(V + Vᴴ)) *
      Matrix.fromBlocks (V + Vᴴ) (Vᴴ - V) (V - Vᴴ) (-(V + Vᴴ)) =
      Matrix.fromBlocks (4 : Matrix N N ℂ) 0 0 (4 : Matrix N N ℂ) := by
    rw [Matrix.fromBlocks_multiply]
    congr 1 <;> noncomm_ring [hv, hv'] <;> norm_num [nsmul_eq_mul]
  unfold rotatedDilation
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hb]
  ext i j
  cases i <;> cases j <;>
    norm_num [Matrix.fromBlocks, Matrix.one_apply, Matrix.ofNat_apply]

/-- A unitary matrix has a unitary rotated Hermitian dilation. -/
theorem rotatedDilation_unitary (V : Matrix N N ℂ)
    (hV : V ∈ Matrix.unitaryGroup N ℂ) :
    rotatedDilation V ∈ Matrix.unitaryGroup (N ⊕ N) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose,
    rotatedDilation_adjoint]
  exact rotatedDilation_square V hV

/-- Every Hermitian signal has a one-flag self-adjoint unitary encoding satisfying Eq. 17. -/
theorem lemma10_existence_of_qubitization
    (V : Matrix (J × I) (J × I) ℂ) (j₀ : J) (A : Matrix I I ℂ)
    (hV : IsBlockEncoding V j₀ A 1) (hA : Aᴴ = A) :
    ∃ (j₀' : Bool × J) (V' : Matrix ((Bool × J) × I) ((Bool × J) × I) ℂ)
      (S : Matrix (Bool × J) (Bool × J) ℂ),
      V' ∈ Matrix.unitaryGroup ((Bool × J) × I) ℂ ∧
      S ∈ Matrix.unitaryGroup (Bool × J) ℂ ∧ S * S = 1 ∧ Sᴴ = S ∧
      QubitizationConditionsEq17 V' S j₀' A ∧
      BlockCorner V' j₀' = A ∧
      Fintype.card (Bool × J) = 2 * Fintype.card J := by
  let e : (J × I) ⊕ (J × I) ≃ (Bool × J) × I :=
    (Equiv.boolProdEquivSum (J × I)).symm.trans (Equiv.prodAssoc Bool J I).symm
  let V' : Matrix ((Bool × J) × I) ((Bool × J) × I) ℂ :=
    Matrix.reindex e e (rotatedDilation V)
  have hu : V' ∈ Matrix.unitaryGroup ((Bool × J) × I) ℂ :=
    unitaryGroup_reindex e (rotatedDilation_unitary V hV.1)
  have hs : V' * V' = 1 := by
    simpa [V', Matrix.reindex, Matrix.submatrix_mul_equiv] using
      congrArg (Matrix.reindex e e) (rotatedDilation_square V hV.1)
  have hc : BlockCorner V' (false, j₀) = A := by
    have hcorner : BlockCorner V j₀ = A := by simpa using hV.2.2
    have hcorner' : BlockCorner Vᴴ j₀ = A := by
      have hc' : BlockCorner Vᴴ j₀ = (BlockCorner V j₀)ᴴ := by
        ext i j
        rfl
      rw [hc', hcorner, hA]
    ext i j
    have h1 := congrFun (congrFun hcorner i) j
    have h2 := congrFun (congrFun hcorner' i) j
    simp only [blockCorner_apply] at h1 h2
    change (1 / 2 : ℂ) * (V (j₀, i) (j₀, j) + Vᴴ (j₀, i) (j₀, j)) = A i j
    rw [h1, h2]
    ring
  refine ⟨(false, j₀), V', 1, hu, Submonoid.one_mem _, one_mul _,
    Matrix.conjTranspose_one, ?_, hc, ?_⟩
  · simp only [QubitizationConditionsEq17, tensorGate_one, Matrix.one_mul]
    refine ⟨hc, ?_⟩
    rw [hs]
    ext i j
    simp [blockCorner_apply, Matrix.one_apply]
  · simp [Fintype.card_prod]

end
end Qatlib.Papers.Qubitization19.MainResults
