/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnitaryLearn09.MainResults.TensorPowerFidelity

set_option backward.isDefEq.respectTransparency false

/-!
# UnitaryLearn09 — vectorization, parallel storage and the identity block

Fixed source: Bisio–Chiribella–D'Ariano–Facchini–Perinotti,
*Optimal quantum learning of a unitary transformation*, arXiv:0903.0543v2
(PDF SHA-256 7740f8bf94c88b19a046c4c627cda8edf148bf92fe178c381fd20bceede57048),
Section II Eq. (2) and the proofs of Lemma 1 and Lemma 2 (Sec. III A).

The paper's Eq. (2) is the vectorized identity
`(A ⊗ I)|B⟩⟩ = (I ⊗ Aᵀ)|B⟩⟩` for commuting `A` and `B`.  It drives both storage
lemmas: the storing board of Lemma 1 can be replaced by the parallel map
`U_o^{⊗N} ⊗ I_i^{⊗N}` on a suitable `|φ⟩ ∈ H_o ⊗ H_i`, and in Lemma 2 the
optimal input state `⊕_j √(p_j/d_j)|I_j⟩⟩` is stored as `⊕_j √(p_j/d_j)|U_j⟩⟩`.

Mathlib's `Matrix.vec` stacks columns, i.e. it is the paper's `|A⟩⟩` with the
two tensor factors exchanged; under that convention the identity above becomes
`(A ⊗ 1)·vec B = vec(B Aᵀ)` and `(1 ⊗ Aᵀ)·vec B = vec(Aᵀ B)`.  This file
records those two halves, the commuting form, the storage of the identity block
`(A ⊗ 1)·vec 1 = vec Aᵀ`, and the invariance of the maximally entangled vector
under `Ū ⊗ U`, which is the fixed-point statement behind Lemma 2's ansatz.

The Choi/comb normalization of Eq. (6) and the Schur decomposition of
`U^{⊗N}` into irreducible representations — needed for the full proofs of
Lemmas 1 and 2 — are not formalized here.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Papers.UnitaryLearn09.MainResults

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- Paper Eq. (2), first half: applying `A` to the left tensor factor of the
vectorized `B` multiplies `B` on the right by `Aᵀ`. -/
theorem parallelStorage_vec (A B : Matrix I I ℂ) :
    (A ⊗ₖ 1) *ᵥ Matrix.vec B = Matrix.vec (B * Aᵀ) := by
  simpa using Matrix.kronecker_mulVec_vec (1 : Matrix I I ℂ) B A

/-- Paper Eq. (2), second half: applying `Aᵀ` to the right tensor factor
multiplies on the left. -/
theorem parallelStorage_vec_left (A B : Matrix I I ℂ) :
    (1 ⊗ₖ Aᵀ) *ᵥ Matrix.vec B = Matrix.vec (Aᵀ * B) := by
  simpa using Matrix.kronecker_mulVec_vec Aᵀ B (1 : Matrix I I ℂ)

/-- Paper Eq. (2): for commuting `A` and `B` the two tensor placements of
`A` give the same vectorized action. -/
theorem parallelStorage_vec_commuting (A B : Matrix I I ℂ)
    (h : B * Aᵀ = Aᵀ * B) :
    (A ⊗ₖ 1) *ᵥ Matrix.vec B = (1 ⊗ₖ Aᵀ) *ᵥ Matrix.vec B := by
  rw [parallelStorage_vec, parallelStorage_vec_left, h]

/-- Lemma 2, storage step: the identity block `|I⟩⟩` is stored as the Choi
vector `|Aᵀ⟩⟩` of the applied matrix. -/
theorem parallelStorage_identity (A : Matrix I I ℂ) :
    (A ⊗ₖ 1) *ᵥ Matrix.vec (1 : Matrix I I ℂ) = Matrix.vec Aᵀ := by
  rw [parallelStorage_vec, Matrix.one_mul]

/-- Lemma 2, invariance step: the maximally entangled vector `|I⟩⟩` is fixed
by `Ū ⊗ U = (Uᴴ)ᵀ ⊗ U` for a unitary `U`.  This is the fixed-point identity
used to restrict to the subspace `H̃ = ⊕_j (H_j ⊗ H_j)`. -/
theorem entangledInvariant {U : Matrix I I ℂ} (hU : U * Uᴴ = 1) :
    ((Uᴴ)ᵀ ⊗ₖ U) *ᵥ Matrix.vec (1 : Matrix I I ℂ) =
      Matrix.vec (1 : Matrix I I ℂ) := by
  rw [Matrix.kronecker_mulVec_vec U (1 : Matrix I I ℂ) ((Uᴴ)ᵀ)]
  simp [hU]

/-- Lemma 1/Lemma 2 at `N` examples: the `N`-fold parallel storing board acts
on the identity block as the Choi vector of `U^{⊗N}`. -/
theorem parallelStorage_kronPow {d N : ℕ} (U : Matrix (Fin d) (Fin d) ℂ) :
    (kronPow d N U ⊗ₖ 1) *ᵥ
        Matrix.vec (1 : Matrix (kronIdx d N) (kronIdx d N) ℂ) =
      Matrix.vec (kronPow d N U)ᵀ :=
  parallelStorage_identity (kronPow d N U)


/-- Lemma 2, block storage: a single scaled identity block `√p · |I⟩⟩` is
stored as the scaled Choi vector `√p · |Aᵀ⟩⟩` of the applied matrix, which is
the blockwise form of the paper's `⊕_j √(p_j/d_j)|U_j⟩⟩`. -/
theorem lemma2_block_storage (A : Matrix I I ℂ) (p : ℝ) :
    (A ⊗ₖ 1) *ᵥ ((Real.sqrt p : ℝ) • Matrix.vec (1 : Matrix I I ℂ)) =
      (Real.sqrt p : ℝ) • Matrix.vec Aᵀ := by
  rw [Matrix.mulVec_smul, parallelStorage_identity]

end Qatlib.Papers.UnitaryLearn09.MainResults
