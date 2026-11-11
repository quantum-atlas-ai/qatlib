/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowHam24.MainResults.Definitions
import Qatlib.Papers.ShadowHam24.MainResults.Lemma6Overlap

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 7 (arXiv:2407.21775, p. 19, Eqs. (51)–(52))

For an orthonormal operator basis `S`, a Hermitian `ρ` and arbitrary `σ`,
`tr(ρ U σ U^†) = ⟨ρ̃| Ũ |σ̃⟩`, where `Ũ = V_S (U ⊗ U) V_S^†` is the shadow-space
representation of the superoperator `σ ↦ U σ U^†`.

Vectorisation convention: `Matrix.vec` is column-major, so
`vec (U σ U^†) = (U* ⊗ₖ U) *ᵥ vec σ` with `U* = U.map star`
(`vec_mul_mul_conjTranspose`).  This differs from the paper's `U ⊗ U` only by the
basis relabelling of the two Kronecker factors induced by `vec` (paper Eq. (42));
`tildeOperator U O` is the corresponding shadow-space operator.  For pure states
`ρ = |ψ⟩⟨ψ|`, Eq. (52) specialises to
`|⟨ψ|U|ψ⟩|² = ⟨ρ;S| Ũ |ρ;S⟩`, which is the statement used for shadow
correlation functions.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace Qatlib.Papers.ShadowHam24.MainResults

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- The shadow amplitude of the updated state `U σ U^†` is `Ũ` applied to the
shadow amplitude of `σ` (paper Eq. (51)). -/
lemma shadowState_conj (U σ : Matrix N N ℂ) (O : N × N → Matrix N N ℂ)
    (horth : gramMatrix O = 1) :
    shadowState (U * σ * Uᴴ) O = tildeOperator U O *ᵥ shadowState σ O := by
  rw [shadowState_eq_shadowTransform_mulVec, vec_mul_mul_conjTranspose]
  have hvec : Matrix.vec σ = (shadowTransform O)ᴴ *ᵥ shadowState σ O := by
    rw [shadowState_eq_shadowTransform_mulVec, Matrix.mulVec_mulVec,
      shadowTransform_conjTranspose_mul_self O horth, Matrix.one_mulVec]
  rw [hvec, tildeOperator]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]

/-- **Lemma 7** (paper p. 19, Eq. (51)): for Hermitian `ρ` and an orthonormal
complete operator basis, `tr(ρ U σ U^†) = ⟨ρ̃| Ũ |σ̃⟩` with
`Ũ = V_S (U* ⊗ U) V_S^†`. -/
theorem correlation_eq_shadow (ρ σ U : Matrix N N ℂ)
    (O : N × N → Matrix N N ℂ) (hρ : ρ.IsHermitian)
    (horth : gramMatrix O = 1)
    (hcomplete : ∀ A : Matrix N N ℂ, A = ∑ ij, ((O ij)ᴴ * A).trace • O ij) :
    (ρ * (U * σ * Uᴴ)).trace
      = ∑ ij, star (shadowState ρ O ij) *
          (tildeOperator U O *ᵥ shadowState σ O) ij := by
  rw [trace_eq_shadow_inner ρ (U * σ * Uᴴ) O hρ horth hcomplete]
  apply Finset.sum_congr rfl
  intro ij _
  rw [shadowState_conj U σ O horth]

end Qatlib.Papers.ShadowHam24.MainResults
