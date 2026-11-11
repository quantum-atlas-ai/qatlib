/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowHam24.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 5 (arXiv:2407.21775, p. 17, Eqs. (42)–(43))

For an orthonormal operator basis `S` (so that the shadow transform `V_S` is
unitary after the natural `1/√λ` normalisation, encoded here as
`gramMatrix O = 1`), the shadow change-of-basis operator `V_S` is unitary, and
for a pure state `ρ = |ψ⟩⟨ψ|` the shadow state is obtained by applying `V_S` to
the vectorised Bell pair `|ψ⟩ ⊗ |ψ̄⟩`.

The vectorised Bell pair is `bellVector ψ (i,j) = ψ_j conj(ψ_i)`, i.e. the
column-major vectorisation of `|ψ⟩⟨ψ|`; see `vec_rankOne` in `Definitions`.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace Qatlib.Papers.ShadowHam24.MainResults

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- A square matrix is unitary if both `U^† U = 1` and `U U^† = 1`. -/
def IsUnitary (U : Matrix (N × N) (N × N) ℂ) : Prop :=
  Uᴴ * U = 1 ∧ U * Uᴴ = 1

/-- **Lemma 5, first part** (paper p. 17, Eq. (42)): if the operator family is
orthonormal (`gramMatrix O = 1`, the normalised form of
`tr(O_ij^† O_i'j') = λ δ`), then `V_S` is unitary. -/
theorem shadowTransform_isUnitary (O : N × N → Matrix N N ℂ)
    (horth : gramMatrix O = 1) : IsUnitary (shadowTransform O) :=
  ⟨shadowTransform_conjTranspose_mul_self O horth,
    by rw [shadowTransform_mul_conjTranspose, horth]⟩

/-- **Lemma 5, second part** (paper p. 17, Eq. (43)): for a pure state
`ρ = |ψ⟩⟨ψ|`, the shadow state equals `V_S` applied to the vectorised Bell
pair `|ψ⟩ ⊗ |ψ̄⟩`, and `V_S` is unitary. -/
theorem pure_shadow_eq_bell (ψ : N → ℂ) (O : N × N → Matrix N N ℂ)
    (horth : gramMatrix O = 1) :
    shadowState (rankOne ψ) O = shadowTransform O *ᵥ bellVector ψ ∧
      IsUnitary (shadowTransform O) :=
  ⟨pure_shadow_eq ψ O, shadowTransform_isUnitary O horth⟩

end Qatlib.Papers.ShadowHam24.MainResults
