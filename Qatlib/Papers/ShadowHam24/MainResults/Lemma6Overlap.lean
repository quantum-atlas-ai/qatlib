/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ShadowHam24.MainResults.Definitions

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 6 (arXiv:2407.21775, pp. 18–19, Eq. (47))

For an orthonormal operator basis `S` and Hermitian density matrices `ρ`, `σ`,
the Hilbert–Schmidt inner product of the states equals the inner product of
their shadow states: `tr(ρ σ) = ⟨ρ̃|σ̃⟩`, where `ρ̃_m = tr(ρ O_m)` are the
(unnormalised) shadow amplitudes.

The paper's Eq. (47) is stated for both `ρ` and `σ` Hermitian.  In the proof we
expand `ρ` in the operator basis, so only Hermiticity of `ρ` is needed for the
identity as stated below (with the conjugate on the first slot of the inner
product); we therefore assume `hρ` only and allow an arbitrary matrix `σ`,
which is a harmless generalisation.

Completeness of the orthonormal basis is passed explicitly as `hcomplete`,
`∀ A, A = ∑_ij tr(O_ij^† A) • O_ij`; orthonormality is `gramMatrix O = 1`.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators Matrix.Norms.Frobenius

namespace Qatlib.Papers.ShadowHam24.MainResults

variable {N : Type*} [Fintype N] [DecidableEq N]

/-- **Lemma 6** (paper pp. 18–19, Eq. (47)): `tr(ρ σ)` equals the shadow-space
inner product `∑_m conj⟨O_m⟩_ρ ⟨O_m⟩_σ` for Hermitian `ρ` and an orthonormal
complete operator basis. -/
theorem trace_eq_shadow_inner (ρ σ : Matrix N N ℂ) (O : N × N → Matrix N N ℂ)
    (hρ : ρ.IsHermitian)
    (horth : gramMatrix O = 1)
    (hcomplete : ∀ A : Matrix N N ℂ, A = ∑ ij, ((O ij)ᴴ * A).trace • O ij) :
    (ρ * σ).trace
      = ∑ ij, star (shadowState ρ O ij) * shadowState σ O ij := by
  conv_lhs => rw [hcomplete ρ]
  rw [Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [Matrix.smul_mul, Matrix.trace_smul,
    trace_conjTranspose_mul_eq_star ρ (O ij) hρ, Matrix.trace_mul_comm (O ij) σ]
  simp [shadowState, expectation]

end Qatlib.Papers.ShadowHam24.MainResults
