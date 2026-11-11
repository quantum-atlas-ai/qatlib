/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMAPerfect26.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Lemma 3.6: the block encoding `U_{z,a,b}`

Fixed paper: Grewal–Rudolph, *QMA has perfect completeness*, arXiv:2609.13032v1, Lemma 3.6, p.9.

For every valid certificate, `U_{z,a,b}` satisfies
`(⟨0| ⊗ I) U_{z,a,b} (|η⟩ ⊗ I) = (a/M)(I − C_{z,a/b})`, and it has a polynomial-size circuit
over `𝓢₂` applying `V` and `V†` once each with return-to-`|0⟩` workspace.

The algebraic identity is modelled by `compressedBlock`, the ancilla-`|0⟩` compression of an
operator on `ancilla × clock × proof` against a returned ancilla state `|η⟩`. The norm
relation below is exactly what converts the identity into the rejection-probability estimate
used in the soundness analysis.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.QMAPerfect26.MainResults

/-- The compressed block `(⟨0| ⊗ I) U (|η⟩ ⊗ I)`, an operator on `clock × proof`: the
`⟨0|`-row of `U` contracted against the returned ancilla state `|η⟩`. The ancilla register is
`Fin (a+1)` so that the distinguished `|0⟩` state is available. -/
def compressedBlock {a n : ℕ}
    (U : Matrix (Fin (a + 1) × Fin n) (Fin (a + 1) × Fin n) ℝ) (η : Fin (a + 1) → ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ∑ b : Fin (a + 1), U (0, i) (b, j) * η b

/-- Lemma 3.6, algebraic content (p.9): if the block encoding satisfies
`(⟨0| ⊗ I) U_{z,a,b} (|η⟩ ⊗ I) = r • (I − C)` with `r = a/M`, then for every `|Ψ⟩`
the norm of the compressed block equals `|r| · ‖(I − C)|Ψ⟩‖`. -/
theorem lemma36 {a n : ℕ}
    (U : Matrix (Fin (a + 1) × Fin n) (Fin (a + 1) × Fin n) ℝ) (η : Fin (a + 1) → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (r : ℝ)
    (henc : compressedBlock U η = r • (1 - C)) :
    ∀ ψ : Fin n → ℝ, ‖compressedBlock U η *ᵥ ψ‖ = ‖r‖ * ‖(1 - C) *ᵥ ψ‖ := by
  intro ψ
  rw [henc, smul_mulVec, norm_smul]

/-- Lemma 3.6 with the certificate ratio `r = a/M` (p.9): the compression has norm
`(|a|/M) · ‖(I − C_{z,a/b})|Ψ⟩‖`. -/
theorem lemma36_ratio {a n : ℕ}
    (U : Matrix (Fin (a + 1) × Fin n) (Fin (a + 1) × Fin n) ℝ) (η : Fin (a + 1) → ℝ)
    (C : Matrix (Fin n) (Fin n) ℝ) (M : ℕ) (num : ℤ)
    (henc : compressedBlock U η = ((num : ℝ) / M) • (1 - C)) :
    ∀ ψ : Fin n → ℝ,
      ‖compressedBlock U η *ᵥ ψ‖ = (|(num : ℝ)| / M) * ‖(1 - C) *ᵥ ψ‖ := by
  intro ψ
  rw [lemma36 U η C _ henc ψ, Real.norm_eq_abs, abs_div]
  simp

end Qatlib.Papers.QMAPerfect26.MainResults
