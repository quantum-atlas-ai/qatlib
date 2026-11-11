/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.PauliPath

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Lemma 12 (single-qubit gate-set orthogonality)

Fixed arXiv:2211.03999v1, Lemma 12, p.20, Eq. (52).

The paper considers the effective single-qubit gate set `RZ(θ₁) V RZ(θ₂)` with
`V ∈ {√X, √Y, √W}` and verifies that it is invariant under right multiplication by a
uniformly random single-qubit Pauli.  Lemma 12 is then the single-qubit instance of the
gate-set orthogonality phenomenon of Lemma 2:

  `E_{U∼D}[U P U† ⊗ U Q U†] = 0` for distinct single-qubit Paulis `P ≠ Q`.

We prove the implication from right-Pauli-invariance to Eq. (52) unconditionally, using
the explicit Pauli matrices and the character orthogonality `Pauli1.char_sum_zero`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.GateSets

open Matrix BigOperators
open scoped Kronecker
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

/-- A single-qubit gate expectation: a complex-linear functional on matrix-valued
functions of `U ∈ U(2)` (an expectation is linear). -/
abbrev CircuitExpectation1 :=
  (Matrix (Fin 2) (Fin 2) ℂ →
      Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) →ₗ[ℂ]
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ

/-- Right-invariance of a single-qubit gate distribution under a uniformly random Pauli,
the single-qubit analogue of Eq. (17). -/
def RightPauliInvariant1 (E : CircuitExpectation1) : Prop :=
  ∀ G : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
    E G = E (fun U => (4 : ℂ)⁻¹ • ∑ V : Pauli1, G (U * V.mat))

/-- Fixed arXiv:2211.03999v1, Lemma 12, p.20, Eq. (52):
if a single-qubit gate distribution is invariant under right multiplication by a uniformly
random Pauli, then for distinct single-qubit Paulis `P ≠ Q`,
`E[U P U† ⊗ U Q U†] = 0`. -/
theorem source_lemma12_single_qubit_orthogonality
    (E : CircuitExpectation1) (hE : RightPauliInvariant1 E)
    (P Q : Pauli1) (hPQ : P ≠ Q) :
    E (fun U => (U * P.mat * Uᴴ) ⊗ₖ (U * Q.mat * Uᴴ)) = 0 := by
  rw [hE]
  have hterm : ∀ (V : Pauli1) (U : Matrix (Fin 2) (Fin 2) ℂ),
      (U * V.mat * P.mat * (U * V.mat)ᴴ) ⊗ₖ (U * V.mat * Q.mat * (U * V.mat)ᴴ) =
        (Pauli1.conjSign V P * Pauli1.conjSign V Q) •
          ((U * P.mat * Uᴴ) ⊗ₖ (U * Q.mat * Uᴴ)) := by
    intro V U
    have hpullP : U * V.mat * P.mat * (U * V.mat)ᴴ =
        U * (V.mat * P.mat * (V.mat)ᴴ) * Uᴴ := by
      rw [conjTranspose_mul]
      simp only [mul_assoc]
    have hpullQ : U * V.mat * Q.mat * (U * V.mat)ᴴ =
        U * (V.mat * Q.mat * (V.mat)ᴴ) * Uᴴ := by
      rw [conjTranspose_mul]
      simp only [mul_assoc]
    rw [hpullP, hpullQ]
    have hconj : ∀ (R : Pauli1),
        U * (V.mat * R.mat * (V.mat)ᴴ) * Uᴴ =
          Pauli1.conjSign V R • (U * R.mat * Uᴴ) := by
      intro R
      rw [Pauli1.mat_conj, mul_smul_comm, smul_mul_assoc]
    rw [hconj P, hconj Q, smul_kronecker, kronecker_smul, smul_smul]
  have hzero : ∀ U : Matrix (Fin 2) (Fin 2) ℂ,
      (4 : ℂ)⁻¹ • ∑ V : Pauli1,
        (U * V.mat * P.mat * (U * V.mat)ᴴ) ⊗ₖ (U * V.mat * Q.mat * (U * V.mat)ᴴ) = 0 := by
    intro U
    simp_rw [hterm]
    rw [← Finset.sum_smul]
    rw [show (∑ V : Pauli1,
        (Pauli1.conjSign V P * Pauli1.conjSign V Q)) = 0 from
      Pauli1.char_sum_zero P Q hPQ]
    simp
  simp_rw [hzero]
  exact map_zero E

end Qatlib.Papers.NoisyCircuit22.MainResults.GateSets
