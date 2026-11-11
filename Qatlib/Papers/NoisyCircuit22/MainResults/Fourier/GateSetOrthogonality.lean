/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel.PauliPath

set_option backward.isDefEq.respectTransparency false

/-!
# NoisyCircuit22 — Lemma 2 (gate-set orthogonality)

Fixed arXiv:2211.03999v1, Lemma 2, p.9, Eqs. (17)--(18).

The paper shows that a gate distribution invariant under right multiplication by a
uniformly random two-qubit Pauli forces the two-copy expectation
`E[U P U† ⊗ U Q U†]` to vanish for distinct two-qubit Paulis `P ≠ Q`.  The only
mathematical input is the finite average over the 16-element Pauli group, Eq. (20).

Formalisation: we keep the expectation as an abstract complex-linear functional on
matrix-valued functions of `U` (an expectation is linear), and state the invariance
hypothesis (17) literally as `E G = E (fun U => (1/16) • ∑_V G (U V))`.  The finite
Pauli identity is proved unconditionally from the explicit `2 × 2` Pauli matrices.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NoisyCircuit22.MainResults.Fourier

open Matrix BigOperators
open scoped Kronecker
open Qatlib.Papers.NoisyCircuit22.MainResults.SourceModel

/-- The two-qubit Pauli matrix `V₁ ⊗ V₂` (unnormalized) on `(Fin 2 × Fin 2)`. -/
def twoQubitMat (P : Pauli1 × Pauli1) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ((P.1.mat : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ (P.2.mat : Matrix (Fin 2) (Fin 2) ℂ))

/-- Conjugation of a two-qubit Pauli by a two-qubit Pauli is scalar: the product of the
two single-qubit conjugation signs, Eq. (20), p.9. -/
theorem twoQubitMat_conj (V P : Pauli1 × Pauli1) :
    twoQubitMat V * twoQubitMat P * (twoQubitMat V)ᴴ =
      (Pauli1.conjSign V.1 P.1 * Pauli1.conjSign V.2 P.2) • twoQubitMat P := by
  unfold twoQubitMat
  rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
  rw [Pauli1.mat_conj, Pauli1.mat_conj, smul_kronecker, kronecker_smul, smul_smul]

/-- The finite Pauli average of Eq. (20): for distinct two-qubit Paulis `P ≠ Q`,
`∑_V (V P V†) ⊗ (V Q V†) = 0`. -/
theorem pauli_average_kron_zero (P Q : Pauli1 × Pauli1) (hPQ : P ≠ Q) :
    (∑ V : Pauli1 × Pauli1,
        (twoQubitMat V * twoQubitMat P * (twoQubitMat V)ᴴ) ⊗ₖ
        (twoQubitMat V * twoQubitMat Q * (twoQubitMat V)ᴴ)) = 0 := by
  have hterm : ∀ V : Pauli1 × Pauli1,
      (twoQubitMat V * twoQubitMat P * (twoQubitMat V)ᴴ) ⊗ₖ
        (twoQubitMat V * twoQubitMat Q * (twoQubitMat V)ᴴ) =
      ((Pauli1.conjSign V.1 P.1 * Pauli1.conjSign V.1 Q.1) *
        (Pauli1.conjSign V.2 P.2 * Pauli1.conjSign V.2 Q.2)) •
        (twoQubitMat P ⊗ₖ twoQubitMat Q) := by
    intro V
    rw [twoQubitMat_conj, twoQubitMat_conj, smul_kronecker, kronecker_smul, smul_smul]
    try ring_nf
  simp_rw [hterm]
  rw [← Finset.sum_smul]
  have hcoef : (∑ V : Pauli1 × Pauli1,
      (Pauli1.conjSign V.1 P.1 * Pauli1.conjSign V.1 Q.1) *
        (Pauli1.conjSign V.2 P.2 * Pauli1.conjSign V.2 Q.2)) = 0 := by
    rw [Fintype.sum_prod_type]
    have hfac : (∑ v1 : Pauli1, ∑ v2 : Pauli1,
        (Pauli1.conjSign v1 P.1 * Pauli1.conjSign v1 Q.1) *
          (Pauli1.conjSign v2 P.2 * Pauli1.conjSign v2 Q.2)) =
        (∑ v1 : Pauli1, Pauli1.conjSign v1 P.1 * Pauli1.conjSign v1 Q.1) *
          (∑ v2 : Pauli1, Pauli1.conjSign v2 P.2 * Pauli1.conjSign v2 Q.2) := by
      simp_rw [← Finset.mul_sum]
      rw [← Finset.sum_mul]
    rw [hfac]
    by_cases h1 : P.1 = Q.1
    · have h2 : P.2 ≠ Q.2 := by
        intro h2
        exact hPQ (Prod.ext h1 h2)
      rw [Pauli1.char_sum_zero P.2 Q.2 h2, mul_zero]
    · rw [Pauli1.char_sum_zero P.1 Q.1 h1, zero_mul]
  rw [hcoef, zero_smul]

/-- A gate distribution's expectation functional: a complex-linear functional on
matrix-valued functions of the running unitary `U ∈ U(4)` (represented on
`Fin 2 × Fin 2`). -/
abbrev CircuitExpectation :=
  (Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
      Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ) →ₗ[ℂ]
    Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ

/-- Right-invariance under a uniformly random two-qubit Pauli, Eq. (17), p.9:
for every measurable matrix-valued `F`,
`E[F(U)] = E_{(U,V)}[F(U V)]`, written with the finite uniform average over `V`. -/
def RightPauliInvariant (E : CircuitExpectation) : Prop :=
  ∀ G : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ →
      Matrix ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ((Fin 2 × Fin 2) × (Fin 2 × Fin 2)) ℂ,
    E G = E (fun U => (16 : ℂ)⁻¹ •
      ∑ V : Pauli1 × Pauli1, G (U * twoQubitMat V))

/-- Fixed arXiv:2211.03999v1, Lemma 2, Eqs. (17)--(18), p.9:
if `E` is right-invariant under uniform random two-qubit Paulis, then for any distinct
two-qubit Paulis `P ≠ Q`, `E[U P U† ⊗ U Q U†] = 0`. -/
theorem source_lemma2_gate_set_orthogonality
    (E : CircuitExpectation) (hE : RightPauliInvariant E)
    (P Q : Pauli1 × Pauli1) (hPQ : P ≠ Q) :
    E (fun U => (U * twoQubitMat P * Uᴴ) ⊗ₖ (U * twoQubitMat Q * Uᴴ)) = 0 := by
  rw [hE]
  have hstep : ∀ (A B U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ),
      (U * A * Uᴴ) ⊗ₖ (U * B * Uᴴ) =
      (U ⊗ₖ U) * (A ⊗ₖ B) * (U ⊗ₖ U)ᴴ := by
    intro A B U
    rw [conjTranspose_kronecker, ← mul_kronecker_mul, ← mul_kronecker_mul]
    try simp only [mul_assoc]
  have hzero : ∀ U : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ,
      (16 : ℂ)⁻¹ • ∑ V : Pauli1 × Pauli1,
        (U * twoQubitMat V * twoQubitMat P * (U * twoQubitMat V)ᴴ) ⊗ₖ
        (U * twoQubitMat V * twoQubitMat Q * (U * twoQubitMat V)ᴴ) = 0 := by
    intro U
    have hpullP : ∀ V : Pauli1 × Pauli1,
        U * twoQubitMat V * twoQubitMat P * (U * twoQubitMat V)ᴴ =
          U * (twoQubitMat V * twoQubitMat P * (twoQubitMat V)ᴴ) * Uᴴ := by
      intro V
      rw [conjTranspose_mul]
      simp only [mul_assoc]
    have hpullQ : ∀ V : Pauli1 × Pauli1,
        U * twoQubitMat V * twoQubitMat Q * (U * twoQubitMat V)ᴴ =
          U * (twoQubitMat V * twoQubitMat Q * (twoQubitMat V)ᴴ) * Uᴴ := by
      intro V
      rw [conjTranspose_mul]
      simp only [mul_assoc]
    have hsum : (∑ V : Pauli1 × Pauli1,
        (U * (twoQubitMat V * twoQubitMat P * (twoQubitMat V)ᴴ) * Uᴴ) ⊗ₖ
        (U * (twoQubitMat V * twoQubitMat Q * (twoQubitMat V)ᴴ) * Uᴴ)) =
        (U ⊗ₖ U) *
          (∑ V : Pauli1 × Pauli1,
            (twoQubitMat V * twoQubitMat P * (twoQubitMat V)ᴴ) ⊗ₖ
            (twoQubitMat V * twoQubitMat Q * (twoQubitMat V)ᴴ)) * (U ⊗ₖ U)ᴴ := by
      simp_rw [hstep]
      rw [Finset.mul_sum, Finset.sum_mul]
      try simp only [mul_assoc]
    rw [show (∑ V : Pauli1 × Pauli1,
        (U * twoQubitMat V * twoQubitMat P * (U * twoQubitMat V)ᴴ) ⊗ₖ
        (U * twoQubitMat V * twoQubitMat Q * (U * twoQubitMat V)ᴴ)) = _ from by
      simp_rw [hpullP, hpullQ]
      exact hsum]
    rw [pauli_average_kron_zero P Q hPQ]
    simp
  simp_rw [hzero]
  exact map_zero E

end Qatlib.Papers.NoisyCircuit22.MainResults.Fourier
