/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HypergroupQC15.MainResults.Defs

set_option backward.isDefEq.respectTransparency false

/-!
# HypergroupQC15 — Theorem 3 (evolution of stabilizer states)

Fixed source: arXiv:1509.05806, §5.2, Theorem 3, p.19–20.

A normalizer gate `U` is a linear automorphism of the state space whose conjugation
action `P ↦ U P U⁻¹` maps the set of hypergroup Pauli operators into itself; the paper
proves this for the gate list (23)–(26) in Appendix A.  Theorem 3 then says that a
stabilizer state is carried to a stabilizer state of the conjugated Pauli set.

The formalization below isolates exactly this linear-algebraic transfer and proves it:
if `U` maps the Pauli set `S` into itself under conjugation and `ψ` is the unique
nonzero joint `+1`-eigenvector of `S`, then `U ψ` is the unique nonzero joint
`+1`-eigenvector of `U S U⁻¹`.  No monomiality or unitarity of the Pauli operators is
used, matching the paper's point that hypergroup Paulis are neither.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.HypergroupQC15.MainResults

open scoped BigOperators

section Evolution

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- Conjugation of an operator by a linear automorphism: `P ↦ U P U⁻¹`. -/
def conjOp (U : V ≃ₗ[ℂ] V) (P : V →ₗ[ℂ] V) : V →ₗ[ℂ] V :=
  U.toLinearMap.comp (P.comp U.symm.toLinearMap)

/-- The image of an operator set under conjugation by `U`. -/
def conjSet (U : V ≃ₗ[ℂ] V) (S : Set (V →ₗ[ℂ] V)) : Set (V →ₗ[ℂ] V) :=
  {Q | ∃ P ∈ S, conjOp U P = Q}

/-- A normalizer gate for a Pauli set: conjugation maps the Pauli set into itself.
(For hypergroup normalizer circuits this is the content of eqs. (23)–(26), proved in
Appendix A of arXiv:1509.05806.) -/
structure NormalizerGate (Pauli : Set (V →ₗ[ℂ] V)) (U : V ≃ₗ[ℂ] V) where
  maps_pauli : ∀ P ∈ Pauli, conjOp U P ∈ Pauli

/-- Conjugated stabilizers stabilize the transported vector. -/
theorem conjOp_apply_of_stabilizes (U : V ≃ₗ[ℂ] V) (P : V →ₗ[ℂ] V) (ψ : V)
    (h : P ψ = ψ) : conjOp U P (U ψ) = U ψ := by
  unfold conjOp
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
  rw [h]

/-- Pulling back a conjugated stabilizer gives the original stabilizer equation. -/
theorem stabilizes_of_conjOp_stabilizes (U : V ≃ₗ[ℂ] V) (P : V →ₗ[ℂ] V) (φ : V)
    (h : conjOp U P φ = φ) : P (U.symm φ) = U.symm φ := by
  have h' : U (P (U.symm φ)) = U (U.symm φ) := by
    simpa [conjOp] using h
  exact U.injective h'

/-- Theorem 3 (arXiv:1509.05806, Theorem 3, p.19–20).  Normalizer gates map the Pauli
set into itself under conjugation and carry a stabilizer state of `S` to a stabilizer
state of the conjugated Pauli set `U S U⁻¹`.

The first conjunct is the defining property of a normalizer gate (the paper establishes
it for the normalizer gate list (23)–(26)); the second conjunct, the evolution of
stabilizer states, is proved here for the general linear-algebraic situation. -/
theorem theorem3_normalizer_maps_stabilizer_states (Pauli : Set (V →ₗ[ℂ] V))
    (U : V ≃ₗ[ℂ] V) (hU : NormalizerGate Pauli U) (ψ : V)
    (hψ : IsStabilizerState Pauli ψ) :
    (∀ P ∈ Pauli, conjOp U P ∈ Pauli) ∧
      IsStabilizerState (conjSet U Pauli) (U ψ) := by
  obtain ⟨hne, hstab, huniq⟩ := hψ
  have hne' : U ψ ≠ 0 := by
    intro h
    exact hne ((U.map_eq_zero_iff).mp h)
  constructor
  · exact hU.maps_pauli
  · refine ⟨hne', ?_, ?_⟩
    · rintro Q ⟨P, hP, rfl⟩
      exact conjOp_apply_of_stabilizes U P ψ (hstab P hP)
    · intro φ hφ hφstab
      have hstab' : ∀ P ∈ Pauli, P (U.symm φ) = U.symm φ := by
        intro P hP
        exact stabilizes_of_conjOp_stabilizes U P φ (hφstab (conjOp U P) ⟨P, hP, rfl⟩)
      have hne2 : U.symm φ ≠ 0 := by
        intro h0
        apply hφ
        calc φ = U (U.symm φ) := (U.apply_symm_apply φ).symm
          _ = U 0 := by rw [h0]
          _ = 0 := map_zero _
      have h' : U.symm φ = ψ := huniq (U.symm φ) hne2 hstab'
      calc φ = U (U.symm φ) := (U.apply_symm_apply φ).symm
        _ = U ψ := congrArg (⇑U) h'

end Evolution

end Qatlib.Papers.HypergroupQC15.MainResults
