/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign

/-!
# Dimensions and uniqueness of stabilizer code states

This module derives the code-space dimension 2^(n - k) for consistent k-row tableaux with
independent generators on n qubits. It also proves existence of normalized code states and
uniqueness up to a scalar of norm one for full independent tableaux, within the stabilizer
framework of [DehaeneDeMoor2003].

Auxiliary results bound the number of independent commuting Hermitian generators and connect
binary row independence to generator independence.

## Main statements

* `independent_length_le`: There are at most n independent commuting Hermitian Pauli generators
  on n qubits.
* `finrank_codeSpace_of_independent`: The code-space dimension is 2^(n - k).
* `unique_stabilizerState_unitPhase`: Normalized states of a full independent code differ by a
  scalar of norm one.

## References

* [Dehaene and De Moor, 2003][DehaeneDeMoor2003]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Foundations.PureStateMath

noncomputable section

namespace Qatlib.Concepts.PauliClifford.PauliAlgebra

open Qatlib
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordTableauConstruction
open Qatlib.Concepts.PauliClifford.PauliAlgebra
open Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Matrix
open scoped Classical ComplexOrder

/-- A list of commuting Hermitian Pauli operators with independent generators has length at most
the number of qubits. -/
theorem independent_length_le {n : ℕ} (gs : List (PauliElem n))
    (hcomm : CommutingHermitianPaulis gs) (hind : IndependentGenerators gs) :
    gs.length ≤ n := by
  have hmul := finrank_range_projectorAux_mul gs rfl hcomm hind
  have hfin : Module.finrank ℂ ((projectorAux gs).toLin'.range) ≠ 0 := by
    intro hz
    rw [hz, zero_mul] at hmul
    exact (Nat.ne_of_gt (by positivity : 0 < (2 : ℕ) ^ n)) hmul.symm
  have hpos := Nat.pos_of_ne_zero hfin
  have hle : (2 : ℕ) ^ gs.length ≤ 2 ^ n := by
    calc 2 ^ gs.length
        ≤ Module.finrank ℂ ((projectorAux gs).toLin'.range) * 2 ^ gs.length :=
          Nat.le_mul_of_pos_left _ hpos
      _ = 2 ^ n := hmul
  exact (Nat.pow_le_pow_iff_right (by decide : 1 < (2 : ℕ))).mp hle

/-- The projector product of m commuting Hermitian independent Pauli generators on n qubits has
range dimension 2^(n - m). -/
theorem finrank_range_of_independent {n : ℕ} (gs : List (PauliElem n))
    (hcomm : CommutingHermitianPaulis gs) (hind : IndependentGenerators gs) :
    Module.finrank ℂ ((projectorAux gs).toLin'.range) = 2 ^ (n - gs.length) :=
  finrank_range_projectorAux gs rfl (independent_length_le gs hcomm hind) hcomm hind

/-- The decoded generators of a consistent tableau are commuting Hermitian Pauli operators. -/
theorem generators_commuting {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) : CommutingHermitianPaulis (tableauGenerators t) := by
  constructor
  · intro p hp
    obtain ⟨a, rfl⟩ := (mem_tableauGenerators t p).mp hp
    exact ht.1 a
  · intro p hp q hq
    obtain ⟨a, rfl⟩ := (mem_tableauGenerators t p).mp hp
    obtain ⟨b, rfl⟩ := (mem_tableauGenerators t q).mp hq
    exact ht.2 a b

/-- A consistent k-row tableau with independent generators on n qubits has code-space dimension
2^(n - k). -/
theorem finrank_codeSpace_of_independent {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    Module.finrank ℂ (codeSpace t) = 2 ^ (n - k) := by
  have hk : k ≤ n := by
    simpa only [tableauGenerators_length] using
      independent_length_le (tableauGenerators t) (generators_commuting t ht) hind
  exact finrank_codeSpace t (tableauGenerators_length t) hk ht hind

/-- The code space of a consistent tableau with independent generators contains a normalized
state. -/
theorem exists_normalized_of_independent {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    ∃ ψ : QState (Reg n), Normalized ψ ∧ ψ ∈ codeSpace t := by
  have hk : k ≤ n := by
    simpa only [tableauGenerators_length] using
      independent_length_le (tableauGenerators t) (generators_commuting t ht) hind
  exact exists_normalized_codeState t (tableauGenerators_length t) hk ht hind

/-- Linear independence of the binary symplectic row vectors implies independence of the decoded
generators. -/
theorem independent_of_row_linearIndependent {n k : ℕ} (t : Tableau n k)
    (hlin : LinearIndependent (ZMod 2) (rowSympVec t)) :
    IndependentGenerators (tableauGenerators t) := by
  apply IndependentGenerators_of_linearIndependent
  have h2 := linearIndependent_comp (rowEquiv t).symm hlin
  have heq : (fun j : Fin (tableauGenerators t).length =>
      rowSympVec t ((rowEquiv t).symm j)) = symplecticVecOfFn (tableauGenerators t) := by
    funext j
    have h1 := symplecticVecOfFn_rowEquiv t ((rowEquiv t).symm j)
    rw [Equiv.apply_symm_apply] at h1
    exact h1.symm
  rwa [heq] at h2

/-- A scalar taking a normalized state to a normalized state has norm one. -/
theorem norm_eq_one_of_normalized_smul {n : ℕ} (ψ : QState (Reg n)) (lam : ℂ)
    (hψ : Normalized ψ) (hscaled : Normalized (lam • ψ)) : ‖lam‖ = 1 := by
  change (∑ i, ‖ψ i‖ ^ 2) = 1 at hψ
  change (∑ i, ‖(lam • ψ) i‖ ^ 2) = 1 at hscaled
  simp_rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow] at hscaled
  rw [← Finset.mul_sum, hψ, mul_one] at hscaled
  nlinarith [norm_nonneg lam]

/-- Two normalized states in the code space of a consistent tableau with n independent
generators on n qubits differ by a scalar of norm one. -/
theorem unique_stabilizerState_unitPhase {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (ψ φ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) (hφ : φ ∈ codeSpace t)
    (hnψ : Normalized ψ) (hnφ : Normalized φ) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ φ = lam • ψ := by
  obtain ⟨lam, _, hrel⟩ := unique_stabilizerState t ht (tableauGenerators_length t)
    hind ψ φ hψ hφ hnψ hnφ
  refine ⟨lam, ?_, hrel⟩
  exact norm_eq_one_of_normalized_smul ψ lam hnψ (hrel ▸ hnφ)

/-- The code space of a tableau with no rows on n qubits has dimension 2^n. -/
theorem finrank_empty_rows (n : ℕ) (t : Tableau n 0) :
    Module.finrank ℂ (codeSpace t) = 2 ^ n :=
  finrank_empty_code n t

/-- The code space of the empty tableau on zero qubits has dimension one. -/
theorem finrank_empty_register (t : Tableau 0 0) :
    Module.finrank ℂ (codeSpace t) = 1 := by
  simpa using finrank_empty_code 0 t

/-- The subgroup generated by an independent list of Pauli elements does not contain the
negative identity. -/
theorem minusI_not_mem_of_independent {n : ℕ} (gs : List (PauliElem n))
    (hind : IndependentGenerators gs) : minusI n ∉ generatedSubgroup gs :=
  not_contains_minusI_of_independent gs hind

end Qatlib.Concepts.PauliClifford.PauliAlgebra
