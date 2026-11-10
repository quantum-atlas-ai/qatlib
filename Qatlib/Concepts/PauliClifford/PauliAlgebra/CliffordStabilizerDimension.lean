/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PauliClifford.PauliAlgebra.StabilizerDesign
set_option warningAsError false
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

theorem finrank_range_of_independent {n : ℕ} (gs : List (PauliElem n))
    (hcomm : CommutingHermitianPaulis gs) (hind : IndependentGenerators gs) :
    Module.finrank ℂ ((projectorAux gs).toLin'.range) = 2 ^ (n - gs.length) :=
  finrank_range_projectorAux gs rfl (independent_length_le gs hcomm hind) hcomm hind

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

theorem finrank_codeSpace_of_independent {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    Module.finrank ℂ (codeSpace t) = 2 ^ (n - k) := by
  have hk : k ≤ n := by
    simpa only [tableauGenerators_length] using
      independent_length_le (tableauGenerators t) (generators_commuting t ht) hind
  exact finrank_codeSpace t (tableauGenerators_length t) hk ht hind

theorem exists_normalized_of_independent {n k : ℕ} (t : Tableau n k)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t)) :
    ∃ ψ : QState (Reg n), Normalized ψ ∧ ψ ∈ codeSpace t := by
  have hk : k ≤ n := by
    simpa only [tableauGenerators_length] using
      independent_length_le (tableauGenerators t) (generators_commuting t ht) hind
  exact exists_normalized_codeState t (tableauGenerators_length t) hk ht hind

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

theorem norm_eq_one_of_normalized_smul {n : ℕ} (ψ : QState (Reg n)) (lam : ℂ)
    (hψ : Normalized ψ) (hscaled : Normalized (lam • ψ)) : ‖lam‖ = 1 := by
  change (∑ i, ‖ψ i‖ ^ 2) = 1 at hψ
  change (∑ i, ‖(lam • ψ) i‖ ^ 2) = 1 at hscaled
  simp_rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow] at hscaled
  rw [← Finset.mul_sum, hψ, mul_one] at hscaled
  nlinarith [norm_nonneg lam]

theorem unique_stabilizerState_unitPhase {n : ℕ} (t : Tableau n n)
    (ht : ConsistentTableau t) (hind : IndependentGenerators (tableauGenerators t))
    (ψ φ : QState (Reg n)) (hψ : ψ ∈ codeSpace t) (hφ : φ ∈ codeSpace t)
    (hnψ : Normalized ψ) (hnφ : Normalized φ) :
    ∃ lam : ℂ, ‖lam‖ = 1 ∧ φ = lam • ψ := by
  obtain ⟨lam, _, hrel⟩ := unique_stabilizerState t ht (tableauGenerators_length t)
    hind ψ φ hψ hφ hnψ hnφ
  refine ⟨lam, ?_, hrel⟩
  exact norm_eq_one_of_normalized_smul ψ lam hnψ (hrel ▸ hnφ)

theorem finrank_empty_rows (n : ℕ) (t : Tableau n 0) :
    Module.finrank ℂ (codeSpace t) = 2 ^ n :=
  finrank_empty_code n t

theorem finrank_empty_register (t : Tableau 0 0) :
    Module.finrank ℂ (codeSpace t) = 1 := by
  simpa using finrank_empty_code 0 t

theorem minusI_not_mem_of_independent {n : ℕ} (gs : List (PauliElem n))
    (hind : IndependentGenerators gs) : minusI n ∉ generatedSubgroup gs :=
  not_contains_minusI_of_independent gs hind

end Qatlib.Concepts.PauliClifford.PauliAlgebra
