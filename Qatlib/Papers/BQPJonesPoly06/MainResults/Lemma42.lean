/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.Bridge
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults

open Model

theorem lemma42_finrank_ne_no_isometry (A B : Type*)
    [NormedAddCommGroup A] [InnerProductSpace ℂ A] [FiniteDimensional ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B] [FiniteDimensional ℂ B]
    (hAB : Module.finrank ℂ A ≠ Module.finrank ℂ B) :
    ¬ Nonempty (A ≃ₗᵢ[ℂ] B) := by
  rintro ⟨e⟩
  exact hAB (e.toLinearEquiv.finrank_eq)

theorem lemma42_decoupling_of_kernel_dense {G : Type*} [Group G]
    (A B : Type*)
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (τa : G →* (A ≃ₗᵢ[ℂ] A)) (τb : G →* (B ≃ₗᵢ[ℂ] B))
    (hker : ∀ U : A ≃ₗᵢ[ℂ] A, ∀ ε : ℝ, 0 < ε →
      ∃ σ : G, τb σ = 1 ∧ FunDistLE (τa σ) U ε) :
    ∀ U : A ≃ₗᵢ[ℂ] A, ∀ ε : ℝ, 0 < ε →
      ∃ σ : G, FunDistLE (τa σ) U ε ∧ FunDistLE (τb σ) (1 : B ≃ₗᵢ[ℂ] B) ε := by
  intro U ε hε
  obtain ⟨σ, hσ, hd⟩ := hker U ε hε
  refine ⟨σ, hd, ?_⟩
  rw [hσ]
  intro x
  have hz : (1 : B ≃ₗᵢ[ℂ] B) x - (1 : B ≃ₗᵢ[ℂ] B) x = 0 := sub_self _
  rw [hz, norm_zero]
  exact mul_nonneg (le_of_lt hε) (norm_nonneg x)

theorem lemma42_decoupling_of_kernel_dense_symm {G : Type*} [Group G]
    (A B : Type*)
    [NormedAddCommGroup A] [InnerProductSpace ℂ A]
    [NormedAddCommGroup B] [InnerProductSpace ℂ B]
    (τa : G →* (A ≃ₗᵢ[ℂ] A)) (τb : G →* (B ≃ₗᵢ[ℂ] B))
    (hker : ∀ V : B ≃ₗᵢ[ℂ] B, ∀ ε : ℝ, 0 < ε →
      ∃ σ : G, τa σ = 1 ∧ FunDistLE (τb σ) V ε) :
    ∀ V : B ≃ₗᵢ[ℂ] B, ∀ ε : ℝ, 0 < ε →
      ∃ σ : G, FunDistLE (τb σ) V ε ∧ FunDistLE (τa σ) (1 : A ≃ₗᵢ[ℂ] A) ε := by
  intro V ε hε
  obtain ⟨σ, hσ, hd⟩ := hker V ε hε
  refine ⟨σ, hd, ?_⟩
  rw [hσ]
  intro x
  have hz : (1 : A ≃ₗᵢ[ℂ] A) x - (1 : A ≃ₗᵢ[ℂ] A) x = 0 := sub_self _
  rw [hz, norm_zero]
  exact mul_nonneg (le_of_lt hε) (norm_nonneg x)

end Qatlib.Papers.BQPJonesPoly06.MainResults
