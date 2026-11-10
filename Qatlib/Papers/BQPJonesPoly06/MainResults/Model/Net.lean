/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.ApproxProducts
set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

def IsEpsNet (S : Set (E ≃ₗᵢ[ℂ] E)) (ε : ℝ) : Prop :=
  ∀ U : E ≃ₗᵢ[ℂ] E, ∃ N ∈ S, FunDistLE N U ε

structure RepresentedNet {ι : Type*} (ρhat : ι → E ≃ₗᵢ[ℂ] E) where

  carrier : Set (E ≃ₗᵢ[ℂ] E)

  word : (E ≃ₗᵢ[ℂ] E) → List ι

  eval_word : ∀ U, U ∈ carrier →
    ∀ x, evalWord (fun i => (ρhat i : E → E)) (word U) x = U x

  bound : ℕ

  length_le : ∀ U, U ∈ carrier → (word U).length ≤ bound

def replacedNet {ι : Type*} {ρhat : ι → E ≃ₗᵢ[ℂ] E} (ρ : ι → E ≃ₗᵢ[ℂ] E)
    (N : RepresentedNet ρhat) : Set (E → E) :=
  { P | ∃ U ∈ N.carrier, P = evalWord (fun i => (ρ i : E → E)) (N.word U) }

def IsEpsNetFun (S : Set (E → E)) (ε : ℝ) : Prop :=
  ∀ U : E ≃ₗᵢ[ℂ] E, ∃ P ∈ S, FunDistLE P U ε

theorem lemma51_net_replacement {ι : Type*} (ρhat ρ : ι → E ≃ₗᵢ[ℂ] E)
    (N : RepresentedNet ρhat) (ε η : ℝ) (hε : 0 < ε) (hη0 : 0 ≤ η)
    (hN : IsEpsNet N.carrier (ε / 2)) (hd : 0 < N.bound)
    (hη : η ≤ ε / (2 * N.bound))
    (hgen : ∀ i, FunDistLE (ρ i) (ρhat i) η) :
    IsEpsNetFun (replacedNet ρ N) ε := by
  intro U
  obtain ⟨N₀, hN₀, hdist⟩ := hN U
  refine ⟨evalWord (fun i => (ρ i : E → E)) (N.word N₀), ⟨N₀, hN₀, rfl⟩, ?_⟩

  have hrep : FunDistLE (evalWord (fun i => (ρ i : E → E)) (N.word N₀))
      (evalWord (fun i => (ρhat i : E → E)) (N.word N₀)) ((N.word N₀).length * η) :=
    evalWord_approx ρ ρhat η hη0 hgen _

  have hsame : FunDistLE (evalWord (fun i => (ρhat i : E → E)) (N.word N₀)) N₀ 0 := by
    intro x
    rw [N.eval_word N₀ hN₀ x]
    simp

  have hbpos : (0 : ℝ) < (N.bound : ℝ) := by exact_mod_cast hd
  have hlen : ((N.word N₀).length : ℝ) * η ≤ ε / 2 := by
    have hb : ((N.word N₀).length : ℝ) ≤ (N.bound : ℝ) := by
      exact_mod_cast N.length_le N₀ hN₀
    have hstep : ((N.word N₀).length : ℝ) * η ≤ (N.bound : ℝ) * η :=
      mul_le_mul_of_nonneg_right hb hη0
    have hhalf : (N.bound : ℝ) * η ≤ (N.bound : ℝ) * (ε / (2 * (N.bound : ℝ))) :=
      mul_le_mul_of_nonneg_left hη (le_of_lt hbpos)
    have heq : (N.bound : ℝ) * (ε / (2 * (N.bound : ℝ))) = ε / 2 := by
      have hb : (N.bound : ℝ) ≠ 0 := ne_of_gt hbpos
      field_simp
    linarith [hstep, hhalf, heq.le]

  have hmain : FunDistLE (evalWord (fun i => (ρ i : E → E)) (N.word N₀)) U
      ((((N.word N₀).length * η) + 0) + ε / 2) :=
    FunDistLE.add (FunDistLE.add hrep hsame) hdist
  refine FunDistLE.mono hmain ?_
  linarith

end Qatlib.Papers.BQPJonesPoly06.MainResults.Model
