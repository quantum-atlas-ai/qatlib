/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPJonesPoly06.MainResults.Model.ApproxProducts

/-!
# Stability of represented isometry nets

This module defines nets of complex linear isometric equivalences using uniform relative error.
A `RepresentedNet` records generator words with a uniform length bound. Replacing each generator
by a close isometry preserves the covering property after enlarging the tolerance from `ε / 2`
to `ε`. See [AharonovArad2011].

## Main statements

* `RepresentedNet`: records word representatives and a common length bound.
* `replacedNet`: evaluates the representatives using replacement generators.
* `lemma51_net_replacement`: bounds the error of the replacement net.

## References

* [Aharonov and Arad, 2011][AharonovArad2011]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.BQPJonesPoly06.MainResults.Model

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Every complex linear isometric equivalence lies within uniform relative error `ε` of some
member of `S`. -/
def IsEpsNet (S : Set (E ≃ₗᵢ[ℂ] E)) (ε : ℝ) : Prop :=
  ∀ U : E ≃ₗᵢ[ℂ] E, ∃ N ∈ S, FunDistLE N U ε

/-- A set of linear isometric equivalences with exact generator-word representatives and a
uniform bound on their lengths. -/
structure RepresentedNet {ι : Type*} (ρhat : ι → E ≃ₗᵢ[ℂ] E) where

  carrier : Set (E ≃ₗᵢ[ℂ] E)

  word : (E ≃ₗᵢ[ℂ] E) → List ι

  eval_word : ∀ U, U ∈ carrier →
    ∀ x, evalWord (fun i => (ρhat i : E → E)) (word U) x = U x

  bound : ℕ

  length_le : ∀ U, U ∈ carrier → (word U).length ≤ bound

/-- The functions obtained by evaluating the word representatives of `N` with the replacement
generators `ρ`. -/
def replacedNet {ι : Type*} {ρhat : ι → E ≃ₗᵢ[ℂ] E} (ρ : ι → E ≃ₗᵢ[ℂ] E)
    (N : RepresentedNet ρhat) : Set (E → E) :=
  { P | ∃ U ∈ N.carrier, P = evalWord (fun i => (ρ i : E → E)) (N.word U) }

/-- Every complex linear isometric equivalence lies within uniform relative error `ε` of a
function in `S`. -/
def IsEpsNetFun (S : Set (E → E)) (ε : ℝ) : Prop :=
  ∀ U : E ≃ₗᵢ[ℂ] E, ∃ P ∈ S, FunDistLE P U ε

/-- If an `ε / 2` net has representative words of positive length bound `N.bound`, replacing
generators with error at most nonnegative `η ≤ ε / (2 * N.bound)` yields an `ε` net. See
[Aharonov and Arad, Lemma 5.1][AharonovArad2011]. -/
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
