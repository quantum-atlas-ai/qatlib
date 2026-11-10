/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.PotentialWord
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.FermionSign

open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.PotentialWord
open Complex

def fermionSign {α : Type*} [DecidableEq α] [Fintype α] (σ : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign σ : ℤˣ) : ℤ)

theorem fermionSign_normSq {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) : Complex.normSq (fermionSign σ) = 1 := by
  unfold fermionSign
  generalize (Equiv.Perm.sign σ : ℤˣ) = u
  obtain (h | h) := Int.units_eq_one_or u
  · rw [h]; norm_num
  · rw [h]; norm_num

theorem fermionSign_mul {α : Type*} [DecidableEq α] [Fintype α]
    (σ τ : Equiv.Perm α) :
    fermionSign (σ * τ) = fermionSign σ * fermionSign τ := by
  unfold fermionSign
  rw [Equiv.Perm.sign_mul]
  push_cast
  ring

theorem fermionSign_swap {α : Type*} [DecidableEq α] [Fintype α]
    (i j : α) (hij : i ≠ j) :
    fermionSign (Equiv.swap i j) = -1 := by
  unfold fermionSign
  rw [Equiv.Perm.sign_swap hij]
  norm_num

theorem exp_pi_is_neg_one : Complex.exp (Real.pi * I) = -1 :=
  Complex.exp_pi_mul_I

theorem sign_eq_prod_of_swap_list {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) (L : List (Equiv.Perm α))
    (hL : ∀ g ∈ L, Equiv.Perm.IsSwap g) (hprod : L.prod = σ) :
    fermionSign σ = (L.map (fun _ => (-1 : ℂ))).prod := by
  unfold fermionSign
  rw [← hprod, Equiv.Perm.sign_prod_list_swap hL]
  rw [List.map_const', List.prod_replicate]
  rw [Units.val_pow_eq_pow_val]
  push_cast
  ring

theorem sign_eq_prod_crossing_phase {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) (L : List (Equiv.Perm α))
    (hL : ∀ g ∈ L, Equiv.Perm.IsSwap g) (hprod : L.prod = σ) :
    fermionSign σ =
      (L.map (fun _ => Complex.exp (Real.pi * I))).prod := by
  rw [sign_eq_prod_of_swap_list σ L hL hprod]
  simp only [List.map_const', List.prod_replicate, Complex.exp_pi_mul_I]

abbrev OccLabel {N : ℕ} (occ : Fin N → Bool) := {i : Fin N // occ i = true}

theorem occSign_normSq {N : ℕ} (occ : Fin N → Bool)
    (σ : Equiv.Perm (OccLabel occ)) :
    Complex.normSq (fermionSign σ) = 1 :=
  fermionSign_normSq σ

theorem fermion_phase_count_le (N : ℕ) : (wirePairs N).length ≤ N ^ 2 :=
  wirePairs_length N

theorem fermion_phase_lattice_count (d l : ℕ) :
    (wirePairs (qubitCount d l)).length ≤ 4 * d ^ 2 * l ^ (2 * d) := by
  calc
    (wirePairs (qubitCount d l)).length ≤ (qubitCount d l) ^ 2 := wirePairs_length _
    _ = 4 * d ^ 2 * l ^ (2 * d) := by
      unfold qubitCount
      rw [mul_pow, mul_pow, ← pow_mul]
      ring

theorem fermion_sign_fragments {N : ℕ} (occ : Fin N → Bool)
    (σ : Equiv.Perm (OccLabel occ)) (L : List (Equiv.Perm (OccLabel occ)))
    (hL : ∀ g ∈ L, Equiv.Perm.IsSwap g) (hprod : L.prod = σ) :
    Complex.normSq (fermionSign σ) = 1 ∧
    fermionSign σ = (L.map (fun _ => (-1 : ℂ))).prod ∧
    fermionSign σ = (L.map (fun _ => Complex.exp (Real.pi * I))).prod :=
  ⟨fermionSign_normSq σ, sign_eq_prod_of_swap_list σ L hL hprod,
    sign_eq_prod_crossing_phase σ L hL hprod⟩

end Qatlib.Papers.QMechSim97.MainResults.FermionSign
