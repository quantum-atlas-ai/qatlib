/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QMechSim97.MainResults.PotentialWord
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic

/-!
# Permutation signs as fermionic phase products

This module expresses the sign bookkeeping of [BoghosianTaylor1998] through the complex-valued
permutation sign `fermionSign`. It proves multiplicativity, unit squared norm, and the sign of a
transposition, then rewrites a given transposition factorization as a product of phases
`exp(πi)`.

The subtype `OccLabel occ` restricts permutation labels to occupied wires. Separate counting
results bound the length of the wire-pair list by `N²` and, for the defined lattice wire count,
by `4 * d² * l ^ (2 * d)`.

## Main statements

* `sign_eq_prod_crossing_phase`: a supplied transposition factorization gives the phase-product
  representation.
* `fermion_phase_lattice_count`: the wire-pair count has the stated lattice-size bound.
* `fermion_sign_fragments`: unit squared norm and both product representations for occupied
  labels.

## References

* [Boghosian and Taylor, 1998][BoghosianTaylor1998]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QMechSim97.MainResults.FermionSign

open Qatlib.Papers.QMechSim97.MainResults.Defs
open Qatlib.Papers.QMechSim97.MainResults.PotentialWord
open Complex

/-- The sign of a permutation, mapped from the integer units into the complex numbers. -/
def fermionSign {α : Type*} [DecidableEq α] [Fintype α] (σ : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign σ : ℤˣ) : ℤ)

/-- The complex permutation sign has squared norm one. See [BoghosianTaylor1998]. -/
theorem fermionSign_normSq {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) : Complex.normSq (fermionSign σ) = 1 := by
  unfold fermionSign
  generalize (Equiv.Perm.sign σ : ℤˣ) = u
  obtain (h | h) := Int.units_eq_one_or u
  · rw [h]; norm_num
  · rw [h]; norm_num

/-- The complex permutation sign is multiplicative under permutation composition. See
[BoghosianTaylor1998]. -/
theorem fermionSign_mul {α : Type*} [DecidableEq α] [Fintype α]
    (σ τ : Equiv.Perm α) :
    fermionSign (σ * τ) = fermionSign σ * fermionSign τ := by
  unfold fermionSign
  rw [Equiv.Perm.sign_mul]
  push_cast
  ring

/-- The complex sign of a transposition of distinct labels is minus one. See
[BoghosianTaylor1998]. -/
theorem fermionSign_swap {α : Type*} [DecidableEq α] [Fintype α]
    (i j : α) (hij : i ≠ j) :
    fermionSign (Equiv.swap i j) = -1 := by
  unfold fermionSign
  rw [Equiv.Perm.sign_swap hij]
  norm_num

/-- The complex exponential `exp(πi)` is minus one. See [BoghosianTaylor1998]. -/
theorem exp_pi_is_neg_one : Complex.exp (Real.pi * I) = -1 :=
  Complex.exp_pi_mul_I

/-- If a list of transpositions multiplies to `σ`, then `fermionSign σ` is the product of one
factor minus one for each list entry. See [BoghosianTaylor1998]. -/
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

/-- If a list of transpositions multiplies to `σ`, then `fermionSign σ` is the product of one
phase `exp(πi)` for each list entry. See [BoghosianTaylor1998]. -/
theorem sign_eq_prod_crossing_phase {α : Type*} [DecidableEq α] [Fintype α]
    (σ : Equiv.Perm α) (L : List (Equiv.Perm α))
    (hL : ∀ g ∈ L, Equiv.Perm.IsSwap g) (hprod : L.prod = σ) :
    fermionSign σ =
      (L.map (fun _ => Complex.exp (Real.pi * I))).prod := by
  rw [sign_eq_prod_of_swap_list σ L hL hprod]
  simp only [List.map_const', List.prod_replicate, Complex.exp_pi_mul_I]

/-- The subtype of wire labels whose occupation value is true. -/
abbrev OccLabel {N : ℕ} (occ : Fin N → Bool) := {i : Fin N // occ i = true}

/-- The complex sign of a permutation of occupied wire labels has squared norm one. -/
theorem occSign_normSq {N : ℕ} (occ : Fin N → Bool)
    (σ : Equiv.Perm (OccLabel occ)) :
    Complex.normSq (fermionSign σ) = 1 :=
  fermionSign_normSq σ

/-- The wire-pair list for `N` wires has length at most `N ^ 2`. See [BoghosianTaylor1998]. -/
theorem fermion_phase_count_le (N : ℕ) : (wirePairs N).length ≤ N ^ 2 :=
  wirePairs_length N

/-- For `qubitCount d l` wires, the wire-pair list has length at most `4 * d ^ 2 * l ^ (2 * d)`.
See [BoghosianTaylor1998]. -/
theorem fermion_phase_lattice_count (d l : ℕ) :
    (wirePairs (qubitCount d l)).length ≤ 4 * d ^ 2 * l ^ (2 * d) := by
  calc
    (wirePairs (qubitCount d l)).length ≤ (qubitCount d l) ^ 2 := wirePairs_length _
    _ = 4 * d ^ 2 * l ^ (2 * d) := by
      unfold qubitCount
      rw [mul_pow, mul_pow, ← pow_mul]
      ring

/-- For a permutation of occupied labels with a supplied transposition factorization, its
complex sign has squared norm one and equals both the product of minus-one factors and the
product of `exp(πi)` phases. See [BoghosianTaylor1998]. -/
theorem fermion_sign_fragments {N : ℕ} (occ : Fin N → Bool)
    (σ : Equiv.Perm (OccLabel occ)) (L : List (Equiv.Perm (OccLabel occ)))
    (hL : ∀ g ∈ L, Equiv.Perm.IsSwap g) (hprod : L.prod = σ) :
    Complex.normSq (fermionSign σ) = 1 ∧
    fermionSign σ = (L.map (fun _ => (-1 : ℂ))).prod ∧
    fermionSign σ = (L.map (fun _ => Complex.exp (Real.pi * I))).prod :=
  ⟨fermionSign_normSq σ, sign_eq_prod_of_swap_list σ L hL hprod,
    sign_eq_prod_crossing_phase σ L hL hprod⟩

end Qatlib.Papers.QMechSim97.MainResults.FermionSign
