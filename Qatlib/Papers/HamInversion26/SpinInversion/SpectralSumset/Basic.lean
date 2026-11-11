/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Find
import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# Spectral sumset criterion — statement layer for Theorem 1 / Theorem S2

Fixed arXiv:2607.29382v2.
* Eq. (S9), page S4: `Σ_q(Λ) := {μ₁ + ⋯ + μ_q : μ_r ∈ Λ}`, `Σ_0(Λ) := {0}`.
* Theorem 1, page 2 (Letter); Theorem S2, pages S4–S7.

This module defines the `q`-fold sumset with repetition (`SumOf`), the sumset criterion
`KappaWitness`, and the minimal exact query number
`kappa Λ = min {q : ∃ c, c − Λ ⊆ Σ_q(Λ)}`.
It proves the purely combinatorial content of Theorem S2: existence of the minimum,
minimality, the bound `κ(Λ) ≤ #Λ − 1` (the `c = ∑Λ` choice of page S7), and the `κ = 0`
characterisation.  The protocol content is stated in `Source.lean` over the query-word
model of `Model.OracleWord`.
-/

open Finset
open scoped BigOperators

namespace Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset

set_option autoImplicit false

attribute [local instance] Classical.propDecidable

variable {V : Type*} [AddCommGroup V] [DecidableEq V]

/-- `Σ_q(Λ)` (paper Eq. (S9), page S4): `s` is a sum of `q` elements of `Λ`, repetition
allowed.  The `q = 0` sum is the empty sum `0`. -/
def SumOf (q : ℕ) (Λ : Finset V) (s : V) : Prop :=
  ∃ m : Multiset V, m.card = q ∧ (∀ x ∈ m, x ∈ Λ) ∧ m.sum = s

/-- The `q = 0` sumset is `{0}` (paper Eq. (S9), page S4). -/
theorem sumOf_zero_iff {Λ : Finset V} {s : V} : SumOf 0 Λ s ↔ s = 0 := by
  constructor
  · rintro ⟨m, hm, -, hs⟩
    rw [Multiset.card_eq_zero.mp hm] at hs
    simpa [eq_comm] using hs
  · rintro rfl
    exact ⟨0, rfl, by simp, by simp⟩

/-- Adding one more element of `Λ` moves `Σ_q(Λ)` into `Σ_{q+1}(Λ)`. -/
theorem sumOf_succ {Λ : Finset V} {q : ℕ} {s : V} (a : V) (ha : a ∈ Λ)
    (h : SumOf q Λ s) : SumOf (q + 1) Λ (s + a) := by
  obtain ⟨m, hm, hmem, hs⟩ := h
  refine ⟨m + {a}, ?_, ?_, ?_⟩
  · rw [Multiset.card_add, hm]; simp
  · intro x hx
    rcases Multiset.mem_add.mp hx with hx | hx
    · exact hmem x hx
    · rw [Multiset.mem_singleton] at hx
      subst hx
      exact ha
  · rw [Multiset.sum_add, hs]; simp

/-- The sumset criterion of Theorem S2, Eq. (S11)/(S13): there is a phase centre `c`
such that every `c − λ` is a sum of `q` eigenvalues. -/
def KappaWitness (Λ : Finset V) (q : ℕ) : Prop :=
  ∃ c : V, ∀ a ∈ Λ, SumOf q Λ (c - a)

/-- The centre `c = ∑_{λ∈Λ} λ` makes every `c − λ` a sum of `#Λ − 1` eigenvalues
(the `c = ΣΛ` choice used for `κ(Λ) ≤ #Λ − 1` in Theorem S2, page S7). -/
theorem kappaWitness_card_sub_one {Λ : Finset V} (hne : Λ.Nonempty) :
    KappaWitness Λ (Λ.card - 1) := by
  classical
  refine ⟨∑ x ∈ Λ, x, ?_⟩
  intro a ha
  refine ⟨(Λ.erase a).val, ?_, ?_, ?_⟩
  · show (Λ.erase a).card = Λ.card - 1
    exact card_erase_of_mem ha
  · intro x hx
    exact Finset.mem_of_mem_erase (show x ∈ Λ.erase a from hx)
  · have hsum : (Λ.erase a).val.sum = ∑ x ∈ Λ.erase a, x := by
      rw [← Finset.sum_map_val]
      simp
    have hse : (∑ x ∈ Λ.erase a, x) + a = ∑ x ∈ Λ, x :=
      Finset.sum_erase_add Λ (fun x => x) ha
    rw [hsum, ← hse]
    abel

/-- The sumset criterion is satisfiable for every finite `Λ` (with the trivial witness
`c = 0`, `q = #Λ`). -/
theorem kappa_exists (Λ : Finset V) : ∃ q, KappaWitness Λ q := by
  classical
  rcases Λ.eq_empty_or_nonempty with h | h
  · subst h
    exact ⟨0, 0, by intro a ha; simp at ha⟩
  · exact ⟨Λ.card - 1, kappaWitness_card_sub_one h⟩

/-- The minimal exact query number `κ(Λ)` of Eq. (S11) (Theorem S2, page S4). -/
noncomputable def kappa (Λ : Finset V) : ℕ :=
  Nat.find (kappa_exists Λ)

/-- `κ(Λ)` is attained: the sumset criterion holds at `κ(Λ)`. -/
theorem kappa_spec {Λ : Finset V} : KappaWitness Λ (kappa Λ) :=
  Nat.find_spec (kappa_exists Λ)

/-- `κ(Λ)` is minimal: no smaller `q` satisfies the sumset criterion. -/
theorem kappa_minimal {Λ : Finset V} {q : ℕ} (hq : q < kappa Λ) :
    ¬ KappaWitness Λ q :=
  Nat.find_min (kappa_exists Λ) hq

/-- Any sumset witness bounds `κ(Λ)` from above. -/
theorem kappa_le {Λ : Finset V} {q : ℕ} (h : KappaWitness Λ q) : kappa Λ ≤ q :=
  Nat.find_min' (kappa_exists Λ) h

/-- `κ(Λ) ≤ #Λ − 1`, independently of eigenspace multiplicities (Theorem S2, page S4:
"In particular, `κ(Λ) ≤ K − 1`, independently of the eigenspace multiplicities"). -/
theorem kappa_le_card_sub_one {Λ : Finset V} (hne : Λ.Nonempty) :
    kappa Λ ≤ Λ.card - 1 :=
  kappa_le (kappaWitness_card_sub_one hne)

/-- Characterization of `κ(Λ) = 0`: the zero-sumset criterion `c − λ = 0` for all `λ`
forces all eigenvalues to coincide, hence a single eigenvalue (the `K = 1` case discussed
on page S6). -/
theorem kappa_eq_zero_iff {Λ : Finset V} (hne : Λ.Nonempty) :
    kappa Λ = 0 ↔ Λ.card = 1 := by
  classical
  constructor
  · intro h
    obtain ⟨c, hc⟩ := kappa_spec (Λ := Λ)
    have hall : ∀ a ∈ Λ, a = c := by
      intro a ha
      have hk : SumOf 0 Λ (c - a) := by simpa [h] using hc a ha
      have h0 : c - a = 0 := sumOf_zero_iff.mp hk
      exact (sub_eq_zero.mp h0).symm
    have hle : Λ.card ≤ 1 := by
      apply Finset.card_le_one.mpr
      intro a ha b hb
      rw [hall a ha, hall b hb]
    have hpos : 0 < Λ.card := Finset.card_pos.mpr hne
    omega
  · intro hcard
    obtain ⟨l0, hl0⟩ := hne
    have hsingle : Λ = {l0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hl0, ?_⟩
      intro y hy
      by_contra hne'
      have h2 : 2 ≤ Λ.card := by
        have hmem : y ∈ Λ.erase l0 := Finset.mem_erase.mpr ⟨hne', hy⟩
        have := Finset.card_pos.mpr ⟨y, hmem⟩
        have := card_erase_of_mem hl0
        omega
      omega
    have hwit : KappaWitness Λ 0 := by
      refine ⟨l0, ?_⟩
      intro a ha
      have haz : a = l0 := Finset.mem_singleton.mp (hsingle ▸ ha)
      subst haz
      exact ⟨0, rfl, by simp, by simp⟩
    have hmin : kappa Λ ≤ 0 := kappa_le hwit
    omega

end Qatlib.Papers.HamInversion26.SpinInversion.SpectralSumset
