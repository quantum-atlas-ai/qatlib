/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.AdiabGaps09.MainResults

abbrev BitString (n : ℕ) := Fin n → Bool

def zeros (n : ℕ) : BitString n := fun _ => false

def ones (n : ℕ) : BitString n := fun _ => true

structure Clause (n : ℕ) where
  i1 : Fin n
  i2 : Fin n
  i3 : Fin n
  w1 : Bool
  w2 : Bool
  w3 : Bool
  deriving DecidableEq, Fintype

def Clause.Violated {n : ℕ} (c : Clause n) (z : BitString n) : Prop :=
  z c.i1 = c.w1 ∧ z c.i2 = c.w2 ∧ z c.i3 = c.w3

def Clause.PlantedConsistent {n : ℕ} (c : Clause n) : Prop :=
  ¬ (c.w1 = false ∧ c.w2 = false ∧ c.w3 = false) ∧
  ¬ (c.w1 = true ∧ c.w2 = true ∧ c.w3 = true)

theorem planted_clause_satisfied_by_both {n : ℕ} (c : Clause n)
    (hc : c.PlantedConsistent) :
    ¬ c.Violated (zeros n) ∧ ¬ c.Violated (ones n) := by
  constructor
  · rintro ⟨h1, h2, h3⟩

    simp only [zeros] at h1 h2 h3
    exact hc.1 ⟨h1.symm, h2.symm, h3.symm⟩
  · rintro ⟨h1, h2, h3⟩
    simp only [ones] at h1 h2 h3
    exact hc.2 ⟨h1.symm, h2.symm, h3.symm⟩

def problemEnergy0 {n : ℕ} (cs : Finset (Clause n)) (z : BitString n) : ℝ := by
  classical
  exact ((cs.filter (fun c => c.Violated z)).card : ℝ)

def penaltyTerm {n : ℕ} (p1 p2 p3 : Fin n) (z : BitString n) : ℝ :=
  if z p1 = false ∧ z p2 = false ∧ z p3 = false then (1 / 2 : ℝ) else 0

def problemEnergy {n : ℕ} (cs : Finset (Clause n))
    (p1 p2 p3 : Fin n) (z : BitString n) : ℝ :=
  problemEnergy0 cs z + penaltyTerm p1 p2 p3 z

theorem problemEnergy0_planted {n : ℕ} (cs : Finset (Clause n))
    (hc : ∀ c ∈ cs, c.PlantedConsistent) (z : BitString n)
    (hz : z = zeros n ∨ z = ones n) :
    problemEnergy0 cs z = 0 := by
  classical
  unfold problemEnergy0
  have hempty : cs.filter (fun c => c.Violated z) = ∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro c hc_mem
    rcases hz with rfl | rfl
    · exact (planted_clause_satisfied_by_both c (hc c hc_mem)).1
    · exact (planted_clause_satisfied_by_both c (hc c hc_mem)).2
  rw [hempty]
  simp

theorem penalty_zeros_ones {n : ℕ} (p1 p2 p3 : Fin n) :
    penaltyTerm p1 p2 p3 (zeros n) = 1 / 2 ∧
    penaltyTerm p1 p2 p3 (ones n) = 0 := by
  classical
  constructor
  · simp [penaltyTerm, zeros]
  · unfold penaltyTerm
    simp [ones]

theorem problemEnergy_nonneg {n : ℕ} (cs : Finset (Clause n))
    (p1 p2 p3 : Fin n) (z : BitString n) : 0 ≤ problemEnergy cs p1 p2 p3 z := by
  classical
  have h0 : 0 ≤ problemEnergy0 cs z := Nat.cast_nonneg _
  unfold problemEnergy penaltyTerm
  split <;> linarith [show (0 : ℝ) ≤ 1 / 2 by norm_num]

theorem planted_pair_after_penalty {n : ℕ} (cs : Finset (Clause n))
    (hc : ∀ c ∈ cs, c.PlantedConsistent) (p1 p2 p3 : Fin n) :
    problemEnergy cs p1 p2 p3 (zeros n) = 1 / 2 ∧
    problemEnergy cs p1 p2 p3 (ones n) = 0 ∧
    (∀ z, 0 ≤ problemEnergy cs p1 p2 p3 z) := by
  classical
  refine ⟨?_, ?_, problemEnergy_nonneg cs p1 p2 p3⟩
  · unfold problemEnergy
    rw [problemEnergy0_planted cs hc (zeros n) (Or.inl rfl),
        (penalty_zeros_ones p1 p2 p3).1]
    norm_num
  · unfold problemEnergy
    rw [problemEnergy0_planted cs hc (ones n) (Or.inr rfl),
        (penalty_zeros_ones p1 p2 p3).2]
    norm_num

def hammingDist {n : ℕ} (a b : BitString n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => a i ≠ b i)).card

theorem planted_pair_hamming_far {n : ℕ} :
    hammingDist (zeros n) (ones n) = n := by
  classical
  unfold hammingDist zeros ones
  simp

def allAllowedClauses (n : ℕ) : Finset (Clause n) := by
  classical
  exact Finset.univ.filter Clause.PlantedConsistent

theorem mem_allAllowedClauses {n : ℕ} (c : Clause n) :
    c ∈ allAllowedClauses n ↔ c.PlantedConsistent := by
  classical
  unfold allAllowedClauses
  simp

theorem exists_allowed_clause_violated {n : ℕ} (z : BitString n)
    (hz0 : z ≠ zeros n) (hz1 : z ≠ ones n) :
    ∃ c : Clause n, c.PlantedConsistent ∧ c.Violated z := by
  classical
  have hex : ∃ i, z i = true := by
    by_contra h
    apply hz0
    funext i
    have : z i ≠ true := fun hh => h ⟨i, hh⟩
    simpa [zeros] using this
  have hey : ∃ j, z j = false := by
    by_contra h
    apply hz1
    funext i
    have : z i ≠ false := fun hh => h ⟨i, hh⟩
    simpa [ones] using this
  obtain ⟨i, hi⟩ := hex
  obtain ⟨j, hj⟩ := hey
  refine ⟨⟨i, i, j, true, true, false⟩, ?_, ?_⟩
  · constructor
    · intro h
      cases h.1
    · intro h
      cases h.2.2
  · exact ⟨hi, hi, hj⟩

theorem problemEnergy0_allAllowed_pos {n : ℕ} (z : BitString n)
    (hz0 : z ≠ zeros n) (hz1 : z ≠ ones n) :
    0 < problemEnergy0 (allAllowedClauses n) z := by
  classical
  obtain ⟨c, hc, hv⟩ := exists_allowed_clause_violated z hz0 hz1
  unfold problemEnergy0
  have hmem : c ∈ (allAllowedClauses n).filter (fun c => c.Violated z) := by
    rw [Finset.mem_filter]
    exact ⟨(mem_allAllowedClauses c).mpr hc, hv⟩
  have hpos : 0 < ((allAllowedClauses n).filter (fun c => c.Violated z)).card :=
    Finset.card_pos.mpr ⟨c, hmem⟩
  exact_mod_cast hpos

theorem problemEnergy0_allAllowed_eq_zero_iff {n : ℕ} (z : BitString n) :
    problemEnergy0 (allAllowedClauses n) z = 0 ↔ z = zeros n ∨ z = ones n := by
  classical
  constructor
  · intro h
    by_contra hne
    push Not at hne
    have hpos := problemEnergy0_allAllowed_pos z hne.1 hne.2
    linarith
  · rintro (rfl | rfl)
    · exact problemEnergy0_planted (allAllowedClauses n)
        (fun c hc => (mem_allAllowedClauses c).mp hc) (zeros n) (Or.inl rfl)
    · exact problemEnergy0_planted (allAllowedClauses n)
        (fun c hc => (mem_allAllowedClauses c).mp hc) (ones n) (Or.inr rfl)

theorem problemEnergy_allAllowed_eq_zero_iff {n : ℕ} (p1 p2 p3 : Fin n)
    (z : BitString n) :
    problemEnergy (allAllowedClauses n) p1 p2 p3 z = 0 ↔ z = ones n := by
  classical
  constructor
  · intro h
    by_contra hne
    rcases eq_or_ne z (zeros n) with hz0 | hz0
    · subst hz0
      unfold problemEnergy at h
      rw [problemEnergy0_planted (allAllowedClauses n)
            (fun c hc => (mem_allAllowedClauses c).mp hc) (zeros n) (Or.inl rfl),
          (penalty_zeros_ones p1 p2 p3).1] at h
      norm_num at h
    · have hpos := problemEnergy0_allAllowed_pos z hz0 hne
      unfold problemEnergy at h
      have hp : 0 ≤ penaltyTerm p1 p2 p3 z := by
        unfold penaltyTerm
        split <;> norm_num
      linarith
  · rintro rfl
    unfold problemEnergy
    rw [problemEnergy0_planted (allAllowedClauses n)
          (fun c hc => (mem_allAllowedClauses c).mp hc) (ones n) (Or.inr rfl),
        (penalty_zeros_ones p1 p2 p3).2]
    norm_num

end Qatlib.Papers.AdiabGaps09.MainResults
