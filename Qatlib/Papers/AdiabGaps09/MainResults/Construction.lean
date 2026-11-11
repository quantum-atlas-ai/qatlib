/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Planted clauses and a penalized energy

This module defines clauses by forbidden bit patterns, the two constant planted strings, and the
clause-count energy with an additional half-unit penalty. For the complete family
`allAllowedClauses`, it proves that exactly the two planted strings have zero unpenalized energy
and that only the all-one string has zero penalized energy, following the construction studied
in [FarhiEtAl2011].

## Main statements

* `planted_pair_after_penalty`: the planted energies are `1/2` and zero, and every energy is
  nonnegative.
* `planted_pair_hamming_far`: the planted strings differ at all `n` positions.
* `problemEnergy_allAllowed_eq_zero_iff`: the penalized complete clause family has a unique
  zero-energy string.

## References

* [Farhi et al., 2011][FarhiEtAl2011]
-/

set_option autoImplicit false
noncomputable section

open Finset

namespace Qatlib.Papers.AdiabGaps09.MainResults

/-- Boolean strings indexed by `Fin n`. -/
abbrev BitString (n : ℕ) := Fin n → Bool

/-- The bit string that is false at every position. -/
def zeros (n : ℕ) : BitString n := fun _ => false

/-- The bit string that is true at every position. -/
def ones (n : ℕ) : BitString n := fun _ => true

/-- Three positions and their forbidden Boolean values, describing when a clause is violated. -/
structure Clause (n : ℕ) where
  i1 : Fin n
  i2 : Fin n
  i3 : Fin n
  w1 : Bool
  w2 : Bool
  w3 : Bool
  deriving DecidableEq, Fintype

/-- The condition that the string matches all three forbidden values at the clause's specified
positions. -/
def Clause.Violated {n : ℕ} (c : Clause n) (z : BitString n) : Prop :=
  z c.i1 = c.w1 ∧ z c.i2 = c.w2 ∧ z c.i3 = c.w3

/-- The condition that the clause's forbidden triple is neither all false nor all true. -/
def Clause.PlantedConsistent {n : ℕ} (c : Clause n) : Prop :=
  ¬ (c.w1 = false ∧ c.w2 = false ∧ c.w3 = false) ∧
  ¬ (c.w1 = true ∧ c.w2 = true ∧ c.w3 = true)

/-- A clause whose forbidden triple is neither constant triple is violated by neither the
all-zero nor the all-one string. See [FarhiEtAl2011]. -/
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

/-- The real-valued number of clauses in `cs` violated by the string `z`. -/
def problemEnergy0 {n : ℕ} (cs : Finset (Clause n)) (z : BitString n) : ℝ := by
  classical
  exact ((cs.filter (fun c => c.Violated z)).card : ℝ)

/-- The penalty equal to `1/2` when all three selected bits are false and zero otherwise. -/
def penaltyTerm {n : ℕ} (p1 p2 p3 : Fin n) (z : BitString n) : ℝ :=
  if z p1 = false ∧ z p2 = false ∧ z p3 = false then (1 / 2 : ℝ) else 0

/-- The clause-count energy plus the half-unit penalty at the three selected positions. -/
def problemEnergy {n : ℕ} (cs : Finset (Clause n))
    (p1 p2 p3 : Fin n) (z : BitString n) : ℝ :=
  problemEnergy0 cs z + penaltyTerm p1 p2 p3 z

/-- Either constant planted string has zero clause-count energy when every clause is
planted-consistent. -/
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

/-- The penalty is `1/2` on the all-zero string and zero on the all-one string. -/
theorem penalty_zeros_ones {n : ℕ} (p1 p2 p3 : Fin n) :
    penaltyTerm p1 p2 p3 (zeros n) = 1 / 2 ∧
    penaltyTerm p1 p2 p3 (ones n) = 0 := by
  classical
  constructor
  · simp [penaltyTerm, zeros]
  · unfold penaltyTerm
    simp [ones]

/-- The penalized clause energy is nonnegative for every bit string. -/
theorem problemEnergy_nonneg {n : ℕ} (cs : Finset (Clause n))
    (p1 p2 p3 : Fin n) (z : BitString n) : 0 ≤ problemEnergy cs p1 p2 p3 z := by
  classical
  have h0 : 0 ≤ problemEnergy0 cs z := Nat.cast_nonneg _
  unfold problemEnergy penaltyTerm
  split <;> linarith [show (0 : ℝ) ≤ 1 / 2 by norm_num]

/-- For planted-consistent clauses, the all-zero string has energy `1/2`, the all-one string has
energy zero, and all strings have nonnegative energy. See [FarhiEtAl2011]. -/
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

/-- The number of positions at which two bit strings differ. -/
def hammingDist {n : ℕ} (a b : BitString n) : ℕ := by
  classical
  exact (Finset.univ.filter (fun i => a i ≠ b i)).card

/-- The Hamming distance between the all-zero and all-one strings is `n`. See [FarhiEtAl2011]. -/
theorem planted_pair_hamming_far {n : ℕ} :
    hammingDist (zeros n) (ones n) = n := by
  classical
  unfold hammingDist zeros ones
  simp

/-- The finite set of all clauses whose forbidden triples are neither all false nor all true. -/
def allAllowedClauses (n : ℕ) : Finset (Clause n) := by
  classical
  exact Finset.univ.filter Clause.PlantedConsistent

/-- A clause belongs to `allAllowedClauses n` exactly when it is planted-consistent. -/
theorem mem_allAllowedClauses {n : ℕ} (c : Clause n) :
    c ∈ allAllowedClauses n ↔ c.PlantedConsistent := by
  classical
  unfold allAllowedClauses
  simp

/-- Every bit string different from both constant planted strings violates some
planted-consistent clause. See [FarhiEtAl2011]. -/
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

/-- A bit string different from both planted strings has strictly positive clause-count energy
for the complete allowed clause family. See [FarhiEtAl2011]. -/
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

/-- For the complete allowed clause family, the clause-count energy is zero exactly on the two
constant planted strings. See [FarhiEtAl2011]. -/
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

/-- For the complete allowed clause family with the stated penalty, the energy is zero exactly
on the all-one string. See [FarhiEtAl2011]. -/
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
