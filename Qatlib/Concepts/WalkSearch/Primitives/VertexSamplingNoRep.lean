/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Primitives.Lemma4Intersection
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Nat.Log
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Concepts.WalkSearch.Primitives

open Qatlib.Concepts.WalkSearch.Primitives

variable {n : ℕ}

def commonNbrs (G : Finset (Fin n × Fin n)) (a b : Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun x => (a, x) ∈ G ∧ (b, x) ∈ G

def thickPairs (G : Finset (Fin n × Fin n)) (ε : ℝ) : Finset (Fin n × Fin n) :=
  (Finset.univ : Finset (Fin n × Fin n)).filter
    fun p => (n : ℝ) ^ (1 - ε) ≤ (commonNbrs G p.1 p.2).card

def survivingSamplings (G : Finset (Fin n × Fin n)) (ε : ℝ) (k : ℕ) :
    Finset (Finset (Fin n)) :=
  (thickPairs G ε).biUnion fun p => avoidingSubsets (commonNbrs G p.1 p.2) k

theorem per_pair_survival_card (G : Finset (Fin n × Fin n)) (a b : Fin n) {ε : ℝ} {k : ℕ}
    (hn : 1 < n) (hX : (n : ℝ) ^ (1 - ε) ≤ (commonNbrs G a b).card)
    (hk : 4 * (n : ℝ) ^ ε * ((Nat.log 2 n : ℝ) + 1) ≤ (k : ℝ)) (hkn : k ≤ n)
    (hpos : 0 < n.choose k) :
    (avoidingSubsets (commonNbrs G a b) k).card * n ^ 3 ≤ n.choose k :=
  lemma3_per_edge_avoid_card (commonNbrs G a b) (ε := ε) (m := k) hn hX hk hkn hpos

theorem thickPairs_card_le (G : Finset (Fin n × Fin n)) (ε : ℝ) :
    (thickPairs G ε).card ≤ n * n := by
  have hle : (thickPairs G ε).card ≤ (Finset.univ : Finset (Fin n × Fin n)).card :=
    Finset.card_le_card (Finset.filter_subset _ _)
  simpa [Finset.card_univ, Fintype.card_prod] using hle

theorem lemma3_union_bound (G : Finset (Fin n × Fin n)) {ε : ℝ} {k : ℕ}
    (hn : 1 < n) (hk : 4 * (n : ℝ) ^ ε * ((Nat.log 2 n : ℝ) + 1) ≤ (k : ℝ)) (hkn : k ≤ n)
    (hpos : 0 < n.choose k) :
    (survivingSamplings G ε k).card * n ≤ n.choose k := by
  classical
  have hnpos : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this

  have hcard_le : ((survivingSamplings G ε k).card : ℝ) ≤
      ∑ p ∈ thickPairs G ε,
        ((avoidingSubsets (commonNbrs G p.1 p.2) k).card : ℝ) := by
    rw [survivingSamplings]
    calc (((thickPairs G ε).biUnion fun p => avoidingSubsets (commonNbrs G p.1 p.2) k).card : ℝ)
        ≤ ((∑ p ∈ thickPairs G ε,
            (avoidingSubsets (commonNbrs G p.1 p.2) k).card) : ℕ) := by
          exact_mod_cast Finset.card_biUnion_le
      _ = ∑ p ∈ thickPairs G ε,
            ((avoidingSubsets (commonNbrs G p.1 p.2) k).card : ℝ) := by push_cast; ring

  have hsum_le : (∑ p ∈ thickPairs G ε,
        ((avoidingSubsets (commonNbrs G p.1 p.2) k).card : ℝ) * (n : ℝ) ^ 3) ≤
      ∑ _p ∈ thickPairs G ε, (n.choose k : ℝ) := by
    refine Finset.sum_le_sum fun p hp => ?_
    have hX : (n : ℝ) ^ (1 - ε) ≤ (commonNbrs G p.1 p.2).card := (Finset.mem_filter.mp hp).2
    have hcard := per_pair_survival_card G p.1 p.2 hn hX hk hkn hpos
    exact_mod_cast hcard

  have hsum_eq : (∑ p ∈ thickPairs G ε,
        ((avoidingSubsets (commonNbrs G p.1 p.2) k).card : ℝ) * (n : ℝ) ^ 3) =
      (∑ p ∈ thickPairs G ε,
        ((avoidingSubsets (commonNbrs G p.1 p.2) k).card : ℝ)) * (n : ℝ) ^ 3 := by
    rw [Finset.sum_mul]
  have hconst : (∑ _p ∈ thickPairs G ε, (n.choose k : ℝ)) =
      (thickPairs G ε).card * (n.choose k : ℝ) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have hthick : ((thickPairs G ε).card : ℝ) ≤ (n : ℝ) * (n : ℝ) := by
    have := thickPairs_card_le G ε
    exact_mod_cast this
  have hmul : ((survivingSamplings G ε k).card : ℝ) * (n : ℝ) ^ 3 ≤
      (n.choose k : ℝ) * (n : ℝ) ^ 2 := by
    have h1 : ((survivingSamplings G ε k).card : ℝ) * (n : ℝ) ^ 3 ≤
        (∑ p ∈ thickPairs G ε,
          ((avoidingSubsets (commonNbrs G p.1 p.2) k).card : ℝ)) * (n : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_right hcard_le (by positivity)
    rw [← hsum_eq] at h1
    have h2 : (∑ p ∈ thickPairs G ε,
          ((avoidingSubsets (commonNbrs G p.1 p.2) k).card : ℝ) * (n : ℝ) ^ 3) ≤
        (n.choose k : ℝ) * (n : ℝ) ^ 2 := by
      refine hsum_le.trans ?_
      rw [hconst]
      have hck : (0 : ℝ) ≤ (n.choose k : ℝ) := by positivity
      calc (thickPairs G ε).card * (n.choose k : ℝ)
          ≤ ((n : ℝ) * (n : ℝ)) * (n.choose k : ℝ) := by
            apply mul_le_mul_of_nonneg_right hthick hck
        _ = (n.choose k : ℝ) * (n : ℝ) ^ 2 := by ring
    exact h1.trans h2

  have hcancel : ((survivingSamplings G ε k).card : ℝ) * (n : ℝ) ≤ (n.choose k : ℝ) := by
    have hsq : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
    have hrew : ((survivingSamplings G ε k).card : ℝ) * (n : ℝ) ^ 3 =
        (((survivingSamplings G ε k).card : ℝ) * (n : ℝ)) * (n : ℝ) ^ 2 := by ring
    rw [hrew] at hmul
    exact le_of_mul_le_mul_right hmul hsq
  exact_mod_cast hcancel

theorem lemma3_failure_prob (G : Finset (Fin n × Fin n)) {ε : ℝ} {k : ℕ}
    (hn : 1 < n) (hk : 4 * (n : ℝ) ^ ε * ((Nat.log 2 n : ℝ) + 1) ≤ (k : ℝ)) (hkn : k ≤ n)
    (hpos : 0 < n.choose k) :
    ((survivingSamplings G ε k).card : ℝ) / (n.choose k : ℝ) ≤ 1 / (n : ℝ) := by
  have h := lemma3_union_bound G hn hk hkn hpos
  have hcast : ((survivingSamplings G ε k).card : ℝ) * (n : ℝ) ≤ (n.choose k : ℝ) := by
    exact_mod_cast h
  have hposR : (0 : ℝ) < (n.choose k : ℝ) := by exact_mod_cast hpos
  have hnR : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := by omega
    exact_mod_cast this
  exact (div_le_div_iff₀ hposR hnR).mpr (by simpa using hcast)

end Qatlib.Concepts.WalkSearch.Primitives
