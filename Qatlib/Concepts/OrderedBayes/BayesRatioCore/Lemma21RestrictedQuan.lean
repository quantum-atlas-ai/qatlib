/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.Omega
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.Lemma21RestrictedStat

open scoped BigOperators

namespace Qatlib.Concepts.OrderedBayes.BayesRatioCore

lemma zoo_bayes_prefix_mass_step {n : ℕ} (a : Fin n → ℝ) {k : ℕ} (hk : k < n) :
    (∑ i : Fin n, if i.val < k + 1 then a i else 0) =
      (∑ i : Fin n, if i.val < k then a i else 0) + a ⟨k, hk⟩ := by
  have hpoint : ∀ i : Fin n,
      (if i.val < k + 1 then a i else 0) =
        (if i.val < k then a i else 0) + (if i.val = k then a i else 0) := by
    intro i
    by_cases h1 : i.val < k
    · rw [if_pos (Nat.lt_trans h1 (Nat.lt_succ_self k)), if_pos h1, if_neg (Nat.ne_of_lt h1),
        add_zero]
    · by_cases h2 : i.val = k
      · rw [if_pos (show i.val < k + 1 by omega), if_neg h1, if_pos h2, zero_add]
      · rw [if_neg (show ¬ i.val < k + 1 by omega), if_neg h1, if_neg h2, add_zero]
  calc (∑ i : Fin n, if i.val < k + 1 then a i else 0)
      = ∑ i : Fin n, ((if i.val < k then a i else 0) + (if i.val = k then a i else 0)) :=
        Finset.sum_congr rfl fun i _ => hpoint i
    _ = (∑ i : Fin n, if i.val < k then a i else 0) +
          (∑ i : Fin n, if i.val = k then a i else 0) := Finset.sum_add_distrib
    _ = (∑ i : Fin n, if i.val < k then a i else 0) + a ⟨k, hk⟩ := by
        congr 1
        refine (Finset.sum_eq_single ⟨k, hk⟩ ?_ ?_).trans (by simp)
        · intro j _ hj
          have hjval : j.val ≠ k := fun hv => hj (Fin.ext hv)
          simp [hjval]
        · intro h
          exact absurd (Finset.mem_univ _) h

lemma zoo_bayes_prefix_mass_zero {n : ℕ} (a : Fin n → ℝ) :
    (∑ i : Fin n, if i.val < 0 then a i else 0) = 0 := by
  simp

lemma zoo_bayes_prefix_mass_total {n : ℕ} (a : Fin n → ℝ) :
    (∑ i : Fin n, if i.val < n then a i else 0) = ∑ i : Fin n, a i :=
  Finset.sum_congr rfl fun i _ => if_pos i.isLt

lemma zoo_bayes_prefix_mass_one {n : ℕ} (a : Fin n → ℝ) (hn : 0 < n) :
    (∑ i : Fin n, if i.val < 1 then a i else 0) = a ⟨0, hn⟩ := by
  refine (Finset.sum_eq_single ⟨0, hn⟩ ?_ ?_).trans (by simp)
  · intro j _ hj
    have hjval : ¬ j.val < 1 := by
      have hne : j.val ≠ 0 := fun hv => hj (Fin.ext hv)
      omega
    simp [hjval]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem zoo_bayes_prefix_mass_threshold :
    ∀ (n : ℕ) (a : Fin n → ℝ) (ε : ℝ),
      0 < ε → ε ≤ 1 / 2 → (∀ i, 0 ≤ a i) → (∑ i, a i) = 1 → (∀ i, a i < ε) →
      ∃ k : ℕ, 0 < k ∧ k < n ∧
        1 / 2 - ε ≤ (∑ i : Fin n, if i.val < k then a i else 0) ∧
        (∑ i : Fin n, if i.val < k then a i else 0) < 1 / 2 := by
  intro n a ε hεpos hεhalf _hanonneg hsum hsmall
  classical
  have hn : 0 < n := by
    by_contra h
    push Not at h
    have hn0 : n = 0 := Nat.le_zero.mp h
    subst hn0
    simp at hsum

  set S : Finset ℕ := (Finset.range (n + 1)).filter
    (fun m => (∑ i : Fin n, if i.val < m then a i else 0) < 1 / 2) with hSdef
  have h0S : 0 ∈ S := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.succ_pos n, by rw [zoo_bayes_prefix_mass_zero]; norm_num⟩
  have h1S : 1 ∈ S := by
    simp only [hSdef, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, by
      rw [zoo_bayes_prefix_mass_one a hn]
      exact lt_of_lt_of_le (hsmall ⟨0, hn⟩) hεhalf⟩

  set k : ℕ := S.max' ⟨0, h0S⟩ with hkdef
  clear_value k
  have hkmem : k ∈ S := by
    rw [hkdef]
    exact Finset.max'_mem _ _
  have hkle : ∀ m ∈ S, m ≤ k := by
    rw [hkdef]
    exact fun m hm => Finset.le_max' _ m hm
  have hk1 : 1 ≤ k := hkle 1 h1S
  have hkmem' : k < n + 1 ∧ (∑ i : Fin n, if i.val < k then a i else 0) < 1 / 2 := by
    have h := hkmem
    simp only [hSdef, Finset.mem_filter, Finset.mem_range] at h
    exact h
  obtain ⟨hkrange, hkP⟩ := hkmem'
  have hkn : k ≠ n := by
    intro h
    subst h
    rw [zoo_bayes_prefix_mass_total, hsum] at hkP
    norm_num at hkP
  have hklt : k < n := by omega

  have hge : 1 / 2 ≤ (∑ i : Fin n, if i.val < k + 1 then a i else 0) := by
    by_contra h
    push Not at h
    have hmem : k + 1 ∈ S := by
      simp only [hSdef, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, h⟩
    have hle := hkle (k + 1) hmem
    omega
  have hlower : 1 / 2 - ε ≤ (∑ i : Fin n, if i.val < k then a i else 0) := by
    rw [zoo_bayes_prefix_mass_step a hklt] at hge
    have hak : a ⟨k, hklt⟩ < ε := hsmall _
    linarith
  exact ⟨k, hk1, hklt, hlower, hkP⟩

theorem zoo_bayes_prefix_mass_threshold_matches_contract :
    Lemma21RestrictedSpec.expected :=
  zoo_bayes_prefix_mass_threshold

end Qatlib.Concepts.OrderedBayes.BayesRatioCore
