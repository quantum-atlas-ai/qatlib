/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.SearchCircuit
import Qatlib.Concepts.SearchStopping.GroverSuccess.Lemma1RestrictedTigh
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SearchStopping.GroverSuccess

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery

open scoped BigOperators
open Qatlib

noncomputable def RandomizedSuccess {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (m : ℕ) : ℝ :=
  (∑ j ∈ Finset.range m, MeasureProb (SearchState A j) A) / (m : ℝ)

noncomputable def MeanQueries (I : Type*) [Fintype I] [DecidableEq I] (m : ℕ) : ℝ :=
  (∑ j ∈ Finset.range m, (QueryCount (SearchCircuit I j) : ℝ)) / (m : ℝ)

theorem search_randomized_angle {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hθ : (Real.sin θ)^2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (h2 : 0 < Real.sin (2 * θ)) (m : ℕ) (hm : 0 < m) :
    RandomizedSuccess A m = 1 / 2 - Real.sin (4 * m * θ) / (4 * m * Real.sin (2 * θ)) ∧
    MeanQueries I m = ((m : ℝ) - 1) / 2 ∧
    (1 / Real.sin (2 * θ) ≤ (m : ℝ) → 1 / 4 ≤ RandomizedSuccess A m) := by
  have hs : Real.sin θ ≠ 0 := by
    intro h
    have h' := h2
    simp [Real.sin_two_mul, h] at h'
  have hc : Real.cos θ ≠ 0 := by
    intro h
    have h' := h2
    simp [Real.sin_two_mul, h] at h'
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hmr
  have hP : RandomizedSuccess A m =
      1 / 2 - Real.sin (4 * m * θ) / (4 * m * Real.sin (2 * θ)) := by
    have hf (j : ℕ) : (Real.sin ((2 * j + 1) * θ))^2 =
        (1 - Real.cos ((2 * j + 1) * (2 * θ))) / 2 := by
      have hcos := Real.cos_two_mul ((2 * j + 1) * θ)
      have ha : 2 * ((2 * (j : ℝ) + 1) * θ) = (2 * j + 1) * (2 * θ) := by ring
      rw [ha] at hcos
      nlinarith [Real.sin_sq_add_cos_sq ((2 * j + 1) * θ)]
    have odd := lemma1_odd_cosine_sum (2 * θ) m (ne_of_gt h2)
    rw [show 2 * (m : ℝ) * (2 * θ) = 4 * m * θ by ring] at odd
    unfold RandomizedSuccess
    simp_rw [search_grover_success hN A θ hθ hs hc, hf, sub_div]
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [← Finset.sum_div, odd]
    field_simp
    ring
  have hQ : MeanQueries I m = ((m : ℝ) - 1) / 2 := by
    have hq (j : ℕ) : QueryCount (SearchCircuit I j) = j :=
      (search_circuit_laws hN A j).1
    have hsum (n : ℕ) : (∑ j ∈ Finset.range n, (j : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        push_cast
        ring
    unfold MeanQueries
    simp_rw [hq]
    rw [hsum]
    field_simp
  refine ⟨hP, hQ, ?_⟩
  intro threshold
  rw [hP]
  have ht : 1 ≤ (m : ℝ) * Real.sin (2 * θ) := (div_le_iff₀ h2).mp threshold
  have hd : 0 < 4 * (m : ℝ) * Real.sin (2 * θ) := by positivity
  have hf : Real.sin (4 * m * θ) / (4 * m * Real.sin (2 * θ)) ≤ 1 / 4 := by
    apply (div_le_iff₀ hd).2
    nlinarith [Real.sin_le_one (4 * m * θ)]
  linarith

theorem search_randomized_search_contract {I : Type*} [Fintype I] [DecidableEq I]
    (A : Finset I) (hA : 0 < A.card) (hproper : A.card < Fintype.card I)
    (m : ℕ) (hm : 0 < m) :
    ∃ θ : ℝ, 0 < θ ∧ θ < Real.pi / 2 ∧
      (Real.sin θ)^2 = (A.card : ℝ) / (Fintype.card I : ℝ) ∧
      RandomizedSuccess A m = 1 / 2 - Real.sin (4 * m * θ) / (4 * m * Real.sin (2 * θ)) ∧
      MeanQueries I m = ((m : ℝ) - 1) / 2 ∧
      (1 / Real.sin (2 * θ) ≤ (m : ℝ) → 1 / 4 ≤ RandomizedSuccess A m) := by
  obtain ⟨θ, hθ0, hθp, hθ, h2⟩ := search_principal_angle A hA hproper
  exact ⟨θ, hθ0, hθp, hθ,
    search_randomized_angle (lt_trans hA hproper) A θ hθ h2 m hm⟩

end Qatlib.Concepts.QueryComplexity.AdaptiveQuery
