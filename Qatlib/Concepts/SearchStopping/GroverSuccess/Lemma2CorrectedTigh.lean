/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.GroverSuccess.Lemma2CorrectedStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QueryComplexity.AdaptiveQuery
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Concepts.SearchStopping.GroverSuccess

theorem search_randomized_formula {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hd : Real.sin θ ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (h2 : Real.sin (2*θ) ≠ 0) (m : ℕ) (hm : 0 < m) :
    RandomizedSuccess A m = 1/2 - Real.sin (4*m*θ)/(4*m*Real.sin (2*θ)) := by
  by_cases hpos : 0 < Real.sin (2*θ)
  · exact (search_randomized_angle hN A θ hd hpos m hm).1
  · have hneg : Real.sin (2*θ) < 0 := lt_of_le_of_ne (le_of_not_gt hpos) h2
    have hminus : Real.sin (-θ)^2 = (A.card : ℝ)/(Fintype.card I : ℝ) := by
      simpa only [Real.sin_neg, neg_sq] using hd
    have hs : 0 < Real.sin (2*(-θ)) := by
      rw [show 2*(-θ) = -(2*θ) by ring, Real.sin_neg]
      linarith
    have h := (search_randomized_angle hN A (-θ) hminus hs m hm).1
    rw [show 4*(m : ℝ)*(-θ) = -(4*m*θ) by ring, Real.sin_neg,
      show 2*(-θ) = -(2*θ) by ring, Real.sin_neg] at h
    simpa only [mul_neg, neg_div_neg_eq] using h

theorem search_randomized_singular {I : Type*} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (θ : ℝ)
    (hd : Real.sin θ ^ 2 = (A.card : ℝ) / (Fintype.card I : ℝ))
    (h2 : Real.sin (2*θ) = 0) (m : ℕ) (hm : 0 < m) :
    RandomizedSuccess A m = (A.card : ℝ) / (Fintype.card I : ℝ) := by
  have hNr : (Fintype.card I : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hprod : Real.sin θ * Real.cos θ = 0 := by
    rw [Real.sin_two_mul] at h2
    nlinarith
  rcases mul_eq_zero.mp hprod with hs | hc
  · have hcardr : (A.card : ℝ) = 0 := by
      have h := (eq_div_iff hNr).mp hd
      rw [hs] at h
      nlinarith
    have hcard : A.card = 0 := by exact_mod_cast hcardr
    have hA : A = ∅ := Finset.card_eq_zero.mp hcard
    subst A
    simp [search_randomized_empty]
  · have hsin : Real.sin θ ^ 2 = 1 := by
      have h := Real.sin_sq_add_cos_sq θ
      rw [hc] at h
      nlinarith
    have hcardr : (A.card : ℝ) = Fintype.card I := by
      have h := (eq_div_iff hNr).mp hd
      rw [hsin] at h
      linarith
    have hcard : A.card = Fintype.card I := by exact_mod_cast hcardr
    have hA : A = Finset.univ := (Finset.card_eq_iff_eq_univ A).mp hcard
    subst A
    rw [search_randomized_univ hN m hm]
    simp [hNr]

universe u

theorem lemma2Corrected : Lemma2Corrected.{u} := by
  intro I _ _ hN A θ hd m hm
  constructor
  · by_cases h2 : Real.sin (2*θ) = 0
    · rw [if_pos h2]
      exact search_randomized_singular hN A θ hd h2 m hm
    · rw [if_neg h2]
      exact search_randomized_formula hN A θ hd h2 m hm
  · intro h2 ht
    exact (search_randomized_angle hN A θ hd h2 m hm).2.2 ht

end Qatlib.Concepts.SearchStopping.GroverSuccess
