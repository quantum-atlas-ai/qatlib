/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.MainResults.Theorem3DecayIdentity
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.MainResults

open Finset Matrix

def QcmaWitnessPattern {ι : Type*} (alpha_sq : ι → ℝ) (inL : Prop) : Prop :=
  (inL → ∃ y, 2 / 3 ≤ alpha_sq y) ∧ (¬ inL → ∀ y, alpha_sq y ≤ 1 / 3)

def witnessPairVertex (j : ℕ) : ℕ := 2 * j

lemma witnessPairVertex_injective : Function.Injective witnessPairVertex := by
  intro a b h
  unfold witnessPairVertex at h
  omega

lemma witnessPairVertex_lt (j : ℕ) : witnessPairVertex j < witnessPairVertex j + 1 :=
  Nat.lt_succ_self _

theorem theorem4_slow_decay_witness {ι : Type*}
    (alpha_sq c : ι → ℝ) (mu T M : ℝ) (hM : 0 < M)
    (hlow : ∀ j, alpha_sq j / M * Real.exp (-(mu * T)) ≤ c j)
    (j : ι) (hwit : 2 / 3 ≤ alpha_sq j) :
    2 / (3 * M) * Real.exp (-(mu * T)) ≤ c j :=
  decay_bound_not_in_L hM hwit (hlow j)

theorem theorem4_fast_decay_all {ι : Type*}
    (alpha_sq c : ι → ℝ) (mu nu T M : ℝ) (hM : 0 < M)
    (hslow : ∀ j, c j ≤ alpha_sq j / M * Real.exp (-(mu * T)) + Real.exp (-(nu * T)))
    (hfast : Real.exp (-(nu * T)) = (1 / (6 * M)) * Real.exp (-(mu * T)))
    (halpha : ∀ j, alpha_sq j ≤ 1 / 3) :
    ∀ j, c j ≤ 1 / (2 * M) * Real.exp (-(mu * T)) :=
  fun j => decay_bound_in_L hM (halpha j) (hslow j) hfast

theorem theorem4_qcma_decision_reduction {ι : Type*}
    (alpha_sq c : ι → ℝ) (mu nu T M a b : ℝ) (hM : 0 < M)
    (hfast : Real.exp (-(nu * T)) = (1 / (6 * M)) * Real.exp (-(mu * T)))
    (hslow : ∀ j, c j ≤ alpha_sq j / M * Real.exp (-(mu * T)) + Real.exp (-(nu * T)))
    (hlow : ∀ j, alpha_sq j / M * Real.exp (-(mu * T)) ≤ c j)
    (ha : a ≤ 2 / (3 * M)) (hb : 1 / (2 * M) ≤ b)
    (inL : Prop) (hqcma : QcmaWitnessPattern alpha_sq inL) :
    (inL → ∃ j, a * Real.exp (-(mu * T)) ≤ c j) ∧
      (¬ inL → ∀ j, c j ≤ b * Real.exp (-(mu * T))) := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨j, hj⟩ := hqcma.1 h
    have h1 := theorem4_slow_decay_witness alpha_sq c mu T M hM hlow j hj
    have h2 : a * Real.exp (-(mu * T)) ≤ 2 / (3 * M) * Real.exp (-(mu * T)) :=
      mul_le_mul_of_nonneg_right ha (le_of_lt (Real.exp_pos _))
    exact ⟨j, by linarith⟩
  · intro h j
    have h1 := theorem4_fast_decay_all alpha_sq c mu nu T M hM hslow hfast (hqcma.2 h) j
    have h2 : 1 / (2 * M) * Real.exp (-(mu * T)) ≤ b * Real.exp (-(mu * T)) :=
      mul_le_mul_of_nonneg_right hb (le_of_lt (Real.exp_pos _))
    linarith

theorem theorem4_answers_exclusive {ι : Type*} (c : ι → ℝ) (a b e : ℝ)
    (hba : b < a) (he : 0 < e) :
    ¬ ((∃ j, a * e ≤ c j) ∧ (∀ j, c j ≤ b * e)) := by
  rintro ⟨⟨j, hj⟩, hall⟩
  have hlt : b * e < a * e := mul_lt_mul_of_pos_right hba he
  linarith [hall j, hj]

theorem theorem4_no_slow_pair_of_no_witness {ι : Type*} (c : ι → ℝ) (mu T M : ℝ)
    (hM : 0 < M)
    (hupper : ∀ j, c j ≤ 1 / (2 * M) * Real.exp (-(mu * T))) :
    ¬ ∃ j, 2 / (3 * M) * Real.exp (-(mu * T)) ≤ c j := by
  rintro ⟨j, hj⟩
  have he : 0 < Real.exp (-(mu * T)) := Real.exp_pos _
  have hlt := mul_lt_mul_of_pos_right (decay_thresholds_ordered hM) he
  linarith [hupper j, hj]

end Qatlib.Papers.BQPMixSparse06.MainResults
