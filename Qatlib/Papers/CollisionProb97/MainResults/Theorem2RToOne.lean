/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.CollisionProb97.MainResults.CollisionCounting
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.CollisionProb97.MainResults

open scoped BigOperators

universe u

theorem sqrt_div_rToOne_le {N : ℝ} {r k : ℕ} (hN : 0 < N) (hr : 2 ≤ r) (hk : 1 ≤ k) :
    Real.sqrt (N / (((r : ℝ) - 1) * (k : ℝ)))
      ≤ Real.sqrt 2 * Real.sqrt (N / ((r : ℝ) * (k : ℝ))) := by
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hkpos : 0 < (k : ℝ) := by linarith
  have hrpos : 0 < (r : ℝ) := by linarith
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hden1 : 0 < ((r : ℝ) - 1) * (k : ℝ) := mul_pos hrm1 hkpos
  have hden2 : 0 < (r : ℝ) * (k : ℝ) := mul_pos hrpos hkpos
  have hck : (r : ℝ) * (k : ℝ) / 2 ≤ ((r : ℝ) - 1) * (k : ℝ) := by nlinarith
  have hle : N / (((r : ℝ) - 1) * (k : ℝ)) ≤ 2 * (N / ((r : ℝ) * (k : ℝ))) := by
    have h1 : N / (((r : ℝ) - 1) * (k : ℝ))
        ≤ N / ((r : ℝ) * (k : ℝ) / 2) :=
      div_le_div_of_nonneg_left hN.le (by positivity) hck
    have h2 : N / ((r : ℝ) * (k : ℝ) / 2) = 2 * (N / ((r : ℝ) * (k : ℝ))) := by
      field_simp
    linarith
  calc Real.sqrt (N / (((r : ℝ) - 1) * (k : ℝ)))
      ≤ Real.sqrt (2 * (N / ((r : ℝ) * (k : ℝ)))) := Real.sqrt_le_sqrt hle
    _ = Real.sqrt 2 * Real.sqrt (N / ((r : ℝ) * (k : ℝ))) :=
        Real.sqrt_mul (by norm_num) _

theorem rToOne_count_and_budget (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {X Y : Type u} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
        (F : X → Y) (r : ℕ) (K : Finset X),
        RToOne F r → 2 ≤ r → 0 < Fintype.card X →
        1 ≤ K.card → K.card ≤ Fintype.card X →
        Set.InjOn F (K : Set X) →
        (collisionCandidates F K).card = (r - 1) * K.card ∧
        (∀ x1 ∈ collisionCandidates F K, ∃ x0 ∈ K, x0 ≠ x1 ∧ F x0 = F x1) ∧
        proposedCollisionBudget (groverCoefficient l) (Fintype.card X)
            ((r - 1) * K.card) K.card
          ≤ C * (K.card + Real.sqrt ((Fintype.card X : ℝ) / ((r : ℝ) * K.card))) ∧
        proposedRecordCount K.card = K.card := by
  refine ⟨groverCoefficient l * Real.sqrt 2 + 2, by
    have hg := groverCoefficient_pos l hl hl4
    have hs := Real.sqrt_nonneg (2 : ℝ)
    nlinarith, ?_⟩
  intro X Y _ _ _ _ F r K hF hr hN hk hkN hinj
  have hcount : (collisionCandidates F K).card = (r - 1) * K.card :=
    collisionCandidates_card F r hF K hinj
  refine ⟨hcount, ?_, ?_, proposedRecordCount_eq K.card⟩
  · intro x1 hx1
    exact collisionCandidates_spec F K hx1
  · have hk1 : (1 : ℝ) ≤ (K.card : ℝ) := by exact_mod_cast hk
    have hNpos : (0 : ℝ) < (Fintype.card X : ℝ) := by exact_mod_cast hN
    have hNpos' : (0 : ℝ) < Fintype.card X := by exact_mod_cast hN
    have hg : 0 < groverCoefficient l := groverCoefficient_pos l hl hl4
    have hsq := sqrt_div_rToOne_le (N := (Fintype.card X : ℝ)) hNpos hr hk
    have hgs : groverCoefficient l * Real.sqrt ((Fintype.card X : ℝ) / (((r : ℝ) - 1) * K.card))
        ≤ groverCoefficient l *
          (Real.sqrt 2 * Real.sqrt ((Fintype.card X : ℝ) / ((r : ℝ) * K.card))) :=
      mul_le_mul_of_nonneg_left hsq hg.le
    have hcoef : 0 ≤ groverCoefficient l * Real.sqrt 2 :=
      mul_nonneg hg.le (Real.sqrt_nonneg _)
    have hsig : 0 ≤ Real.sqrt ((Fintype.card X : ℝ) / ((r : ℝ) * K.card)) :=
      Real.sqrt_nonneg _
    have hck : 0 ≤ groverCoefficient l * Real.sqrt 2 * (K.card : ℝ) :=
      mul_nonneg hcoef (by linarith)
    unfold proposedCollisionBudget
    nlinarith [hgs]

theorem rToOne_cubeRoot {N k : ℝ} {r : ℕ} (hr : 0 < r) (hk : 1 ≤ k)
    (hcube : k ^ 3 = N / (r : ℝ)) :
    k + Real.sqrt (N / ((r : ℝ) * k)) = 2 * k := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hNk : N / ((r : ℝ) * k) = k ^ 2 := by
    have hN : N = (r : ℝ) * k ^ 3 := by
      rw [eq_div_iff hrpos.ne'] at hcube
      rw [← hcube, mul_comm]
    rw [hN]
    field_simp
  rw [hNk, Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
  ring

theorem rToOne_real_cube_budget (l : ℝ) (hl : 1 < l) (hl4 : l < 4 / 3)
    {N k : ℝ} {r : ℕ} (hr : 2 ≤ r) (hk : 1 ≤ k) (hcube : k ^ 3 = N / (r : ℝ)) :
    proposedCollisionBudget (groverCoefficient l) N (((r : ℝ) - 1) * k) k
      ≤ (groverCoefficient l * Real.sqrt 2 + 2) * k := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hrm1 : 0 < (r : ℝ) - 1 := by linarith
  have hden : 0 < ((r : ℝ) - 1) * k := mul_pos hrm1 hkpos
  have hN : N = (r : ℝ) * k ^ 3 := by
    rw [eq_div_iff hrpos.ne'] at hcube
    rw [← hcube, mul_comm]
  have hle : N / (((r : ℝ) - 1) * k) ≤ 2 * k ^ 2 := by
    rw [hN, div_le_iff₀ hden]
    have hk3 : (0 : ℝ) ≤ k ^ 3 := (pow_pos hkpos 3).le
    have hfac : (0 : ℝ) ≤ k ^ 3 * ((r : ℝ) - 2) := mul_nonneg hk3 (by linarith)
    nlinarith [hfac]
  have hs : Real.sqrt (N / (((r : ℝ) - 1) * k)) ≤ Real.sqrt 2 * k := by
    calc Real.sqrt (N / (((r : ℝ) - 1) * k))
        ≤ Real.sqrt (2 * k ^ 2) := Real.sqrt_le_sqrt hle
      _ = Real.sqrt 2 * k := by
          rw [show 2 * k ^ 2 = 2 * (k * k) by ring, Real.sqrt_mul (by norm_num),
            Real.sqrt_mul_self hkpos.le]
  have hg : 0 < groverCoefficient l := groverCoefficient_pos l hl hl4
  have hgs : groverCoefficient l * Real.sqrt (N / (((r : ℝ) - 1) * k))
      ≤ groverCoefficient l * (Real.sqrt 2 * k) :=
    mul_le_mul_of_nonneg_left hs hg.le
  unfold proposedCollisionBudget
  nlinarith [hgs]

end Qatlib.Papers.CollisionProb97.MainResults
