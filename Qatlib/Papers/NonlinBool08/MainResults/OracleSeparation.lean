/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland.SqrtQueries
import Qatlib.Papers.NonlinBool08.MainResults.HiddenShift.Theorems
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset

namespace Qatlib.Papers.NonlinBool08.MainResults.OracleSeparation

open Qatlib.Papers.NonlinBool08.MainResults.BentCore
open Qatlib.Papers.NonlinBool08.MainResults.HiddenShift
open Qatlib.Papers.NonlinBool08.MainResults.MaioranaMcFarland

theorem hsp_recover (n : ℕ) :
    ∃ recover : (ℕ → (BVec n × ZMod 2)) → BVec n,
      ∀ (s : BVec n) (k : ℕ) (t : Fin k → BVec n × ZMod 2),
        (∀ i, orth (t i) s) →
        (∀ δ : BVec n, δ ≠ 0 → ∃ i, dot (t i).1 δ ≠ 0) →
        recover (fun j => if h : j < k then t ⟨j, h⟩ else (0, 0)) = s := by
  classical
  refine ⟨fun t => if h : ∃ s : BVec n, ∀ j : ℕ, orth (t j) s then
      Classical.choose h else 0, ?_⟩
  intro s k t hs hδ

  have huniq : ∀ s₁ s₂ : BVec n, (∀ i, orth (t i) s₁) → (∀ i, orth (t i) s₂) → s₁ = s₂ := by
    intro s₁ s₂ h₁ h₂
    by_contra hne
    have hne0 : s₁ + s₂ ≠ 0 := fun h => hne ((add_eq_zero_iff_eq_bvec s₁ s₂).mp h)
    obtain ⟨i, hi⟩ := hδ (s₁ + s₂) hne0
    apply hi
    have h1 := h₁ i
    have h2 := h₂ i
    unfold orth at h1 h2
    rw [dot_add_dot]

    have e1 : dot (t i).1 s₁ = (t i).2 := by
      calc dot (t i).1 s₁ = dot (t i).1 s₁ + 0 := (add_zero _).symm
        _ = dot (t i).1 s₁ + ((t i).2 + (t i).2) := by rw [BentCore.add_self_zmod2]
        _ = (dot (t i).1 s₁ + (t i).2) + (t i).2 := by abel
        _ = 0 + (t i).2 := by rw [h1]
        _ = (t i).2 := zero_add _
    have e2 : dot (t i).1 s₂ = (t i).2 := by
      calc dot (t i).1 s₂ = dot (t i).1 s₂ + 0 := (add_zero _).symm
        _ = dot (t i).1 s₂ + ((t i).2 + (t i).2) := by rw [BentCore.add_self_zmod2]
        _ = (dot (t i).1 s₂ + (t i).2) + (t i).2 := by abel
        _ = 0 + (t i).2 := by rw [h2]
        _ = (t i).2 := zero_add _
    rw [e1, e2, BentCore.add_self_zmod2]

  have hex : ∃ s' : BVec n, ∀ j : ℕ,
      orth (if h : j < k then t ⟨j, h⟩ else (0, 0)) s' :=
    ⟨s, by
      intro j
      by_cases hj : j < k
      · rw [dif_pos hj]
        exact hs ⟨j, hj⟩
      · rw [dif_neg hj]
        show orth (0, 0) s
        unfold orth
        simp⟩
  (try dsimp only)
  rw [dif_pos hex]
  have hcompat : ∀ i : Fin k, orth (t i) (Classical.choose hex) := by
    intro i
    have hi := Classical.choose_spec hex (i : ℕ)
    rwa [dif_pos i.2] at hi
  refine huniq (Classical.choose hex) s hcompat ?_
  intro i
  exact hs i

theorem corollary10_query_separation {c m : ℕ} (harith : 4 * (2 * (c * m)) ^ 2 + 1 < 2 ^ m) :
    (∀ A : NonAdaptiveAlg m, A.qset.card ≤ c * m →
        ¬ ∀ (π : Equiv.Perm (BVec m)) (s : BVec m),
            A.decide (fun p : ↥A.qset => strongOracle π s p) = s) ∧
      (∃ (recover : (ℕ → (BVec m × ZMod 2)) → BVec m),
        ∀ (k : ℕ) (t : Fin k → BVec m × ZMod 2) (s : BVec m),
          (∀ i, orth (t i) s) →
          (∀ δ : BVec m, δ ≠ 0 → ∃ i, dot (t i).1 δ ≠ 0) →
          recover (fun j => if h : j < k then t ⟨j, h⟩ else (0, 0)) = s) := by
  constructor
  · intro A hk hcorr
    have h2 : (2 * A.qset.card) ≤ 2 * (c * m) := by omega
    have h3 : (2 * A.qset.card) ^ 2 ≤ (2 * (c * m)) ^ 2 := Nat.pow_le_pow_left h2 2
    have h4 : 4 * (2 * A.qset.card) ^ 2 + 1 < 2 ^ m :=
      lt_of_le_of_lt (by omega) harith
    exact sqrt_lower_bound A h4 hcorr
  · obtain ⟨recover, hrec⟩ := hsp_recover m
    exact ⟨recover, fun k t s => hrec s k t⟩

end Qatlib.Papers.NonlinBool08.MainResults.OracleSeparation
