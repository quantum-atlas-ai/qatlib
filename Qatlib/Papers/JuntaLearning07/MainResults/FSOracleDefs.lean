/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.JuntaLearningDefs
import Qatlib.Papers.JuntaLearning07.MainResults.ParsevalIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Sqrt
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open scoped BigOperators

variable {n : ℕ}

def transcriptUnion {T : ℕ} (s : Fin T → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion s

@[simp]
theorem mem_transcriptUnion {T : ℕ} (s : Fin T → Finset (Fin n)) {j : Fin n} :
    j ∈ transcriptUnion s ↔ ∃ t : Fin T, j ∈ s t := by
  unfold transcriptUnion
  rw [Finset.mem_biUnion]
  constructor
  · rintro ⟨t, _, ht⟩
    exact ⟨t, ht⟩
  · rintro ⟨t, ht⟩
    exact ⟨t, Finset.mem_univ t, ht⟩

theorem transcriptUnion_subset {T : ℕ} {s : Fin T → Finset (Fin n)} {J : Finset (Fin n)}
    (h : ∀ t, s t ⊆ J) : transcriptUnion s ⊆ J := by
  intro j hj
  rw [mem_transcriptUnion] at hj
  obtain ⟨t, ht⟩ := hj
  exact h t ht

def fsProb (f : (Fin n → Bool) → Bool) (T : ℕ)
    (E : (Fin T → Finset (Fin n)) → Prop) : ℝ := by
  classical
  exact ∑ s : Fin T → Finset (Fin n), if E s then ∏ t : Fin T, fsWeight f (s t) else 0

def FSAlgorithm (n T : ℕ) : Type := (Fin T → Finset (Fin n)) → Bool

def FSTestsJuntas {n T : ℕ} (k : ℕ) (ε : ℝ) (A : FSAlgorithm n T) : Prop :=
  (∀ f : (Fin n → Bool) → Bool, IsKJunta (n := n) k f →
      (2 / 3 : ℝ) ≤ fsProb f T (fun s => A s = true)) ∧
    (∀ f : (Fin n → Bool) → Bool, farFromJunta (n := n) k ε f →
      (2 / 3 : ℝ) ≤ fsProb f T (fun s => A s = false))

end Qatlib.Papers.JuntaLearning07.MainResults
