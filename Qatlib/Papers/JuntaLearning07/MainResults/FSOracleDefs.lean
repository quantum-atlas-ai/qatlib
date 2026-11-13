/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.JuntaLearningDefs
import Qatlib.Papers.JuntaLearning07.MainResults.ParsevalIdentity
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.Sqrt

/-!
# Fourier-sampling transcripts and junta tests

`fsProb` assigns event probabilities to finite transcripts using products of the Fourier weights
`fsWeight`. The module defines the union of sampled variable sets, deterministic transcript
algorithms `FSAlgorithm`, and the two-sided junta-testing condition `FSTestsJuntas`. See
[AticiServedio2007].

## Main statements

* `mem_transcriptUnion`: A variable belongs to the transcript union exactly when it occurs in at
  least one sampled set.
* `FSTestsJuntas`: The algorithm accepts every k-junta and rejects every function ε-far from
  k-juntas, each with Fourier-sampling probability at least two thirds.

## References

* [Atici and Servedio, 2007][AticiServedio2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open scoped BigOperators

variable {n : ℕ}

/-- The union of all variable sets appearing in a finite sampling transcript. -/
def transcriptUnion {T : ℕ} (s : Fin T → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion s

/-- A variable belongs to the transcript union exactly when it occurs in at least one sampled
set. -/
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

/-- If every sampled set is contained in J, their transcript union is contained in J. -/
theorem transcriptUnion_subset {T : ℕ} {s : Fin T → Finset (Fin n)} {J : Finset (Fin n)}
    (h : ∀ t, s t ⊆ J) : transcriptUnion s ⊆ J := by
  intro j hj
  rw [mem_transcriptUnion] at hj
  obtain ⟨t, ht⟩ := hj
  exact h t ht

/-- The total product Fourier weight of transcripts satisfying E for T independent samples from
f. -/
def fsProb (f : (Fin n → Bool) → Bool) (T : ℕ)
    (E : (Fin T → Finset (Fin n)) → Prop) : ℝ := by
  classical
  exact ∑ s : Fin T → Finset (Fin n), if E s then ∏ t : Fin T, fsWeight f (s t) else 0

/-- A Boolean decision function on transcripts of T sampled subsets of n variables. -/
def FSAlgorithm (n T : ℕ) : Type := (Fin T → Finset (Fin n)) → Bool

/-- The algorithm accepts every k-junta and rejects every function ε-far from k-juntas, each
with Fourier-sampling probability at least two thirds. -/
def FSTestsJuntas {n T : ℕ} (k : ℕ) (ε : ℝ) (A : FSAlgorithm n T) : Prop :=
  (∀ f : (Fin n → Bool) → Bool, IsKJunta (n := n) k f →
      (2 / 3 : ℝ) ≤ fsProb f T (fun s => A s = true)) ∧
    (∀ f : (Fin n → Bool) → Bool, farFromJunta (n := n) k ε f →
      (2 / 3 : ℝ) ≤ fsProb f T (fun s => A s = false))

end Qatlib.Papers.JuntaLearning07.MainResults
