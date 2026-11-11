/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.JuntaLearning07.MainResults.FSOracleDefs
import Qatlib.Papers.JuntaLearning07.MainResults.InfluenceIdentification

/-!
# The zero-query obstruction to junta testing

This module establishes the zero-query base case for Fourier-sampling junta testing in the
setting of [AticiServedio2007], Theorem III.5. `fsProb_zero` evaluates every event on the unique
empty transcript, and `isKJunta_const_true` supplies a target that every valid tester must
accept.

If a function far from all `k`-juntas exists, `fs_testing_zero_queries_fails` shows that a
zero-query algorithm cannot meet the acceptance and rejection requirements simultaneously. This
gives the elementary query obstruction used in the lower-bound setting.

## Main statements

* `fsProb_zero` makes zero-query event probabilities equal to zero or one according to the empty
  transcript.
- `isKJunta_const_true` realizes the constant true function as a `k`-junta for every `k`.
* `fs_testing_zero_queries_fails` rules out zero-query testing whenever the far case is
  nonempty.

## References

* [Atici and Servedio, 2007][AticiServedio2007], Quantum Algorithms for Learning and Testing
  Juntas, Theorem III.5.
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.JuntaLearning07.MainResults

open scoped BigOperators

variable {n : ℕ}

/-- With zero Fourier samples, an event has probability one if it holds on the unique empty
transcript and probability zero otherwise. -/
theorem fsProb_zero (f : (Fin n → Bool) → Bool)
    (E : (Fin 0 → Finset (Fin n)) → Prop) [DecidablePred E] :
    fsProb f 0 E = if E (fun i => i.elim0) then 1 else 0 := by
  classical
  rw [fsProb_eq_sum]
  have hprod : ∀ s : Fin 0 → Finset (Fin n), (∏ t : Fin 0, fsWeight f (s t)) = 1 := by
    intro s
    exact Finset.prod_empty
  have hall : ∀ s : Fin 0 → Finset (Fin n), s = (fun i => i.elim0) := by
    intro s
    funext i
    exact i.elim0
  have hcongr : (∑ s : Fin 0 → Finset (Fin n),
        (if E s then ∏ t : Fin 0, fsWeight f (s t) else 0))
      = ∑ _s : Fin 0 → Finset (Fin n),
        (if E (fun i => i.elim0) then (1 : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro s _
    rw [hprod, hall s]
  rw [hcongr, Finset.sum_const, Finset.card_univ]
  have hcard : Fintype.card (Fin 0 → Finset (Fin n)) = 1 := by simp
  rw [hcard]
  simp

/-- The constant true function is a `k`-junta for every natural number `k`, since it depends on
the empty coordinate set. -/
theorem isKJunta_const_true (k : ℕ) :
    IsKJunta (n := n) k (fun _ => true) := by
  refine ⟨∅, by simp, ?_⟩
  intro x y _
  rfl

/-- If there exists a function `ε`-far from every `k`-junta, no zero-query Fourier-sampling
algorithm satisfies the junta-testing guarantees. -/
theorem fs_testing_zero_queries_fails {k : ℕ} {ε : ℝ}
    (hfar : ∃ f : (Fin n → Bool) → Bool, farFromJunta (n := n) k ε f)
    (A : FSAlgorithm n 0) : ¬ FSTestsJuntas (n := n) k ε A := by
  classical
  intro hA
  obtain ⟨haccJ, hrejF⟩ := hA
  have haccept : (2 / 3 : ℝ) ≤ fsProb (fun _ => true) 0 (fun s => A s = true) :=
    haccJ _ (isKJunta_const_true (n := n) k)
  obtain ⟨f, hf⟩ := hfar
  have hreject : (2 / 3 : ℝ) ≤ fsProb f 0 (fun s => A s = false) :=
    hrejF _ hf
  rw [fsProb_zero] at haccept hreject
  have hAtrue : A (fun i : Fin 0 => i.elim0) = true := by
    by_cases h : A (fun i : Fin 0 => i.elim0) = true
    · exact h
    · simp only [h] at haccept
      norm_num at haccept
  have hAfalse : A (fun i : Fin 0 => i.elim0) = false := by
    by_cases h : A (fun i : Fin 0 => i.elim0) = false
    · exact h
    · simp only [h] at hreject
      norm_num at hreject
  rw [hAtrue] at hAfalse
  exact Bool.noConfusion hAfalse

end Qatlib.Papers.JuntaLearning07.MainResults
