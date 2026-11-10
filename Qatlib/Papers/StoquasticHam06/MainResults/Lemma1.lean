/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Defs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Lemma1

def bitEquiv (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  (Equiv.piCongrRight (fun _ : Fin m => finTwoEquiv.symm)).trans
    (finFunctionFinEquiv : (Fin m → Fin 2) ≃ Fin (2 ^ m))

def boolRank {m : ℕ} (t : Fin m → Bool) : Fin (2 ^ m) :=
  bitEquiv m t

lemma sum_fin_indicator_lt (N p : ℕ) :
    (∑ k : Fin N, (if (k : ℕ) < p then (1 : ℚ) else 0)) = ((min p N : ℕ) : ℚ) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (if k < p then (1 : ℚ) else 0)) N]
  have hfilter : (Finset.range N).filter (fun k => k < p) = Finset.range (min p N) := by
    ext k
    simp [Finset.mem_filter, Finset.mem_range, and_comm]
  rw [← Finset.sum_filter]
  rw [hfilter]
  simp

theorem lemma1_dyadic_boolean_average {n m : ℕ} (p : Sigma n → ℕ)
    (hp : ∀ x, p x < 2 ^ m) :
    ∃ f : Sigma n → (Fin m → Bool) → Bool,
      ∀ x, (∑ t : Fin m → Bool, (if f x t then (1 : ℚ) else 0)) = (p x : ℚ) := by
  classical
  refine ⟨fun x t => decide (boolRank t < p x), ?_⟩
  intro x
  calc (∑ t : Fin m → Bool, (if decide (boolRank t < p x) then (1 : ℚ) else 0))
      = (∑ k : Fin (2 ^ m), (if (k : ℕ) < p x then (1 : ℚ) else 0)) := by
        refine Fintype.sum_equiv (bitEquiv m) _ _ ?_
        intro t
        simp [boolRank]
    _ = ((min (p x) (2 ^ m) : ℕ) : ℚ) := sum_fin_indicator_lt (2 ^ m) (p x)
    _ = (p x : ℚ) := by rw [Nat.min_eq_left (Nat.le_of_lt (hp x))]

theorem lemma1_dyadic_boolean_average_ratio {n m : ℕ} (p : Sigma n → ℕ)
    (hp : ∀ x, p x < 2 ^ m) :
    ∃ f : Sigma n → (Fin m → Bool) → Bool,
      ∀ x, (∑ t : Fin m → Bool, (if f x t then (1 : ℚ) else 0)) / (2 : ℚ) ^ m
        = (p x : ℚ) / (2 : ℚ) ^ m := by
  obtain ⟨f, hf⟩ := lemma1_dyadic_boolean_average p hp
  exact ⟨f, fun x => by rw [hf x]⟩

structure OneQueryCircuit (n m : ℕ) where

  size : ℕ

  eval : (Sigma n → ℕ) → Sigma n → (Fin m → Bool) → Bool

  usesOneQuery : ∃ post : ℕ → (Fin m → Bool) → Bool,
    ∀ (g : Sigma n → ℕ) (x : Sigma n) (t : Fin m → Bool), eval g x t = post (g x) t

theorem lemma1_one_query_circuit {n m : ℕ} :
    ∃ C : OneQueryCircuit n m, C.size ≤ m + 1 ∧
      ∀ (g : Sigma n → ℕ) (x : Sigma n) (t : Fin m → Bool),
        C.eval g x t = decide (boolRank t < g x) := by
  refine ⟨⟨m + 1, fun g x t => decide (boolRank t < g x),
    ⟨fun k t => decide (boolRank t < k), ?_⟩⟩, le_rfl, ?_⟩
  · intro g x t
    rfl
  · intro g x t
    rfl

end Qatlib.Papers.StoquasticHam06.MainResults.Lemma1
