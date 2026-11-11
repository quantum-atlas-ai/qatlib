/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Defs

/-!
# Boolean representations of dyadic averages

`bitEquiv` ranks Boolean strings by a finite index. Thresholding this rank realizes every
numerator below `2 ^ m` as a Boolean acceptance count, and `OneQueryCircuit` packages a size
parameter and evaluation that factors through one queried value. See [BravyiEtAl2008Stoquastic].

## Main statements

* `lemma1_dyadic_boolean_average`: a bounded numerator is represented by a Boolean count.
* `lemma1_dyadic_boolean_average_ratio`: the corresponding normalized count gives a dyadic
  ratio.
* `lemma1_one_query_circuit`: the rank comparison has a one-query model with size at most `m +
  1`.

## References

* [Bravyi et al., 2008][BravyiEtAl2008Stoquastic]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.ComplexityDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Lemma1

/-- An equivalence between Boolean strings of length `m` and the indices in `Fin (2 ^ m)`. -/
def bitEquiv (m : ℕ) : (Fin m → Bool) ≃ Fin (2 ^ m) :=
  (Equiv.piCongrRight (fun _ : Fin m => finTwoEquiv.symm)).trans
    (finFunctionFinEquiv : (Fin m → Fin 2) ≃ Fin (2 ^ m))

/-- The finite rank of a Boolean string under `bitEquiv`. -/
def boolRank {m : ℕ} (t : Fin m → Bool) : Fin (2 ^ m) :=
  bitEquiv m t

/-- The rational sum of the indicators `k < p` over `Fin N` equals `min p N`. -/
lemma sum_fin_indicator_lt (N p : ℕ) :
    (∑ k : Fin N, (if (k : ℕ) < p then (1 : ℚ) else 0)) = ((min p N : ℕ) : ℚ) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => (if k < p then (1 : ℚ) else 0)) N]
  have hfilter : (Finset.range N).filter (fun k => k < p) = Finset.range (min p N) := by
    ext k
    simp [Finset.mem_filter, Finset.mem_range, and_comm]
  rw [← Finset.sum_filter]
  rw [hfilter]
  simp

/-- If every `p x` is less than `2 ^ m`, a Boolean predicate on `m` auxiliary bits has exactly
`p x` accepting strings for each `x`. See [BravyiEtAl2008Stoquastic]. -/
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

/-- If every `p x` is less than `2 ^ m`, a Boolean predicate on `m` auxiliary bits has
normalized acceptance count `p x / 2 ^ m`. See [BravyiEtAl2008Stoquastic]. -/
theorem lemma1_dyadic_boolean_average_ratio {n m : ℕ} (p : Sigma n → ℕ)
    (hp : ∀ x, p x < 2 ^ m) :
    ∃ f : Sigma n → (Fin m → Bool) → Bool,
      ∀ x, (∑ t : Fin m → Bool, (if f x t then (1 : ℚ) else 0)) / (2 : ℚ) ^ m
        = (p x : ℚ) / (2 : ℚ) ^ m := by
  obtain ⟨f, hf⟩ := lemma1_dyadic_boolean_average p hp
  exact ⟨f, fun x => by rw [hf x]⟩

/-- A circuit model with a size parameter and an evaluation function that factors through a
single value `g x`. -/
structure OneQueryCircuit (n m : ℕ) where

  size : ℕ

  eval : (Sigma n → ℕ) → Sigma n → (Fin m → Bool) → Bool

  usesOneQuery : ∃ post : ℕ → (Fin m → Bool) → Bool,
    ∀ (g : Sigma n → ℕ) (x : Sigma n) (t : Fin m → Bool), eval g x t = post (g x) t

/-- There exists a `OneQueryCircuit` of size at most `m + 1` whose output tests whether the
auxiliary string's rank is less than `g x`. See [BravyiEtAl2008Stoquastic]. -/
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
