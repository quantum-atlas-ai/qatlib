/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSDPsolver17.MainResults.PaperInterface.PaperDefs
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

@[expose] public section


/-! # The legacy list-merger cost is independent of its exact output function.
This refutes a record-level lower bound. It does not refute the source result for
algorithms restricted to index-list oracle queries.
-/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Qatlib.Papers.QSDPsolver17.MainResults.MergeCounter

/-- The old list-input record carries only a length bound for each complete list. -/
structure MergeInstance (d k : ℕ) where
  /-- Complete lists are available as unrestricted values. -/
  lists : Fin (k + 1) → List ℤ
  /-- Each input list has length at most the supplied bound. -/
  length_le : ∀ i, (lists i).length ≤ d

/-- Number of distinct entries in all the complete input lists. -/
def mergedSize {d k : ℕ} (R : MergeInstance d k) : ℕ :=
  (Finset.univ.biUnion (fun i : Fin (k + 1) => (R.lists i).toFinset)).card

/-- The old list-size decision threshold. -/
def mergeThreshold (d k : ℕ) : ℕ := d + d * k / 2

/-- The legacy merger output and its independent declared query count. -/
structure MergeAlgorithm (d k : ℕ) where
  /-- An unrestricted function on complete list data. -/
  output : MergeInstance d k → Bool
  /-- Reported query count, unrelated to evaluating the output function. -/
  queries : ℕ
  /-- Correctness of the reported decision imposes no restriction on the count. -/
  correct : ∀ R : MergeInstance d k,
    mergedSize R ≤ mergeThreshold d k ∨ mergeThreshold d k + 1 ≤ mergedSize R →
      output R = decide (mergedSize R ≤ mergeThreshold d k)

/-- The old interface admits exact decisions while declaring zero queries. -/
def zeroMerger (d k : ℕ) : MergeAlgorithm d k where
  output := fun R => decide (mergedSize R ≤ mergeThreshold d k)
  queries := 0
  correct := fun _ _ => rfl

/-- Every positive-dimensional legacy Lemma 51 lower-bound contract is false. -/
theorem merge_counterexample (d k : ℕ) (hd : 0 < d) (hk : 0 < k) :
    ¬ (∃ c : ℝ, 0 < c ∧ ∀ A : MergeAlgorithm d k,
      c * (d : ℝ) * (k : ℝ) ≤ (A.queries : ℝ)) := by
  rintro ⟨c, hc, hall⟩
  have hzero := hall (zeroMerger d k)
  have hpos : 0 < c * (d : ℝ) * (k : ℝ) :=
    mul_pos (mul_pos hc (Nat.cast_pos.mpr hd)) (Nat.cast_pos.mpr hk)
  norm_num [zeroMerger] at hzero
  linarith

end Qatlib.Papers.QSDPsolver17.MainResults.MergeCounter
