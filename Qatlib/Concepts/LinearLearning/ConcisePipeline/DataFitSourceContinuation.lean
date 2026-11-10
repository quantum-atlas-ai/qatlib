/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitSourceContinuationDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

theorem clause8_endpoint :
    (∀ (k : ℕ) {p : ℝ}, 0 < p → p ≤ 1 →
      (k : ℝ) ≤ expectedFreshCopies k p) ∧
    (∀ (k : ℕ) {p c : ℝ}, 0 < p → p ≤ 1 → 0 ≤ c →
      (k : ℝ) * c ≤ freshCopyPreparationCost k p c) ∧
    (∀ p : ℝ, expectedFreshCopies 1 p = 1 / p) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k p hp hp1
    exact expectedFreshCopies_ge_k k hp hp1
  · intro k p c hp hp1 hc
    exact freshCopyPreparationCost_ge k hp hp1 hc
  · intro p
    exact expectedFreshCopies_one p

theorem clause9_endpoint :
    (∀ s s' b b' : ℕ, s ≤ s' → b ≤ b' →
      dataLoadingGates s b ≤ dataLoadingGates s' b') ∧
    (∀ (r m : ℕ) {p : ℝ}, p ≤ 1 → 0 ≤ selectionMissBound r m p) ∧
    (∀ (r r' m : ℕ) {p : ℝ}, p ≤ 1 → r ≤ r' →
      selectionMissBound r m p ≤ selectionMissBound r' m p) ∧
    (∀ r r' f f' : ℕ, r ≤ r' → f ≤ f' →
      tomographyMeasurements r f ≤ tomographyMeasurements r' f') := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s s' b b' hs hb
    exact dataLoadingGates_mono s s' b b' hs hb
  · intro r m p hp1
    exact selectionMissBound_nonneg r m hp1
  · intro r r' m p hp1 h
    exact selectionMissBound_mono_r r r' m hp1 h
  · intro r r' f f' hr hf
    exact tomographyMeasurements_mono r r' f f' hr hf

theorem clause5_endpoint :
    (∀ M M' r r' k k' : ℕ, M ≤ M' → r ≤ r' → k ≤ k' →
      dataFitQueryLedger M r k ≤ dataFitQueryLedger M' r' k') ∧
    (∀ M r k : ℕ, M * r ≤ dataFitQueryLedger M r k) := by
  refine ⟨?_, ?_⟩
  · intro M M' r r' k k' hM hr hk
    exact dataFitQueryLedger_mono M M' r r' k k' hM hr hk
  · intro M r k
    exact dataFitQueryLedger_ge M r k

theorem clause4_endpoint :
    (∀ r r' f f' : ℕ, r ≤ r' → f ≤ f' →
      tomographyMeasurements r f ≤ tomographyMeasurements r' f') := by
  intro r r' f f' hr hf
  exact tomographyMeasurements_mono r r' f f' hr hf

end Qatlib.Concepts.LinearLearning.ConcisePipeline
