/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedQuan
import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedQuan

/-!
# Elementary resource expressions for data fitting

This module defines real-valued expressions for fresh-copy overhead and selection failure,
together with natural-number ledgers for data loading, tomography, and queries. The definitions
`expectedFreshCopies`, `selectionMissBound`, and `dataFitQueryLedger` expose the dependence on
success parameters and repetition counts in the data-fitting setting of [WiebeBraunLloyd2012].

The accompanying lemmas establish elementary lower bounds, nonnegativity, and monotonicity of
these expressions under their stated parameter conditions.

## Main definitions and statements

* `expectedFreshCopies_ge_k`: the copy-count expression is at least `k` for `0 < p ≤ 1`.
* `freshCopyPreparationCost_ge`: the corresponding preparation-cost lower bound.
* `selectionMissBound_mono_r`: monotonicity in the selection-size parameter.
* `dataFitQueryLedger_mono`: monotonicity of the query ledger.

## References

* [Wiebe, Braun, and Lloyd, 2012][WiebeBraunLloyd2012]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.QuantumDataFitting2012

set_option autoImplicit false

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

open Matrix
open Qatlib
open scoped Classical BigOperators

/-- The real-valued copy-count expression `k / p` for obtaining `k` fresh copies with success
parameter `p`. -/
noncomputable def expectedFreshCopies (k : ℕ) (p : ℝ) : ℝ := (k : ℝ) / p

/-- For `0 < p ≤ 1`, the expected fresh-copy expression is at least the requested number of
copies. -/
theorem expectedFreshCopies_ge_k (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (k : ℝ) ≤ expectedFreshCopies k p := by
  unfold expectedFreshCopies
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hmul : (k : ℝ) * p ≤ (k : ℝ) * 1 := by nlinarith [hp1, hk]
  have hdiv : (k : ℝ) ≤ (k : ℝ) / p := (le_div_iff₀ hp).2 (by simpa using! hmul)
  exact hdiv

/-- The fresh-copy count expression multiplied by the preparation cost per attempt. -/
noncomputable def freshCopyPreparationCost (k : ℕ) (p c : ℝ) : ℝ :=
  expectedFreshCopies k p * c

/-- For `0 < p ≤ 1` and nonnegative preparation cost `c`, the fresh-copy preparation-cost
expression is at least `k * c`. -/
theorem freshCopyPreparationCost_ge (k : ℕ) {p c : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hc : 0 ≤ c) :
    (k : ℝ) * c ≤ freshCopyPreparationCost k p c := by
  unfold freshCopyPreparationCost
  have h := expectedFreshCopies_ge_k k hp hp1
  nlinarith [hc, mul_self_nonneg c]

/-- The single-copy count expression equals `1 / p`. -/
theorem expectedFreshCopies_one (p : ℝ) : expectedFreshCopies 1 p = 1 / p := by
  simp [expectedFreshCopies]

/-- The data-loading gate-count expression given by the product of the two natural-number
parameters. -/
def dataLoadingGates (s b : ℕ) : ℕ := s * b

/-- The data-loading gate-count expression is monotone in both parameters. -/
theorem dataLoadingGates_mono (s s' b b' : ℕ) (hs : s ≤ s') (hb : b ≤ b') :
    dataLoadingGates s b ≤ dataLoadingGates s' b' := by
  simp only [dataLoadingGates]
  calc s * b ≤ s' * b := Nat.mul_le_mul hs (Nat.le_refl b)
    _ ≤ s' * b' := Nat.mul_le_mul_left s' hb

/-- The data-loading gate count with both parameters equal to one is one. -/
theorem dataLoadingGates_single : dataLoadingGates 1 1 = 1 := rfl

/-- The selection-miss bound expression `r * (1 - p) ^ m`. -/
noncomputable def selectionMissBound (r m : ℕ) (p : ℝ) : ℝ :=
  (r : ℝ) * (1 - p) ^ m

/-- The selection-miss bound expression is nonnegative when `p ≤ 1`. -/
theorem selectionMissBound_nonneg (r m : ℕ) {p : ℝ} (hp1 : p ≤ 1) :
    0 ≤ selectionMissBound r m p := by
  unfold selectionMissBound
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  positivity

/-- When `p ≤ 1`, the selection-miss bound expression is monotone in the size parameter `r`. -/
theorem selectionMissBound_mono_r (r r' m : ℕ) {p : ℝ} (hp1 : p ≤ 1) (hr : r ≤ r') :
    selectionMissBound r m p ≤ selectionMissBound r' m p := by
  unfold selectionMissBound
  have h0 : (0 : ℝ) ≤ (1 - p) ^ m := by
    have h1 : (0 : ℝ) ≤ 1 - p := by linarith
    exact pow_nonneg h1 m
  calc (r : ℝ) * (1 - p) ^ m ≤ (r' : ℝ) * (1 - p) ^ m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hr) h0
    _ = selectionMissBound r' m p := rfl

/-- The tomography measurement-count expression given by the product of its two natural-number
parameters. -/
def tomographyMeasurements (r f : ℕ) : ℕ := r * f

/-- The tomography measurement-count expression is monotone in both parameters. -/
theorem tomographyMeasurements_mono (r r' f f' : ℕ) (hr : r ≤ r') (hf : f ≤ f') :
    tomographyMeasurements r f ≤ tomographyMeasurements r' f' := by
  simp only [tomographyMeasurements]
  calc r * f ≤ r' * f := Nat.mul_le_mul hr (Nat.le_refl f)
    _ ≤ r' * f' := Nat.mul_le_mul_left r' hf

/-- The data-fitting query-count expression `M * (r + k)`. -/
def dataFitQueryLedger (M r k : ℕ) : ℕ := M * (r + k)

/-- The data-fitting query ledger is monotone in each of its three natural-number parameters. -/
theorem dataFitQueryLedger_mono (M M' r r' k k' : ℕ) (hM : M ≤ M') (hr : r ≤ r')
    (hk : k ≤ k') :
    dataFitQueryLedger M r k ≤ dataFitQueryLedger M' r' k' := by
  simp only [dataFitQueryLedger]
  exact Nat.mul_le_mul hM (by omega : r + k ≤ r' + k')

/-- The data-fitting query ledger is at least `M * r`. -/
theorem dataFitQueryLedger_ge (M r k : ℕ) :
    M * r ≤ dataFitQueryLedger M r k := by
  simp only [dataFitQueryLedger]
  have h := Nat.mul_le_mul_left M (Nat.le_add_right r k)
  simpa [Nat.add_assoc] using! h

end Qatlib.Concepts.LinearLearning.ConcisePipeline
