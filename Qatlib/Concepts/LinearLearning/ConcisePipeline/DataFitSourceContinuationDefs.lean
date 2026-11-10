/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedQuan
import Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitActualQualityRestrictedStat.QuantumDataFitting2012
open Qatlib.Concepts.LinearLearning.ConcisePipeline.DataFitConciseSelectionRestrictedStat.QuantumDataFitting2012

set_option autoImplicit false

namespace Qatlib.Concepts.LinearLearning.ConcisePipeline

open Matrix
open Qatlib
open scoped Classical BigOperators

noncomputable def expectedFreshCopies (k : ℕ) (p : ℝ) : ℝ := (k : ℝ) / p

theorem expectedFreshCopies_ge_k (k : ℕ) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    (k : ℝ) ≤ expectedFreshCopies k p := by
  unfold expectedFreshCopies
  have hk : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hmul : (k : ℝ) * p ≤ (k : ℝ) * 1 := by nlinarith [hp1, hk]
  have hdiv : (k : ℝ) ≤ (k : ℝ) / p := (le_div_iff₀ hp).2 (by simpa using! hmul)
  exact hdiv

noncomputable def freshCopyPreparationCost (k : ℕ) (p c : ℝ) : ℝ :=
  expectedFreshCopies k p * c

theorem freshCopyPreparationCost_ge (k : ℕ) {p c : ℝ} (hp : 0 < p) (hp1 : p ≤ 1)
    (hc : 0 ≤ c) :
    (k : ℝ) * c ≤ freshCopyPreparationCost k p c := by
  unfold freshCopyPreparationCost
  have h := expectedFreshCopies_ge_k k hp hp1
  nlinarith [hc, mul_self_nonneg c]

theorem expectedFreshCopies_one (p : ℝ) : expectedFreshCopies 1 p = 1 / p := by
  simp [expectedFreshCopies]

def dataLoadingGates (s b : ℕ) : ℕ := s * b

theorem dataLoadingGates_mono (s s' b b' : ℕ) (hs : s ≤ s') (hb : b ≤ b') :
    dataLoadingGates s b ≤ dataLoadingGates s' b' := by
  simp only [dataLoadingGates]
  calc s * b ≤ s' * b := Nat.mul_le_mul hs (Nat.le_refl b)
    _ ≤ s' * b' := Nat.mul_le_mul_left s' hb

theorem dataLoadingGates_single : dataLoadingGates 1 1 = 1 := rfl

noncomputable def selectionMissBound (r m : ℕ) (p : ℝ) : ℝ :=
  (r : ℝ) * (1 - p) ^ m

theorem selectionMissBound_nonneg (r m : ℕ) {p : ℝ} (hp1 : p ≤ 1) :
    0 ≤ selectionMissBound r m p := by
  unfold selectionMissBound
  have h0 : (0 : ℝ) ≤ 1 - p := by linarith
  positivity

theorem selectionMissBound_mono_r (r r' m : ℕ) {p : ℝ} (hp1 : p ≤ 1) (hr : r ≤ r') :
    selectionMissBound r m p ≤ selectionMissBound r' m p := by
  unfold selectionMissBound
  have h0 : (0 : ℝ) ≤ (1 - p) ^ m := by
    have h1 : (0 : ℝ) ≤ 1 - p := by linarith
    exact pow_nonneg h1 m
  calc (r : ℝ) * (1 - p) ^ m ≤ (r' : ℝ) * (1 - p) ^ m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hr) h0
    _ = selectionMissBound r' m p := rfl

def tomographyMeasurements (r f : ℕ) : ℕ := r * f

theorem tomographyMeasurements_mono (r r' f f' : ℕ) (hr : r ≤ r') (hf : f ≤ f') :
    tomographyMeasurements r f ≤ tomographyMeasurements r' f' := by
  simp only [tomographyMeasurements]
  calc r * f ≤ r' * f := Nat.mul_le_mul hr (Nat.le_refl f)
    _ ≤ r' * f' := Nat.mul_le_mul_left r' hf

def dataFitQueryLedger (M r k : ℕ) : ℕ := M * (r + k)

theorem dataFitQueryLedger_mono (M M' r r' k k' : ℕ) (hM : M ≤ M') (hr : r ≤ r')
    (hk : k ≤ k') :
    dataFitQueryLedger M r k ≤ dataFitQueryLedger M' r' k' := by
  simp only [dataFitQueryLedger]
  exact Nat.mul_le_mul hM (by omega : r + k ≤ r' + k')

theorem dataFitQueryLedger_ge (M r k : ℕ) :
    M * r ≤ dataFitQueryLedger M r k := by
  simp only [dataFitQueryLedger]
  have h := Nat.mul_le_mul_left M (Nat.le_add_right r k)
  simpa [Nat.add_assoc] using! h

end Qatlib.Concepts.LinearLearning.ConcisePipeline
