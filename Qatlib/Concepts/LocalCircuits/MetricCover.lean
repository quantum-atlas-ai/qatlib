/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FrameMeasures.HaarFrames.OuterContent

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator NNReal ENNReal
namespace Qatlib.Concepts.LocalCircuits.MetricCover

theorem finite_cover_outer_bound {α : Type*} (μ : OuterMeasure α)
    (S : Set α) (m : ℕ) (C : Fin m → Set α) (B : ℝ≥0∞)
    (hcover : S ⊆ ⋃ i, C i) (hB : ∀ i, μ (C i) ≤ B) :
    μ S ≤ (m : ℝ≥0∞) * B := by
  calc
    μ S ≤ μ (⋃ i, C i) := measure_mono hcover
    _ ≤ ∑' i, μ (C i) := measure_iUnion_le C
    _ ≤ ∑' _i : Fin m, B := by
      rw [tsum_fintype, tsum_fintype]
      exact Finset.sum_le_sum fun i _ => hB i
    _ = _ := by simp [nsmul_eq_mul]

end Qatlib.Concepts.LocalCircuits.MetricCover
