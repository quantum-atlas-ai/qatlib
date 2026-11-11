/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FrameMeasures.HaarFrames.OuterContent

/-!
# Outer measure bounds for finite covers

`finite_cover_outer_bound` bounds the outer measure of a set covered by finitely many sets of
uniformly bounded outer measure. This elementary estimate supplies the measure-theoretic step in
covering arguments for local circuit approximation, as studied in [Knill1995].

## Main statements

* `finite_cover_outer_bound`: a cover by `m` sets of outer measure at most `B` gives the bound
  `m * B`.

## References

* [Knill, 1995][Knill1995]
-/

set_option autoImplicit false
noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator NNReal ENNReal
namespace Qatlib.Concepts.LocalCircuits.MetricCover

/-- If `S` is covered by `m` sets each having outer measure at most `B`, then its outer measure
is at most `m * B`. -/
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
