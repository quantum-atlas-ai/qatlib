/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Trainability23.HaarAverages.HaarInfrastructure
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Algebra.Star
set_option warningAsError false

namespace Qatlib.Papers.Trainability23.HaarAverages

open scoped BigOperators Matrix

theorem isClosed_unitaryGroup (n : Type*) [Fintype n] [DecidableEq n] :
    IsClosed (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) := by
  have h : (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) = {A | A * star A = 1} := by
    ext A
    exact Matrix.mem_unitaryGroup_iff
  rw [h]
  exact isClosed_eq (Continuous.matrix_mul continuous_id continuous_star) continuous_const

theorem isCompact_entryBall (n : Type*) [Fintype n] [DecidableEq n] :
    IsCompact {A : Matrix n n ℂ | ∀ i j, ‖A i j‖ ≤ 1} := by
  have hS : IsCompact (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  have hset : Matrix.of '' (Set.univ.pi fun _ : n => Set.univ.pi fun _ : n =>
      Metric.closedBall (0 : ℂ) 1) = {A : Matrix n n ℂ | ∀ i j, ‖A i j‖ ≤ 1} := by
    ext A
    constructor
    · rintro ⟨f, hf, rfl⟩ i j
      simpa [Matrix.of_apply, Metric.mem_closedBall, dist_eq_norm] using hf i (Set.mem_univ i) j
        (Set.mem_univ j)
    · intro hA
      refine ⟨fun i j => A i j, fun i _ j _ => ?_, ?_⟩
      · simpa [Metric.mem_closedBall, dist_eq_norm] using hA i j
      · ext i j
        rw [Matrix.of_apply]
  rw [← hset]
  exact hS.image (by fun_prop)

theorem isCompact_unitaryGroup (n : Type*) [Fintype n] [DecidableEq n] :
    IsCompact (Matrix.unitaryGroup n ℂ : Set (Matrix n n ℂ)) :=
  (isCompact_entryBall n).of_isClosed_subset (isClosed_unitaryGroup n)
    fun _ hA i j => unitaryGroup_entry_norm_le_one hA i j

instance instCompactSpaceUnitaryGroup (n : Type*) [Fintype n] [DecidableEq n] :
    CompactSpace (Matrix.unitaryGroup n ℂ) :=
  isCompact_iff_compactSpace.mp (isCompact_unitaryGroup n)

end Qatlib.Papers.Trainability23.HaarAverages
