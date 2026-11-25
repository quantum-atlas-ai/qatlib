/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QSystemSim96.MainResults.BinaryTreePrep

@[expose] public section

/-!
# Loading distributions that have zero-weight leaves

A zero-weight leaf is reached through a first zero-mass child.
Its parent has positive mass, so the corresponding branching ratio
and hence the entire path amplitude vanish.
-/

set_option autoImplicit false

open scoped BigOperators
open Qatlib.Papers.QSystemSim96.MainResults

namespace Qatlib.Papers.QSystemSim96.MainResults

/-- A path from a positive root to a zero-weight leaf contains a
positive parent followed by a zero conditional weight. -/
theorem zero_leaf_path_step (l : ℕ) (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m)
    (hroot : 0 < dyadicMass l w 0 0) {n : ℕ} (hn : n < 2 ^ l) (hzero : w n = 0) :
    ∃ i < l, 0 < pathMass l w n i ∧ pathRatio l w n i = 0 := by
  classical
  let mass := pathMass l w n
  have hm0 : 0 < mass 0 := by
    simpa [mass, pathMass, pathNode_root, Nat.div_eq_of_lt hn] using hroot
  have hml : mass l = 0 := by
    simp [mass, pathMass, pathNode_leaf, dyadicMass_leaf, hzero]
  have h : ∃ j, mass j = 0 := ⟨l, hml⟩
  let j := Nat.find h
  have hjl : j ≤ l := Nat.find_min' h hml
  have hj0 : 0 < j := by
    by_contra! hnot
    have heq : j = 0 := by omega
    have hz : mass j = 0 := Nat.find_spec h
    rw [heq] at hz
    exact (ne_of_gt hm0) hz
  have hj : mass (j - 1 + 1) = 0 := by
    rw [Nat.sub_add_cancel (show 1 ≤ j by omega)]
    exact Nat.find_spec h
  have hprev : mass (j - 1) ≠ 0 := Nat.find_min h (by omega)
  refine ⟨j - 1, by omega, ?_, ?_⟩
  · exact lt_of_le_of_ne (dyadicMass_nonneg hw _ _) (Ne.symm hprev)
  · change mass (j - 1 + 1) / mass (j - 1) = 0
    rw [hj, zero_div]

/-- With a positive root and nonnegative weights, the squared loading
amplitude is the prescribed normalized weight, including zero leaves. -/
theorem pathAmplitude_sq_nonneg_general (l : ℕ) (w : ℕ → ℝ) (hw : ∀ m, 0 ≤ w m)
    (hroot : 0 < dyadicMass l w 0 0) {n : ℕ} (hn : n < 2 ^ l) :
    pathAmplitude l w n ^ 2 = dyadicMass l w l n / dyadicMass l w 0 0 := by
  by_cases hnpos : 0 < w n
  · exact pathAmplitude_sq_nonneg l w hw hnpos hn
  · have hz : w n = 0 := le_antisymm (le_of_not_gt hnpos) (hw n)
    obtain ⟨i, hi, _, hratio⟩ := zero_leaf_path_step l w hw hroot hn hz
    have hamp : pathAmplitude l w n = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 hi) (by rw [hratio, Real.sqrt_zero])
    simp [hamp, dyadicMass_leaf, hz]

end Qatlib.Papers.QSystemSim96.MainResults
