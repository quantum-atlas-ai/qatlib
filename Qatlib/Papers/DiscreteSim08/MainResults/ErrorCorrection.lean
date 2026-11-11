/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DiscreteSim08.MainResults.Defs

/-!
# Numerical bounds for query error correction

This module proves the scalar inequalities used in the correction-cost analysis: a biased-walk
reciprocal bound, a segmentation identity, and a recurrence bound for branching cost. A
normalized nonnegative weight family with weight at least three quarters at zero has remaining
mass at most one quarter.

This development follows [CleveEtAl2009].

## Main statements

* `biasedWalk_expected_steps`: the reciprocal drift expression is at most two.
* `branchingProcess_cost_le_one`: the stated branching recurrence bounds the cost by one.
* `errorMass_le_quarter`: the total weight away from zero is at most one quarter.

## References

* [Cleve et al., 2009][CleveEtAl2009]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.DiscreteSim08.MainResults

/-- If `p ≥ 3 / 4` and `q = 1 - p`, the reciprocal drift `1 / (p - q)` is at most two. -/
theorem biasedWalk_expected_steps (p q : ℝ) (hp : 3 / 4 ≤ p) (hq : q = 1 - p) :
    1 / (p - q) ≤ 2 := by
  have hpq : (1 / 2 : ℝ) ≤ p - q := by rw [hq]; linarith
  have hpos : 0 < p - q := by linarith
  rw [div_le_iff₀ hpos]
  nlinarith

/-- If `m * θ = 1 / 4`, the segmentation expression `T / (m * θ)` equals `4 * T`. -/
theorem segmentation_count (T m θ : ℝ) (hm : m * θ = 1 / 4) :
    T / (m * θ) = 4 * T := by
  rw [hm]
  ring

/-- The stated recurrence bounds nonnegative cost `C0` by one when `A ≤ 2`, `qpos ≤ 1 / 4`, and
`0 ≤ qerr ≤ 1 / 4`. -/
theorem branchingProcess_cost_le_one (C0 A qpos qerr : ℝ)
    (hC0 : 0 ≤ C0) (hA2 : A ≤ 2)
    (hqpos : qpos ≤ 1 / 4)
    (hqerr0 : 0 ≤ qerr) (hqerr : qerr ≤ 1 / 4)
    (hrec : C0 ≤ 2 * C0 * qpos + A * qerr) :
    C0 ≤ 1 := by
  have h1 : 2 * C0 * qpos ≤ 2 * C0 * (1 / 4) :=
    mul_le_mul_of_nonneg_left hqpos (by positivity)
  have h2 : A * qerr ≤ 2 * (1 / 4) :=
    mul_le_mul hA2 hqerr hqerr0 (by norm_num)
  nlinarith

/-- For nonnegative weights summing to one with weight at least three quarters at zero, the
total weight on nonzero indices is at most one quarter. See [CleveEtAl2009]. -/
theorem errorMass_le_quarter {m : ℕ} (q : Fin (m + 1) → ℝ)
    (hqnn : ∀ a, 0 ≤ q a) (hq0 : (3 / 4 : ℝ) ≤ q 0)
    (hsum : ∑ a, q a = 1) :
    (Finset.univ.filter (fun a : Fin (m + 1) => a ≠ 0)).sum q ≤ 1 / 4 := by
  have hq0nn : 0 ≤ q 0 := hqnn 0
  have hsplit := Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
    (p := fun a : Fin (m + 1) => a ≠ 0) (f := q)
  have hcomp : (Finset.univ.filter (fun a : Fin (m + 1) => ¬ a ≠ 0)).sum q = q 0 := by
    rw [show Finset.univ.filter (fun a : Fin (m + 1) => ¬ a ≠ 0) = {0} by
      ext a
      simp]
    simp
  rw [hcomp, hsum] at hsplit
  linarith [hq0nn]

end Qatlib.Papers.DiscreteSim08.MainResults
