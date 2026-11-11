/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TensorNetwork08.MainResults.Circuit

/-!
# Scaled promise separation for tensor-network computation

Proves the real-number separation argument associated with Corollary 4.2 of [AradLandau2010].
For positive scale `p`, an approximation error below `1 / (3 * p)` preserves the separation of
`p * a ≥ 2` from `p * a ≤ 1` at threshold `3 / 2`.

The results state the two threshold implications, their combination under the promise, and the
incompatibility of the two promised branches.

## Main statements

* `corollary4_2_ratio_separation`: proves the two scaled threshold implications.
* `corollary4_2_decides`: identifies the branch under the promise.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option warningAsError false

set_option autoImplicit false

namespace Qatlib.Papers.TensorNetwork08.MainResults.Cor42

/-- For positive `p` and `|a - b| < 1 / (3 * p)`, the cases `p * a ≥ 2` and `p * a ≤ 1` force `p
* b` above and below `3 / 2`, respectively. See [AradLandau2010]. -/
theorem corollary4_2_ratio_separation
    (p a b : ℝ) (hp : 0 < p) (happ : |a - b| < 1 / (3 * p)) :
    (2 ≤ p * a → 3 / 2 < p * b) ∧ (p * a ≤ 1 → p * b < 3 / 2) := by
  have hkey : p * (1 / (3 * p)) = 1 / 3 := by
    field_simp
  obtain ⟨hlow, hhigh⟩ := abs_lt.1 happ
  constructor
  · intro ha
    have h1 : -(1 / 3) < p * (a - b) := by
      have h := mul_lt_mul_of_pos_left hlow hp
      rwa [mul_neg, hkey] at h
    have hsub : p * (a - b) = p * a - p * b := by ring
    nlinarith
  · intro ha
    have h1 : p * (a - b) < 1 / 3 := by
      have h := mul_lt_mul_of_pos_left hhigh hp
      rwa [hkey] at h
    have hsub : p * (a - b) = p * a - p * b := by ring
    nlinarith

/-- Under the scaled approximation bound and the two-branch promise, `p * b` lies on the
corresponding side of `3 / 2` and the associated promise branch holds. See [AradLandau2010]. -/
theorem corollary4_2_decides
    (p a b : ℝ) (hp : 0 < p) (happ : |a - b| < 1 / (3 * p))
    (hpromise : 2 ≤ p * a ∨ p * a ≤ 1) :
    (3 / 2 < p * b ∧ 2 ≤ p * a) ∨ (p * b < 3 / 2 ∧ p * a ≤ 1) := by
  obtain ⟨hyes, hno⟩ := corollary4_2_ratio_separation p a b hp happ
  rcases hpromise with h | h
  · exact Or.inl ⟨hyes h, h⟩
  · exact Or.inr ⟨hno h, h⟩

/-- The scaled inequalities `2 ≤ p * a` and `p * a ≤ 1` cannot both hold. -/
theorem corollary4_2_branches_disjoint (p a : ℝ) :
    ¬(2 ≤ p * a ∧ p * a ≤ 1) := by
  intro ⟨h1, h2⟩
  linarith

end Qatlib.Papers.TensorNetwork08.MainResults.Cor42
