/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LearningGraph11.MainResults.Theorem9QueryBound
import Qatlib.Papers.LearningGraph11.MainResults.Theorem10MinimumDegree

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 Theorem 11: the combined bound

Fixed source: arXiv:1109.5135v1 (LaTeX `chicago_submitted.tex`, lines 1083-1092), Theorem 11
(p. 16), and the introduction (p. 2) where the same result is announced.

For a graph `H` on `k ≥ 3` vertices with `m` edges and minimum degree `d ≥ 1` there is a
quantum query algorithm deciding whether `H` is a subgraph of an `n`-vertex graph with
`O(n^{2−2/k−t})` queries, where

`t = max { (k² − 2(m+1)) / (k(k+1)(m+1)), (2k − d − 3) / (k(d+1)(m−d+2)) }`.

The paper notes that this is an immediate consequence of Theorems 9 and 10. The first
fraction is Theorem 9's exponent rewritten in the `2 − 2/k − t` form, and the second is
Theorem 10's; the better of the two algorithms has cost at most the smaller of the two
powers, and for `n ≥ 1` the smaller of `n^{2−2/k−t₁}` and `n^{2−2/k−t₂}` is
`n^{2−2/k−max(t₁,t₂)}` (`rpow_min`, `min_sub_max`).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

/-- Theorem 11's first exponent drop `(k² − 2(m+1))/(k(k+1)(m+1))` (Theorem 9 form, p. 16). -/
def thm11t1 (k m : ℕ) : ℝ :=
  ((k : ℝ) ^ 2 - 2 * ((m : ℝ) + 1)) / ((k : ℝ) * ((k : ℝ) + 1) * ((m : ℝ) + 1))

/-- Theorem 11's second exponent drop `(2k − d − 3)/(k(d+1)(m−d+2))` (Theorem 10 form,
p. 16). -/
def thm11t2 (k d m : ℕ) : ℝ :=
  (2 * (k : ℝ) - (d : ℝ) - 3) / ((k : ℝ) * ((d : ℝ) + 1) * ((m : ℝ) - (d : ℝ) + 2))

/-- Theorem 11's combined exponent `2 − 2/k − max t₁ t₂` (p. 16). -/
def thm11Exponent (k d m : ℕ) : ℝ :=
  2 - 2 / (k : ℝ) - max (thm11t1 k m) (thm11t2 k d m)

/-- Theorem 9's exponent coincides with `2 − 2/k − t₁` (the identity behind the first entry
of Theorem 11's maximum, p. 16). -/
theorem thm9Exponent_eq_t1 (k m : ℕ) (hk : 3 ≤ k) :
    thm9Exponent k m = 2 - 2 / (k : ℝ) - thm11t1 k m := by
  rw [thm9Exponent, thm11t1]
  have hk0 : (k : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    exact ne_of_gt h
  have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
  have hm1 : ((m : ℝ) + 1) ≠ 0 := by positivity
  field_simp
  ring

/-- Theorem 10's exponent coincides with `2 − 2/k − t₂` (the identity behind the second
entry of Theorem 11's maximum, p. 16). -/
theorem thm10Exponent_eq_t2 (k d m : ℕ) :
    thm10Exponent k d m = 2 - 2 / (k : ℝ) - thm11t2 k d m := by
  rw [thm10Exponent, thm11t2]

/-- Fixed source arXiv:1109.5135v1, Theorem 11 (p. 16): the combination of the algorithms of
Theorems 9 and 10. If a cost `c` is at most both Theorem 9's bound `n^{2−2/(k+1)−t}` and
Theorem 10's bound `n^{2−2/k−t}`, then it is at most `n^{2−2/k−max(t₁,t₂)}` with the two
fractions `t₁, t₂` of Theorem 11. -/
theorem source_theorem_11 (k d m : ℕ) (hk : 3 ≤ k) (hd : 1 ≤ d) (hdm : d ≤ m)
    (n : ℝ) (hn : 1 ≤ n) (c : ℝ)
    (h9 : c ≤ n ^ (thm9Exponent k m))
    (h10 : c ≤ n ^ (thm10Exponent k d m)) :
    c ≤ n ^ thm11Exponent k d m := by
  rw [thm11Exponent]
  by_cases hn1 : n ≤ 1
  · have hn_eq : n = 1 := le_antisymm hn1 hn
    subst hn_eq
    simpa using h9
  · have h1 : 1 < n := lt_of_not_ge hn1
    have hmin : min (n ^ (2 - 2 / (k : ℝ) - thm11t1 k m))
        (n ^ (2 - 2 / (k : ℝ) - thm11t2 k d m))
        = n ^ (2 - 2 / (k : ℝ) - max (thm11t1 k m) (thm11t2 k d m)) := by
      rw [rpow_min h1, min_sub_max]
    rw [← hmin]
    refine le_min ?_ ?_
    · rwa [thm9Exponent_eq_t1 k m hk] at h9
    · rwa [thm10Exponent_eq_t2 k d m] at h10

end Qatlib.Papers.LearningGraph11.MainResults
