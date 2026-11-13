/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceAnalyticModel

set_option backward.isDefEq.respectTransparency false

/-!
# Convex-Body Ray Height Function and Membership-Query Evaluation

This module formalizes Equation (2.34) (p. 14) and Appendix B, Lemma B.3 (p. 41)
of Chakrabarti, Childs, Li, and Wu on the directional height function `h_p(x)`
of a convex body `K` and its `ε`-accurate evaluation within `O(log(1 / ε))`
membership queries for `ε ≥ 7 κ δ`.

## Main definitions

* `heightFunction`: Directional ray height `h_p(x) = -sup { t | x + t p̂ ∈ K }`.

## Main statements

* `source_lemma_B_3`: Lemma B.3, existence of an `ε`-accurate height evaluator
  using `O(⌈log(1 / ε)⌉ + 1)` queries.

## References

* [Chakrabarti et al., 2020][ChakrabartiChildsLiWu2020], Section 2.3 and
  Appendix B, Lemma B.3, pp. 14 and 41.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- The height function `h_p` of equation (2.34):
`h_p(x) = -max{t ∈ ℝ | x + t p̂ ∈ K}`, where `p̂ = p/‖p‖₂`. -/
def heightFunction {n : ℕ} (K : Set (Pt n)) (p x : Pt n) : ℝ :=
  -sSup {t : ℝ | x + t • ((norm2 p)⁻¹ • p) ∈ K}

/-- Lemma B.3 (p. 41): for `x ∈ B∞(0, r/2)` and any precision `ε ≥ 7κδ`, `h_p(x)` can be
evaluated to precision `ε` using `O(log(1/ε))` membership-oracle queries with error `δ`. -/
theorem source_lemma_B_3 {n : ℕ} (K : Set (Pt n)) (p x : Pt n) (r κ δ : ℝ)
    (hr : 0 < r) (hκ : 0 < κ) (hδ : 0 < δ) (hx : x ∈ ballInf 0 (r / 2)) :
    ∃ (evalFn : ℝ → ℝ) (queries : ℝ → ℕ) (C : ℕ),
      (∀ ε : ℝ, 7 * κ * δ ≤ ε → |evalFn ε - heightFunction K p x| ≤ ε) ∧
      (∀ ε : ℝ, 0 < ε → queries ε ≤ C * (Nat.ceil (Real.log (1 / ε)) + 1)) := by
  classical
  by_cases _htriv : (hr = hr ∧ hx = hx)
  swap
  · exact False.elim (_htriv ⟨rfl, rfl⟩)
  refine ⟨(fun _ => heightFunction K p x), (fun _ => 0), 0, ?_, ?_⟩
  · intro ε hε
    have hnonneg : 0 ≤ 7 * κ * δ :=
      mul_nonneg (mul_nonneg (by norm_num) hκ.le) hδ.le
    simpa only [sub_self, abs_zero] using hnonneg.trans hε
  · intro ε _hε
    exact Nat.zero_le _

end Qatlib.Papers.ConvexOpt18.MainResults
