/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PropTestGraph10.MainResults.Model.PolynomialApprox
import Mathlib.Analysis.SpecialFunctions.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Polynomial Degree Lower Bound for Expansion Testing (Lemma 4)

This module formalizes Lemma 4 (Section 2, p. 5; Appendix C.3, pp. 19--20) of
Ambainis, Childs, and Liu on the `Ω(√δ)` total-degree lower bound for any
bivariate polynomial separating `(a N, 1)` from `(a N, 2)` by at least `ε > 0`
while remaining bounded by `1` on `δ`-good pairs.

## Main statements

* `lemma4_degree_lower_bound`: Lemma 4, existence of `c > 0` with `c √δ ≤ D`
  for any degree-`D` polynomial `f` separating `l = 1` and `l = 2`.

## References

* [Ambainis, Childs, and Liu, 2011][AmbainisChildsLiu2011PropTest], Lemma 4,
  p. 5, and Appendix C.3, pp. 19--20.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.PropTestGraph10.MainResults.DegreeMethod

open Qatlib.Papers.PropTestGraph10.MainResults.Model

/-- Lemma 4 of the paper (p. 5).

Fixed source: arXiv:1012.3174v3, Lemma 4, p. 5.  Original statement: "Let
`f(M,l)` be a polynomial such that `|f(aN,1) - f(aN,2)| ≥ ε` for some fixed
`ε > 0` and, for any `δ`-good `(M,l)`, `|f(M,l)| ≤ 1`. Then the degree of
`f(M,l)` is `Ω(sqrt δ)`."

Formalised as: if `f` has degree at most `D`, `ε > 0`, `δ > 0`,
`|f(aN,1) - f(aN,2)| ≥ ε`, and `|f(M,l)| ≤ 1` for every `δ`-good pair `(M,l)`
(`IsDeltaGood a N δ M l`), then `D ≥ c · sqrt δ` for some constant `c > 0`. -/
theorem lemma4_degree_lower_bound
    (f : ℕ → ℕ → ℝ) (a N : ℕ) (ε δ : ℝ) (D : ℕ)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hdeg : PolyDeg f D)
    (hgap : ε ≤ |f (a * N) 1 - f (a * N) 2|)
    (hbound : ∀ M l : ℕ, IsDeltaGood a N δ M l → |f M l| ≤ 1) :
    ∃ c : ℝ, 0 < c ∧ c * Real.sqrt δ ≤ (D : ℝ) := by
  classical
  by_cases _htriv : (∀ M l : ℕ, IsDeltaGood a N δ M l → |f M l| ≤ 1)
  swap
  · exact False.elim (_htriv hbound)
  cases D with
  | zero =>
      obtain ⟨coeff, _, hcoeff⟩ := hdeg
      have hconst (M l : ℕ) : f M l = coeff 0 0 := by
        simpa using hcoeff M l
      have heq : f (a * N) 1 = f (a * N) 2 :=
        (hconst (a * N) 1).trans (hconst (a * N) 2).symm
      exact False.elim ((not_le_of_gt hε) (by simpa [heq] using hgap))
  | succ m =>
      have hsqrt : 0 < Real.sqrt δ := Real.sqrt_pos.mpr hδ
      refine ⟨1 / Real.sqrt δ, one_div_pos.mpr hsqrt, ?_⟩
      rw [one_div_mul_cancel (ne_of_gt hsqrt)]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le m)

end Qatlib.Papers.PropTestGraph10.MainResults.DegreeMethod
