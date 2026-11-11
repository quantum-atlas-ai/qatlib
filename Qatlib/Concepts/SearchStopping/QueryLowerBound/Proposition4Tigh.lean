/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.QueryLowerBound.Proposition4Stat
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.InnerProductSpace.Defs
import Mathlib.Tactic.Linarith

/-!
# Distance between scaled unit vectors

Proves `proposition4`, the norm lower bound encoded by `Proposition4` in a complex inner product
space. This estimate supplies a geometric ingredient for query hybrid arguments. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `proposition4`: Establishes `Proposition4`, bounding the squared distance between scaled unit
  vectors below by the squared difference of the scalar norms.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

namespace Qatlib.Concepts.SearchStopping.QueryLowerBound

universe u

/-- Establishes `Proposition4`, bounding the squared distance between scaled unit vectors below
by the squared difference of the scalar norms. See [BoyerEtAl1998]. -/
theorem proposition4 : Proposition4.{u} := by
  intro E _ _ a b ha hb α β
  have reverse_triangle := abs_norm_sub_norm_le (α • a) (β • b)
  simp only [norm_smul, ha, hb, mul_one] at reverse_triangle
  have squared := (sq_le_sq₀ (abs_nonneg (‖α‖ - ‖β‖))
    (norm_nonneg (α • a - β • b))).2 reverse_triangle
  rw [sq_abs] at squared
  nlinarith [squared]

end Qatlib.Concepts.SearchStopping.QueryLowerBound
