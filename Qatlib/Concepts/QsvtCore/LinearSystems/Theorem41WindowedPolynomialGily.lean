/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41WindowedPolynomialStat
import Qatlib.Concepts.QsvtCore.LinearSystems.WindowedReciprocal

/-!
# Existence of a windowed reciprocal polynomial

`theorem41WindowedPolynomial` establishes the proposition `Theorem41WindowedPolynomial` from
`windowed_reciprocal_exists`. The polynomial is odd, bounded by one on `[-1, 1]`, and
approximates `(δ/2)/x` on `[δ, 1]` with explicit truncation and degree bounds.

This supplies the polynomial component of the pseudoinverse construction associated with Theorem
41 of [GilyenSuLowWiebe2019].

## Main statements

* `theorem41WindowedPolynomial`: proves the packaged windowed-polynomial existence statement.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.QsvtCore.LinearSystems

/-- Establishes `Theorem41WindowedPolynomial`: for 0 < ε ≤ δ ≤ 1/2 there is a bounded odd
polynomial approximating (δ/2)/x on [δ, 1], with the stated parameter and degree bounds.
This supplies the reciprocal-polynomial component of [Gilyén et al., Theorem
41][GilyenSuLowWiebe2019]. -/
theorem theorem41WindowedPolynomial : Theorem41WindowedPolynomial :=
  Qatlib.Concepts.QsvtCore.LinearSystems.windowed_reciprocal_exists

end Qatlib.Concepts.QsvtCore.LinearSystems
