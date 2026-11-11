/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.OracleTwirling
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Group.TypeTags.Basic

/-!
# Two-point group and plus density

This module defines `SourceTwoPointGroup` as the multiplicative form of `ZMod 2` and
`sourcePlusDensity` as its constant matrix with entry one half. These objects supply the finite
example used in the twirling counterexample. See [Watrous2018] for the mathematical background.

## Main statements

* `SourceTwoPointGroup`: the group of order two.
* `sourcePlusDensity`: the constant two-by-two density matrix.

## References

* [Watrous, 2018][Watrous2018]
-/

open scoped ComplexOrder
set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.RecordExtract
/-- The additive group `ZMod 2` viewed in multiplicative notation. -/
abbrev SourceTwoPointGroup := Multiplicative (ZMod 2)
/-- The matrix indexed by the two-point group whose every entry is `1 / 2`. -/
noncomputable def sourcePlusDensity : Matrix SourceTwoPointGroup SourceTwoPointGroup ℂ :=
  fun _ _ => 1 / 2
end Qatlib.Concepts.HspRecovery.RecordExtract
