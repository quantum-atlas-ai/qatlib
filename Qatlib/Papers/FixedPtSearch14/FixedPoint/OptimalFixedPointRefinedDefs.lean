/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointExt

/-!
# Uniform word and access-ledger predicates

This module defines two propositions for the access-word interface to the fixed-point search
construction of [YoderLowChuang2014]. `UniformWord` asserts that a single access list realizes
the public word for every real good-mass parameter.

`UniformAccessLedger` specifies the exact preparation, query, phase, and phase-bit counts of
that access list. Its resource counts depend on the iterate and bit parameters.

## Main definitions

* `UniformWord`: realization for all good-mass parameters.
* `UniformAccessLedger`: the four exact resource-count identities.

## References

* [Yoder et al., 2014][YoderLowChuang2014]
-/

open Qatlib.Papers.FixedPtSearch14.FixedPoint

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix
open scoped BigOperators Classical
open Qatlib.Papers.FixedPtSearch14.FixedPoint

/-- The proposition that a fixed access word realizes `publicWord l delta lam` for every real
`lam`. -/
def UniformWord (l : ℕ) (delta bits : ℕ) : Prop :=
  ∀ lam : ℝ, accessWordMatrix lam (fixedPointAccessWord l delta bits)
    = publicWord l delta lam

/-- The proposition that the fixed access word has preparation, query, and phase counts `2 * l`
and phase-bit count `2 * l * bits`. -/
def UniformAccessLedger (l : ℕ) (delta bits : ℕ) : Prop :=
  prepAccessCount (fixedPointAccessWord l delta bits) = 2 * l ∧
  queryAccessCount (fixedPointAccessWord l delta bits) = 2 * l ∧
  phaseAccessCount (fixedPointAccessWord l delta bits) = 2 * l ∧
  phaseBitCount (fixedPointAccessWord l delta bits) = 2 * l * bits

end Qatlib.Papers.FixedPtSearch14.FixedPoint
