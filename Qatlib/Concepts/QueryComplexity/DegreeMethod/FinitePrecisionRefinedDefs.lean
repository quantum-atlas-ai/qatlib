/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordEmitterDefs

/-!
# Fixed-point representations

This module defines `FixedPoint` as a bit-list mantissa with a natural binary scale. The
rational interpretation `FixedPoint.value` divides the mantissa value by the corresponding power
of two, giving a concrete finite representation of nonnegative dyadic values as used in finite
arithmetic [KitaevShenVyalyi2002].

The functions `fixedPointBitTime` and `roundingScale` record the sum of two input bit lengths
and the sum of a mantissa length with its scale, respectively.

## Main statements

* `FixedPoint`: a bit list and a binary scale.
* `FixedPoint.value`: the rational interpretation of the representation.
* `fixedPointBitTime`: the sum of the stored input bit lengths.
* `roundingScale`: the stored bit length plus the scale.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.IntervalArith.IntervalOps

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib

set_option autoImplicit false

/-- An unsigned fixed-point representation consisting of a bit-list mantissa and a natural
binary scale. -/
structure FixedPoint where

  bits : List Bool

  scale : ℕ

/-- The rational value of a fixed-point representation, equal to its binary mantissa divided by
two raised to its scale. -/
def FixedPoint.value (f : FixedPoint) : ℚ :=
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue f.bits : ℚ) / 2 ^ f.scale

/-- The bit-time count assigned to two fixed-point inputs, equal to the sum of their stored bit
lengths. -/
def fixedPointBitTime (x y : FixedPoint) : ℕ := x.bits.length + y.bits.length

/-- The rounding scale assigned to a fixed-point representation, equal to its stored bit length
plus its binary scale. -/
def roundingScale (f : FixedPoint) : ℕ := f.bits.length + f.scale

end Qatlib.Concepts.QueryComplexity.DegreeMethod
