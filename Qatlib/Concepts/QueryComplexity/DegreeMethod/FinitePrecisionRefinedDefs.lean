/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCoreDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionNative
import Qatlib.Concepts.BitWordCompiler.CanonicalCodec.BitWordEmitterDefs
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.IntervalArith.IntervalOps

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod

open Qatlib

set_option autoImplicit false

structure FixedPoint where

  bits : List Bool

  scale : ℕ

def FixedPoint.value (f : FixedPoint) : ℚ :=
    (Qatlib.Concepts.BitWordCompiler.CanonicalCodec.binaryValue f.bits : ℚ) / 2 ^ f.scale

def fixedPointBitTime (x y : FixedPoint) : ℕ := x.bits.length + y.bits.length

def roundingScale (f : FixedPoint) : ℕ := f.bits.length + f.scale

end Qatlib.Concepts.QueryComplexity.DegreeMethod
