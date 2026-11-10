/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPointExt
set_option warningAsError false
open Qatlib.Papers.FixedPtSearch14.FixedPoint

set_option autoImplicit false

namespace Qatlib.Papers.FixedPtSearch14.FixedPoint

open Matrix
open scoped BigOperators Classical
open Qatlib.Papers.FixedPtSearch14.FixedPoint

def UniformWord (l : ℕ) (delta bits : ℕ) : Prop :=
  ∀ lam : ℝ, accessWordMatrix lam (fixedPointAccessWord l delta bits)
    = publicWord l delta lam

def UniformAccessLedger (l : ℕ) (delta bits : ℕ) : Prop :=
  prepAccessCount (fixedPointAccessWord l delta bits) = 2 * l ∧
  queryAccessCount (fixedPointAccessWord l delta bits) = 2 * l ∧
  phaseAccessCount (fixedPointAccessWord l delta bits) = 2 * l ∧
  phaseBitCount (fixedPointAccessWord l delta bits) = 2 * l * bits

end Qatlib.Papers.FixedPtSearch14.FixedPoint
