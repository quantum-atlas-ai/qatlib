/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Qatlib

/-!
# Root re-export regression

An ordinary root-only import makes leaf definitions and theorems available to consumers.
-/

open Qatlib.Foundations.ScaledSqrt.SqrtBounds

example (n : ℕ) : signedCount false n = (n : ℤ) := rfl

example (negative : Bool) (n : ℕ) : (signedCount negative n).natAbs = n :=
  signedCount_natAbs negative n
