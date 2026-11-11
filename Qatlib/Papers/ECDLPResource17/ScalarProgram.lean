/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CurveGroups.AffineAdd.CyclicBitRun

/-!
# Double scalar word semantics

This module connects the ideal double scalar word program with elliptic curve group operations.
The theorem `source_double_scalar` evaluates the run from an offset as the offset plus the two
binary scalars applied to `P` and `m • P`. The word length theorem counts the scheduled
additions for two words of length `n + 1`.

The mathematical setting follows [RoettelerEtAl2017].

## Main statements

* `source_double_scalar`: ideal double scalar execution agrees with the group expression.
* `source_double_scalar_calls`: the scheduled word has length `2 * (n + 1)`.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.ScalarProgram

open Qatlib.Concepts.CurveGroups.AffineAdd
open Qatlib.Concepts.FiniteCounts.OffsetWord

/-- The ideal double scalar run from `a0`, viewed on the curve, equals `a0` plus the first
binary scalar times `P` plus the second binary scalar times `m • P`. See [Roetteler et al.,
2017, Section4.2: binary scalar multiplication and precomputation][RoettelerEtAl2017]. -/
theorem source_double_scalar (p : ℕ) [Fact p.Prime] {a b : ZMod p}
    (P : (shortCurve a b).Point) (m n : ℕ) (a0 : AddSubgroup.zmultiples P)
    (k l : Fin (n+1) → Bool) :
    ((idealRun a0 (doubleWord (cyclicGenerator P) (m • cyclicGenerator P)
      (List.ofFn k) (List.ofFn l)) : AddSubgroup.zmultiples P) : (shortCurve a b).Point) =
      (a0 : (shortCurve a b).Point) + binaryValue (List.ofFn k) • P +
        binaryValue (List.ofFn l) • (m • P) :=
  native_double_scalar P m a0 (List.ofFn k) (List.ofFn l)

/-- The double scalar word built from two bit words of length `n + 1` has length `2 * (n + 1)`.
See [Roetteler et al., 2017, Section4.2: binary scalar multiplication and
precomputation][RoettelerEtAl2017]. -/
theorem source_double_scalar_calls {G : Type*} [AddCommGroup G] (P Q : G)
    (n : ℕ) (k l : Fin (n+1) → Bool) :
    (doubleWord P Q (List.ofFn k) (List.ofFn l)).length = 2*(n+1) := by
  simp [doubleWord, binaryWord_length, Nat.two_mul]

end Qatlib.Papers.ECDLPResource17.ScalarProgram
