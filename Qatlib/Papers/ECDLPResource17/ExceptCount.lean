/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteCounts.ExceptionalBits.NativeTrace
import Qatlib.Concepts.CurveGroups.AffineAdd.FiniteCurve

/-!
# Exceptional scalar counts on elliptic curves

This module specializes the native exceptional scalar count to points on a short Weierstrass
curve. The theorem `actual_curve_exceptional_count` bounds the cardinality of the exceptional
set in terms of the bit width and the binary ceiling logarithm of the scalar, under point order
and width hypotheses.

The mathematical setting follows [RoettelerEtAl2017].

## Main statements

* `actual_curve_exceptional_count`: an exceptional set bound of `2^(n - Nat.clog 2 a) + 8`.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.ExceptCount

open Qatlib.Foundations.FiniteCounts.ExceptionalBits
open Qatlib.Concepts.CurveGroups.AffineAdd

/-- For positive width `n` and scalar `a` below the order of `P`, with `2^(n - 1)` at most that
order, the native exceptional set has cardinality at most `2^(n - Nat.clog 2 a) + 8`. See
[Roetteler et al., 2017, Section4.3: exceptional doubling scalar count][RoettelerEtAl2017]. -/
theorem actual_curve_exceptional_count {K : Type*} [Field K] [DecidableEq K]
    {a4 a6 : K} (P : (shortCurve a4 a6).Point) (n a : ℕ)
    (hn : 1 ≤ n) (ha : 1 ≤ a) (har : a < addOrderOf P)
    (hwidth : 2^(n-1) ≤ addOrderOf P) :
    (nativeExceptionalSet (n:=n) P a).card ≤ 2^(n-Nat.clog 2 a)+8 :=
  native_exceptional_card_le P hn ha har hwidth

end Qatlib.Papers.ECDLPResource17.ExceptCount
