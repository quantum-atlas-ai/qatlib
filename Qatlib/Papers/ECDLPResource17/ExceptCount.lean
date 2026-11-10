/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.FiniteCounts.ExceptionalBits.NativeTrace
import Qatlib.Concepts.CurveGroups.AffineAdd.FiniteCurve
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.ExceptCount

open Qatlib.Foundations.FiniteCounts.ExceptionalBits
open Qatlib.Concepts.CurveGroups.AffineAdd

theorem actual_curve_exceptional_count {K : Type*} [Field K] [DecidableEq K]
    {a4 a6 : K} (P : (shortCurve a4 a6).Point) (n a : ℕ)
    (hn : 1 ≤ n) (ha : 1 ≤ a) (har : a < addOrderOf P)
    (hwidth : 2^(n-1) ≤ addOrderOf P) :
    (nativeExceptionalSet (n:=n) P a).card ≤ 2^(n-Nat.clog 2 a)+8 :=
  native_exceptional_card_le P hn ha har hwidth

end Qatlib.Papers.ECDLPResource17.ExceptCount
