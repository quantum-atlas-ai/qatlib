/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CurveGroups.AffineAdd.CyclicBitRun
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.ScalarProgram

open Qatlib.Concepts.CurveGroups.AffineAdd
open Qatlib.Concepts.FiniteCounts.OffsetWord

theorem source_double_scalar (p : ℕ) [Fact p.Prime] {a b : ZMod p}
    (P : (shortCurve a b).Point) (m n : ℕ) (a0 : AddSubgroup.zmultiples P)
    (k l : Fin (n+1) → Bool) :
    ((idealRun a0 (doubleWord (cyclicGenerator P) (m • cyclicGenerator P)
      (List.ofFn k) (List.ofFn l)) : AddSubgroup.zmultiples P) : (shortCurve a b).Point) =
      (a0 : (shortCurve a b).Point) + binaryValue (List.ofFn k) • P +
        binaryValue (List.ofFn l) • (m • P) :=
  native_double_scalar P m a0 (List.ofFn k) (List.ofFn l)

theorem source_double_scalar_calls {G : Type*} [AddCommGroup G] (P Q : G)
    (n : ℕ) (k l : Fin (n+1) → Bool) :
    (doubleWord P Q (List.ofFn k) (List.ofFn l)).length = 2*(n+1) := by
  simp [doubleWord, binaryWord_length, Nat.two_mul]

end Qatlib.Papers.ECDLPResource17.ScalarProgram
