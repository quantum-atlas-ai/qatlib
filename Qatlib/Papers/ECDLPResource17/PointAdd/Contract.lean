/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CurveGroups.AffineAdd.NativeXor
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.ECDLPResource17.PointAdd

open WeierstrassCurve.Affine
open Qatlib.Concepts.CurveGroups.AffineAdd

theorem source_algorithm1_corrected {K : Type*} [Field K] [DecidableEq K]
    {a b x1 y1 x2 y2 : K}
    (h1 : (shortCurve a b).Nonsingular x1 y1)
    (h2 : (shortCurve a b).Nonsingular x2 y2) (hx : x1 ≠ x2)
    (hminus2 : Point.some x1 y1 h1 ≠ -(Point.some x2 y2 h2 + Point.some x2 y2 h2)) :
    (∃ h3 : (shortCurve a b).Nonsingular
        (run true x2 y2 x1 y1).x1 (run true x2 y2 x1 y1).y1,
      Point.some x1 y1 h1 + Point.some x2 y2 h2 = Point.some _ _ h3) ∧
    (run true x2 y2 x1 y1).lam = 0 ∧ (run true x2 y2 x1 y1).t0 = 0 :=
  corrected_schedule h1 h2 hx hminus2

theorem source_prime_bitword (p w : ℕ) [Fact p.Prime] (hp : p ≤ 2^w)
    {a b x1 y1 x2 y2 : ZMod p}
    (h1 : (shortCurve a b).Nonsingular x1 y1)
    (h2 : (shortCurve a b).Nonsingular x2 y2) (hx : x1 ≠ x2)
    (hminus2 : Point.some x1 y1 h1 ≠ -(Point.some x2 y2 h2 + Point.some x2 y2 h2)) :
    let E := primeFieldEncoding p w hp
    ∃ x3 y3, ∃ h3 : (shortCurve a b).Nonsingular x3 y3,
      Point.some x1 y1 h1 + Point.some x2 y2 h2 = Point.some x3 y3 h3 ∧
      sourcePermutation E x2 y2 ⟨E.encode x1,E.encode y1,0,0⟩ =
        ⟨E.encode x3,E.encode y3,0,0⟩ :=
  sourcePermutation_native (primeFieldEncoding p w hp) h1 h2 hx hminus2

end Qatlib.Papers.ECDLPResource17.PointAdd
