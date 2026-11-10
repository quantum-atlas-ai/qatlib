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

private instance primeFive : Fact (Nat.Prime 5) := ⟨by decide⟩

theorem source_cleanup_counterexample :
    let E := primeFieldEncoding 5 3 (by decide)
    ∃ h1 : (shortCurve (2 : ZMod 5) 1).Nonsingular 1 2,
    ∃ h2 : (shortCurve (2 : ZMod 5) 1).Nonsingular 0 1,
      Point.some 1 2 h1 ≠ Point.some 0 1 h2 ∧
      Point.some 1 2 h1 ≠ -Point.some 0 1 h2 ∧
      (sourcePermutation E 0 1 ⟨E.encode 1,E.encode 2,0,0⟩).lam = E.encode 1 ∧
      (sourcePermutation E 0 1 ⟨E.encode 1,E.encode 2,0,0⟩).lam ≠ 0 := by
  let E := primeFieldEncoding 5 3 (by decide)
  have h1 : (shortCurve (2 : ZMod 5) 1).Nonsingular 1 2 := by
    norm_num [nonsingular_iff', equation_iff', shortCurve]; decide
  have h2 : (shortCurve (2 : ZMod 5) 1).Nonsingular 0 1 := by
    norm_num [nonsingular_iff', equation_iff', shortCurve]; decide
  have hx : (1 : ZMod 5) ≠ 0 := by decide
  have hp := (not_iff_not.mpr (Point.X_eq_iff (h₁:=h1) (h₂:=h2))).mp hx
  have hb := xorPointRun_zero_second E (1 : ZMod 5) 2 0 1 hx (by norm_num)
  have hl : (sourcePermutation E 0 1 ⟨E.encode 1,E.encode 2,0,0⟩).lam = E.encode 1 := by
    rw [sourcePermutation_clean_apply, hb]
    norm_num
  refine ⟨h1,h2,fun h => hp (Or.inl h),fun h => hp (Or.inr h),hl,?_⟩
  rw [hl]
  intro hz
  have : (1 : ZMod 5) = 0 := E.encode.injective (hz.trans E.encode_zero.symm)
  exact hx this

end Qatlib.Papers.ECDLPResource17.PointAdd
