/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Nat.Totient
set_option autoImplicit false
namespace Qatlib.Papers.AmpTransform14.TotientLimInf

def TotientLimInf : Prop :=
  Filter.liminf
    (fun N : ℕ => (Nat.totient N : ℝ) * Real.log (Real.log (N : ℝ)) / (N : ℝ))
    Filter.atTop = Real.exp (-Real.eulerMascheroniConstant)

end Qatlib.Papers.AmpTransform14.TotientLimInf
