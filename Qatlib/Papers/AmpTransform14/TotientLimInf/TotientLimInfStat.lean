/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Data.Nat.Totient

/-!
# The totient lower-limit statement

The proposition `TotientLimInf` states Landau's lower-limit formula for the normalized totient
carrier `φ(N) * log(log N) / N`. It names the statement independently of its analytic proof.
This development supports the treatment in [Cornwell2014].

## Main statements

* `TotientLimInf`: the lower limit equals the exponential of the negative Euler–Mascheroni
  constant.

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false
namespace Qatlib.Papers.AmpTransform14.TotientLimInf

/-- The proposition that the lower limit of `φ(N) * log(log N) / N` along the natural numbers
equals `exp(-eulerMascheroniConstant)`. -/
def TotientLimInf : Prop :=
  Filter.liminf
    (fun N : ℕ => (Nat.totient N : ℝ) * Real.log (Real.log (N : ℝ)) / (N : ℝ))
    Filter.atTop = Real.exp (-Real.eulerMascheroniConstant)

end Qatlib.Papers.AmpTransform14.TotientLimInf
