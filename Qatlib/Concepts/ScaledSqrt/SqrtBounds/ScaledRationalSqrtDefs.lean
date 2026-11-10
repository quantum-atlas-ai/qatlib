/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

set_option autoImplicit false
namespace Qatlib.Concepts.ScaledSqrt.SqrtBounds
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

def bracket (q S : ℚ) (k : ℕ) : ℚ × ℚ × ℕ :=
  let b := Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q/(S*S)) k
  (S*b.1,S*b.2.1,b.2.2)
def uncertain (a b S : ℚ) (k : ℕ) : ℚ × ℚ := ((bracket a S k).1,(bracket b S k).2.1)

end Qatlib.Concepts.ScaledSqrt.SqrtBounds
