/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.PayoffRotation.RationalPayoffRotation

/-!
# Scaled rational square-root routines

This module defines `bracket` by applying `rationalSqrtBracket` to `q / (S * S)` and multiplying
its two endpoints by `S`, while preserving its comparison counter. The definition `uncertain`
selects a lower endpoint from `a` and an upper endpoint from `b`; their enclosure guarantees are
proved in `ScaledRationalSqrt`. The imported payoff-rotation setting connects this numerical
construction to quantum mean estimation in [Montanaro2015].

## Main statements

* `bracket`: rescales a unit-interval square-root bracket and retains its counter.
* `uncertain`: combines the lower bracket for `a` with the upper bracket for `b`.

## References

* [Montanaro, 2015][Montanaro2015]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation

set_option autoImplicit false
namespace Qatlib.Concepts.ScaledSqrt.SqrtBounds
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Applies `rationalSqrtBracket` to `q / (S * S)`, multiplies both rational endpoints by `S`,
and preserves the comparison counter. -/
def bracket (q S : ℚ) (k : ℕ) : ℚ × ℚ × ℕ :=
  let b := Qatlib.Concepts.MonteCarloMean.PayoffRotation.rationalSqrtBracket (q/(S*S)) k
  (S*b.1,S*b.2.1,b.2.2)
/-- Returns the lower endpoint of `bracket a S k` and the upper endpoint of `bracket b S k` as a
rational endpoint pair. -/
def uncertain (a b S : ℚ) (k : ℕ) : ℚ × ℚ := ((bracket a S k).1,(bracket b S k).2.1)

end Qatlib.Concepts.ScaledSqrt.SqrtBounds
