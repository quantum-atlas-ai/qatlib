/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.ExceptionalPhaseGradientTransportStat

/-!
# Specification of almost-affine coordinate readout

`AlmostAffineCoordinateReadout` states a per-coordinate success bound when the phase is close to
affine on all but a `1/1000` fraction of the grid. It includes unitarity and resource counts for
the robust gradient readout associated with [GilyenArunachalamWiebe2019].

## Main statements

* `AlmostAffineCoordinateReadout`: each signed coordinate estimate has error at most `4/2^n`
  with probability at least `2/3`.

## References

* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SignalPrimitive.GridGradient

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib
open scoped Classical BigOperators

/-- The proposition that an almost-affine phase on all but a `1/1000` fraction of the grid gives
each signed coordinate error at most `4/2^n` with probability at least `2/3`, together with
unitarity and circuit counts. -/
def AlmostAffineCoordinateReadout : Prop :=
  ∀ (d n : ℕ) (hN : 0 < 2^n) (φ : GradientGrid d (2^n) → ℝ)
    (g : Fin d → ℝ) (c : ℝ) (S : Finset (GradientGrid d (2^n))),
    (∀ j, |g j| ≤ 1/3) →
    ((Finset.univ \ S).card : ℝ) ≤ ((2 : ℝ)^n)^d/1000 →
    (∀ x ∈ S, |φ x-(c+∑ j, g j*(x j).val)| ≤ 1/(42*Real.pi)) →
    (∀ j : Fin d,
      2/3 ≤ MeasureProb (gradientReadout d (2^n) hN φ)
        (Finset.univ.filter fun z => |signedGridValue (2^n) (z j)-g j| ≤ 4/(2 : ℝ)^n)) ∧
    IsUnitaryCircuit (gradientWord d (2^n)) ∧
    QueryCount (gradientWord d (2^n)) = 1 ∧ GateCount (gradientWord d (2^n)) = 2*d

end Qatlib.Concepts.GradientOracle.ReadoutTools
