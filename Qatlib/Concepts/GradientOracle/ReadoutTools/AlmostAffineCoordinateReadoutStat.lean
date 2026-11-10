/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.ReadoutTools.ExceptionalPhaseGradientTransportStat
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.SignalPrimitive.GridGradient

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath

set_option autoImplicit false
namespace Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib
open scoped Classical BigOperators

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
