/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel

/-!
# Contractive fixed point error specification

`ContractionFixedPointError` states the perturbation estimate for a quantum channel that
contracts Schatten one distance on density operators. A reference density operator with one step
residual at most `ε` is within `ε / (1 - η)` of the fixed density operator. The specification
follows the fixed point error estimate in [TemmeEtAl2011].

## Main statements

* `ContractionFixedPointError`: The proposition that density domain contraction by `0 ≤ η < 1`
  bounds the distance from a fixed density operator to a reference density operator by its
  residual bound `ε / (1 - η)`.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MixedInstrument.Contraction

open Qatlib

/-- The proposition that density domain contraction by `0 ≤ η < 1` bounds the distance from a
fixed density operator to a reference density operator by its residual bound `ε / (1 - η)`. -/
def ContractionFixedPointError : Prop :=
  ∀ (D : ℕ) (T : QuantumChannel D D) (σs ρG : Operator D),
    IsDensityOperator σs → IsDensityOperator ρG → T.map σs = σs →
    ∀ η : ℝ, 0 ≤ η → η < 1 →
      (∀ X Y : Operator D, IsDensityOperator X → IsDensityOperator Y →
        SchattenOne (T.map X - T.map Y) ≤ η * SchattenOne (X - Y)) →
      ∀ ε : ℝ, 0 ≤ ε → SchattenOne (T.map ρG - ρG) ≤ ε →
        SchattenOne (σs - ρG) ≤ ε / (1 - η)

end Qatlib.Concepts.MixedInstrument.Contraction
