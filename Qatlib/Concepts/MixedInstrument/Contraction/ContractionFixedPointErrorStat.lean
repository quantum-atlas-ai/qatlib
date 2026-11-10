/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MixedInstrument.Contraction

open Qatlib

def ContractionFixedPointError : Prop :=
  ∀ (D : ℕ) (T : QuantumChannel D D) (σs ρG : Operator D),
    IsDensityOperator σs → IsDensityOperator ρG → T.map σs = σs →
    ∀ η : ℝ, 0 ≤ η → η < 1 →
      (∀ X Y : Operator D, IsDensityOperator X → IsDensityOperator Y →
        SchattenOne (T.map X - T.map Y) ≤ η * SchattenOne (X - Y)) →
      ∀ ε : ℝ, 0 ≤ ε → SchattenOne (T.map ρG - ρG) ≤ ε →
        SchattenOne (σs - ρG) ≤ ε / (1 - η)

end Qatlib.Concepts.MixedInstrument.Contraction
