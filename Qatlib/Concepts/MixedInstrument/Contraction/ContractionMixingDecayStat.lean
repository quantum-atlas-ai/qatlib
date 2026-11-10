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

def ContractionMixingDecay : Prop :=
  ∀ (D : ℕ) (T : QuantumChannel D D) (σs ρ0 : Operator D),
    IsDensityOperator σs → IsDensityOperator ρ0 → T.map σs = σs →
    ∀ η : ℝ, 0 ≤ η → η < 1 →
      (∀ X Y : Operator D, IsDensityOperator X → IsDensityOperator Y →
        SchattenOne (T.map X - T.map Y) ≤ η * SchattenOne (X - Y)) →
      ∀ m : ℕ, SchattenOne ((T.map^[m]) ρ0 - σs) ≤ η ^ m * SchattenOne (ρ0 - σs)

end Qatlib.Concepts.MixedInstrument.Contraction
