/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.QuantumChannel

/-!
# Geometric channel mixing specification

`ContractionMixingDecay` specifies geometric convergence to a fixed density operator for a
channel contracting Schatten one distance on the density domain. The bound multiplies the
initial distance by `η ^ m`, as used in quantum Metropolis mixing estimates [TemmeEtAl2011].

## Main statements

* `ContractionMixingDecay`: The proposition that `m` iterations of a density domain contraction
  with factor `0 ≤ η < 1` reduce distance to a fixed density operator by at least the factor `η
  ^ m`.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MixedInstrument.Contraction

open Qatlib

/-- The proposition that `m` iterations of a density domain contraction with factor `0 ≤ η < 1`
reduce distance to a fixed density operator by at least the factor `η ^ m`. -/
def ContractionMixingDecay : Prop :=
  ∀ (D : ℕ) (T : QuantumChannel D D) (σs ρ0 : Operator D),
    IsDensityOperator σs → IsDensityOperator ρ0 → T.map σs = σs →
    ∀ η : ℝ, 0 ≤ η → η < 1 →
      (∀ X Y : Operator D, IsDensityOperator X → IsDensityOperator Y →
        SchattenOne (T.map X - T.map Y) ≤ η * SchattenOne (X - Y)) →
      ∀ m : ℕ, SchattenOne ((T.map^[m]) ρ0 - σs) ≤ η ^ m * SchattenOne (ρ0 - σs)

end Qatlib.Concepts.MixedInstrument.Contraction
