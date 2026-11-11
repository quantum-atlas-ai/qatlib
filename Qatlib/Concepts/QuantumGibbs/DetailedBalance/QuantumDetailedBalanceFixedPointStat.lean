/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalance

/-!
# The detailed-balance fixed-point contract

This module states `QuantumDetailedBalanceFixedPoint`, the stationarity implication for a
quantum channel and a density operator. It isolates the precise channel and state assumptions
used with the detailed-balance symmetry of [TemmeEtAl2011].

## Main statements

* `QuantumDetailedBalanceFixedPoint`: The quantified stationarity implication.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath


namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Qatlib

/-- The proposition that every density operator satisfying quantum detailed balance for a
quantum channel is fixed by the channel. -/
def QuantumDetailedBalanceFixedPoint : Prop :=
  ∀ (D : ℕ) (T : QuantumChannel D D) (σ : Operator D),
    IsDensityOperator σ → QuantumDetailedBalance T.map σ → T.map σ = σ

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
