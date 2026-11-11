/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.RejectionInstrumentSubgoalStat

/-!
# Metropolis acceptance and coin guarantees

This module proves the Metropolis rejection-instrument subgoal by combining pointwise detailed
balance of accepted transitions with the unitary acceptance coin. These are finite transition
and measurement ingredients of the quantum Metropolis construction in [TemmeEtAl2011].

## Main statements

* `rejectionInstrumentSubgoal`: Detailed balance and a unitary coin with the specified
  acceptance probability.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.WalkSearch.TwoLevelLower

namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Qatlib

/-- Prove pointwise detailed balance for Metropolis-accepted transitions and, for every
acceptance parameter in `[0, 1]`, unitarity of the Metropolis coin with Born probability
equal to that parameter. -/
theorem rejectionInstrumentSubgoal : RejectionInstrumentSubgoal :=
  fun I _ _ P hP π hπ =>
    ⟨fun x y => Qatlib.Concepts.WalkSearch.TwoLevelLower.metropolisAcceptance_detailed_balance P hP hπ x y,
     fun a h0 h1 => ⟨Qatlib.Concepts.WalkSearch.TwoLevelLower.metropolisCoin_unitary h0 h1,
       Qatlib.Concepts.WalkSearch.TwoLevelLower.metropolisCoin_accept_prob h0⟩⟩

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
