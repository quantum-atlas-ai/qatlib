/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DiamondQdrift.FairQdrift.MixtureExpectationSubgoalStat

/-!
# Density preservation by unitary mixtures

This module proves `MixtureExpectationSubgoal`: a finite probability mixture of unitary
conjugations maps density operators to density operators. This is the state preservation
property of the randomized channel construction used in qDRIFT [Campbell2019].

## Main statements

* `mixtureExpectationSubgoal`: unitary channel mixtures preserve density operators.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option warningAsError false

open Qatlib.Concepts.ReferenceError.RefTraceError

namespace Qatlib.Concepts.DiamondQdrift.FairQdrift

open Qatlib

/-- A finite probability mixture of unitary conjugations preserves density operators
[Campbell2019]. -/
theorem mixtureExpectationSubgoal : MixtureExpectationSubgoal :=
  fun _J _ _ _D d U hU _ρ hρ => Qatlib.Concepts.ReferenceError.RefTraceError.channelMixture_maps_density d U hU hρ

end Qatlib.Concepts.DiamondQdrift.FairQdrift
