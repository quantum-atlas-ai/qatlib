/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Unrestricted perturbation counterexample specification

`UnrestrictedPerturbationCounterexample` names `UnrestrictedPerturbationCounterexampleContract`.
It provides the counterexample proposition used when specifying the scope of perturbation
arguments in Johnson-walk collision-search analysis [Ambainis2007ElementDistinctness].

## Main statements

* `UnrestrictedPerturbationCounterexample`: the named counterexample contract.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.UniqueCollision

/-- The proposition `UnrestrictedPerturbationCounterexampleContract`, naming the unrestricted
perturbation counterexample specification. -/
def UnrestrictedPerturbationCounterexample : Prop := UnrestrictedPerturbationCounterexampleContract
end Qatlib.Concepts.WalkFind.UniqueCollision
