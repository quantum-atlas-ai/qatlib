/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Statement of Algorithm 3 collision isolation

`Algorithm3Isolation` names the collision-isolation contract for the retention step in recursive
search. It is the interface connecting quantitative retention estimates to the success argument.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `Algorithm3Isolation`: names the isolation contract.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.SearchAlgorithm

/-- The proposition given by `Algorithm3IsolationContract`. -/
def Algorithm3Isolation : Prop := Algorithm3IsolationContract
end Qatlib.Concepts.WalkFind.SearchAlgorithm
