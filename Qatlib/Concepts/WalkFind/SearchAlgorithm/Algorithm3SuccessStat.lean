/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Statement of Algorithm 3 success

`Algorithm3Success` names the success contract for recursive collision search. The contract
serves as the target of the argument combining isolation probabilities, recursion-depth bounds,
and guarantees for calls on unique collisions.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `Algorithm3Success`: names the recursive search success contract.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.SearchAlgorithm

/-- The proposition given by `Algorithm3SuccessContract`. -/
def Algorithm3Success : Prop := Algorithm3SuccessContract
end Qatlib.Concepts.WalkFind.SearchAlgorithm
