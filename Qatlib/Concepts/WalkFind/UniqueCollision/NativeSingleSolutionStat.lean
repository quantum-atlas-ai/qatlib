/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

@[expose] public section

/-!
# Native unique-collision search specification

`NativeSingleSolution` names `NativeSingleSolutionContract`, the proposition specifying native
Johnson-walk search for an input with a unique collision. It is the interface for the native
version of the unique-solution analysis in [Ambainis2007ElementDistinctness].

## Main statements

* `NativeSingleSolution`: the native unique-collision search proposition.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.UniqueCollision

/-- The proposition `NativeSingleSolutionContract`, specifying native search with a unique
collision. -/
def NativeSingleSolution : Prop := NativeSingleSolutionContract
end Qatlib.Concepts.WalkFind.UniqueCollision
