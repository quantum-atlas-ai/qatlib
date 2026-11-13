/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Native Johnson data-access specification

`NativeJohnsonData` names `NativeJohnsonDataContract`, the specification for implementing the
setup, walk, and marked flip with stored input values. It provides the interface used to connect
the Johnson walk to the oracle-query model of collision search
[Ambainis2007ElementDistinctness].

## Main statements

* `NativeJohnsonData`: the native Johnson data-access proposition.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.UniqueCollision

/-- The proposition `NativeJohnsonDataContract`, specifying the native data-access
implementation of the Johnson walk. -/
def NativeJohnsonData : Prop := NativeJohnsonDataContract
end Qatlib.Concepts.WalkFind.UniqueCollision
