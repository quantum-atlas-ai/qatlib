/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Grover interpolation contract including minus one

This module names the native-source proposition `GroverIncludingMinusOneContract` as
`GroverIncludingMinusOne`. This is the contract used for the Grover interpolation case in which
the background spectrum may contain eigenvalue minus one.

For background, see [Ambainis2007ElementDistinctness].

## Main statements

* `GroverIncludingMinusOne`: the local name for the native-source interpolation contract.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.GroverInterp

/-- The native-source Grover interpolation contract `GroverIncludingMinusOneContract`, allowing
eigenvalue minus one in the background spectrum. -/
def GroverIncludingMinusOne : Prop := GroverIncludingMinusOneContract
end Qatlib.Concepts.WalkFind.GroverInterp
