/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Statement of the truncation hybrid estimate

`TruncationHybrid` names the contract comparing finite unitary evolutions that agree outside
designated bad components. The contract supplies the norm estimate used to control errors from
truncating data-structure operations.

The mathematical background is developed in [Ambainis2007ElementDistinctness].

## Main statements

* `TruncationHybrid`: names the hybrid error contract.

## References

* [Ambainis, 2007][Ambainis2007ElementDistinctness]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.QRAMModel

/-- The proposition given by `TruncationHybridContract`. -/
def TruncationHybrid : Prop := TruncationHybridContract
end Qatlib.Concepts.WalkFind.QRAMModel
