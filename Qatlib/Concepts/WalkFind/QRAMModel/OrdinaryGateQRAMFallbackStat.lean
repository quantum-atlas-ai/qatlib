/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkFind.SearchAlgorithm.NativeSourceDefs

/-!
# Statement of the ordinary gate QRAM fallback

`OrdinaryGateQRAMFallback` names the contract for replacing QRAM source operations by ordinary
finite-gate circuits. This statement provides the interface used by the quantitative
implementation.

The mathematical background is developed in [NielsenChuang2010].

## Main statements

* `OrdinaryGateQRAMFallback`: names the finite-gate fallback contract.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.WalkFind.SearchAlgorithm
set_option autoImplicit false
namespace Qatlib.Concepts.WalkFind.QRAMModel

/-- The proposition given by `OrdinaryGateQRAMFallbackContract`. -/
def OrdinaryGateQRAMFallback : Prop := OrdinaryGateQRAMFallbackContract
end Qatlib.Concepts.WalkFind.QRAMModel
