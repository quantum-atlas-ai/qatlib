/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.StoppingJointDefs

/-!
# Definitions for finite-bit execution charges

This module defines `jointFiniteBitCharge` as the maximum branch charge of a joint program and
`zeroPriceBranch` as the predicate that a branch has cost zero. These definitions provide the
accounting vocabulary for the execution charge identities. See [NielsenChuang2010] for quantum
computation background.

## Main statements

* `jointFiniteBitCharge`: records the maximum branch charge.
* `zeroPriceBranch`: expresses zero branch cost.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdaptiveCP.BranchTrace

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The maximum branch charge of a joint program, used as its finite-bit charge. -/
noncomputable def jointFiniteBitCharge {S O X : Type} [Fintype S] [Fintype X] {D E : ℕ}
    (P : JointProgram S O X D E) : ℕ :=
  maxCharge P

/-- The predicate that the branch at classical state `s` has zero cost. -/
def zeroPriceBranch {S O X : Type} [Fintype X] {D E : ℕ}
    (P : JointProgram S O X D E) (s : S) : Prop :=
  P.cost s = 0

end Qatlib.Concepts.MixedInstrument.ClockBridge
