/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AdaptiveCP.BranchTrace.StoppingJointDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdversaryBounds.AdvDuality
open Qatlib.Concepts.AdaptiveCP.BranchTrace

namespace Qatlib.Concepts.MixedInstrument.ClockBridge

open Matrix
open Qatlib
open scoped BigOperators Classical ComplexOrder ENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

noncomputable def jointFiniteBitCharge {S O X : Type} [Fintype S] [Fintype X] {D E : ℕ}
    (P : JointProgram S O X D E) : ℕ :=
  maxCharge P

def zeroPriceBranch {S O X : Type} [Fintype X] {D E : ℕ}
    (P : JointProgram S O X D E) (s : S) : Prop :=
  P.cost s = 0

end Qatlib.Concepts.MixedInstrument.ClockBridge
