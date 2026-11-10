/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.CopyEvolution
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.WalkFind.SearchAlgorithm

namespace Qatlib.Concepts.RandCompile.ChannelBudget

open Matrix
open Qatlib
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

def qpePeakSpace (D M : ℕ) : ℕ := M * 2 * D

noncomputable def sourceBitTime (cs : List SourceCode) : ℕ :=
  (cs.map (fun g => (sourceDescription g).length)).sum

end Qatlib.Concepts.RandCompile.ChannelBudget
