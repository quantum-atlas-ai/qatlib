/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.MultiControl.BarencoSharpDefs
import Mathlib.Topology.MetricSpace.HausdorffDimension
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.MultiKnownQubitControl
import Qatlib.Concepts.CircuitImpl.MultiControl.NoWorkTwoLevelSynthesis
import Qatlib.Concepts.GateTables.GrayUniversal.GrayCodeSynthesis
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Matrix
open scoped Classical BigOperators
open Qatlib
open Qatlib.Concepts.CircuitImpl.MultiControl.CountPackedCommutator
open Qatlib.Concepts.GateTables.GrayUniversal

namespace Qatlib.Concepts.CircuitImpl.MultiControl
noncomputable section

theorem barenco_dimension_threshold (n r : ℕ) (hn : 2 ≤ n) :
    9*r + 3*n + 1 < 4^n ↔ r < (4^n - 3*n - 1 + 8) / 9 := by
  have h4 : 16 ≤ 4^n := by
    calc 16 = 4^2 := by norm_num
      _ ≤ 4^n := Nat.pow_le_pow_right (by norm_num) hn
  omega
end
end Qatlib.Concepts.CircuitImpl.MultiControl
