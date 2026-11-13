/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma2FiberCorrectedStat
import Qatlib.Papers.HamLCUSim12.LCUDeferred.NearbyLCUCorrectedAlgebra

/-!
# Output fibers of the corrected two-unitary LCU circuit

This module proves `lemma2FiberCorrected`, identifying the two ancilla fibers of the corrected
circuit output. The false fiber is the weighted combination (κUa + Ub)/(κ + 1), while the true
fiber is the difference term √κ(Ub − Ua)/(κ + 1), both applied to the input state. See
[ChildsWiebe2012] for the multiproduct and linear-combination simulation framework.

## Main statements

* `lemma2FiberCorrected`: The corrected two-unitary LCU output has success fiber ((κUa + Ub)/(κ
  + 1))ψ and failure fiber (√κ/(κ + 1))(Ub − Ua)ψ under the hypotheses of
  `Lemma2FiberCorrected`.

## References

* [Childs and Wiebe, 2012][ChildsWiebe2012]
-/

open Qatlib.Papers.HamLCUSim12.LCUDeferred

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Qatlib.Papers.HamLCUSim12.Multiproduct
open Matrix
open scoped Classical Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The corrected two-unitary LCU output has success fiber ((κUa + Ub)/(κ + 1))ψ and failure
fiber (√κ/(κ + 1))(Ub − Ua)ψ under the hypotheses of `Lemma2FiberCorrected`. See
[ChildsWiebe2012]. -/
theorem lemma2FiberCorrected : Lemma2FiberCorrected := by
  intro I _ _ κ hκ Ua Ub _hUa _hUb ψ
  exact lemma2OutputCorrected_formula κ hκ Ua Ub ψ

end Qatlib.Papers.HamLCUSim12.Multiproduct
