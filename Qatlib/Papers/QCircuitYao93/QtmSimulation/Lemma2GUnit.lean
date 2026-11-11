/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.StandardModel.WindowSim.GUnitExistenceQuan

/-!
# Existence of the local simulation unitary

`lemma2_g_unit_existence` exposes the local unitary existence property `GUnitExistence`. This
supplies the unitary construction used by the finite-window circuit simulation. See [Yao1993].

## Main statements

* `lemma2_g_unit_existence`: establishes the local unitary existence contract.

## References

* [Yao, 1993][Yao1993]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QCircuitYao93.QtmSimulation.Lemma2GUnit

open Qatlib.Foundations.StandardDefs.WindowSim

/-- The local unitary existence property `GUnitExistence` holds. This is the formal endpoint
associated with Lemma 2 of [Yao1993]. -/
theorem lemma2_g_unit_existence : GUnitExistence :=
  gUnitExistence

end Qatlib.Papers.QCircuitYao93.QtmSimulation.Lemma2GUnit
