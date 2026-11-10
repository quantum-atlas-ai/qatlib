/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LchsSimulation.InteractHybrid.InteractionPictureLchsReprStat
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.LchsSimulation.TimeOrdered

namespace Qatlib.Concepts.LchsSimulation.InteractHybrid

open Matrix
open scoped Matrix.Norms.L2Operator
set_option warningAsError false

theorem interactionPictureLchsRepresentation : InteractionPictureLchsRepresentation := by
  intro I _ _ L H k t hL hH hHerm
  have h := ordered_interaction_picture_identity I (k • L) H
    (hL.smul (R := ℝ) (IsSelfAdjoint.all k)) hH hHerm t
  simpa only [add_comm] using! h

end Qatlib.Concepts.LchsSimulation.InteractHybrid
