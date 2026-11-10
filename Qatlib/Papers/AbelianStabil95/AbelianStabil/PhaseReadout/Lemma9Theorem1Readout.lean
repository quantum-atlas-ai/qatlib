/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseEstimateSubgoalQuan
import Qatlib.Concepts.HspRecovery.KitaevReadout.PhaseEstimationExactSubgoalQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

open Qatlib.Concepts.HspRecovery.KitaevReadout

theorem lemma9_eigenphase_estimation : EigenphaseEstimateSubgoal :=
  eigenphaseEstimateSubgoal

theorem on_grid_exact_phase_readout : PhaseEstimationExactSubgoal :=
  phaseEstimationExactSubgoal

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
