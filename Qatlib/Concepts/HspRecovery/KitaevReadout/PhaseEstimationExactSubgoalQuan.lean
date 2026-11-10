/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.PhaseEstimationExactSubgoalStat
set_option warningAsError false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

open Qatlib

theorem phaseEstimationExactSubgoal : PhaseEstimationExactSubgoal :=
  fun M I _ _ U hM ψ hψn j hψ => Qatlib.Concepts.SpectralFilter.PhaseReadout.qpe_exact_readout hM hψn j hψ

end Qatlib.Concepts.HspRecovery.KitaevReadout
