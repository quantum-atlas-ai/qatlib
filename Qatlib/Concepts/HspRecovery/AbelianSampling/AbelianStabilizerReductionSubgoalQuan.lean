/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.AbelianStabilizerReductionSubgoalStat
set_option warningAsError false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

open Qatlib

theorem abelianStabilizerReductionSubgoal : AbelianStabilizerReductionSubgoal :=
  fun M hM Idx I _ _ _ _ U c ψ k heig =>
    Qatlib.Concepts.SpectralFilter.PhaseReadout.qpe_exact_readout_linear M hM U c ψ k heig

end Qatlib.Concepts.HspRecovery.AbelianSampling
