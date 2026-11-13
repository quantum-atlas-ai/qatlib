/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseEstimateSubgoalQuan
import Qatlib.Concepts.HspRecovery.KitaevReadout.PhaseEstimationExactSubgoalQuan

/-!
# Eigenphase estimation and exact grid readout

This module exposes the established eigenphase estimation and exact grid-readout propositions in
the paper namespace. `lemma9_eigenphase_estimation` supplies `EigenphaseEstimateSubgoal`, while
`on_grid_exact_phase_readout` supplies `PhaseEstimationExactSubgoal` for phases on the
estimation grid. The development follows [Kitaev1995].

## Main statements

* `lemma9_eigenphase_estimation`: establishes the eigenphase estimation proposition.
* `on_grid_exact_phase_readout`: establishes the exact grid-readout proposition.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout

open Qatlib.Concepts.HspRecovery.KitaevReadout

/-- Establishes `EigenphaseEstimateSubgoal`, the eigenphase estimation proposition used for
[Kitaev, 1995, Lemma 9][Kitaev1995]. -/
theorem lemma9_eigenphase_estimation : EigenphaseEstimateSubgoal :=
  eigenphaseEstimateSubgoal

/-- Establishes `PhaseEstimationExactSubgoal` for exact readout on the phase-estimation grid, a
component of the phase-readout development for [Kitaev, 1995, Theorem 1][Kitaev1995]. -/
theorem on_grid_exact_phase_readout : PhaseEstimationExactSubgoal :=
  phaseEstimationExactSubgoal

end Qatlib.Papers.AbelianStabil95.AbelianStabil.PhaseReadout
