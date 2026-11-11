/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.PhaseEstimationExactSubgoalStat

/-!
# Exact phase estimation on the Fourier grid

This module proves `PhaseEstimationExactSubgoal` using exact phase readout for an eigenvalue on
a finite Fourier grid. The controlled-powers circuit followed by the inverse Fourier transform
returns the exact label while preserving the eigenvector, in the phase estimation setting of
[Kitaev1995].

## Main statements

* `phaseEstimationExactSubgoal`: the exact output state and probability-one label measurement.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

open Qatlib

/-- Proves exact phase estimation for a normalized eigenvector on a positive Fourier grid: the
label register equals `Ket j` and is measured as `j` with probability one; see [Kitaev1995]. -/
theorem phaseEstimationExactSubgoal : PhaseEstimationExactSubgoal :=
  fun M I _ _ U hM ψ hψn j hψ => Qatlib.Concepts.SpectralFilter.PhaseReadout.qpe_exact_readout hM hψn j hψ

end Qatlib.Concepts.HspRecovery.KitaevReadout
