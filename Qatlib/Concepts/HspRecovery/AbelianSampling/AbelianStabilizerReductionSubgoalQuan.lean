/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.AbelianStabilizerReductionSubgoalStat

/-!
# Exact phase readout for stabilizer reduction

The theorem `abelianStabilizerReductionSubgoal` proves exact phase readout for finite
superpositions of eigenvectors with eigenvalues on an `M`th root of unity grid. Controlled
powers followed by an inverse Fourier transform replace the uniform control state by the
corresponding phase label in each summand. [Kitaev1995]

## Main statements

* `abelianStabilizerReductionSubgoal`: establishes the linear exact readout identity.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

open Qatlib.Concepts.SpectralFilter.PhaseReadout

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

open Qatlib

/-- Controlled powers followed by an inverse Fourier transform read out the exact phase label of
each term in a finite eigenvector superposition with eigenvalues on the `M`th root of unity
grid. This establishes `AbelianStabilizerReductionSubgoal` in the setting of [Kitaev1995]. -/
theorem abelianStabilizerReductionSubgoal : AbelianStabilizerReductionSubgoal :=
  fun M hM Idx I _ _ _ _ U c ψ k heig =>
    Qatlib.Concepts.SpectralFilter.PhaseReadout.qpe_exact_readout_linear M hM U c ψ k heig

end Qatlib.Concepts.HspRecovery.AbelianSampling
