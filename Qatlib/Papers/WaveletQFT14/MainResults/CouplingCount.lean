/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.WaveletQFT14.MainResults.CouplingSparsity.SourceCouplingSparsity
public import Qatlib.Papers.WaveletQFT14.MainResults.GateScaling.SourceGateScaling

@[expose] public section

/-!
# Wavelet coupling candidates in terms of the mode count

The geometric sparsity estimate gives a linear factor in the scale
count. Expressing that factor through the logarithm of the mode count
gives the one-dimensional bound associated with Eqs. (26) and (30).
-/

set_option autoImplicit false

open Qatlib.Papers.WaveletQFT14.MainResults

namespace Qatlib.Papers.WaveletQFT14.MainResults

/-- The set of geometric overlap candidates fits an explicit
mode-count times log-mode-count budget. -/
theorem coupling_candidates_le_modes_log (L lmax : ℕ) (hL : 1 ≤ L) :
    (CouplingSparsity.nonzeroCouplings L lmax).card ≤
      20 * GateScaling.modeCount L lmax * (GateScaling.modeCount L lmax).log2 :=
  GateScaling.hamiltonian_summands_le L lmax _ hL
    (CouplingSparsity.source_coupling_sparsity L lmax)

end Qatlib.Papers.WaveletQFT14.MainResults
