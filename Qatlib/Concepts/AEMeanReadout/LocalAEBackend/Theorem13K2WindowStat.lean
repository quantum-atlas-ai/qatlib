/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers

/-!
# Specification of quantum counting windows

This module defines the counting-window proposition `expected` for a marked subset of `Fin N`.
The estimate is `N * aeEstimate M z` under uniform preparation by `QFTMatrix N`, with the error
radius and larger-parameter success bound of [BrassardEtAl2002].

## Main definitions

* `expected`: the counting error guarantee for positive `N`, `M ≥ 2`, and `k ≥ 2`.

## References

* [Brassard et al., Theorem 13][BrassardEtAl2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem13K2WindowSpec

/-- The proposition that uniform-preparation counting with positive `N`, `M ≥ 2`, and `k ≥ 2`
assigns mass at least `1 - 1 / (2 * (k - 1))` to the error window of radius `2πk√(t(N -
t))/M + π²k²N/M²`, where `t = S.card` [BrassardEtAl2002]. -/
def expected : Prop :=
  ∀ (N M : ℕ) (S : Finset (Fin N)) (hN : 0 < N) (hM : 2 ≤ M) (k : ℕ), 2 ≤ k →
    ∑ z ∈ Finset.univ.filter (fun z : Fin M =>
        |(N : ℝ)*Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeEstimate M z-(S.card : ℝ)| ≤
          2*Real.pi*(k : ℝ)*Real.sqrt ((S.card : ℝ)*((N : ℝ)-S.card))/(M : ℝ)
            +Real.pi^2*(k : ℝ)^2*(N : ℝ)/(M : ℝ)^2),
      (Qatlib.Concepts.AmplitudeCore.PreparedReadout.aeLaw M (Qatlib.Concepts.SpectralFilter.PhaseReadout.QFTMatrix N) (⟨0,hN⟩ : Fin N) S
        (Qatlib.Concepts.SpectralFilter.PhaseReadout.qftMatrix_unitary hN) hM).prob z ≥ 1-1/(2*((k : ℝ)-1))

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem13K2WindowSpec
