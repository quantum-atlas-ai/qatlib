/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers

/-!
# Specification of approximate counting

`Theorem5ApproximateCounting` specifies the probability of a strict count-error bound under the
Fourier-prepared amplitude-estimation law. Its parameters require a positive search-space size,
marked size at most half that size, and precision at least four. For background, see
[BrassardHoyerTapp1998Counting].

## Main statements

* `Theorem5ApproximateCounting`: The proposition that the count estimate `N * aeEstimate P z`
  has error strictly below `2π * sqrt (|S| * N) / P + π² * N / P²` with mass at least `8 / π²`,
  under the stated size and precision hypotheses.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib

/-- The proposition that the count estimate `N * aeEstimate P z` has error strictly below `2π *
sqrt (|S| * N) / P + π² * N / P²` with mass at least `8 / π²`, under the stated size and
precision hypotheses. -/
def Theorem5ApproximateCounting : Prop :=
  ∀ (N P : ℕ) (S : Finset (Fin N)),
    (hN : 0 < N) → (hS : S.card ≤ N / 2) → (hP : 4 ≤ P) →
    8 / Real.pi ^ 2 ≤
      ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
          |(N : ℝ) * aeEstimate P z - (S.card : ℝ)| <
            2 * Real.pi / (P : ℝ) * Real.sqrt ((S.card : ℝ) * (N : ℝ)) +
              Real.pi ^ 2 / (P : ℝ) ^ 2 * (N : ℝ)),
        (aeLaw P (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN)
          (by omega)).prob z

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
