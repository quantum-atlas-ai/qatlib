/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib

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
