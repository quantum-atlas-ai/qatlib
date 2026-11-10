/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib

def Corollary2FixedBudget : Prop :=
  ∀ (N P : ℕ) (S : Finset (Fin N)) (c : ℝ),
    (hN : 0 < N) → (hS : S.card ≤ N / 2) → (hc : 0 < c) →
    (hPc : (P : ℝ) = c * Real.sqrt (N : ℝ)) → (hP : 4 ≤ P) →
    QueryCount (countedAECircuit P (QFTMatrix N) ⟨0, hN⟩) = P - 1 ∧
      8 / Real.pi ^ 2 ≤
        ∑ z ∈ Finset.univ.filter (fun z : Fin P =>
            |(N : ℝ) * aeEstimate P z - (S.card : ℝ)| <
              2 * Real.pi / c * Real.sqrt (S.card : ℝ) + Real.pi ^ 2 / c ^ 2),
          (aeLaw P (QFTMatrix N) ⟨0, hN⟩ S (qftMatrix_unitary hN)
            (by omega : 2 ≤ P)).prob z

end Qatlib.Concepts.AEMeanReadout.RankOneSubspace
