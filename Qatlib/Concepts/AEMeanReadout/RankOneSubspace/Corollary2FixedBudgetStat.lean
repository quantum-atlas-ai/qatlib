/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AmplitudeCountingConsumers

/-!
# Fixed-budget counting specification

`Corollary2FixedBudget` states the counting guarantee when the estimation grid is a positive
constant times `sqrt N`, as in [BrassardHoyerTapp1998Counting]. It records `P - 1` queries and
the corresponding strict count-error window of mass at least `8 / π^2`.

## Main statements

* `Corollary2FixedBudget`: the square-root-budget query and count-error specification.

## References

* [Brassard et al., 1998][BrassardHoyerTapp1998Counting]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.SpectralFilter.PhaseReadout

open Qatlib.Concepts.AmplitudeCore.PreparedReadout

namespace Qatlib.Concepts.AEMeanReadout.RankOneSubspace

open Qatlib

/-- Specifies the `P - 1` query count and probability at least `8 / π^2` for count error
strictly below `2 * π * sqrt S.card / c + π^2 / c^2`, assuming `P = c * sqrt N`, `P ≥ 4`, `c
> 0`, and `S.card ≤ N / 2`. -/
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
