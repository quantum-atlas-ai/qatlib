/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.AbelianSampling.OrbitFourierBasis

/-!
# Specification of ideal Fourier sample generation

`OrbitFourierIdealGenerationSubgoal` states uniformity and generation guarantees for the
character distribution `fourierBornDist`. A finite abelian group of size at most `2 ^ n`, with
`n > 0`, requires `n + 4` independent samples for the specified failure bound of `1 / 3`.
[Kitaev1995]

## Main statements

* `OrbitFourierIdealGenerationSubgoal`: the proposition specifying uniformity and generation of
  the full character group.

## References

* [Kitaev, 1995][Kitaev1995]
-/

set_option warningAsError false

open scoped Classical

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

/-- The proposition that `fourierBornDist` is uniform on characters and that `n + 4` independent
samples fail to generate the full character group with probability at most `1 / 3` when the
original group has size at most `2 ^ n` and `n > 0`. -/
def OrbitFourierIdealGenerationSubgoal : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (E : Type) [AddCommGroup E] [Fintype E] [DecidableEq E],
      Fintype.card E ≤ 2 ^ n →
      (∀ χ : AddChar E ℂ, (fourierBornDist E).prob χ = (Fintype.card E : ℝ)⁻¹)
      ∧ Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n + 4) (fourierBornDist E)
          (fun hs => Subgroup.closure (Set.range hs) ≠ ⊤) ≤ 1 / 3

end Qatlib.Concepts.HspRecovery.AbelianSampling
