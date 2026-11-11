/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Specification of generation from nearly uniform samples

`AbelianStabilizerWideGenerationSubgoal` specifies generation of a subgroup of size at most `2 ^
n` from a distribution on the ambient finite abelian group. A uniform bound of `1 / (6 * (n +
4))` on all subgroup subset probability errors gives failure probability at most `1 / 3` after
`n + 4` independent samples. [Kitaev1995]

## Main statements

* `AbelianStabilizerWideGenerationSubgoal`: the proposition specifying the wider near uniform
  error tolerance.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

/-- The proposition that, for `n > 0`, a distribution within `1 / (6 * (n + 4))` of uniform on
every subset of a subgroup of size at most `2 ^ n` generates that subgroup from `n + 4`
independent samples with failure probability at most `1 / 3`. -/
def AbelianStabilizerWideGenerationSubgoal : Prop :=
  ∀ (n : ℕ), 0 < n →
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G), Fintype.card ↥H ≤ 2 ^ n →
    ∀ μ : FinDist G,
      (∀ L : Finset ↥H,
          |(∑ g ∈ L, μ.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)|
            ≤ 1 / ((6 : ℝ) * ↑(n + 4))) →
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n + 4) μ
          (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G))
        ≤ 1 / 3

end Qatlib.Concepts.HspRecovery.AbelianSampling
