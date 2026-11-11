/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Abelian stabilizer generation specification

This module specifies a finite-sampling guarantee for subgroup generation in the abelian
stabilizer setting of [Kitaev1995]. A distribution whose mass on every subset of a subgroup is
sufficiently close to the uniform mass must generate that subgroup with high probability from
`n+4` independent samples.

The proposition `AbelianStabilizerGenerationSubgoal` records the cardinality bound `|H| ≤ 2^n`,
discrepancy `1/(6*k*(n+4))`, and failure bound `1/3`.

## Main statements

* `AbelianStabilizerGenerationSubgoal`: the near-uniform sampling and generation guarantee.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

/-- For positive `n` and `k`, a finite distribution with subset discrepancy at most
`1/(6*k*(n+4))` from uniform on a subgroup of size at most `2^n` fails to generate that
subgroup in `n+4` independent samples with probability at most `1/3`. -/
def AbelianStabilizerGenerationSubgoal : Prop :=
  ∀ (n k : ℕ), 0 < n → 0 < k →
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G), Fintype.card ↥H ≤ 2 ^ n →
    ∀ μ : FinDist G,
      (∀ L : Finset ↥H,
          |(∑ g ∈ L, μ.prob (g : G)) - (L.card : ℝ) / (Fintype.card ↥H : ℝ)|
            ≤ 1 / ((6 : ℝ) * ↑k * ↑(n + 4))) →
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n + 4) μ
          (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G))
        ≤ 1 / 3

end Qatlib.Concepts.HspRecovery.AbelianSampling
