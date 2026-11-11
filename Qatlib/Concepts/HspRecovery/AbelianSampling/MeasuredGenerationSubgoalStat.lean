/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator

/-!
# Specification of measured stabilizer generation

`AbelianStabilizerMeasuredGenerationSubgoal` states a generation guarantee for a finite abelian
subgroup from a uniform mixture of conditional measurement distributions. With subgroup size at
most `2 ^ n` and the prescribed conditional accuracy, `n + 4` independent samples fail to
generate the subgroup with probability at most `1 / 3`. [Kitaev1995]

## Main statements

* `AbelianStabilizerMeasuredGenerationSubgoal`: the proposition specifying the measured sample
  generation bound.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open scoped Classical

namespace Qatlib.Concepts.HspRecovery.AbelianSampling

/-- The proposition that `n + 4` independent samples from a uniform mixture of conditional
measurements generate a subgroup of size at most `2 ^ n` with failure probability at most `1
/ 3`, provided `n > 0` and each conditional label has probability at least `1 - 1 / (6 * (n
+ 4))`. -/
def AbelianStabilizerMeasuredGenerationSubgoal : Prop :=
  ∀ (n : ℕ), 0 < n →
  ∀ (G : Type) [AddCommGroup G] [Fintype G] [DecidableEq G]
    (H : AddSubgroup G), Fintype.card ↥H ≤ 2 ^ n →
    ∀ (μ : FinDist G) (cond : ↥H → FinDist G),
      (∀ g : G, μ.prob g =
        (Fintype.card ↥H : ℝ)⁻¹ * ∑ h' : ↥H, (cond h').prob g) →
      (∀ h' : ↥H,
          1 - 1 / ((6 : ℝ) * ↑(n + 4)) ≤ (cond h').prob (h' : G)) →
      Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.probEvent (L := n + 4) μ
          (fun hs => AddSubgroup.closure (Set.range hs) ≠ (H : AddSubgroup G))
        ≤ 1 / 3

end Qatlib.Concepts.HspRecovery.AbelianSampling
