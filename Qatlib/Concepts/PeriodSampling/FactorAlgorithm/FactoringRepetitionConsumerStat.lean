/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPrograms

/-!
# Repeated factoring attempt contract

Defines `FactoringRepetitionConsumer`, specifying the success probability of repeated attempts
for odd inputs with at least two distinct prime factors. It also requires soundness of every
individual factor output in the probability model associated with [Shor1997].

## Main statements

* `FactoringRepetitionConsumer`: Specifies amplified attempt success and output soundness.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib

/-- For the stated odd inputs, sampler capacity, and Fourier-modulus bound, requires repeated
success probability at least `1 - (1 - shorAttemptBound N k) ^ R` and soundness of all
individual attempt factors. -/
def FactoringRepetitionConsumer : Prop :=
  ∀ (N M k R : ℕ) [NeZero N] (hM : 0 < M)
    (hk : Fintype.card (ZMod N)ˣ ≤ 2 ^ k), 3 ≤ N → Odd N →
    2 ≤ N.primeFactors.card →
    2 * N ^ 2 < M →
    (attemptLaw N M k hM hk).probEvent (attemptRepSuccess N M k R)
      ≥ 1 - (1 - shorAttemptBound N k) ^ R ∧
    (∀ (a : (ZMod N)ˣ) (y z : Fin M) (d : ℕ),
        attemptFactor N M a (y, z) = some d → 1 < d ∧ d < N ∧ d ∣ N)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
