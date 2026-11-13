/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPrograms

/-!
# Sampled factoring attempt success contract

Defines `SampledAttemptSuccess`, the one-attempt probability and soundness specification for
unit-based factoring. It assumes an odd input with at least two distinct prime factors and a
sufficiently large Fourier modulus, as used in the model associated with [Shor1997].

## Main statements

* `SampledAttemptSuccess`: Specifies the unit-based attempt success bound and factor soundness.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.PeriodSampling.OrderRecovery
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib

/-- For the stated odd inputs, sampler capacity, and Fourier-modulus bound, requires
single-attempt success probability at least `shorAttemptBound N k` and every returned factor
to be a proper nontrivial divisor of `N`. -/
def SampledAttemptSuccess : Prop :=
  ∀ (N M k : ℕ) [NeZero N] (hM : 0 < M)
    (hk : Fintype.card (ZMod N)ˣ ≤ 2 ^ k), 3 ≤ N → Odd N →
    2 ≤ N.primeFactors.card →
    2 * N ^ 2 < M →
    (attemptLaw N M k hM hk).probEvent (L := 1)
        (fun ω => attemptSuccess N M k (ω 0))
      ≥ shorAttemptBound N k ∧
    (∀ (a : (ZMod N)ˣ) (y z : Fin M) (d : ℕ),
        attemptFactor N M a (y, z) = some d → 1 < d ∧ d < N ∧ d ∣ N)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
