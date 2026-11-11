/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RiskEstimation.PopulationGap.ResidueFactoringPrograms

/-!
# Residue factoring attempt success contract

Defines `ResidueAttemptSuccess`, the lower bound on success for a residue-based attempt using a
sufficiently large Fourier modulus. The contract also requires sound factors from the classical
gcd branch and the unit-based order-recovery branch in the setting of [Shor1997].

## Main statements

* `ResidueAttemptSuccess`: Specifies one-attempt success and factor soundness for both branches.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist
open Qatlib.Concepts.RiskEstimation.PopulationGap
open Qatlib.Concepts.PeriodSampling.OrderRecovery
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib

/-- For the stated odd inputs with at least two distinct prime factors, requires residue-attempt
success probability at least `shorResidueAttemptBound N k` and sound factors from both the
classical residue and unit-attempt routines. -/
def ResidueAttemptSuccess : Prop :=
  ∀ (N M k : ℕ) [NeZero N] (hM : 0 < M) (hk : N ≤ 2 ^ k),
    3 ≤ N → Odd N → 2 ≤ N.primeFactors.card → 2 * N ^ 2 < M →
    (residueAttemptLaw N M k hM hk).probEvent (L := 1)
        (fun ω => residueAttemptSuccessEvent N M k (ω 0))
      ≥ shorResidueAttemptBound N k ∧
    (∀ (y : ZMod N) (d : ℕ),
        residueClassicalFactor N y = some d → 1 < d ∧ d < N ∧ d ∣ N) ∧
    (∀ (a : (ZMod N)ˣ) (y z : Fin M) (d : ℕ),
        attemptFactor N M a (y, z) = some d → 1 < d ∧ d < N ∧ d ∣ N)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
