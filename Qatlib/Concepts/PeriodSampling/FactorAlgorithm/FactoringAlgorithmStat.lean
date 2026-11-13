/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPrograms

/-!
# Factoring algorithm probability contract

Defines `FactoringAlgorithm`, the complete success and soundness statement for preprocessing
followed by repeated unit-based attempts. For composite inputs and a sufficiently large Fourier
modulus, it specifies the amplification bound used in the finite probability model associated
with [Shor1997].

## Main statements

* `FactoringAlgorithm`: Specifies preprocessing soundness, amplified success, and attempt
  soundness.

## References

* [Shor, 1997][Shor1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

open Qatlib

/-- For composite `N ≥ 3` and `M > 2 * N ^ 2`, requires sound preprocessing factors, program
success at least `1 - (1 - shorAttemptBound N k) ^ R`, and sound outputs from every
individual attempt. -/
def FactoringAlgorithm : Prop :=
  ∀ (N R k M : ℕ) [NeZero N] (hM : 0 < M)
    (hk : Fintype.card (ZMod N)ˣ ≤ 2 ^ k), 3 ≤ N → ¬Nat.Prime N →
    2 * N ^ 2 < M →
    (∀ d : ℕ, shorPreprocess N = ShorPreResult.factor d →
        1 < d ∧ d < N ∧ d ∣ N) ∧
    shorProgramSuccessProb N R k M hM hk
      ≥ 1 - (1 - shorAttemptBound N k) ^ R ∧
    (∀ (a : (ZMod N)ˣ) (y z : Fin M) (d : ℕ),
        attemptFactor N M a (y, z) = some d → 1 < d ∧ d < N ∧ d ∣ N)

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
