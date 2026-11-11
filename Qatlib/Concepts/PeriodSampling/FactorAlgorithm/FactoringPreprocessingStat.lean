/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.FactorAlgorithm.FactoringPrograms

/-!
# Factoring preprocessing contract

Defines `FactoringPreprocessing`, the specification for the deterministic preprocessing stage.
It separates sound factor outputs from the structural properties of inputs passed to the
residue-based stage of the factoring construction associated with [Shor1997].

## Main statements

* `FactoringPreprocessing`: Specifies factor soundness and the residue-branch conditions.

## References

* [Shor, 1997][Shor1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

namespace Qatlib.Concepts.PeriodSampling.FactorAlgorithm

/-- Requires preprocessing factors to be proper nontrivial divisors for `N ≥ 3`, and requires
residue-branch inputs to be odd and either prime or possess at least two distinct prime
factors. -/
def FactoringPreprocessing : Prop :=
  (∀ (N d : ℕ), 3 ≤ N → shorPreprocess N = ShorPreResult.factor d →
      1 < d ∧ d < N ∧ d ∣ N) ∧
    (∀ (N : ℕ), 3 ≤ N → shorPreprocess N = ShorPreResult.residue →
      Odd N ∧ (Nat.Prime N ∨ 2 ≤ N.primeFactors.card))

end Qatlib.Concepts.PeriodSampling.FactorAlgorithm
