/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.KitaevReadout.EigenphaseHadamardTest

/-!
# Specification of phase estimation accuracy

`EigenphaseEstimateSubgoal` specifies an accuracy guarantee for `eigenphaseDecode` under
`eigenphaseSampleLaw`, following the constant-precision phase estimation setting of
[Kitaev1995]. For `0 < δ ≤ 1/2` and `0 < ε < 1`, the specified sample size bounds the
probability of phase error greater than `δ` modulo integers by `ε`.

## Main statements

* `EigenphaseEstimateSubgoal`: the sample-size condition and estimator failure bound.

## References

* [Kitaev, 1995][Kitaev1995]
-/

open Matrix
open scoped Classical

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.HspRecovery.KitaevReadout

/-- Specifies that, for `0 < δ ≤ 1/2` and `0 < ε < 1`, at least `36 * log (4 / ε) / sin (π *
δ)^2` samples per block bound the probability of decoder error greater than `δ` modulo
integers by `ε`. -/
def EigenphaseEstimateSubgoal : Prop :=
  ∀ (δ ε : ℝ), 0 < δ → δ ≤ 1 / 2 → 0 < ε → ε < 1 →
    ∀ (I : Type) [Fintype I] [DecidableEq I] (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ),
      (U *ᵥ ψ = eigenPhase φ • ψ) →
      ∀ s : ℕ,
        36 * Real.log (4 / ε) / (Real.sin (Real.pi * δ)) ^ 2 ≤ s →
        (eigenphaseSampleLaw φ s).probEvent (L := 1)
            (fun ω => ¬ ∃ m : ℤ, |eigenphaseDecode s (ω 0) - φ + m| ≤ δ)
          ≤ ε

end Qatlib.Concepts.HspRecovery.KitaevReadout
