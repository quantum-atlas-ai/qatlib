/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Sqrt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ApproxCountStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostDefs

/-!
# Expected cost specification for approximate counting

`Theorem15ExpectedCostSpec.expected` states explicit bounds for the expected total cost of the
adaptive approximate counter in [BrassardEtAl2002]. It separates the empty-set scale `sqrt N /
ε` from the nonempty-set scale `sqrt (N / t) / ε`, where `t` is the marked cardinality.

## Main statements

* `Theorem15ExpectedCostSpec.expected`: the empty and nonempty expected-cost bounds.

## References

* [Brassard et al., 2002][BrassardEtAl2002]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open scoped Classical

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostSpec

/-- Specifies explicit lower and upper expected-cost bounds for relative error in `(0, 1]`, with
scales `sqrt N / ε` for an empty marked set and `sqrt (N / S.card) / ε` otherwise. -/
def expected : Prop :=
  ∀ (N : ℕ) (S : Finset (Fin N)) (hN : 0 < N) (ε : ℝ), 0 < ε → ε ≤ 1 →
    (S.card = 0 →
      (40*Real.pi^2/ε*Real.sqrt (N : ℝ) ≤
        ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((basicApproxCountTotalCost N ε ω : ℕ) : ℝ)) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((basicApproxCountTotalCost N ε ω : ℕ) : ℝ) ≤
        (9+80*Real.pi^2/ε)*Real.sqrt (N : ℝ))) ∧
    (0 < S.card →
      (7*Real.pi/2*(1/ε)*Real.sqrt ((N : ℝ)/(S.card : ℝ)) ≤
        ∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((basicApproxCountTotalCost N ε ω : ℕ) : ℝ)) ∧
      (∑ ω : (l : Fin (basicApproxCountLoopCap N)) → Fin (2*2^l.val),
          basicApproxCountPrefixWeight hN S ω *
            ((basicApproxCountTotalCost N ε ω : ℕ) : ℝ) ≤
        2000*(1/ε)*Real.sqrt ((N : ℝ)/(S.card : ℝ))))

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem15ExpectedCostSpec
