/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalance
import Qatlib.Concepts.QuantumGibbs.DetailedBalance.QuantumDetailedBalanceCriterionDefs

/-!
# The basis criterion for quantum detailed balance

This module states the weighted matrix-element criterion for detailed balance in a complete
orthonormal basis. The contract combines quantum detailed balance with stationarity for a
quantum channel and normalized nonnegative weights, following the criterion in [TemmeEtAl2011].

## Main statements

* `QuantumDetailedBalanceCriterion`: The basis-entry hypothesis implies detailed balance and a
  fixed point.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QuantumGibbs.DetailedBalance

open Matrix

variable {D : ℕ}

/-- The proposition that the stated square-root-weighted matrix-element identities in a complete
orthonormal basis imply quantum detailed balance and stationarity of `gibbsBasis ψ p` for a
quantum channel. The weights are nonnegative and sum to one; compare [Temme et al., Equation
(72)][TemmeEtAl2011]. -/
def QuantumDetailedBalanceCriterion : Prop :=
  ∀ (D : ℕ) (T : QuantumChannel D D) (ψ : Fin D → QState (Fin D)) (p : Fin D → ℝ),
    (∀ i j : Fin D, Inner (ψ i) (ψ j) = if i = j then 1 else 0) →
    (∀ x : QState (Fin D), ∑ i, Inner (ψ i) x • ψ i = x) →
    (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
    (∀ i j n m : Fin D,
        Real.sqrt (p n * p m) * braKetElem (T.map (ketbra (ψ n) (ψ m))) (ψ i) (ψ j)
          = Real.sqrt (p i * p j) * braKetElem (T.map (ketbra (ψ j) (ψ i))) (ψ m) (ψ n)) →
    QuantumDetailedBalance T.map (gibbsBasis ψ p) ∧
      T.map (gibbsBasis ψ p) = gibbsBasis ψ p

end Qatlib.Concepts.QuantumGibbs.DetailedBalance
