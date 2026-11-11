/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Legacy projector and rejection contracts

This module records the propositions `JordanTwoProjectorsLegacy` and `RejectionBudgetLegacy` for
comparison with later formulations. The first requires both families of Jordan vectors to be
normalized even at endpoint parameters; the second assumes a tail estimate only for positive
round counts while quantifying its conclusion over all round counts. Their setting is the two
projector rejection method in [TemmeEtAl2011].

## Main statements

* `JordanTwoProjectorsLegacy`: The legacy two projector decomposition proposition requiring both
  vector families to be orthonormal at every parameter value, together with a commuting residual
  projector and the specified projector actions.
* `RejectionBudgetLegacy`: The legacy budget proposition deriving `(1 - pfail n) ^ m ≥ c` for
  all natural `n` from a failure bound assumed only for `n ≥ 1` and the stated budget
  inequality.

## References

* [Temme et al., 2011][TemmeEtAl2011]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Matrix
open scoped Classical BigOperators

/-- The legacy two projector decomposition proposition requiring both vector families to be
orthonormal at every parameter value, together with a commuting residual projector and the
specified projector actions. -/
def JordanTwoProjectorsLegacy : Prop :=
  ∀ (D : ℕ) (P Q : Operator D), P.IsHermitian → P * P = P → Q.IsHermitian → Q * Q = Q →
    ∃ (k : ℕ) (u v : Fin k → QState (Fin D)) (d : Fin k → ℝ) (W : Operator D),
      (∀ i, 0 ≤ d i ∧ d i ≤ 1) ∧
      (∀ i j, Inner (u i) (u j) = if i = j then 1 else 0) ∧
      (∀ i j, Inner (v i) (v j) = if i = j then 1 else 0) ∧
      (∀ i j, Inner (u i) (v j) = 0) ∧
      W.IsHermitian ∧ W * W = W ∧ W * Q = Q * W ∧
      (∀ x : QState (Fin D),
          (∑ i, Inner (u i) x • u i + ∑ i, Inner (v i) x • v i) + W *ᵥ x = x) ∧
      (∀ x : QState (Fin D), P *ᵥ x = ∑ i, Inner (u i) x • u i) ∧
      (∀ i, Q *ᵥ (u i) = d i • u i + Real.sqrt (d i * (1 - d i)) • v i) ∧
      (∀ i, Q *ᵥ (v i) = Real.sqrt (d i * (1 - d i)) • u i + (1 - d i) • v i)

/-- The legacy budget proposition deriving `(1 - pfail n) ^ m ≥ c` for all natural `n` from a
failure bound assumed only for `n ≥ 1` and the stated budget inequality. -/
def RejectionBudgetLegacy : Prop :=
  ∀ pfail : ℕ → ℝ,
    (∀ n, 1 ≤ n → 0 ≤ pfail n ∧ pfail n ≤ 1 / (2 * (n + 1))) →
    ∀ (m n : ℕ) (c : ℝ), 0 ≤ c → c < 1 → 0 < m →
      (n + 1) * (2 * (1 - c)) ≥ m → (1 - pfail n) ^ m ≥ c

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
