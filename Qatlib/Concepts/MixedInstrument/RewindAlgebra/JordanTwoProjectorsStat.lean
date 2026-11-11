/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.MixedState

/-!
# Two projector decomposition specification

`JordanTwoProjectors` specifies an orthogonal decomposition for a pair of Hermitian idempotents.
It records the action of both projectors, the coupling coefficients `sqrt (d * (1 - d))`, and a
residual projector commuting with the second projector. Companion vectors vanish at endpoint
eigenvalues, as appropriate for the one dimensional blocks in the Jordan framework
[NagajWocjanZhang2009].

## Main statements

* `JordanTwoProjectors`: The proposition specifying a two projector decomposition with
  orthonormal range vectors, companion vectors normalized for `0 < d < 1` and zero otherwise,
  and a commuting residual projector.

## References

* [Nagaj, Wocjan, and Zhang, 2009][NagajWocjanZhang2009]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra

open Matrix

/-- The proposition specifying a two projector decomposition with orthonormal range vectors,
companion vectors normalized for `0 < d < 1` and zero otherwise, and a commuting residual
projector. -/
def JordanTwoProjectors : Prop :=
  ∀ (D : ℕ) (P Q : Operator D), P.IsHermitian → P * P = P → Q.IsHermitian → Q * Q = Q →
    ∃ (k : ℕ) (u v : Fin k → QState (Fin D)) (d : Fin k → ℝ) (W : Operator D),
      (∀ i, 0 ≤ d i ∧ d i ≤ 1) ∧
      (∀ i j, Inner (u i) (u j) = if i = j then 1 else 0) ∧
      (∀ i j, Inner (v i) (v j) = if i = j then
        (if 0 < d i ∧ d i < 1 then 1 else 0) else 0) ∧
      (∀ i j, Inner (u i) (v j) = 0) ∧
      W.IsHermitian ∧ W * W = W ∧ W * Q = Q * W ∧
      (∀ x : QState (Fin D),
          (∑ i, Inner (u i) x • u i + ∑ i, Inner (v i) x • v i) + W *ᵥ x = x) ∧
      (∀ x : QState (Fin D), P *ᵥ x = ∑ i, Inner (u i) x • u i) ∧
      (∀ i, Q *ᵥ (u i) = d i • u i + Real.sqrt (d i * (1 - d i)) • v i) ∧
      (∀ i, Q *ᵥ (v i) = Real.sqrt (d i * (1 - d i)) • u i + (1 - d i) • v i)

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
