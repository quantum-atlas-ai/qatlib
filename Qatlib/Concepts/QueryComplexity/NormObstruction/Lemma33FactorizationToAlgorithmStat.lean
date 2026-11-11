/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.CbForms

/-!
# Factorization-to-algorithm contract

Defines `Lemma3_3FactorizationToAlgorithm`, the assertion that a real tensor of order `2 * t`
possessing a completely bounded factorization has a `t`-query sign algorithm for `tensorBias T`.
The proposition isolates the construction interface from its implementation.

The operator-theoretic terminology follows the setting of completely bounded maps [Paulsen2002].

## Main statements

* `Lemma3_3FactorizationToAlgorithm`: the implication from tensor factorization to exact
  sign-bias realization.

## References

* [Paulsen, 2002][Paulsen2002]
-/

open Qatlib.Concepts.QueryComplexity.CbDegreeBridge

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.QueryComplexity.NormObstruction

/-- The assertion that every real tensor of order `2 * t` possessing a completely bounded
factorization has a `t`-query sign algorithm for its tensor bias. -/
def Lemma3_3FactorizationToAlgorithm : Prop :=
  ∀ (n : ℕ) (t : ℕ) (T : RealTensor (Fin n ⊕ Fin n) (2 * t)),
    HasCbFactorization T → HasSignAlgorithm (tensorBias T) t

end Qatlib.Concepts.QueryComplexity.NormObstruction
