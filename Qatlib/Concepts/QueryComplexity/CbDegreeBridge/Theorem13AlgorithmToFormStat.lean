/-
Copyright (c) 2026 Quantum Atlas Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quantum Atlas Contributors
-/

module

public import Qatlib.Concepts.QueryComplexity.CbDegreeBridge.CbForms

@[expose] public section
open Qatlib.Concepts.QueryComplexity.CbDegreeBridge Qatlib.Foundations.PureStateMath Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Concepts.QueryComplexity.CbDegreeBridge

def Theorem1_3AlgorithmToForm : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℕ) (β : (Fin n → Bool) → ℝ),
    HasSignAlgorithm β t →
      ∃ S : RealTensor (Fin n ⊕ Fin n) (2 * t),
        IsSymmTensor S ∧ formCbNorm S ≤ 1 ∧
          ∀ x : Fin n → Bool, formBias S x = β x

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
