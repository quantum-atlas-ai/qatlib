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

def Lemma3_3AlgorithmToTensor : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ (t : ℕ) (β : (Fin n → Bool) → ℝ),
    HasSignAlgorithm β t →
      ∃ T : RealTensor (Fin n ⊕ Fin n) (2 * t),
        HasCbFactorization T ∧
          ∀ x : Fin n → Bool, tensorEval T (fun _ => signVecC x) = (β x : ℂ)

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
