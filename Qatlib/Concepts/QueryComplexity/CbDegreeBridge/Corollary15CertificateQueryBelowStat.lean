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

def Corollary1_5CertificateQueryBelow : Prop :=
  ∀ (n : ℕ) (D : Finset (Fin n → Bool)) (f : (Fin n → Bool) → ℝ) (ε : ℝ) (t : ℕ),
    0 ≤ ε → 1 ≤ t →
    (∃ S : RealTensor (Fin n ⊕ Fin n) (2 * t),
      HasCbFormCertificate S ∧ ∀ x ∈ D, |formBias S x - f x| ≤ 2 * ε) →
    ComputesBiasOn D f ε t

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
