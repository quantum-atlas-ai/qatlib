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

def Theorem1_3CertificateFormToAlgorithm : Prop :=
  ∀ (n : ℕ) (t : ℕ) (S : RealTensor (Fin n ⊕ Fin n) (2 * t)),
    HasCbFormCertificate S → HasSignAlgorithm (formBias S) t

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
