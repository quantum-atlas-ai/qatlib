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

def FactorizationBoundsTensorCbNorm : Prop :=
  ∀ (κ : Type) [Fintype κ] (s : ℕ) (T : RealTensor κ s),
    HasCbFactorization T → tensorCbNorm T ≤ 1

end Qatlib.Concepts.QueryComplexity.CbDegreeBridge
