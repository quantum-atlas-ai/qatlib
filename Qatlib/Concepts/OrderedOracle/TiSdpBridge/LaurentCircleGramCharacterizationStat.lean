/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorization
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped BigOperators Classical ComplexOrder

def LaurentCircleGramCharacterization : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℂ),
    complexLaurentNonnegative a ↔
      ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef ∧
        (∀ j : ℤ, genTrace A j = complexLaurentCoefficient a j) ∧
        (∀ z : ℂ, matrixLaurent A z = complexLaurentEval a z) ∧
        A.trace = complexLaurentCoefficient a 0

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
