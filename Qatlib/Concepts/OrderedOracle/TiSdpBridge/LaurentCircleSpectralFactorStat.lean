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

def LaurentCircleSpectralFactor : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℂ), complexLaurentNonnegative a →
    ∃ p : Fin n → ℂ,
      (laurentCoefficientPolynomial p).natDegree ≤ n-1 ∧
      (∀ z : ℂ, ‖z‖=1 → complexLaurentEval a z =
        ((‖(laurentCoefficientPolynomial p).eval z‖^2 : ℝ) : ℂ)) ∧
      (∀ j : ℤ, genTrace (gramOuter p) j = complexLaurentCoefficient a j) ∧
      (gramOuter p).PosSemidef ∧
      (∑ i : Fin n, Complex.normSq (p i)) = (complexLaurentCoefficient a 0).re ∧
      (laurentCoefficientPolynomial p ≠ 0 →
        ∀ z : ℂ, (laurentCoefficientPolynomial p).eval z = 0 → ‖z‖ ≤ 1)

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
