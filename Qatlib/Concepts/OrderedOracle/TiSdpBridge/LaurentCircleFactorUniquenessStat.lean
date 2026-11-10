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

def LaurentCircleFactorUniqueness : Prop :=
  ∀ (n : ℕ) [NeZero n] (a p q : Fin n → ℂ),
    complexLaurentNonnegative a →
    a ⟨n-1,by have := NeZero.pos n; omega⟩ ≠ 0 →
    (∀ z : ℂ, ‖z‖=1 → complexLaurentEval a z =
      ((‖(laurentCoefficientPolynomial p).eval z‖^2 : ℝ) : ℂ)) →
    (∀ z : ℂ, ‖z‖=1 → complexLaurentEval a z =
      ((‖(laurentCoefficientPolynomial q).eval z‖^2 : ℝ) : ℂ)) →
    (∀ z : ℂ, (laurentCoefficientPolynomial p).eval z = 0 → ‖z‖ ≤ 1) →
    (∀ z : ℂ, (laurentCoefficientPolynomial q).eval z = 0 → ‖z‖ ≤ 1) →
    (laurentCoefficientPolynomial p).natDegree = n-1 ∧
    (laurentCoefficientPolynomial q).natDegree = n-1 ∧
    ∃ u : ℂ, ‖u‖=1 ∧ ∀ i : Fin n, q i = u*p i

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
