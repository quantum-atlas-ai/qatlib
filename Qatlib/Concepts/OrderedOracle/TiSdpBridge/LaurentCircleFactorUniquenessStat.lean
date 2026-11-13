/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorization
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP

/-!
# Laurent circle factor uniqueness statement

`LaurentCircleFactorUniqueness` specifies uniqueness up to a unit complex scalar for two circle
square-norm factors whose roots lie in the closed unit disk. The proposition assumes a nonzero
highest Laurent coefficient and records exact factor degrees, refining the factorization
vocabulary used for ordered-search semidefinite programs [ChildsLandahlParrilo2007].

## Main statements

* `LaurentCircleFactorUniqueness`: two closed-disk factors have degree `n - 1` and coefficient
  vectors related by a scalar of norm one.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped BigOperators Classical ComplexOrder

/-- The proposition that two closed-disk polynomial square-norm factors of a nonnegative Laurent
family with nonzero highest coefficient both have degree `n - 1`. It further requires their
coefficient vectors to differ by multiplication by a complex scalar of norm one. -/
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
