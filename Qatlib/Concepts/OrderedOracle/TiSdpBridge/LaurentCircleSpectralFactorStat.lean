/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorization
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP

/-!
# Laurent circle spectral factor statement

The Lean proposition `LaurentCircleSpectralFactor` packages a polynomial factor for a
nonnegative complex Laurent polynomial on the unit circle. Its degree, Gram coefficients,
coefficient norm sum, and root location requirements refine the spectral factorization used in
[ChildsLandahlParrilo2007].

## Main statements

* `LaurentCircleSpectralFactor`: existence of a factor of degree at most `n - 1`, with squared
  modulus equal to the Laurent evaluation and roots in the closed unit disk when nonzero.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped BigOperators Classical ComplexOrder

/-- The proposition that every finite complex Laurent polynomial that is nonnegative on the unit
circle has a polynomial factor of degree at most `n - 1` whose squared modulus agrees there.
It also requires matching outer Gram coefficients, positive semidefiniteness, the
coefficient norm sum identity, and closed unit disk roots for a nonzero factor. -/
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
