/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorization
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.OrderedSearchSDP

/-!
# Laurent circle Gram characterization statement

The Lean proposition `LaurentCircleGramCharacterization` states the equivalence between circle
nonnegativity and a positive semidefinite Gram representation of a complex Laurent polynomial.
It packages coefficient matching, evaluation matching, and trace normalization for the
semidefinite approach to ordered search in [ChildsLandahlParrilo2007].

## Main statements

* `LaurentCircleGramCharacterization`: the Gram representation equivalence for every finite
  coefficient family.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped BigOperators Classical ComplexOrder

/-- The proposition that circle nonnegativity of every finite complex Laurent coefficient family
is equivalent to a positive semidefinite matrix representation. The representation preserves
every generalized trace coefficient, every Laurent evaluation, and the constant coefficient
as its trace. -/
def LaurentCircleGramCharacterization : Prop :=
  ∀ (n : ℕ) (a : Fin n → ℂ),
    complexLaurentNonnegative a ↔
      ∃ A : Matrix (Fin n) (Fin n) ℂ, A.PosSemidef ∧
        (∀ j : ℤ, genTrace A j = complexLaurentCoefficient a j) ∧
        (∀ z : ℂ, matrixLaurent A z = complexLaurentEval a z) ∧
        A.trace = complexLaurentCoefficient a 0

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
