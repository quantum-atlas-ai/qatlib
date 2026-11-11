/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleGramCharacterizationStat
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleSpectralFactorTran

/-!
# Laurent circle Gram characterization proof

The Lean theorem `laurentCircleGramCharacterization` proves the equivalence between circle
nonnegativity and a positive semidefinite Gram representation. Spectral factorization supplies
the forward direction, while positivity of a matrix quadratic form supplies the reverse
direction, in the Laurent polynomial framework of [ChildsLandahlParrilo2007].

## Main statements

* `laurentCircleGramCharacterization`: proves `LaurentCircleGramCharacterization`, including
  coefficient, evaluation, and trace identities.

## References

* [Childs, Landahl, and Parrilo, 2007][ChildsLandahlParrilo2007]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.OrderedOracle.TiSdpBridge
open Qatlib.Concepts.OrderedOracle.TiSdpBridge Polynomial Matrix
open scoped Classical BigOperators ComplexOrder

/-- Proves the equivalence between circle nonnegativity and a positive semidefinite Gram
representation, with matching coefficients, evaluations, and trace. -/
theorem laurentCircleGramCharacterization : LaurentCircleGramCharacterization := by
  intro n a
  constructor
  · intro ha
    obtain ⟨p,_,_,hcoeff,hps,_,_⟩ := laurentCircleSpectralFactor n a ha
    refine ⟨gramOuter p,hps,hcoeff,?_,?_⟩
    · intro z
      exact (complexLaurentEval_eq_matrixLaurent_of_genTrace a (gramOuter p) hcoeff z).symm
    · simpa only [genTrace_zero] using hcoeff 0
  · rintro ⟨A,hps,hcoeff,_,_⟩
    exact complexLaurentNonnegative_of_gram_posSemidef a A hps hcoeff

end Qatlib.Concepts.OrderedOracle.TiSdpBridge
