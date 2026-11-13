/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterOrderedCommutatorContracts

/-!
# Corrected ordered-commutator statement

This module defines `TrotterOrderedCommutator`, combining the ordered conjugation coefficient
expansion with bounds using `pfCommAlphaOrderedV2`. The remainder budget is divided by `p!`, and
the general-matrix case includes exponential norm inflation, in the setting of Theorem 10 of
[ChildsEtAl2021Trotter].

## Main statements

* `TrotterOrderedCommutator`: specifies the corrected coefficient and remainder contract.

## References

* [Childs et al., 2021][ChildsEtAl2021Trotter]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.TrotterFormula.GeneralOrder.ConjugationWordRemainders
open Qatlib.Concepts.TrotterFormula.SuzukiFourth

namespace Qatlib.Concepts.TrotterFormula.GeneralOrder

open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The corrected proposition combining the ordered coefficient expansion with remainder bounds
based on `pfCommAlphaOrderedV2`. -/
def TrotterOrderedCommutator : Prop :=
  ∀ (I : Type) [Fintype I] [DecidableEq I] (xs : List (Matrix I I ℂ))
    (B : Matrix I I ℂ) (p : ℕ),

    (∀ n : ℕ,
      pfConjCoeff xs B n =
        ∑ q ∈ pfCompositions xs.length n,
          (∏ i, ((q i).factorial : ℝ))⁻¹ •
            pfNestedCommList (B :: pfOrderedCompositionWord xs q)) ∧

    (∀ t : ℝ, (∀ X ∈ xs, Xᴴ = -X) →
      ‖pfConjWord xs B t - pfConjTrunc xs B p t‖ ≤
        pfCommAlphaOrderedV2 xs B p * |t| ^ p / (p.factorial : ℝ)) ∧

    (∀ t : ℝ,
      ‖pfConjWord xs B t - pfConjTrunc xs B p t‖ ≤
        pfCommAlphaOrderedV2 xs B p * |t| ^ p / (p.factorial : ℝ) *
          Real.exp (2 * |t| * suzukiMass xs))

end Qatlib.Concepts.TrotterFormula.GeneralOrder
