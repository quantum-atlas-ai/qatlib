/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.FilteredNorm.AdaptiveModels
import Qatlib.Concepts.BitWordCompiler.WordComposition.FiniteModels
import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

/-!
# Boolean value compatibility specification

Defines `BooleanValueCompatibility`, expressing agreement between the source alphabet model and
the Boolean filtered Gram model. It compares rectangular values, the coherent state conversion
optimization at nonnegative tolerance, and real Hermitian adversary values.

These equalities connect the reusable source model to the Boolean formulations of [LeeEtAl2011].

## Main statements

* `BooleanValueCompatibility`: specifies the three value identities under Boolean symbol
  encoding.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
noncomputable section
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.FilteredNorm
open Qatlib.Concepts.GramQueryCore.GammaDuality
open Qatlib.Concepts.GramQueryCore.LowerBoundTools

namespace Qatlib.Concepts.GramQueryCore.ModelSemantics
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ENNReal ComplexOrder

/-- The proposition that Boolean alphabet encoding identifies the rectangular filtered value
with `filteredGamma2`, the nonnegative-tolerance coherent approximation with
`stateConversionSDP`, and the adversary value with `generalAdversaryValue`. -/
def BooleanValueCompatibility : Prop :=
  ∀ (X : Type) [Fintype X] [DecidableEq X] (n : ℕ) (input : X → Fin n → Bool)
    (R S : Matrix X X ℂ) (δ : ℝ),
    sourceRectValue R (sourceAlphabetDelta (fun x j => sourceBooleanSymbol (input x j)))=
      filteredGamma2 R (gramFilterDelta input) ∧
    (0 ≤ δ → sourceQDelta (fun x j => sourceBooleanSymbol (input x j)) δ R S=
      stateConversionSDP input δ R S) ∧
    (∀ (E : Type) [Fintype E] [DecidableEq E] (f : X → E),
      sourceAdversary (sourceAlphabetDelta (fun x j => sourceBooleanSymbol (input x j))) f=
        generalAdversaryValue input f)
end Qatlib.Concepts.GramQueryCore.ModelSemantics
