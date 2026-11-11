/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.GammaDuality.FilteredGamma2Optimization

/-!
# General adversary value identification specification

`GeneralAdversaryValueIdentification` packages an equality between the general adversary value
and the evaluation-masked filtered γ₂ value. It includes the comparison with the unmasked query
filters and the explicit factor depending on the output alphabet size.

The mathematical context is discussed in [LeeEtAl2011].

## Main statements

* `GeneralAdversaryValueIdentification`: The identification and comparison proposition for
  finite input and output types.

## References

* [Lee et al., 2011][LeeEtAl2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
open Qatlib.Concepts.GramQueryCore.FilteredCert
open Qatlib.Concepts.GramQueryCore.GammaDuality

namespace Qatlib.Concepts.ConversionCore.AdversaryValue
open Qatlib
open scoped ENNReal

/-- The statement identifying the general adversary value with the evaluation-masked filtered γ₂
value and bounding the unmasked value between it and `2 * (1 - 1 / Fintype.card E)` times
it. -/
def GeneralAdversaryValueIdentification : Prop :=
  ∀ (X E : Type) [Fintype X] [DecidableEq X] [Fintype E] [DecidableEq E]
    (n : ℕ) (input : X → Fin n → Bool) (f : X → E),
    generalAdversaryValue input f = filteredGamma2 (gramFunctionEvaluationMatrix f)
      (fun j x y => gramFilterDelta input j x y * gramFunctionEvaluationMatrix f x y) ∧
    generalAdversaryValue input f ≤
      filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) ∧
    filteredGamma2 (gramFunctionEvaluationMatrix f) (gramFilterDelta input) ≤
      ENNReal.ofReal (2 * (1 - 1 / (Fintype.card E : ℝ))) * generalAdversaryValue input f

end Qatlib.Concepts.ConversionCore.AdversaryValue
