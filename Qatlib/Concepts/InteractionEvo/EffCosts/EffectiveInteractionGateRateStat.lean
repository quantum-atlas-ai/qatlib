/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018
set_option autoImplicit false
namespace Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.ComputedGrid Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018 Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable def EffectiveInteractionGateRate : Prop :=
  ∀ (gamma : ℝ), 0 < gamma → ∀ (tau delta : ℚ) (nd : ℕ)
      (CA : ℝ) (cost : ℕ → ℕ),
    0 ≤ tau → 0 < delta → 0 ≤ CA →
    (∀ j ≤ nd, (cost j : ℝ) ≤
      CA*abs (effectiveIPDyadicTime tau nd j)*
        (1+Real.log (1+abs (effectiveIPDyadicTime tau nd j)/(delta : ℝ)))^gamma+1) →
    ((∑ j ∈ Finset.range (nd+1), cost j) : ℝ) ≤
      2*CA*(tau : ℝ)*(1+Real.log (1+(tau : ℝ)/(delta : ℝ)))^gamma+(nd+1)
end Qatlib.Concepts.InteractionEvo.EffCosts
