/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.EffCosts.EffectiveDysonDefinitions

/-!
# Statement of the reverse-product perturbation bound

`EffectiveProductPerturbation` expresses a weighted bound for the difference between two
reverse-ordered finite products. It is formulated for an arbitrary normed ring with identity
norm at most one. These estimates support the interaction-picture simulation analysis of
[LowWiebe2018].

## Main statements

* `EffectiveProductPerturbation`: the local-error sum with surrounding norm products.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018
set_option autoImplicit false
namespace Qatlib.Concepts.InteractionEvo.SegmentProduct
open Qatlib.Concepts.InteractionEvo.ComputedGrid Qatlib.Concepts.InteractionEvo.EffCosts
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid
open Qatlib.Concepts.InteractionEvo.MeanDerivGrid.InteractionPicture2018 Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder
/-- The proposition bounding the difference of two reverse-ordered products by a sum of local
differences multiplied by the corresponding later `u` and earlier `v` factor norms. -/
noncomputable def EffectiveProductPerturbation : Prop :=
  ∀ (A : Type) [NormedRing A] (u v : ℕ → A) (L : ℕ),
    ‖(1 : A)‖ ≤ 1 →
    ‖((List.range L).map u).reverse.prod - ((List.range L).map v).reverse.prod‖ ≤
      ∑ j ∈ Finset.range L,
        (((List.range' (j+1) (L-(j+1))).map (fun i => ‖u i‖)).prod) *
          ‖u j-v j‖ * (((List.range j).map (fun i => ‖v i‖)).prod)
end Qatlib.Concepts.InteractionEvo.SegmentProduct
