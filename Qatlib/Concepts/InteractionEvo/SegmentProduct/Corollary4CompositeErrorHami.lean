/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.SegmentProduct.Corollary4CompositeErrorStat
import Qatlib.Concepts.InteractionEvo.SegmentProduct.Lemma6SegmentCompositeHami
import Qatlib.Concepts.InteractionEvo.SegmentProduct.SegmentProductPerturbation

/-!
# Accumulated error for repeated simulation segments

`corollary4CompositeError` propagates a single-segment approximation error through repeated
multiplication. For Hermitian `A` and `B`, a contraction `W` within δ of one exact
interaction-picture segment approximates the full evolution after `L` segments within `L * δ`.
These estimates support the interaction-picture simulation analysis of [LowWiebe2018].

## Main statements

* `corollary4CompositeError`: linear accumulation of the single-segment error.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.LchsSimulation.TimeOrdered
open Qatlib.Concepts.TimeEvolution.TimeOrderedEvolution

namespace Qatlib.Concepts.InteractionEvo.SegmentProduct

open scoped BigOperators Matrix.Norms.L2Operator

/-- Proves that repeating a contraction with single-segment error at most δ yields error at most
`L * δ` for evolution under `A + B` through time `L * τ`; see [Low and Wiebe, Corollary
4][LowWiebe2018]. -/
theorem corollary4CompositeError : Corollary4CompositeError := by
  intro I _ _ A B hA hB L τ δ _hδ W hW herror
  let seg : Matrix I I ℂ := HamiltonianEvolution A τ *
    orderedEvolution (fun u => Complex.I • interactionGenerator A (fun _ => B) u) 0 τ
  have hseg : seg = HamiltonianEvolution (A + B) τ := by
    simpa [seg] using! (lemma6SegmentComposite I A B hA hB 1 τ)
  have hnorm : ‖seg‖ ≤ 1 := by
    rw [hseg]
    exact l2_norm_unitary_le_one (hamiltonianEvolution_unitary (hA.add hB) τ)
  have hprod := segment_product_perturbation_contraction_sum I
    (fun _ => W) (fun _ => seg) L (fun _ _ => hW) (fun _ _ => hnorm)
  have hmap (X : Matrix I I ℂ) : ((List.range L).map (fun _ => X)).prod = X ^ L := by
    simp [List.prod_replicate]
  rw [hmap W, hmap seg] at hprod
  have hcomposite : seg ^ L = HamiltonianEvolution (A + B) ((L : ℝ) * τ) :=
    lemma6SegmentComposite I A B hA hB L τ
  rw [hcomposite] at hprod
  refine hprod.trans ?_
  calc
    (∑ k ∈ Finset.range L, ‖W - seg‖) ≤ ∑ k ∈ Finset.range L, δ :=
      Finset.sum_le_sum (fun _ _ => herror)
    _ = (L : ℝ) * δ := by simp

end Qatlib.Concepts.InteractionEvo.SegmentProduct
