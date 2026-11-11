/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.InteractionEvo.SegmentProduct.EffectiveProductPerturbationStat

/-!
# Perturbation bounds for reverse products

`effectiveProductPerturbation` establishes a telescoping norm bound for reverse-ordered products
in a normed ring whose identity has norm at most one. Each local difference is weighted by
products of norms of the surrounding factors. These estimates support the interaction-picture
simulation analysis of [LowWiebe2018].

## Main statements

* `norm_reverse_prod_le`: the norm bound for a reversed list product.
* `effectiveProductPerturbation`: the weighted perturbation estimate.

## References

* [Low and Wiebe, 2018][LowWiebe2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.InteractionEvo.SegmentProduct
open scoped BigOperators
set_option warningAsError false

/-- Bounds the norm of a reversed list product by the product of the factor norms, assuming the
identity has norm at most one. -/
private theorem norm_reverse_prod_le {A : Type} [NormedRing A]
    (l : List A) (h1 : ‖(1 : A)‖ ≤ 1) :
    ‖l.reverse.prod‖ ≤ (l.map norm).prod := by
  induction l with
  | nil => simpa using! h1
  | cons a l ih =>
    simp only [List.reverse_cons, List.prod_append, List.prod_cons, List.prod_nil,
      mul_one, List.map_cons]
    calc
      _ ≤ ‖l.reverse.prod‖ * ‖a‖ := norm_mul_le _ _
      _ ≤ (l.map norm).prod * ‖a‖ := mul_le_mul_of_nonneg_right ih (norm_nonneg _)
      _ = _ := mul_comm _ _

/-- Proves the weighted perturbation bound for reverse-ordered products in
`EffectiveProductPerturbation`; compare [Low and Wiebe, Equation (12)][LowWiebe2018]. -/
theorem effectiveProductPerturbation : EffectiveProductPerturbation := by
  intro A _ u v L h1
  induction L with
  | zero => simp
  | succ L ih =>
    let term (m j : ℕ) : ℝ :=
      (((List.range' (j+1) (m-(j+1))).map (fun i => ‖u i‖)).prod) *
        ‖u j-v j‖ * (((List.range j).map (fun i => ‖v i‖)).prod)
    have hs (j : ℕ) (hj : j ∈ Finset.range L) :
        term (L+1) j = ‖u L‖ * term L j := by
      have hjL : j+1 ≤ L := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
      have hlen : L+1-(j+1) = (L-(j+1))+1 := by omega
      dsimp [term]
      rw [hlen, List.range'_concat]
      simp only [List.map_append, List.map_cons, List.map_nil, List.prod_append,
        List.prod_cons, List.prod_nil, mul_one, one_mul]
      rw [Nat.add_sub_of_le hjL]
      ring
    have he : term (L+1) L =
        ‖u L-v L‖ * (((List.range L).map (fun i => ‖v i‖)).prod) := by
      simp [term]
    have hr : (∑ j ∈ Finset.range (L+1), term (L+1) j) =
        ‖u L‖ * (∑ j ∈ Finset.range L, term L j) +
          ‖u L-v L‖ * (((List.range L).map (fun i => ‖v i‖)).prod) := by
      rw [Finset.sum_range_succ, he, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl hs
    change _ ≤ ∑ j ∈ Finset.range (L+1), term (L+1) j
    rw [hr]
    simp only [List.range_succ, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.prod_cons]
    have hid : u L * ((List.range L).map u).reverse.prod -
        v L * ((List.range L).map v).reverse.prod =
        u L * (((List.range L).map u).reverse.prod - ((List.range L).map v).reverse.prod) +
        (u L-v L) * ((List.range L).map v).reverse.prod := by noncomm_ring
    rw [hid]
    refine (norm_add_le _ _).trans ((add_le_add (norm_mul_le _ _) (norm_mul_le _ _)).trans ?_)
    apply add_le_add
    · exact mul_le_mul_of_nonneg_left ih (norm_nonneg _)
    · have hn := norm_reverse_prod_le ((List.range L).map v) h1
      simpa only [List.map_map, Function.comp_def] using!
        mul_le_mul_of_nonneg_left hn (norm_nonneg (u L-v L))

end Qatlib.Concepts.InteractionEvo.SegmentProduct
