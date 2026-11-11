/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-!
# Consistent difference labels and delta-network sums

Encodes tree-edge labels and cycle constraints over `ZMod q` for the difference-model network in
[AradLandau2010]. The map `extend` determines each non-tree label from the tree labels, and
`consistentEquiv` identifies consistent full labelings with arbitrary tree labelings.

The constrained sum `deltaNetworkValue` reduces to a sum over tree labels and hence to a sum
over all consistent labels. A final scalar identity records the normalization by a nonzero
color-count factor.

## Main statements

* `consistentEquiv`: identifies consistent full labelings with tree labelings.
* `deltaNetworkValue_eq_treeSum`: eliminates the constrained cycle-label sum.
* `lemma5_8_network_value_eq_consistent_sum`: expresses the network value as a consistent-label
  sum.

## References

* [Arad and Landau, 2010][AradLandau2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Finset BigOperators
open Classical

namespace Qatlib.Papers.TensorNetwork08.MainResults.DeltaNetwork

variable {Edge : Type*} [Fintype Edge]

/-- The subtype of edges marked true by `isTree`. -/
abbrev TreeEdge (isTree : Edge → Bool) : Type _ := {e : Edge // isTree e = true}

/-- The subtype of edges not marked true by `isTree`. -/
abbrev CycleEdge (isTree : Edge → Bool) : Type _ := {e : Edge // ¬ isTree e = true}

/-- The condition that each non-tree label plus the prescribed integer linear combination of
tree labels vanishes in `ZMod q`. -/
def IsConsistent (q : ℕ) (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ)
    (δ : Edge → ZMod q) : Prop :=
  ∀ e, ¬ isTree e = true →
    δ e + ∑ f : TreeEdge isTree, (cycleCoeff e f.val : ZMod q) * δ f.val = 0

/-- Extends tree-edge labels by assigning each non-tree edge the negative prescribed linear
combination of tree labels. -/
def extend (q : ℕ) (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ)
    (δtr : TreeEdge isTree → ZMod q) : Edge → ZMod q :=
  fun e =>
    if h : isTree e = true then δtr ⟨e, h⟩
    else -∑ f : TreeEdge isTree, (cycleCoeff e f.val : ZMod q) * δtr f

/-- Every labeling constructed by `extend` satisfies the specified cycle consistency equations. -/
theorem extend_consistent (q : ℕ) (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ)
    (δtr : TreeEdge isTree → ZMod q) :
    IsConsistent q isTree cycleCoeff (extend q isTree cycleCoeff δtr) := by
  intro e he
  have hval : extend q isTree cycleCoeff δtr e
      = -∑ f : TreeEdge isTree, (cycleCoeff e f.val : ZMod q) * δtr f := by
    unfold extend
    rw [dif_neg he]
  have hsum : (∑ f : TreeEdge isTree,
        (cycleCoeff e f.val : ZMod q) * extend q isTree cycleCoeff δtr f)
      = ∑ f : TreeEdge isTree, (cycleCoeff e f.val : ZMod q) * δtr f := by
    apply Finset.sum_congr rfl
    intro f _
    rw [extend, dif_pos f.property]
  rw [hval, hsum]
  exact neg_add_cancel _

/-- The extension map from tree-edge labelings to all-edge labelings is injective. -/
theorem extend_injective (q : ℕ) (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ) :
    Function.Injective (extend q isTree cycleCoeff) := by
  intro a b hab
  funext f
  have h := congrFun hab f.val
  simp only [extend, dif_pos f.property] at h
  simpa using h

/-- Restricting a consistent labeling to tree edges and extending it recovers the original
labeling. -/
theorem eq_extend_restrict (q : ℕ) (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ)
    (δ : Edge → ZMod q) (hδ : IsConsistent q isTree cycleCoeff δ) :
    extend q isTree cycleCoeff (fun f => δ f.val) = δ := by
  classical
  funext e
  by_cases he : isTree e = true
  · unfold extend
    rw [dif_pos he]
  · have hcon := hδ e he
    rw [add_comm] at hcon
    have hsum : (∑ f : TreeEdge isTree, (cycleCoeff e f.val : ZMod q) * δ f.val)
        = -δ e := eq_neg_of_add_eq_zero_left hcon
    unfold extend
    rw [dif_neg he, hsum, neg_neg]

/-- The equivalence between all-edge labelings satisfying the cycle equations and arbitrary
tree-edge labelings. See [AradLandau2010]. -/
def consistentEquiv (q : ℕ) (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ) :
    {δ : Edge → ZMod q // IsConsistent q isTree cycleCoeff δ} ≃
      (TreeEdge isTree → ZMod q) where
  toFun x := fun f => x.val f.val
  invFun δtr := ⟨extend q isTree cycleCoeff δtr, extend_consistent q isTree cycleCoeff δtr⟩
  left_inv x := by
    apply Subtype.ext
    exact eq_extend_restrict q isTree cycleCoeff x.val x.property
  right_inv δtr := by
    funext f
    show extend q isTree cycleCoeff δtr f.val = δtr f
    unfold extend
    rw [dif_pos f.property]

/-- Reindexes the weighted sum over consistent full labelings as the weighted sum over their
tree-label extensions. -/
theorem sum_consistent_eq_sum_tree (q : ℕ) [NeZero q] (isTree : Edge → Bool)
    (cycleCoeff : Edge → Edge → ℤ) (w : Edge → ZMod q → ℂ) :
    (∑ δ : {δ : Edge → ZMod q // IsConsistent q isTree cycleCoeff δ},
        ∏ e, w e (δ.val e))
      = ∑ δtr : (TreeEdge isTree → ZMod q),
          ∏ e, w e (extend q isTree cycleCoeff δtr e) := by
  classical
  let ev := consistentEquiv q isTree cycleCoeff
  have hsplit := Equiv.sum_comp ev.symm
    (fun δ : {δ : Edge → ZMod q // IsConsistent q isTree cycleCoeff δ} =>
      ∏ e, w e (δ.val e))
  try simp only at hsplit
  rw [← hsplit]
  apply Finset.sum_congr rfl
  intro δtr _
  rfl

/-- The product of edge weights over tree and non-tree subtypes equals the product over all
edges. -/
theorem prod_tree_mul_cycle (q : ℕ) (isTree : Edge → Bool)
    (g : Edge → ZMod q) (w : Edge → ZMod q → ℂ) :
    (∏ f : TreeEdge isTree, w f.val (g f.val)) *
        (∏ e : CycleEdge isTree, w e.val (g e.val))
      = ∏ e : Edge, w e (g e) := by
  classical
  have hT : (∏ f : TreeEdge isTree, w f.val (g f.val))
      = ∏ e ∈ (univ : Finset Edge).filter (fun e => isTree e = true), w e (g e) :=
    (Finset.prod_subtype (s := (univ : Finset Edge).filter (fun e => isTree e = true))
      (h := by intro x; simp) (f := fun e => w e (g e))).symm
  have hC : (∏ e : CycleEdge isTree, w e.val (g e.val))
      = ∏ e ∈ (univ : Finset Edge).filter (fun e => ¬ isTree e = true), w e (g e) :=
    (Finset.prod_subtype (s := (univ : Finset Edge).filter (fun e => ¬ isTree e = true))
      (h := by intro x; simp) (f := fun e => w e (g e))).symm
  rw [hT, hC]
  simpa using Finset.prod_filter_mul_prod_filter_not (univ : Finset Edge)
    (fun e => isTree e = true) (fun e => w e (g e))

/-- The sum over tree and non-tree labelings of their edge-weight products, constrained to the
non-tree labels prescribed by `extend`. -/
def deltaNetworkValue (q : ℕ) [NeZero q] (isTree : Edge → Bool)
    (cycleCoeff : Edge → Edge → ℤ) (w : Edge → ZMod q → ℂ) : ℂ :=
  ∑ δtr : (TreeEdge isTree → ZMod q),
    ∑ δcyc : (CycleEdge isTree → ZMod q),
      (if ∀ e : CycleEdge isTree,
          δcyc e = extend q isTree cycleCoeff δtr e.val then 1 else 0)
        * ((∏ f : TreeEdge isTree, w f.val (δtr f)) *
            ∏ e : CycleEdge isTree, w e.val (δcyc e))

/-- The constrained delta-network value equals the sum over tree labelings of the full
edge-weight product of their extensions. See [AradLandau2010]. -/
theorem deltaNetworkValue_eq_treeSum (q : ℕ) [NeZero q] (isTree : Edge → Bool)
    (cycleCoeff : Edge → Edge → ℤ) (w : Edge → ZMod q → ℂ) :
    deltaNetworkValue q isTree cycleCoeff w
      = ∑ δtr : (TreeEdge isTree → ZMod q),
          ∏ e : Edge, w e (extend q isTree cycleCoeff δtr e) := by
  unfold deltaNetworkValue
  apply Finset.sum_congr rfl
  intro δtr _
  rw [Finset.sum_eq_single (fun e : CycleEdge isTree =>
        extend q isTree cycleCoeff δtr e.val)]
  · rw [if_pos (fun _ => rfl), one_mul]
    have htree : (∏ f : TreeEdge isTree, w f.val (δtr f))
        = ∏ f : TreeEdge isTree,
            w f.val (extend q isTree cycleCoeff δtr f.val) := by
      apply Finset.prod_congr rfl
      intro f _
      rw [extend, dif_pos f.property]
    rw [htree, prod_tree_mul_cycle q isTree
      (fun e => extend q isTree cycleCoeff δtr e) w]
  · intro b _ hb
    have hcond : ¬ ∀ e : CycleEdge isTree,
        b e = extend q isTree cycleCoeff δtr e.val := by
      intro h
      exact hb (funext h)
    rw [if_neg hcond, zero_mul]
  · intro hg
    exact absurd (Finset.mem_univ (fun e : CycleEdge isTree =>
      extend q isTree cycleCoeff δtr e.val)) hg

/-- The delta-network value equals the sum of edge-weight products over all labelings satisfying
the specified cycle constraints. See [AradLandau2010]. -/
theorem lemma5_8_network_value_eq_consistent_sum (q : ℕ) [NeZero q]
    (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ) (w : Edge → ZMod q → ℂ) :
    deltaNetworkValue q isTree cycleCoeff w
      = ∑ δ : {δ : Edge → ZMod q // IsConsistent q isTree cycleCoeff δ},
          ∏ e, w e (δ.val e) := by
  rw [deltaNetworkValue_eq_treeSum]
  exact (sum_consistent_eq_sum_tree q isTree cycleCoeff w).symm

/-- The sum over tree-label extensions equals the sum over all consistent edge labelings. -/
theorem networkValue_eq_consistentSum (q : ℕ) [NeZero q] (isTree : Edge → Bool)
    (cycleCoeff : Edge → Edge → ℤ) (w : Edge → ZMod q → ℂ) :
    (∑ δtr : (TreeEdge isTree → ZMod q),
        ∏ e, w e (extend q isTree cycleCoeff δtr e))
      = ∑ δ : {δ : Edge → ZMod q // IsConsistent q isTree cycleCoeff δ},
          ∏ e, w e (δ.val e) :=
  (sum_consistent_eq_sum_tree q isTree cycleCoeff w).symm

/-- If `Z = qC * S` with nonzero `qC`, then `S = qC⁻¹ * Z`. -/
theorem normalized_partition (Z S qC : ℂ) (hq : qC ≠ 0)
    (hZ : Z = qC * S) : S = qC⁻¹ * Z := by
  rw [hZ]
  field_simp

end Qatlib.Papers.TensorNetwork08.MainResults.DeltaNetwork
