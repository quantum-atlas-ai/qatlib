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
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false

noncomputable section

open Finset BigOperators
open Classical

namespace Qatlib.Papers.TensorNetwork08.MainResults.DeltaNetwork

variable {Edge : Type*} [Fintype Edge]

abbrev TreeEdge (isTree : Edge → Bool) : Type _ := {e : Edge // isTree e = true}

abbrev CycleEdge (isTree : Edge → Bool) : Type _ := {e : Edge // ¬ isTree e = true}

def IsConsistent (q : ℕ) (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ)
    (δ : Edge → ZMod q) : Prop :=
  ∀ e, ¬ isTree e = true →
    δ e + ∑ f : TreeEdge isTree, (cycleCoeff e f.val : ZMod q) * δ f.val = 0

def extend (q : ℕ) (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ)
    (δtr : TreeEdge isTree → ZMod q) : Edge → ZMod q :=
  fun e =>
    if h : isTree e = true then δtr ⟨e, h⟩
    else -∑ f : TreeEdge isTree, (cycleCoeff e f.val : ZMod q) * δtr f

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

theorem extend_injective (q : ℕ) (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ) :
    Function.Injective (extend q isTree cycleCoeff) := by
  intro a b hab
  funext f
  have h := congrFun hab f.val
  simp only [extend, dif_pos f.property] at h
  simpa using h

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

def deltaNetworkValue (q : ℕ) [NeZero q] (isTree : Edge → Bool)
    (cycleCoeff : Edge → Edge → ℤ) (w : Edge → ZMod q → ℂ) : ℂ :=
  ∑ δtr : (TreeEdge isTree → ZMod q),
    ∑ δcyc : (CycleEdge isTree → ZMod q),
      (if ∀ e : CycleEdge isTree,
          δcyc e = extend q isTree cycleCoeff δtr e.val then 1 else 0)
        * ((∏ f : TreeEdge isTree, w f.val (δtr f)) *
            ∏ e : CycleEdge isTree, w e.val (δcyc e))

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

theorem lemma5_8_network_value_eq_consistent_sum (q : ℕ) [NeZero q]
    (isTree : Edge → Bool) (cycleCoeff : Edge → Edge → ℤ) (w : Edge → ZMod q → ℂ) :
    deltaNetworkValue q isTree cycleCoeff w
      = ∑ δ : {δ : Edge → ZMod q // IsConsistent q isTree cycleCoeff δ},
          ∏ e, w e (δ.val e) := by
  rw [deltaNetworkValue_eq_treeSum]
  exact (sum_consistent_eq_sum_tree q isTree cycleCoeff w).symm

theorem networkValue_eq_consistentSum (q : ℕ) [NeZero q] (isTree : Edge → Bool)
    (cycleCoeff : Edge → Edge → ℤ) (w : Edge → ZMod q → ℂ) :
    (∑ δtr : (TreeEdge isTree → ZMod q),
        ∏ e, w e (extend q isTree cycleCoeff δtr e))
      = ∑ δ : {δ : Edge → ZMod q // IsConsistent q isTree cycleCoeff δ},
          ∏ e, w e (δ.val e) :=
  (sum_consistent_eq_sum_tree q isTree cycleCoeff w).symm

theorem normalized_partition (Z S qC : ℂ) (hq : qC ≠ 0)
    (hZ : Z = qC * S) : S = qC⁻¹ * Z := by
  rw [hZ]
  field_simp

end Qatlib.Papers.TensorNetwork08.MainResults.DeltaNetwork
