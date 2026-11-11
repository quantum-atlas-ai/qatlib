/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

/-
# Rooted-tree ancestor chains and the parallel-flow telescoping identity

Guoming Wang, *Span-program-based quantum algorithm for tree detection*,
fixed arXiv:1309.7713v3 (5 Mar 2014).

Section 2.1 fixes an arbitrary tree `T = (V_T, E_T)` with root `r`, the children
sets `C(x)`, the subtrees `T^x` with leaf sets `V^x_{T,l}`, and the leaf
intersections `S_{x,y} = V^x_{T,l} ∩ V^y_{T,l}`. Section 3 builds the tree-detection
span program on top of these data, and its positive analysis (Eq. (11)) rewrites
the target vector as the sum of one input vector per edge of `T`.

This module supplies that tree vocabulary in the rooted form used by the
construction (a parent map with a unique root), together with the telescoping
identity that makes Eq. (11) a statement about root-to-leaf chains.
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Basic

/-!
# RootedTreeChain

Paper-specific rooted tree chain constructions and proofs for SpanProgTree13.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Finset
open Classical

namespace Qatlib.Papers.SpanProgTree13.MainResults

/-- The total step map underlying `par : VT → Option VT`: it forgets the option
wrapper and applies `par`. -/
def step {VT : Type*} (par : VT → Option VT) : Option VT → Option VT :=
  fun o => o.bind par

/-- A finite rooted tree presented by its parent map. The root is the unique
parentless vertex, every vertex reaches the root, and no parent chain closes up;
these three conditions are exactly what "arbitrary tree `T` with root `r`"
means once the tree is routed at `r`. -/
structure RootedTree (VT : Type*) [Fintype VT] where
  /-- The root `r` of `T`. -/
  root : VT
  /-- The parent map of `T`. -/
  par : VT → Option VT
  /-- The root has no parent. -/
  par_root : par root = none
  /-- Every vertex reaches the root along the parent chain. -/
  reachable : ∀ a : VT, ∃ k : ℕ, (step par)^[k] (some a) = some root
  /-- No parent chain returns to its starting vertex. -/
  no_cycle : ∀ (a : VT) (k : ℕ), 0 < k → (step par)^[k] (some a) = some a → False

variable {VT : Type*} [Fintype VT]

namespace RootedTree

variable (t : RootedTree VT)

/-- The `k`-fold ancestor of `a`, still packaged as an option. -/
def ancOpt (a : VT) (k : ℕ) : Option VT := (step t.par)^[k] (some a)

/-- The distance from `a` to the root, i.e. the length of its ancestor chain. -/
def depth (a : VT) : ℕ := Nat.find (t.reachable a)

/-- The `k`-th ancestor of `a`, with the root as the out-of-range default. -/
def anc (a : VT) (k : ℕ) : VT := (t.ancOpt a k).getD t.root

/-- The parent of `a`, with the root as the default at the root itself. -/
def parB (a : VT) : VT := (t.par a).getD t.root

/-- `b` is a child of `a`, i.e. `b ∈ C(a)`. -/
def child (a b : VT) : Prop := t.par b = some a

/-- A vertex is a leaf of `T` when no vertex has it as a parent, i.e. `b ∈ V_{T,l}`. -/
def IsLeaf (f : VT) : Prop := ∀ a, ¬ t.child a f

/-- `b` lies on the ancestor chain of `f`, i.e. `b` is a node of the subtree `T^f`
lying on the route from `f` to the root. -/
def Subtree (b f : VT) : Prop := ∃ k : ℕ, t.ancOpt f k = some b

/-- The leaf set `V^a_{T,l}` of the subtree `T^a`. -/
def VLeaf (a : VT) : Finset {f : VT // t.IsLeaf f} :=
  Finset.univ.filter (fun f => t.Subtree a f.val)

/-- The zeroth ancestor is the vertex itself. -/
@[simp] theorem ancOpt_zero (a : VT) : t.ancOpt a 0 = some a := rfl

/-- Unfolding one step of the ancestor chain. -/
theorem ancOpt_succ (a : VT) (k : ℕ) :
    t.ancOpt a (k + 1) = (t.ancOpt a k).bind t.par := by
  rw [ancOpt, Function.iterate_succ_apply']
  rfl

/-- Once the chain has died it stays dead. -/
theorem iterate_none (j : ℕ) : (step t.par)^[j] none = none := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      rfl

/-- The step map sends the root past the end of the chain. -/
theorem step_root : step t.par (some t.root) = none := by
  simp [step, t.par_root]

/-- Any positive number of steps from the root leaves the chain. -/
theorem iterate_root {j : ℕ} (h : 0 < j) : (step t.par)^[j] (some t.root) = none := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp h)
  rw [Function.iterate_succ_apply, t.step_root]
  exact t.iterate_none i

/-- Splitting the ancestor chain at `k`. -/
theorem ancOpt_add (a : VT) (k j : ℕ) :
    t.ancOpt a (k + j) = (step t.par)^[j] (t.ancOpt a k) := by
  rw [ancOpt, Nat.add_comm, Function.iterate_add_apply]
  rfl

/-- The depth is exactly the distance to the root. -/
@[simp] theorem depth_spec (a : VT) : t.ancOpt a (t.depth a) = some t.root :=
  Nat.find_spec (t.reachable a)

/-- The depth is the least distance to the root. -/
theorem depth_le {a : VT} {k : ℕ} (h : t.ancOpt a k = some t.root) : t.depth a ≤ k :=
  Nat.find_min' (t.reachable a) h

/-- At its depth the ancestor chain has arrived at the root. -/
@[simp] theorem anc_at_depth (a : VT) : t.anc a (t.depth a) = t.root := by
  rw [anc, t.depth_spec]
  rfl

/-- The `k`-th ancestor is defined whenever `k` does not exceed the depth: the
chain only degenerates after it has reached the root. -/
theorem ancOpt_ne_none {a : VT} {k : ℕ} (h : k ≤ t.depth a) : t.ancOpt a k ≠ none := by
  intro hk
  have hsplit : t.ancOpt a (t.depth a)
      = (step t.par)^[t.depth a - k] (t.ancOpt a k) := by
    conv_lhs => rw [← Nat.add_sub_cancel' h]
    exact t.ancOpt_add a k (t.depth a - k)
  rw [hk, t.iterate_none, t.depth_spec] at hsplit
  simp at hsplit

/-- The `k`-th ancestor is a genuine vertex whenever `k` does not exceed the depth. -/
theorem ancOpt_eq_some_anc {a : VT} {k : ℕ} (h : k ≤ t.depth a) :
    t.ancOpt a k = some (t.anc a k) := by
  have hne := t.ancOpt_ne_none h
  cases hk : t.ancOpt a k with
  | none => exact absurd hk hne
  | some b =>
      have hb : t.anc a k = b := by simp [anc, hk]
      rw [← hb]

/-- The zeroth ancestor is the vertex itself. -/
@[simp] theorem anc_zero (a : VT) : t.anc a 0 = a := by
  simp [anc]

/-- Consecutive ancestors are related by the parent map: this is the summation
index of Eq. (11), where the `k`-th edge of the route from `f` to the root
contributes `|(ι a, ι b)⟩`. -/
theorem par_anc {a : VT} {k : ℕ} (h : k < t.depth a) :
    t.par (t.anc a k) = some (t.anc a (k + 1)) := by
  have hk : t.ancOpt a k = some (t.anc a k) := t.ancOpt_eq_some_anc (Nat.le_of_lt h)
  have h1 : t.ancOpt a (k + 1) = t.par (t.anc a k) := by
    rw [t.ancOpt_succ, hk]
    rfl
  have h2 : t.ancOpt a (k + 1) = some (t.anc a (k + 1)) :=
    t.ancOpt_eq_some_anc (Nat.succ_le_of_lt h)
  exact h1.symm.trans h2

/-- Every vertex other than the root sits at positive depth. -/
theorem depth_pos_of_ne_root {a : VT} (h : a ≠ t.root) : 0 < t.depth a := by
  by_contra hz
  have h0 : t.depth a = 0 := Nat.eq_zero_of_not_pos hz
  have hsome : t.ancOpt a 0 = some t.root := by rw [← h0]; exact t.depth_spec a
  exact h (Option.some.inj hsome)

/-- Only the root is parentless. -/
theorem par_ne_none {a : VT} (h : a ≠ t.root) : t.par a ≠ none := by
  intro hnone
  have hp : 0 < t.depth a := t.depth_pos_of_ne_root h
  have h1 : t.ancOpt a 1 = none := by
    simp [ancOpt, step, hnone]
  exact t.ancOpt_ne_none (k := 1) hp h1

/-- Off the root, `parB` is the genuine parent. -/
theorem par_parB {a : VT} (h : a ≠ t.root) : t.par a = some (t.parB a) := by
  have hp := t.par_ne_none h
  cases hq : t.par a with
  | none => exact absurd hq hp
  | some b => simp [parB, hq]

/-- The ancestor chain is injective below the depth: this is precisely acyclicity. -/
theorem anc_inj {a : VT} {k j : ℕ} (hk : k ≤ t.depth a) (hj : j ≤ t.depth a)
    (h : t.anc a k = t.anc a j) : k = j := by
  wlog hkj : k ≤ j generalizing k j with H
  · exact (H hj hk h.symm (by omega)).symm
  rcases Nat.eq_or_lt_of_le hkj with heq | hlt
  · exact heq
  · exfalso
    have hstep : t.ancOpt a j = (step t.par)^[j - k] (t.ancOpt a k) := by
      conv_lhs => rw [← Nat.add_sub_cancel' hkj]
      exact t.ancOpt_add a k (j - k)
    rw [t.ancOpt_eq_some_anc hk, t.ancOpt_eq_some_anc hj, h] at hstep
    exact t.no_cycle (t.anc a j) (j - k) (by omega) hstep.symm

/-- An ancestor strictly below the depth is not the root. -/
theorem anc_ne_root {a : VT} {k : ℕ} (h : k < t.depth a) : t.anc a k ≠ t.root := by
  intro heq
  have hsome : t.ancOpt a k = some t.root := by
    rw [t.ancOpt_eq_some_anc (Nat.le_of_lt h), heq]
  have := t.depth_le hsome
  omega

/-- For a non-root `b`, the subtree relation is exactly membership in the
ancestor chain at a distance below the depth. -/
theorem subtree_iff {b f : VT} (hb : b ≠ t.root) :
    t.Subtree b f ↔ ∃ k, k < t.depth f ∧ t.anc f k = b := by
  constructor
  · rintro ⟨k, hk⟩
    rcases lt_or_ge k (t.depth f) with hlt | hge
    · refine ⟨k, hlt, ?_⟩
      have hone := t.ancOpt_eq_some_anc (Nat.le_of_lt hlt)
      rw [hone] at hk
      exact Option.some.inj hk
    · exfalso
      have hsplit : t.ancOpt f k = (step t.par)^[k - t.depth f] (some t.root) := by
        conv_lhs => rw [← Nat.add_sub_cancel' hge]
        rw [t.ancOpt_add, t.depth_spec]
      rcases Nat.eq_or_lt_of_le hge with heq | hlt2
      · rw [heq, Nat.sub_self, Function.iterate_zero_apply] at hsplit
        rw [hsplit] at hk
        exact hb (Option.some.inj hk).symm
      · rw [hsplit, t.iterate_root (by omega)] at hk
        simp at hk
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, t.ancOpt_eq_some_anc (Nat.le_of_lt hk)⟩

/-- Eq. (11) in chain form: summing the parent differences along the route from
`f` to the root telescopes to the difference between the root and `f`. -/
theorem sum_chain (f : VT) (φ : VT → ℝ) :
    (∑ k ∈ Finset.range (t.depth f), (φ (t.anc f (k + 1)) - φ (t.anc f k)))
      = φ t.root - φ f := by
  have h := Finset.sum_range_sub (fun k => φ (t.anc f k)) (t.depth f)
  simpa using h

/-- Reindexing the strict ancestors of `f` as the range of its ancestor chain. -/
theorem sum_subtree (f : VT) (ψ : VT → ℝ) [DecidableEq VT] :
    (∑ b ∈ Finset.univ.filter (fun b => b ≠ t.root ∧ t.Subtree b f), ψ b)
      = ∑ k ∈ Finset.range (t.depth f), ψ (t.anc f k) := by
  have hinj : Set.InjOn (t.anc f) (↑(Finset.range (t.depth f)) : Set ℕ) := by
    intro k hk j hj hkj
    exact t.anc_inj (Finset.mem_range.mp hk).le (Finset.mem_range.mp hj).le hkj
  have hset : Finset.univ.filter (fun b => b ≠ t.root ∧ t.Subtree b f)
      = (Finset.range (t.depth f)).image (t.anc f) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_image, Finset.mem_range, true_and]
    constructor
    · rintro ⟨hb, hsub⟩
      exact t.subtree_iff hb |>.mp hsub
    · rintro ⟨k, hk, rfl⟩
      exact ⟨t.anc_ne_root hk, t.subtree_iff (t.anc_ne_root hk) |>.mpr ⟨k, hk, rfl⟩⟩
  rw [hset, Finset.sum_image hinj]

end RootedTree

end Qatlib.Papers.SpanProgTree13.MainResults
