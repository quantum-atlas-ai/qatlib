/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Bool.Basic
import Mathlib.Order.Lattice
import Mathlib.Tactic

/-!
# Threshold reduction for Min-Max trees

`Tree` describes finite rooted trees with indexed leaves and nonempty lists of children at Min
or Max gates. The evaluator `Tree.eval` works over any linear order, is monotone in the inputs,
and always returns an input value.

The threshold identity `threshold_eval_iff` converts evaluation over an ordered type into
Boolean evaluation, giving the Min-Max to And-Or reduction of [CleveGavinskyYongeMallo2007].

## Main statements

* `threshold_eval_iff`: Thresholding the leaves commutes with tree evaluation.
* `eval_mono`: Tree evaluation is monotone in all input values.
* `exists_leaf_eq_eval`: Every evaluation equals some indexed input value.

## References

* [Cleve et al., 2007][CleveGavinskyYongeMallo2007]
-/

set_option autoImplicit false

namespace Qatlib.Papers.MinMaxTree07.ThresholdTree

/-- The two gate kinds used in a Min-Max tree: minimum and maximum. -/
inductive Gate where
  | min : Gate
  | max : Gate
deriving DecidableEq, Repr

/-- A finite Min-Max tree with natural-number leaf indices and a nonempty list of children at
each internal node. -/
inductive Tree where
  | leaf : ℕ → Tree
  | node : Gate → Tree → List Tree → Tree

namespace Tree

/-- The total number of leaf and internal nodes in a tree. -/
def size : Tree → ℕ
  | .leaf _ => 1
  | .node _ c cs => 1 + size c + (cs.map size).sum

/-- The immediate children of a tree, listed with the distinguished first child before the
remaining children. -/
def children : Tree → List Tree
  | .leaf _ => []
  | .node _ c cs => c :: cs

/-- A leaf has no children. -/
@[simp] theorem children_leaf (i : ℕ) : children (.leaf i) = [] := rfl

/-- The children of an internal node are its distinguished child followed by its remaining
children. -/
@[simp] theorem children_node (g : Gate) (c : Tree) (cs : List Tree) :
    children (.node g c cs) = c :: cs := rfl

/-- The size of any listed child is at most the sum of the sizes of all listed children. -/
theorem size_le_sum_map {c d : Tree} {cs : List Tree} (hd : d ∈ c :: cs) :
    size d ≤ ((c :: cs).map size).sum :=
  List.le_sum_of_mem (List.mem_map_of_mem (f := size) hd)

/-- Prove a property of a tree by assuming it holds for every immediate child. -/
theorem inductionOnSize {motive : Tree → Prop} (t : Tree)
    (h : ∀ t, (∀ d ∈ children t, motive d) → motive t) : motive t := by
  suffices ∀ n, ∀ t, size t < n → motive t from this (size t + 1) t (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro t ht; exact absurd ht (Nat.not_lt_zero _)
  | succ n ih =>
    intro t ht
    refine h t (fun d hd => ih d ?_)
    cases t with
    | leaf i => simp at hd
    | node g c cs =>
      simp only [children_node] at hd
      have hle : size d ≤ ((c :: cs).map size).sum := size_le_sum_map hd
      simp only [List.map_cons, List.sum_cons] at hle
      have ht' : size (Tree.node g c cs) < n + 1 := ht
      rw [size] at ht'
      omega

/-- The binary minimum or maximum operation selected by the gate `g`. -/
def merge {α : Type*} [LinearOrder α] (g : Gate) (a b : α) : α :=
  match g with
  | .min => min a b
  | .max => max a b

/-- Merging with a minimum gate is the ordinary minimum operation. -/
@[simp] theorem merge_min {α : Type*} [LinearOrder α] (a b : α) :
    merge .min a b = min a b := rfl

/-- Merging with a maximum gate is the ordinary maximum operation. -/
@[simp] theorem merge_max {α : Type*} [LinearOrder α] (a b : α) :
    merge .max a b = max a b := rfl

/-- Evaluate a Min-Max tree by looking up indexed leaf values and folding the gate operation
over each node's children. -/
def eval {α : Type*} [LinearOrder α] (t : Tree) (x : ℕ → α) : α :=
  match t with
  | .leaf i => x i
  | .node g c cs => cs.foldr (fun d acc => merge g (eval d x) acc) (eval c x)
termination_by size t
decreasing_by
  all_goals
    simp only [size]
    first
      | omega
      | (exact Nat.lt_of_le_of_lt
          (List.le_sum_of_mem (List.mem_map_of_mem (f := size) (by assumption))) (by omega))

/-- Evaluating a leaf returns its indexed input value. -/
@[simp] theorem eval_leaf {α : Type*} [LinearOrder α] (i : ℕ) (x : ℕ → α) :
    eval (.leaf i) x = x i := by
  conv_lhs => rw [eval]

/-- Evaluating an internal node folds its gate operation over the evaluations of its children. -/
@[simp] theorem eval_node {α : Type*} [LinearOrder α] (g : Gate) (c : Tree)
    (cs : List Tree) (x : ℕ → α) :
    eval (.node g c cs) x = cs.foldr (fun d acc => merge g (eval d x) acc) (eval c x) := by
  conv_lhs => rw [eval]

/-- A threshold lies below a folded minimum exactly when it lies below the initial value and
every listed value. -/
theorem le_foldr_min_map_iff {α : Type*} [LinearOrder α] (cs : List Tree) (f : Tree → α)
    (a v : α) :
    v ≤ cs.foldr (fun d acc => min (f d) acc) a ↔ v ≤ a ∧ ∀ d ∈ cs, v ≤ f d := by
  induction cs with
  | nil => simp
  | cons d ds ih => simp [ih, and_left_comm]

/-- A threshold lies below a folded maximum exactly when it lies below the initial value or some
listed value. -/
theorem le_foldr_max_map_iff {α : Type*} [LinearOrder α] (cs : List Tree) (f : Tree → α)
    (a v : α) :
    v ≤ cs.foldr (fun d acc => max (f d) acc) a ↔ v ≤ a ∨ ∃ d ∈ cs, v ≤ f d := by
  induction cs with
  | nil => simp
  | cons d ds ih => simp [ih, or_left_comm]

/-- A threshold lies below a minimum node's value exactly when it lies below every child value. -/
theorem le_eval_node_min_iff {α : Type*} [LinearOrder α] (c : Tree) (cs : List Tree)
    (x : ℕ → α) (v : α) :
    v ≤ eval (.node .min c cs) x ↔ v ≤ eval c x ∧ ∀ d ∈ cs, v ≤ eval d x := by
  simp only [eval_node, merge_min]
  rw [le_foldr_min_map_iff]

/-- A threshold lies below a maximum node's value exactly when it lies below at least one child
value. -/
theorem le_eval_node_max_iff {α : Type*} [LinearOrder α] (c : Tree) (cs : List Tree)
    (x : ℕ → α) (v : α) :
    v ≤ eval (.node .max c cs) x ↔ v ≤ eval c x ∨ ∃ d ∈ cs, v ≤ eval d x := by
  simp only [eval_node, merge_max]
  rw [le_foldr_max_map_iff]

/-- Increasing the initial value and every listed value can only increase their folded minimum. -/
theorem foldr_min_map_mono {α : Type*} [LinearOrder α] (cs : List Tree) {f g : Tree → α}
    {a b : α} (hab : a ≤ b) (h : ∀ d ∈ cs, f d ≤ g d) :
    cs.foldr (fun d acc => min (f d) acc) a ≤ cs.foldr (fun d acc => min (g d) acc) b := by
  induction cs with
  | nil => simpa using hab
  | cons d ds ih =>
    simp only [List.foldr_cons]
    refine le_min ?_ ?_
    · exact le_trans (min_le_left _ _) (h d (by simp))
    · exact le_trans (min_le_right _ _) (ih (fun e he => h e (by simp [he])))

/-- Increasing the initial value and every listed value can only increase their folded maximum. -/
theorem foldr_max_map_mono {α : Type*} [LinearOrder α] (cs : List Tree) {f g : Tree → α}
    {a b : α} (hab : a ≤ b) (h : ∀ d ∈ cs, f d ≤ g d) :
    cs.foldr (fun d acc => max (f d) acc) a ≤ cs.foldr (fun d acc => max (g d) acc) b := by
  induction cs with
  | nil => simpa using hab
  | cons d ds ih =>
    simp only [List.foldr_cons]
    refine max_le ?_ ?_
    · exact le_trans (h d (by simp)) (le_max_left _ _)
    · exact le_trans (ih (fun e he => h e (by simp [he]))) (le_max_right _ _)

/-- A Boolean is at least `true` precisely when it equals `true`. -/
theorem true_le_bool_iff (b : Bool) : (true ≤ b) ↔ b = true := by
  cases b <;> simp

/-- Evaluating the Boolean leaf tests `v ≤ x i` yields `true` exactly when `v ≤ eval t x`, the
threshold reduction in [Cleve et al., Lemma 1][CleveGavinskyYongeMallo2007]. -/
theorem threshold_eval_iff {α : Type*} [LinearOrder α] (t : Tree) (x : ℕ → α) (v : α) :
    eval t (fun i => decide (v ≤ x i)) = true ↔ v ≤ eval t x := by
  refine inductionOnSize (motive := fun t =>
    eval t (fun i => decide (v ≤ x i)) = true ↔ v ≤ eval t x) t (fun t ih => ?_)
  match t with
  | .leaf i => simp
  | .node g c cs =>
    have hc : eval c (fun i => decide (v ≤ x i)) = true ↔ v ≤ eval c x :=
      ih c (by simp)
    have hd : ∀ d ∈ cs, (eval d (fun i => decide (v ≤ x i)) = true ↔ v ≤ eval d x) :=
      fun d hd => ih d (by simp [hd])
    cases g with
    | min =>
      simp only [eval_node, merge_min]
      rw [← true_le_bool_iff, le_foldr_min_map_iff, le_foldr_min_map_iff]
      simp only [true_le_bool_iff]
      exact ⟨fun h => ⟨hc.1 h.1, fun d hd' => (hd d hd').1 (h.2 d hd')⟩,
        fun h => ⟨hc.2 h.1, fun d hd' => (hd d hd').2 (h.2 d hd')⟩⟩
    | max =>
      simp only [eval_node, merge_max]
      rw [← true_le_bool_iff, le_foldr_max_map_iff, le_foldr_max_map_iff]
      simp only [true_le_bool_iff]
      constructor
      · rintro (h | ⟨d, hd', h⟩)
        · exact Or.inl (hc.1 h)
        · exact Or.inr ⟨d, hd', (hd d hd').1 h⟩
      · rintro (h | ⟨d, hd', h⟩)
        · exact Or.inl (hc.2 h)
        · exact Or.inr ⟨d, hd', (hd d hd').2 h⟩

/-- Evaluating the Boolean leaf tests `v ≤ x i` yields `false` exactly when the tree value fails
the threshold test; see [CleveGavinskyYongeMallo2007]. -/
theorem threshold_eval_false_iff {α : Type*} [LinearOrder α] (t : Tree) (x : ℕ → α) (v : α) :
    eval t (fun i => decide (v ≤ x i)) = false ↔ ¬ v ≤ eval t x := by
  have h := threshold_eval_iff t x v
  constructor
  · intro hf hv
    rw [h.2 hv] at hf
    exact Bool.noConfusion hf
  · intro hnv
    cases hb : eval t (fun i => decide (v ≤ x i))
    · rfl
    · exact absurd (h.1 hb) hnv

/-- The minimum of two Booleans is their conjunction. -/
theorem bool_min_eq_and (a b : Bool) : min a b = (a && b) := by
  cases a <;> cases b <;> rfl

/-- The maximum of two Booleans is their disjunction. -/
theorem bool_max_eq_or (a b : Bool) : max a b = (a || b) := by
  cases a <;> cases b <;> rfl

/-- A Boolean minimum node evaluates to `true` exactly when every child evaluates to `true`; see
[CleveGavinskyYongeMallo2007]. -/
theorem bool_eval_node_min (c : Tree) (cs : List Tree) (x : ℕ → Bool) :
    eval (.node .min c cs) x = true ↔ eval c x = true ∧ ∀ d ∈ cs, eval d x = true := by
  rw [← true_le_bool_iff, le_eval_node_min_iff]
  simp only [true_le_bool_iff]

/-- A Boolean maximum node evaluates to `true` exactly when at least one child evaluates to
`true`; see [CleveGavinskyYongeMallo2007]. -/
theorem bool_eval_node_max (c : Tree) (cs : List Tree) (x : ℕ → Bool) :
    eval (.node .max c cs) x = true ↔ eval c x = true ∨ ∃ d ∈ cs, eval d x = true := by
  rw [← true_le_bool_iff, le_eval_node_max_iff]
  simp only [true_le_bool_iff]

/-- Pointwise increasing the input values can only increase the value of a Min-Max tree. -/
theorem eval_mono {α : Type*} [LinearOrder α] (t : Tree) {x y : ℕ → α}
    (hxy : ∀ i, x i ≤ y i) : eval t x ≤ eval t y := by
  refine inductionOnSize (motive := fun t => eval t x ≤ eval t y) t (fun t ih => ?_)
  match t with
  | .leaf i => simpa using hxy i
  | .node g c cs =>
    have hc := ih c (by simp)
    have hd : ∀ d ∈ cs, eval d x ≤ eval d y := fun d hd => ih d (by simp [hd])
    cases g with
    | min =>
      simp only [eval_node, merge_min]
      exact foldr_min_map_mono cs hc hd
    | max =>
      simp only [eval_node, merge_max]
      exact foldr_max_map_mono cs hc hd

/-- The minimum of two elements of a linear order equals one of the two elements. -/
theorem min_eq_left_or_right {α : Type*} [LinearOrder α] (a b : α) :
    min a b = a ∨ min a b = b := by
  rcases le_total a b with h | h
  · exact Or.inl (min_eq_left h)
  · exact Or.inr (min_eq_right h)

/-- The maximum of two elements of a linear order equals one of the two elements. -/
theorem max_eq_left_or_right {α : Type*} [LinearOrder α] (a b : α) :
    max a b = a ∨ max a b = b := by
  rcases le_total a b with h | h
  · exact Or.inr (max_eq_right h)
  · exact Or.inl (max_eq_left h)

/-- A fold of gate operations equals an indexed input whenever its initial value and all folded
child values do. -/
theorem fold_attained {α : Type*} [LinearOrder α] (g : Gate) (x : ℕ → α) :
    ∀ (cs : List Tree) (a : α) (i : ℕ), a = x i →
      (∀ d ∈ cs, ∃ j, eval d x = x j) →
      ∃ k, cs.foldr (fun d acc => merge g (eval d x) acc) a = x k := by
  intro cs
  induction cs with
  | nil => intro a i hi _; exact ⟨i, by simpa using hi⟩
  | cons d ds ih =>
    intro a i hi hd
    rw [List.foldr_cons]
    obtain ⟨j, hj⟩ := hd d (by simp)
    obtain ⟨k, hk⟩ := ih a i hi (fun e he => hd e (by simp [he]))
    cases g with
    | min =>
      simp only [merge_min] at hk ⊢
      rcases min_eq_left_or_right (eval d x)
          (ds.foldr (fun d acc => min (eval d x) acc) a) with h | h
      · exact ⟨j, by rw [h, hj]⟩
      · exact ⟨k, by rw [h, hk]⟩
    | max =>
      simp only [merge_max] at hk ⊢
      rcases max_eq_left_or_right (eval d x)
          (ds.foldr (fun d acc => max (eval d x) acc) a) with h | h
      · exact ⟨j, by rw [h, hj]⟩
      · exact ⟨k, by rw [h, hk]⟩

/-- Every Min-Max tree value equals `x i` for some natural-number input index `i`. -/
theorem exists_leaf_eq_eval {α : Type*} [LinearOrder α] (t : Tree) (x : ℕ → α) :
    ∃ i, eval t x = x i := by
  refine inductionOnSize (motive := fun t => ∃ i, eval t x = x i) t (fun t ih => ?_)
  match t with
  | .leaf i => exact ⟨i, eval_leaf i x⟩
  | .node g c cs =>
    obtain ⟨i, hi⟩ := ih c (by simp)
    have hd : ∀ d ∈ cs, ∃ j, eval d x = x j := fun d hd => ih d (by simp [hd])
    simpa only [eval_node] using fold_attained g x cs (eval c x) i hi hd

end Tree

end Qatlib.Papers.MinMaxTree07.ThresholdTree
