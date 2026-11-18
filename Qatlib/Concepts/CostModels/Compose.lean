/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CostModels.Profile

@[expose] public section

/-! # Recursion consumption for cost profiles

`CostTree` is an abstract composition skeleton whose leaves carry measured
profiles; `treeCost` folds it with `serial` and `par`. The theorems here
derive the cost of a composite structure purely from its component costs —
the algebra-level reading of "`c ++ d` costs the sum of its parts" — without
any circuit representation. This is the interface that recursive resource
analyses (for example prime-factor cost recurrences) consume.
-/

set_option autoImplicit false

namespace Qatlib.Concepts.CostModels.Compose

open Qatlib.Concepts.CostModels.Profile

/-- Abstract costed composition: a leaf carries a measured profile, `app` runs
the left tree and then the right tree (serial), and `fork` runs both trees on
disjoint wires (independent parallel). -/
inductive CostTree where
  /-- A segment with its measured cost profile. -/
  | leaf : CostProfile → CostTree
  /-- Serial composition: run the left tree, then the right tree. -/
  | app : CostTree → CostTree → CostTree
  /-- Independent-parallel composition on disjoint wires. -/
  | fork : CostTree → CostTree → CostTree

/-- The measured cost profile of a costed composition, folded with `serial`
and `par`. -/
def treeCost : CostTree → CostProfile
  | .leaf p => p
  | .app t u => serial (treeCost t) (treeCost u)
  | .fork t u => par (treeCost t) (treeCost u)

/-- The cost of a serial composition is derived from the two component
costs. -/
theorem costAppend (t u : CostTree) :
    treeCost (.app t u) = serial (treeCost t) (treeCost u) := rfl

/-- The cost of an independent-parallel composition is derived from the two
component costs. -/
theorem costFork (t u : CostTree) :
    treeCost (.fork t u) = par (treeCost t) (treeCost u) := rfl

/-- Serial repetition of one segment `k` times; zero repetitions is the empty
segment. -/
def treeRepeat (p : CostProfile) : ℕ → CostTree
  | 0 => .leaf emptyProfile
  | k + 1 => .app (.leaf p) (treeRepeat p k)

/-- Repeating a segment with `a` queries `k` times costs `a * k` queries. -/
theorem repeatQueryMul {p : CostProfile} {a : ℕ} (ha : p.queries = some a)
    (k : ℕ) : (treeCost (treeRepeat p k)).queries = some (a * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : (treeCost (treeRepeat p (k + 1))).queries
        = optAdd p.queries (treeCost (treeRepeat p k)).queries := rfl
    rw [h, ha, ih]
    show some (a + a * k) = some (a * (k + 1))
    rw [Nat.mul_succ, Nat.add_comm]

/-- Repeating a segment with `g` macro gates `k` times costs `g * k` macro
gates. -/
theorem repeatMacroMul {p : CostProfile} {g : ℕ} (hg : p.macroGates = some g)
    (k : ℕ) : (treeCost (treeRepeat p k)).macroGates = some (g * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : (treeCost (treeRepeat p (k + 1))).macroGates
        = optAdd p.macroGates (treeCost (treeRepeat p k)).macroGates := rfl
    rw [h, hg, ih]
    show some (g + g * k) = some (g * (k + 1))
    rw [Nat.mul_succ, Nat.add_comm]

/-- Repeating a segment of depth `e` `k` times costs depth `e * k`: serial
depths add. -/
theorem repeatDepthMul {p : CostProfile} {e : ℕ} (he : p.depth = some e)
    (k : ℕ) : (treeCost (treeRepeat p k)).depth = some (e * k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h : (treeCost (treeRepeat p (k + 1))).depth
        = optAdd p.depth (treeCost (treeRepeat p k)).depth := rfl
    rw [h, he, ih]
    show some (e + e * k) = some (e * (k + 1))
    rw [Nat.mul_succ, Nat.add_comm]

/-- Serial repetition leaves width undetermined for every nonempty
repetition: each serial step discards width. Zero repetitions is the empty
segment, whose width is the genuine measured zero `some 0`. -/
theorem repeatWidthNone (p : CostProfile) (k : ℕ) :
    (treeCost (treeRepeat p (k + 1))).width = none := rfl

/-- The serial composition of a list of segments; the empty list is the empty
segment. -/
def treeOfList : List CostProfile → CostTree
  | [] => .leaf emptyProfile
  | p :: ps => .app (.leaf p) (treeOfList ps)

/-- The query cost of a serially composed list is the fold of the segment
query costs: the cost of `c₁ ++ … ++ cₖ` is derived from the component costs
alone, with unmodeled counts absorbing. -/
theorem listQueryFold (ps : List CostProfile) :
    (treeCost (treeOfList ps)).queries
      = (ps.map CostProfile.queries).foldr optAdd (some 0) := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have h : (treeCost (treeOfList (p :: ps))).queries
        = optAdd p.queries (treeCost (treeOfList ps)).queries := rfl
    rw [h, ih, List.map_cons, List.foldr_cons]

end Qatlib.Concepts.CostModels.Compose
