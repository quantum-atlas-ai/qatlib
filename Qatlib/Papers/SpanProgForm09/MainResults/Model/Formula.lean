/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GramQueryCore.LowerBoundTools.ResidualModels

set_option backward.isDefEq.respectTransparency false

/-!
# Formula model for Reichardt, *Span-program-based quantum algorithm for evaluating
unbalanced formulas* (fixed arXiv:0907.1622v1)

This module gives the paper's notion of a formula (Section 1), of the general adversary
bound `Adv±(φ)` of the Boolean function a (sub)formula computes, of the balance parameter
`β` of Definition 1.8, and of the path quantity `σ₋` of Definition 1.10.

The adversary bound is *not* re-axiomatized: `advPlus` is the library's general
adversary bound `Qatlib.Concepts.GramQueryCore.LowerBoundTools.sourceAdversary`
evaluated on the truth table of the formula, i.e. exactly Eq. (2.1) of the paper with
uniform unit costs, read off the concrete function `φ.eval : (I → Bool) → Bool`.

Boundary: a formula is a read-once tree over an arity-indexed gate set `G`; leaves are
labelled by the input-bit type `I`, and a subformula keeps the ambient leaf labels and
reads only the leaves it actually uses. Since `sourceAdversary` ranges over the full
cube `I → Bool`, a subformula that ignores some coordinates has exactly the adversary
of the function on its own leaves (unused coordinates contribute the zero delta
matrix in Eq. (2.1)). Nothing here assumes the paper's later span-program construction;
the statements that consume it live in the `Source*` modules.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgForm09.MainResults

open Matrix
open Qatlib.Concepts.GramQueryCore.LowerBoundTools
open scoped Classical BigOperators ENNReal

/-- A `k`-bit Boolean gate, i.e. a function `{0,1}^k → {0,1}` (Section 1). -/
abbrev Gate (k : ℕ) : Type := (Fin k → Bool) → Bool

/-- A gate set `S`: an arity-indexed family of Boolean gates, each carried with its
evaluation map (Section 1: "a formula over a set of gates S"). Gate *sets* are finite;
finiteness is not needed for the mathematical statements and is recorded where used. -/
structure GateSet where
  /-- The gates of arity `k`. -/
  gate : ℕ → Type
  /-- Evaluation of a gate on `k` Boolean inputs. -/
  eval : (k : ℕ) → gate k → Gate k

/-- A read-once formula over a gate set `G`, with leaves labelled by the input-bit type
`I` (Section 1). Every internal node of arity `k` carries a `k`-bit gate and exactly `k`
children. -/
inductive Formula (I : Type) (G : GateSet) : Type where
  /-- A leaf holding input bit `i`. -/
  | leaf (i : I) : Formula I G
  /-- An internal node carrying the `k`-bit gate `g` and `k` children. -/
  | node (k : ℕ) (g : G.gate k) (children : Fin k → Formula I G) : Formula I G

namespace Formula

variable {I : Type} {G : GateSet}

/-- Number of tree nodes, used as the termination measure of `eval` and `pathSum`. -/
def size : Formula I G → ℕ
  | .leaf _ => 1
  | .node k _ ch => 1 + ∑ j : Fin k, size (ch j)

/-- `size` of a leaf is one, by the defining equation. -/
@[simp] theorem size_leaf (i : I) : (leaf (G := G) i).size = 1 := rfl

/-- `size` of an internal node is one plus the sum of its children's sizes, by the
defining equation. -/
@[simp] theorem size_node (k : ℕ) (g : G.gate k) (ch : Fin k → Formula I G) :
    (node k g ch).size = 1 + ∑ j : Fin k, (ch j).size := rfl

/-- Every child of an internal node has strictly smaller `size` than the node. -/
theorem size_child_lt (k : ℕ) (g : G.gate k) (ch : Fin k → Formula I G) (j : Fin k) :
    (ch j).size < (node k g ch).size := by
  rw [size_node]
  have hle : (ch j).size ≤ ∑ i : Fin k, (ch i).size :=
    Finset.single_le_sum (f := fun i : Fin k => (ch i).size)
      (fun i _ => Nat.zero_le _) (Finset.mem_univ j)
  omega

/-- Evaluation of a formula on the assignment `x`. -/
def eval : (φ : Formula I G) → (I → Bool) → Bool
  | .leaf i, x => x i
  | .node k g ch, x => G.eval k g (fun j => eval (ch j) x)
termination_by φ => φ.size
decreasing_by
  exact size_child_lt k g ch j

/-- Evaluation at a leaf, by the defining equation of `eval`. -/
theorem eval_leaf (i : I) (x : I → Bool) : (leaf (G := G) i).eval x = x i := by
  simp only [eval]

/-- Evaluation at an internal node, by the defining equation of `eval`. -/
theorem eval_node (k : ℕ) (g : G.gate k) (ch : Fin k → Formula I G) (x : I → Bool) :
    (node k g ch).eval x = G.eval k g (fun j => (ch j).eval x) := by
  simp only [eval]

/-- `ψ` is the subformula rooted at some vertex of `φ` (Definition 1.8's `φ_v`). -/
inductive Subformula : Formula I G → Formula I G → Prop where
  | refl (φ : Formula I G) : Subformula φ φ
  | child {k : ℕ} {g : G.gate k} {ch : Fin k → Formula I G} {ψ : Formula I G} (j : Fin k) :
      Subformula ψ (ch j) → Subformula ψ (node k g ch)

/-- The number of leaves of a formula (the paper's `n`, Definition 1.10). -/
def leafCount : Formula I G → ℕ
  | .leaf _ => 1
  | .node k _ ch => ∑ j : Fin k, leafCount (ch j)

/-- A Boolean gate depends on bit `i` if flipping only that bit changes its value. -/
def DependsOnBit {k : ℕ} (g : Gate k) (i : Fin k) : Prop :=
  ∃ y : Fin k → Bool, g y ≠ g (Function.update y i (!(y i)))

/-- The paper's restriction (Lemma 3.2 and the proof of Theorem 1.9) that a gate depends
on at least two input bits. -/
def DependsOnAtLeastTwo {k : ℕ} (g : Gate k) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ DependsOnBit g i ∧ DependsOnBit g j

end Formula

variable {I : Type} [Fintype I] [DecidableEq I] {G : GateSet}

/-- The canonical enumeration of the input-bit type `I` used to present a string
`x : I → Bool` as an element of `{0,1}^n` for `sourceAlphabetDelta`, with the alphabet
`{0,1}` written `Fin 2`. -/
def bitInput (I : Type) [Fintype I] : (I → Bool) → Fin (Fintype.card I) → Fin 2 :=
  fun x j => if x ((Fintype.equivFin I).symm j) then 1 else 0

/-- The inverse presentation of `bitInput`: a string on `Fin (Fintype.card I)` read back
as an assignment on `I`. -/
def decodeBit (I : Type) [Fintype I] : (Fin (Fintype.card I) → Bool) → (I → Bool) :=
  fun x i => x (Fintype.equivFin I i)

/-- `Adv±(φ)`, the general adversary bound of Definition 2.1 / Eq. (2.1) with uniform
unit costs, of the Boolean function `φ.eval`. Real-valued projection of the library's
`sourceAdversary`; the adversary of a total Boolean function on a finite cube is finite,
so `toReal` is faithful here. -/
noncomputable def advPlus (φ : Formula I G) : ℝ :=
  (sourceAdversary (sourceAlphabetDelta (bitInput I)) (fun x => φ.eval x)).toReal

/-- `Adv±(φ)` as an extended nonnegative real, kept for statements that compare it with
`sourceFunctionQ`. -/
noncomputable def advPlusE (φ : Formula I G) : ℝ≥0∞ :=
  sourceAdversary (sourceAlphabetDelta (bitInput I)) (fun x => φ.eval x)

/-- The `max_j` of `Adv±` over the children of an internal node; `0` on a node with no
children (which the paper excludes by assuming every gate has fan-in at least two). -/
noncomputable def childMax (k : ℕ) (ch : Fin k → Formula I G) : ℝ :=
  (List.ofFn (fun j : Fin k => advPlus (ch j))).foldr max 0

/-- `σ₋(φ_v)`: the simple-path sum of Definition 1.10, `max` over simple paths `ξ` from
`v` to a leaf of `∑_{w∈ξ} 1/Adv±(φ_w)`. On the read-once tree this is `1/Adv±` at the
root plus the maximum of the same quantity over the children. -/
noncomputable def pathSum : (φ : Formula I G) → ℝ
  | .leaf i => 1 / advPlus (Formula.leaf (G := G) i)
  | .node k g ch =>
      1 / advPlus (Formula.node (G := G) k g ch) +
        (List.ofFn (fun j : Fin k => pathSum (ch j))).foldr max 0
termination_by φ => φ.size
decreasing_by
  exact Formula.size_child_lt k g ch j

/-- `σ₋(φ)` of Definition 1.10, at the root of `φ`. -/
noncomputable def sigmaMinus (φ : Formula I G) : ℝ := pathSum φ

/-- β-balance of Definition 1.8: at every internal node the general adversary bounds of
the children differ by at most a factor `β`, phrased as `∀ j l, α_j ≤ β α_l`. -/
noncomputable def Balanced (β : ℝ) : (φ : Formula I G) → Prop
  | .leaf _ => True
  | .node k _ ch => (∀ j, Balanced β (ch j)) ∧ ∀ j l : Fin k, advPlus (ch j) ≤ β * advPlus (ch l)
termination_by φ => φ.size
decreasing_by
  exact Formula.size_child_lt k _ ch j

/-- Every gate appearing in the formula depends on at least two input bits. -/
noncomputable def AllGatesDependsOnAtLeastTwo : (φ : Formula I G) → Prop
  | .leaf _ => True
  | .node k g ch => (∀ j, AllGatesDependsOnAtLeastTwo (ch j)) ∧
      Formula.DependsOnAtLeastTwo (G.eval k g)
termination_by φ => φ.size
decreasing_by
  exact Formula.size_child_lt k _ ch j

/-- A formula is *almost balanced* (Definition 1.8): `β`-balanced for a finite `β`. -/
def AlmostBalanced (φ : Formula I G) : Prop := ∃ β : ℝ, 1 ≤ β ∧ Balanced β φ

/-- The two kinds of gate in an AND-OR formula (Theorem 1.11). -/
inductive AndOrKind where
  | and
  | or
deriving DecidableEq

/-- Evaluation of the `k`-bit AND gate and the `k`-bit OR gate. -/
def andOrEval (k : ℕ) (kind : AndOrKind) : Gate k :=
  fun y =>
    match kind with
    | .and => decide (∀ j : Fin k, y j = true)
    | .or => decide (∃ j : Fin k, y j = true)

/-- The AND/OR gate set of every arity (Theorem 1.11). -/
def andOrGates : GateSet where
  gate _ := AndOrKind
  eval k kind := andOrEval k kind

end Qatlib.Papers.SpanProgForm09.MainResults
