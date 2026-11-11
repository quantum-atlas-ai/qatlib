/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QueryModelComparisonDefs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# ReadManyQry11 — source model

Fixed paper: Childs, Kimmel and Kothari, *The quantum query complexity of read-many
formulas*, arXiv:1112.0548v1 (2 December 2011).  The asset copy
`prove/assets/1112.0548.pdf` (text
`prove/assets/1112.0548.txt`) was used; all
page/line references below are to that v1 PDF.

This module owns the paper-layer objects used by every claim in
`QuantumAlgorithmDev.Papers.ReadManyQry11.MainResults`:

* `Formula n` — the paper's read-many formulas (Section 1, pp. 1–3 and Section 2,
  p. 4): a rooted tree of `not` gates and unbounded-fanin `and`/`or` gates, with
  the paper's restriction that every `and`/`or` gate has fan-in at least two
  (`and a b rest` has fan-in `2 + rest.length`).  Leaves are input indices
  `Fin n`, and one index may occur many times (read-many).  `size` is the paper's
  formula size `S` (inputs counted with multiplicity), `gateCount` is the paper's
  gate count `G` (only `and`/`or` are counted, p. 2), and `depth` is the length of
  a longest root-to-leaf path.
* `Circuit n` — the paper's circuits (Section 1, p. 3): a topologically ordered
  list of `and`/`or`/`not` gates over DAG wires, i.e. fan-out is allowed for
  gates and inputs.  `gateCount` is the circuit size (only `and`/`or` gates,
  p. 3), `depth` is the longest input-to-output path, `IsFormula` says no gate
  has fan-out, and `IsMonotone` says there is no `not` gate.
* Bounded-error quantum query complexity, expressed over the frozen concrete
  model of legal query programs `QuantumAlgorithm.Concepts.QueryComplexity.
  DegreeMethod.DecisionProgram` (a counted bit-oracle circuit, its initial
  state and its acceptance set).  `BoundedErrorQueryAtMost f b` means some legal
  program decides `f` with error at most `1/3` using at most `b` queries;
  `BoundedErrorQueryLowerBound f b` means every legal program deciding `f` with
  error at most `1/3` pays at least `b` queries.  These are the paper's
  `Q(f) ≤ b` and `Q(f) ≥ b` statements (bounded error `1/3`, p. 2).
* `min3` is the paper's `min{n, √S, n^{1/2}G^{1/4}}`.

Everything is a definition; the claim theorems live in the sibling files.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Real

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.QueryWordCore.Circuit

namespace Qatlib.Papers.ReadManyQry11.MainResults

/-! ## §1. Read-many formulas (Section 1, pp. 1–3; Section 2, p. 4) -/

/-- A Boolean formula on `n` numbered inputs in the paper's gate set
`{and, or, not}`.  `and k hk f` / `or k hk f` are `and`/`or` gates of fan-in
`k ≥ 2` over the child formulas `f : Fin k → Formula n` (the paper's unbounded
fan-in, p. 1).  Leaves read an input bit; the same index may occur many times,
which is exactly the paper's read-many setting. -/
inductive Formula (n : ℕ) where
  | leaf : Fin n → Formula n
  | not : Formula n → Formula n
  | and : (k : ℕ) → 2 ≤ k → (Fin k → Formula n) → Formula n
  | or : (k : ℕ) → 2 ≤ k → (Fin k → Formula n) → Formula n

namespace Formula

variable {n : ℕ}

/-- Evaluate a formula on a Boolean input. -/
def eval : Formula n → (Fin n → Bool) → Bool
  | leaf i, x => x i
  | not a, x => !(a.eval x)
  | and k _ f, x => (List.finRange k).all (fun i => (f i).eval x)
  | or k _ f, x => (List.finRange k).any (fun i => (f i).eval x)

/-- Formula size `S` (p. 2): the number of inputs counted with multiplicity. -/
def size : Formula n → ℕ
  | leaf _ => 1
  | not a => a.size
  | and k _ f => ∑ i : Fin k, (f i).size
  | or k _ f => ∑ i : Fin k, (f i).size

/-- Gate count `G` (p. 2): the number of `and` and `or` gates; `not` gates are
not counted. -/
def gateCount : Formula n → ℕ
  | leaf _ => 0
  | not a => a.gateCount
  | and k _ f => 1 + ∑ i : Fin k, (f i).gateCount
  | or k _ f => 1 + ∑ i : Fin k, (f i).gateCount

/-- Longest root-to-leaf path length (`depth` in the paper, p. 3). -/
def depth : Formula n → ℕ
  | leaf _ => 0
  | not a => a.depth + 1
  | and k _ f => 1 + (List.finRange k).foldr (fun i m => max (f i).depth m) 0
  | or k _ f => 1 + (List.finRange k).foldr (fun i m => max (f i).depth m) 0

/-- The input indices occurring at the leaves, left to right. -/
def leafLabels : Formula n → List (Fin n)
  | leaf i => [i]
  | not a => a.leafLabels
  | and k _ f => (List.finRange k).flatMap (fun i => (f i).leafLabels)
  | or k _ f => (List.finRange k).flatMap (fun i => (f i).leafLabels)

/-- A formula is read-once when each input index appears at most once. -/
def IsReadOnce (φ : Formula n) : Prop := φ.leafLabels.Nodup

/-- A formula is monotone when it has no `not` gate. -/
def IsMonotone : Formula n → Prop
  | leaf _ => True
  | not _ => False
  | and _ _ f => ∀ i, (f i).IsMonotone
  | or _ _ f => ∀ i, (f i).IsMonotone

/-- The size leaf property in the paper model. -/
@[simp] theorem size_leaf (i : Fin n) : (leaf i).size = 1 := rfl

/-- The size not property in the paper model. -/
@[simp] theorem size_not (a : Formula n) : (not a).size = a.size := rfl

/-- The size and property in the paper model. -/
@[simp] theorem size_and (k : ℕ) (hk : 2 ≤ k) (f : Fin k → Formula n) :
    (and k hk f).size = ∑ i : Fin k, (f i).size := rfl

/-- The size or property in the paper model. -/
@[simp] theorem size_or (k : ℕ) (hk : 2 ≤ k) (f : Fin k → Formula n) :
    (or k hk f).size = ∑ i : Fin k, (f i).size := rfl

/-- The gate Count leaf property in the paper model. -/
@[simp] theorem gateCount_leaf (i : Fin n) : (leaf i).gateCount = 0 := rfl

/-- The gate Count not property in the paper model. -/
@[simp] theorem gateCount_not (a : Formula n) : (not a).gateCount = a.gateCount := rfl

/-- The gate Count and property in the paper model. -/
@[simp] theorem gateCount_and (k : ℕ) (hk : 2 ≤ k) (f : Fin k → Formula n) :
    (and k hk f).gateCount = 1 + ∑ i : Fin k, (f i).gateCount := rfl

/-- The gate Count or property in the paper model. -/
@[simp] theorem gateCount_or (k : ℕ) (hk : 2 ≤ k) (f : Fin k → Formula n) :
    (or k hk f).gateCount = 1 + ∑ i : Fin k, (f i).gateCount := rfl

/-- The depth leaf property in the paper model. -/
@[simp] theorem depth_leaf (i : Fin n) : (leaf i).depth = 0 := rfl

/-- The eval leaf property in the paper model. -/
@[simp] theorem eval_leaf (i : Fin n) (x : Fin n → Bool) : (leaf i).eval x = x i := rfl

/-- The eval not property in the paper model. -/
@[simp] theorem eval_not (a : Formula n) (x : Fin n → Bool) : (not a).eval x = !(a.eval x) := rfl

/-- The eval and property in the paper model. -/
@[simp] theorem eval_and (k : ℕ) (hk : 2 ≤ k) (f : Fin k → Formula n) (x : Fin n → Bool) :
    (and k hk f).eval x = (List.finRange k).all (fun i => (f i).eval x) := rfl

/-- The eval or property in the paper model. -/
@[simp] theorem eval_or (k : ℕ) (hk : 2 ≤ k) (f : Fin k → Formula n) (x : Fin n → Bool) :
    (or k hk f).eval x = (List.finRange k).any (fun i => (f i).eval x) := rfl

/-- Formula size is positive. -/
theorem size_pos : ∀ φ : Formula n, 0 < φ.size
  | leaf _ => by simp
  | not a => by simpa using size_pos a
  | and k hk f => by
      have hk' : 0 < k := by omega
      simp only [size]
      exact Finset.sum_pos (fun i _ => size_pos (f i))
        ⟨⟨0, hk'⟩, Finset.mem_univ _⟩
  | or k hk f => by
      have hk' : 0 < k := by omega
      simp only [size]
      exact Finset.sum_pos (fun i _ => size_pos (f i))
        ⟨⟨0, hk'⟩, Finset.mem_univ _⟩

/-- Every formula with at least one gate has size at least two (a gate has
fan-in at least two and every subformula has positive size). -/
theorem size_ge_two_of_gateCount_pos (φ : Formula n) (h : 0 < φ.gateCount) :
    2 ≤ φ.size := by
  induction φ with
  | leaf i => simp at h
  | not a ih =>
      have h' : 0 < a.gateCount := by simpa using h
      have := ih h'
      simpa using this
  | and k hk f ih =>
      have hk2 : 2 ≤ k := hk
      simp only [size]
      -- each child has positive size
      have : ∀ i : Fin k, 1 ≤ (f i).size := fun i => size_pos (f i)
      have hsum : k ≤ ∑ i : Fin k, (f i).size := by
        have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => this i)
        simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
      omega
  | or k hk f ih =>
      have hk2 : 2 ≤ k := hk
      simp only [size]
      have : ∀ i : Fin k, 1 ≤ (f i).size := fun i => size_pos (f i)
      have hsum : k ≤ ∑ i : Fin k, (f i).size := by
        have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => this i)
        simpa [Finset.sum_const, Finset.card_univ, Fintype.card_fin] using this
      omega

/-- The paper's basic fact `G < S` (p. 2), under the paper's convention that all
`and`/`or` gates have fan-in at least two. -/
theorem gateCount_lt_size : ∀ φ : Formula n, φ.gateCount < φ.size
  | leaf _ => by simp
  | not a => by simpa using gateCount_lt_size a
  | and k hk f => by
      have hchild : ∀ i : Fin k, (f i).gateCount + 1 ≤ (f i).size :=
        fun i => by have := gateCount_lt_size (f i); omega
      have hsum : ∑ i : Fin k, ((f i).gateCount + 1) ≤ ∑ i : Fin k, (f i).size :=
        Finset.sum_le_sum (fun i _ => hchild i)
      have hsplit : ∑ i : Fin k, ((f i).gateCount + 1) =
          (∑ i : Fin k, (f i).gateCount) + k := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [gateCount_and, size_and]
      omega
  | or k hk f => by
      have hchild : ∀ i : Fin k, (f i).gateCount + 1 ≤ (f i).size :=
        fun i => by have := gateCount_lt_size (f i); omega
      have hsum : ∑ i : Fin k, ((f i).gateCount + 1) ≤ ∑ i : Fin k, (f i).size :=
        Finset.sum_le_sum (fun i _ => hchild i)
      have hsplit : ∑ i : Fin k, ((f i).gateCount + 1) =
          (∑ i : Fin k, (f i).gateCount) + k := by
        rw [Finset.sum_add_distrib]
        simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [gateCount_or, size_or]
      omega

end Formula

/-! ## §2. Circuits (Section 1, p. 3; Section 3.1, p. 6) -/

/-- Gate kinds of the paper: `and`, `or`, `not`. -/
inductive GateOp
  | and
  | or
  | not
  deriving DecidableEq

/-- A gate reads a list of wires: input wires (`inl i`) or output wires of
earlier gates (`inr j`). -/
structure Gate (n : ℕ) where
  op : GateOp
  args : List (Fin n ⊕ ℕ)

/-- A gate is well-formed at position `i` when every gate wire it reads refers to
an earlier gate. -/
def Gate.WfAt {n : ℕ} (i : ℕ) (g : Gate n) : Prop :=
  ∀ a ∈ g.args, ∀ j, a = Sum.inr j → j < i

/-- A Boolean circuit on `n` inputs in the paper's DAG model: a topologically
ordered gate list plus an output wire.  Fan-out is allowed. -/
structure Circuit (n : ℕ) where
  gates : List (Gate n)
  out : Fin n ⊕ ℕ
  wf : ∀ (i : Fin gates.length), (gates.get i).WfAt i
  out_wf : ∀ j, out = Sum.inr j → j < gates.length

namespace Circuit

variable {n : ℕ}

/-- Values of a wire list, given the already computed gate values. -/
def evalArgs (x : Fin n → Bool) (acc : List Bool) : List (Fin n ⊕ ℕ) → List Bool
  | [] => []
  | Sum.inl i :: rest => x i :: evalArgs x acc rest
  | Sum.inr j :: rest => acc.getD j false :: evalArgs x acc rest

/-- Evaluate one gate from the values of the earlier gates. -/
def evalGate (x : Fin n → Bool) (acc : List Bool) (g : Gate n) : Bool :=
  match g.op with
  | GateOp.and => (evalArgs x acc g.args).all id
  | GateOp.or => (evalArgs x acc g.args).any id
  | GateOp.not => !((evalArgs x acc g.args).headD false)

/-- Evaluate the gate list left to right, appending each computed value. -/
def evalAux (x : Fin n → Bool) : List Bool → List (Gate n) → List Bool
  | acc, [] => acc
  | acc, g :: gs => evalAux x (acc ++ [evalGate x acc g]) gs

/-- Values of all gates, in order. -/
def evalAll (x : Fin n → Bool) (C : Circuit n) : List Bool := evalAux x [] C.gates

/-- Evaluate the circuit. -/
def eval (C : Circuit n) (x : Fin n → Bool) : Bool :=
  match C.out with
  | Sum.inl i => x i
  | Sum.inr j => (evalAll x C).getD j false

/-- Circuit size (p. 3): the number of `and` and `or` gates; `not` gates are not
counted. -/
def gateCount (C : Circuit n) : ℕ :=
  (C.gates.filter (fun g => g.op != GateOp.not)).length

/-- Depths of a wire list (`0` for an input wire, the gate's depth otherwise). -/
def depthArgs (acc : List ℕ) : List (Fin n ⊕ ℕ) → List ℕ
  | [] => []
  | Sum.inl _ :: rest => 0 :: depthArgs acc rest
  | Sum.inr j :: rest => acc.getD j 0 :: depthArgs acc rest

/-- Depth of one gate: one plus the maximum depth of its inputs. -/
def depthGate (acc : List ℕ) (g : Gate n) : ℕ :=
  1 + (depthArgs acc g.args).foldr max 0

/-- Depths of the gates, in order. -/
def depthAux : List ℕ → List (Gate n) → List ℕ
  | acc, [] => acc
  | acc, g :: gs => depthAux (acc ++ [depthGate acc g]) gs

/-- Circuit depth (p. 3): the length of a longest input-to-output path. -/
def depth (C : Circuit n) : ℕ :=
  match C.out with
  | Sum.inl _ => 0
  | Sum.inr j => (depthAux [] C.gates).getD j 0

/-- Number of wires (gate outputs and the circuit output) that read gate `j`. -/
def gateFanoutAt (C : Circuit n) (j : ℕ) : ℕ :=
  (C.gates.flatMap (fun g => g.args)).count (Sum.inr j) +
    (if C.out = Sum.inr j then 1 else 0)

/-- No gate has fan-out: the circuit is a formula (inputs may still fan out, as
in the paper's "general formula", p. 3). -/
def IsFormula (C : Circuit n) : Prop := ∀ j, C.gateFanoutAt j ≤ 1

/-- The circuit has no `not` gate. -/
def IsMonotone (C : Circuit n) : Prop := ∀ g ∈ C.gates, g.op ≠ GateOp.not

/-- The circuit's output is a gate of the prescribed kind. -/
def TopGateIs (C : Circuit n) (op : GateOp) : Prop :=
  ∃ j, ∃ h : j < C.gates.length, C.out = Sum.inr j ∧ (C.gates.get ⟨j, h⟩).op = op

end Circuit

/-! ## §3. Bounded-error quantum query complexity

The frozen `DecisionProgram` model is the paper's black-box query model: a
counted bit-oracle circuit, an initial state, and an acceptance event.  The
paper's `Q(f)` (bounded error `1/3`, p. 2) is expressed through the two
predicates below, exactly as `Q(f) ≤ b` and `Q(f) ≥ b`. -/

/-- A bounded-error upper bound: some legal query program decides `f` with error
at most `1/3` and uses at most `b` queries. -/
def BoundedErrorQueryAtMostAux (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (f : (Fin n → Bool) → Bool) (b : ℝ) : Prop :=
  ∃ P : DecisionProgram (Fin n) W, P.BoundedFor f ∧ (QueryCount P.circuit : ℝ) ≤ b

/-- `Q(f) ≤ b` for the paper's bounded-error query complexity. -/
def BoundedErrorQueryAtMost {n : ℕ} (f : (Fin n → Bool) → Bool) (b : ℝ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W),
    BoundedErrorQueryAtMostAux n W f b

/-- A bounded-error lower bound on a fixed workspace `W`. -/
def BoundedErrorQueryLowerBoundAux (n : ℕ) (W : Type) [Fintype W] [DecidableEq W]
    (f : (Fin n → Bool) → Bool) (b : ℝ) : Prop :=
  ∀ P : DecisionProgram (Fin n) W, P.BoundedFor f → b ≤ (QueryCount P.circuit : ℝ)

/-- `Q(f) ≥ b` for the paper's bounded-error query complexity: every legal
program for `f` on any workspace pays at least `b` queries. -/
def BoundedErrorQueryLowerBound {n : ℕ} (f : (Fin n → Bool) → Bool) (b : ℝ) : Prop :=
  ∀ (W : Type) (_ : Fintype W) (_ : DecidableEq W),
    BoundedErrorQueryLowerBoundAux n W f b

/-- Query-upper-bound transfer `Q(f) ≤ Q(g)`: every bounded-error algorithm for
`g` converts to one for `f` with no additional queries.  This is the paper's
meaning of `Q(f) ≤ Q(f′)` in Lemma 3, p. 6. -/
def QueryReduction {n m : ℕ} (g : (Fin m → Bool) → Bool) (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ b : ℝ, BoundedErrorQueryAtMost g b → BoundedErrorQueryAtMost f b

/-- The paper's `min{n, √S, n^{1/2}G^{1/4}}`. -/
def min3 (a b c : ℝ) : ℝ := min a (min b c)

/-- The paper's `n^{1/2}G^{1/4}` (with real powers). -/
def pruningBound (n G : ℕ) : ℝ := (n : ℝ) ^ ((1 : ℝ) / 2) * (G : ℝ) ^ ((1 : ℝ) / 4)

/-- Shorthand for the paper's three-term bound at parameters `n`, `S`, `G`. -/
def mainBound (n S G : ℕ) : ℝ :=
  min3 (n : ℝ) (Real.sqrt (S : ℝ)) (pruningBound n G)

end Qatlib.Papers.ReadManyQry11.MainResults
