/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GateVocabulary.LocalReflectionGates
import Lean.Elab.Tactic.Omega

/-!
# Boolean graphs and reversible gate-list data

This module defines `BooleanNode` and `BooleanDAG`, their Boolean evaluation, and their
compilation into local reflection gates. `booleanDAGSteps` computes graph values, copies
selected bits into an output register by XOR, and reverses the computation.

The register layouts and state embedding support reversible computation in the circuit model
described in [NielsenChuang2010].

## Main statements

* `booleanDAGValue`: evaluates all input and graph coordinates.
* `booleanDAGSteps`: constructs the compute-copy-uncompute gate list.
* `booleanDAGEmbed`: inserts clean graph workspace into a state.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.GateVocabulary.LocalReflectionGates

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open scoped Classical BigOperators
set_option autoImplicit false

/-- A Boolean operation using n available source coordinates: a constant, negation, XOR, or
conjunction. -/
inductive BooleanNode (n : ℕ) where
  | constant (b : Bool)
  | neg (a : Fin n)
  | xor (a b : Fin n)
  | conj (a b : Fin n)

/-- Evaluates a Boolean node on the supplied source register. -/
def booleanNodeValue {n : ℕ} : BooleanNode n → Reg n → Bool
  | .constant b, _ => b
  | .neg a, x => !(x a)
  | .xor a b, x => x a ^^ x b
  | .conj a b, x => x a && x b

/-- The local gate list that XORs a node's Boolean value into wire n of a larger register. -/
noncomputable def booleanNodeSteps {n L : ℕ} (node : BooleanNode n)
    (h : n < L) : List (ReflectionGate L) :=
  let src : Fin n → Fin L := Fin.castLE h.le
  let t : Fin L := ⟨n,h⟩
  match node with
  | .constant false => []
  | .constant true => [.inl (t,PauliX)]
  | .neg a => [.inr (src a,t),.inl (t,PauliX)]
  | .xor a b => [.inr (src a,t),.inr (src b,t)]
  | .conj a b => if a=b then [.inr (src a,t)] else toffoliLocalSteps (src a) (src b) t

/-- A Boolean directed acyclic graph with m inputs and a specified number of sequentially
appended nodes, each referencing only available coordinates. -/
inductive BooleanDAG (m : ℕ) : ℕ → Type where
  | nil : BooleanDAG m 0
  | snoc {n : ℕ} (previous : BooleanDAG m n) (node : BooleanNode (m+n)) :
      BooleanDAG m (n+1)

/-- Evaluates a Boolean graph, returning its input bits followed by every computed node value. -/
def booleanDAGValue {m : ℕ} : {n : ℕ} → BooleanDAG m n → Reg m → Reg (m+n)
  | _, .nil, x => x
  | _, .snoc g node, x =>
    let e := booleanDAGValue g x
    Fin.lastCases (booleanNodeValue node e) e

/-- Compiles the forward graph evaluation into a sufficiently large physical register. -/
noncomputable def booleanDAGComputeInto {m L : ℕ} :
    {n : ℕ} → BooleanDAG m n → (m+n ≤ L) → List (ReflectionGate L)
  | _, .nil, _ => []
  | _, .snoc g node, h =>
    booleanDAGComputeInto g (by omega) ++ booleanNodeSteps node (by omega)

/-- Compiles the forward graph evaluation with room for an additional output register. -/
noncomputable def booleanDAGCompute {m n : ℕ} (g : BooleanDAG m n) (o : ℕ) :
    List (ReflectionGate (m+n+o)) :=
  booleanDAGComputeInto g (by omega)

/-- The CNOT list XORing selected input or graph coordinates into the output register. -/
noncomputable def booleanDAGCopy (m n o : ℕ) (out : Fin o → Fin (m+n)) :
    List (ReflectionGate (m+n+o)) :=
  (List.finRange o).map fun j => .inr
    (Fin.castLE (by omega) (out j),⟨m+n+j.val,by omega⟩)

/-- The compute-copy-uncompute gate list for XORing selected graph values into the output
register. -/
noncomputable def booleanDAGSteps {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) : List (ReflectionGate (m+n+o)) :=
  booleanDAGCompute g o ++ booleanDAGCopy m n o out ++ reflectionAdjoint (booleanDAGCompute g o)

/-- The basis register consisting of input bits, false work bits, and the supplied output bits. -/
def booleanDAGInput (m n o : ℕ) (x : Reg m) (y : Reg o) : Reg (m+n+o) := fun i =>
  if hx : i.val < m then x ⟨i.val,hx⟩
  else if hw : i.val < m+n then false
  else y ⟨i.val-(m+n),by omega⟩

/-- The basis register consisting of evaluated input and graph values followed by the supplied
output bits. -/
def booleanDAGComputed {m n : ℕ} (g : BooleanDAG m n) (o : ℕ)
    (x : Reg m) (y : Reg o) : Reg (m+n+o) := fun i =>
  if hi : i.val < m+n then booleanDAGValue g x ⟨i.val,hi⟩
  else y ⟨i.val-(m+n),by omega⟩

/-- The output word formed by XORing selected evaluated graph values with the original output
bits. -/
def booleanDAGOutput {m n o : ℕ} (g : BooleanDAG m n)
    (out : Fin o → Fin (m+n)) (x : Reg m) (y : Reg o) : Reg o :=
  fun j => y j ^^ booleanDAGValue g x (out j)

/-- Embeds an arbitrary input-output state into the physical register with every graph work bit
initialized to false. -/
noncomputable def booleanDAGEmbed (m n o : ℕ) (ψ : QState (Reg m × Reg o)) :
    QState (Reg (m+n+o)) :=
  ∑ xy, ψ xy • Ket (booleanDAGInput m n o xy.1 xy.2)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
