/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSpliceData

/-!
# Boolean DAG constructions for unsigned multiplication

`BooleanDAGWord` packages a graph, output wires, and a distinguished wire for zero.
`booleanWordMulRound` forms a controlled partial product, shifts it, and appends an adder to the
accumulated word.

`booleanWordMulProgram` performs all rounds, and `booleanWordMulResult` evaluates its width
`2*w` output on a pair of input words. The circuit background is described in
[KitaevShenVyalyi2002].

## Main statements

* `BooleanDAGWord`: graph and word-output data.
* `booleanWordAndPrefix`, `booleanWordAndDAG`: bitwise masking by a common control.
* `booleanWordMulPrefix`, `booleanWordMulProgram`: shift-and-add multiplication graphs.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- A word-valued Boolean graph with its node count, selected output wires, and a distinguished
wire intended to represent zero. -/
structure BooleanDAGWord (m w : ℕ) where
  nodes : ℕ
  graph : BooleanDAG m nodes
  output : Fin w → Fin (m+nodes)
  zero : Fin (m+nodes)

/-- Build the first `n` conjunctions of a width `w` word with the final common control input. -/
def booleanWordAndPrefix (w : ℕ) : (n : ℕ) → n ≤ w → BooleanDAG (w+1) n
  | 0, _ => .nil
  | n+1, hn =>
    (booleanWordAndPrefix w n (by omega)).snoc
      (.conj ⟨n,by omega⟩ ⟨w,by omega⟩)

/-- Build the graph masking every bit of a width `w` word by one common control bit. -/
def booleanWordAndDAG (w : ℕ) : BooleanDAG (w+1) w :=
  booleanWordAndPrefix w w (Nat.le_refl w)

/-- Initialize multiplication with one false node, selecting it for every accumulator bit and
for the zero wire. -/
def booleanWordMulStart (w : ℕ) : BooleanDAGWord (2*w) w where
  nodes := 1
  graph := .snoc .nil (.constant false)
  output := fun _ => ⟨2*w,by omega⟩
  zero := ⟨2*w,by omega⟩

/-- Append the partial product controlled by bit `i` of the second operand, shift it by `i`
positions, and add it to the accumulator. -/
def booleanWordMulRound (w i : ℕ) (hi : i < w)
    (p : BooleanDAGWord (2*w) (w+i)) : BooleanDAGWord (2*w) (w+i+1) :=
  let inputMap : Fin (w+1) → Fin (2*w+p.nodes) := fun j =>
    if hj : j.val < w then ⟨j.val,by omega⟩ else ⟨w+i,by omega⟩
  let g := booleanDAGSplice p.graph inputMap (booleanWordAndDAG w)
  let left : Fin (w+i) → Fin (2*w+(p.nodes+w)) :=
    fun j => Fin.castLE (by omega) (p.output j)
  let right : Fin (w+i) → Fin (2*w+(p.nodes+w)) := fun j =>
    if hj : j.val < i then Fin.castLE (by omega) p.zero
    else ⟨2*w+p.nodes+(j.val-i),by have := j.isLt; omega⟩
  ⟨p.nodes+w+(5*(w+i)+1), booleanDAGAppendAdder g (w+i) left right,
    booleanDAGAppendAdderSelect (w+i) left right, Fin.castLE (by omega) p.zero⟩

/-- Build the shift-and-add multiplication graph after processing the first `i` bits of the
second operand. -/
def booleanWordMulPrefix (w : ℕ) : (i : ℕ) → i ≤ w → BooleanDAGWord (2*w) (w+i)
  | 0, _ => booleanWordMulStart w
  | i+1, hi =>
    booleanWordMulRound w i (by omega) (booleanWordMulPrefix w i (by omega))

/-- Build the full unsigned multiplication graph, with a width `w+w` output word. -/
def booleanWordMulProgram (w : ℕ) : BooleanDAGWord (2*w) (w+w) :=
  booleanWordMulPrefix w w (Nat.le_refl w)

/-- Select the width `2*w` product wires from the completed multiplication graph. -/
def booleanWordMulSelect (w : ℕ) :
    Fin (2*w) → Fin (2*w+(booleanWordMulProgram w).nodes) :=
  fun j => (booleanWordMulProgram w).output ⟨j.val,by have := j.isLt; omega⟩

/-- Evaluate the selected product word on two packed unsigned width `w` operands. -/
def booleanWordMulResult (w : ℕ) (a b : Reg w) : Reg (2*w) := fun j =>
  booleanDAGValue (booleanWordMulProgram w).graph (booleanWordAdderInput w a b)
    (booleanWordMulSelect w j)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
