/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdderData

/-!
# Source renaming and Boolean DAG splicing

`booleanNodeRename` changes source indices without changing a node operation. `booleanDAGSplice`
appends a graph whose inputs are mapped to wires of an existing graph; `booleanSpliceSource`
tracks both mapped inputs and newly appended nodes.

`booleanDAGAppendAdder` specializes this construction to two selected word operands, with
`booleanDAGAppendAdderSelect` identifying the sum output wires. The circuit background is
described in [KitaevShenVyalyi2002].

## Main statements

* `booleanNodeRename`, `booleanSpliceSource`: source-index transformations.
* `booleanDAGSplice`: graph composition by a source map.
* `booleanDAGAppendAdder`, `booleanDAGAppendAdderSelect`: appended word adder.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- Rename every source index of a Boolean node while preserving its constant, negation, XOR, or
conjunction operation. -/
def booleanNodeRename {n k : ℕ} (r : Fin n → Fin k) : BooleanNode n → BooleanNode k
  | .constant b => .constant b
  | .neg a => .neg (r a)
  | .xor a b => .xor (r a) (r b)
  | .conj a b => .conj (r a) (r b)

/-- Map an appended graph's inputs through `r` and place its node wires after the existing
graph's nodes. -/
def booleanSpliceSource {M K m n : ℕ} (r : Fin m → Fin (M+K))
    (i : Fin (m+n)) : Fin (M+(K+n)) :=
  if h : i.val < m then Fin.castLE (by omega) (r ⟨i.val,h⟩)
  else ⟨M+K+(i.val-m),by have := i.isLt; omega⟩

/-- Append a Boolean graph to an existing graph by renaming its inputs and node sources
according to the splicing source map. -/
def booleanDAGSplice {M K m : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) : {n : ℕ} → BooleanDAG m n → BooleanDAG M (K+n)
  | _, .nil => g
  | _, .snoc h node =>
    (booleanDAGSplice g r h).snoc (booleanNodeRename (booleanSpliceSource r) node)

/-- Append a width `w` unsigned adder whose operands are selected wires of the existing graph. -/
def booleanDAGAppendAdder {M K : ℕ} (g : BooleanDAG M K) (w : ℕ)
    (a b : Fin w → Fin (M+K)) : BooleanDAG M (K+(5*w+1)) :=
  booleanDAGSplice g (fun i : Fin (2*w) =>
    if hi : i.val < w then a ⟨i.val,hi⟩ else b ⟨i.val-w,by omega⟩)
    (booleanWordAdderDAG w)

/-- Select the width `w+1` sum and carry output wires of the appended unsigned adder. -/
def booleanDAGAppendAdderSelect {M K : ℕ} (w : ℕ)
    (a b : Fin w → Fin (M+K)) : Fin (w+1) → Fin (M+(K+(5*w+1))) :=
  fun j => booleanSpliceSource (fun i : Fin (2*w) =>
    if hi : i.val < w then a ⟨i.val,hi⟩ else b ⟨i.val-w,by omega⟩)
    (booleanWordAdderSelect w j)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
