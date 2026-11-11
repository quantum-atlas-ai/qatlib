/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGMultiplierData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGConditionalSubtractData

/-!
# Boolean DAG constructions for unsigned division

`BooleanDAGDivState` records a division graph together with quotient, remainder, zero, and
divisor nonzero wires. `booleanWordDivRound` shifts the partial remainder and conditionally
subtracts the divisor.

`booleanWordDivDAG` masks the final quotient with the divisor nonzero flag. Its selected output
consists of a width `w` quotient and a width `2*w` remainder. The circuit background is
described in [KitaevShenVyalyi2002].

## Main statements

* `booleanWordDivPrefix`, `booleanWordDivProgram`: iterative division states.
* `booleanWordDivDAG`, `booleanWordDivSelect`: final graph and output selection.
* `booleanWordDivQuotient`, `booleanWordDivRemainder`: evaluated output words.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- A Boolean division state with a graph, an `i`-bit quotient, a `w+i`-bit remainder, and
distinguished zero and divisor nonzero wires. -/
structure BooleanDAGDivState (w i : ℕ) where
  nodes : ℕ
  graph : BooleanDAG (2*w) nodes
  quotient : Fin i → Fin (2*w+nodes)
  remainder : Fin (w+i) → Fin (2*w+nodes)
  zero : Fin (2*w+nodes)
  nonzero : Fin (2*w+nodes)

/-- Build a graph accumulating the OR of the first `i` bits of the right input word, starting
from a false constant. -/
def booleanWordNonzeroPrefix (w : ℕ) :
    (i : ℕ) → i ≤ w → BooleanDAG (2*w) (3*i+1)
  | 0, _ => .snoc .nil (.constant false)
  | i+1, hi =>
    let g₀ := booleanWordNonzeroPrefix w i (by omega)
    let g₁ := g₀.snoc (.xor ⟨2*w+3*i,by omega⟩ ⟨w+i,by omega⟩)
    let g₂ := g₁.snoc (.conj ⟨2*w+3*i,by omega⟩ ⟨w+i,by omega⟩)
    let g₃ := g₂.snoc (.xor ⟨2*w+3*i+1,by omega⟩ ⟨2*w+3*i+2,by omega⟩)
    by simpa only [Nat.mul_succ,Nat.add_assoc] using g₃

/-- Initialize division with an empty quotient, a zero remainder, and a nonzero test of the full
divisor. -/
def booleanWordDivStart (w : ℕ) : BooleanDAGDivState w 0 where
  nodes := 3*w+1
  graph := booleanWordNonzeroPrefix w w (Nat.le_refl w)
  quotient := Fin.elim0
  remainder := fun _ => ⟨2*w,by omega⟩
  zero := ⟨2*w,by omega⟩
  nonzero := ⟨2*w+3*w,by omega⟩

/-- Append a conditional-subtraction round using the next high dividend bit, extending the
quotient and remainder by one bit. -/
def booleanWordDivRound (w i : ℕ) (hi : i < w)
    (p : BooleanDAGDivState w i) : BooleanDAGDivState w (i+1) :=
  let u := w+i+1
  let r : Fin (2*u) → Fin (2*w+p.nodes) := fun j =>
    if hj : j.val < u then
      if hz : j.val = 0 then ⟨w-1-i,by omega⟩
      else p.remainder ⟨j.val-1,by dsimp [u] at hj; omega⟩
    else
      if hb : j.val-u < w then ⟨w+(j.val-u),by omega⟩
      else p.zero
  let nc := 7*u+1+3*u+1
  let out := fun j : Fin (u+1) => booleanSpliceSource (n := nc) r
    (booleanWordCondSubSelect u j)
  ⟨p.nodes+nc,booleanDAGSplice p.graph r (booleanWordCondSubDAG u),
    (fun j => if hj : j.val = 0 then out (Fin.last u)
      else Fin.castLE (by omega) (p.quotient ⟨j.val-1,by have := j.isLt; omega⟩)),
    (fun j => out (Fin.castSucc (⟨j.val,by have := j.isLt; dsimp [u]; omega⟩ : Fin u))),
    Fin.castLE (by omega) p.zero,Fin.castLE (by omega) p.nonzero⟩

/-- Build the partial division state after `i` rounds, processing dividend bits from most
significant to least significant. -/
def booleanWordDivPrefix (w : ℕ) : (i : ℕ) → i ≤ w → BooleanDAGDivState w i
  | 0, _ => booleanWordDivStart w
  | i+1, hi => booleanWordDivRound w i (by omega) (booleanWordDivPrefix w i (by omega))

/-- Build the division state after processing all `w` dividend bits. -/
def booleanWordDivProgram (w : ℕ) : BooleanDAGDivState w w :=
  booleanWordDivPrefix w w (Nat.le_refl w)

/-- Append a mask to the final division graph so that its quotient bits are gated by the divisor
nonzero flag. -/
def booleanWordDivDAG (w : ℕ) : BooleanDAG (2*w) ((booleanWordDivProgram w).nodes+w) :=
  let p := booleanWordDivProgram w
  let r : Fin (w+1) → Fin (2*w+p.nodes) := fun j =>
    if hj : j.val < w then p.quotient ⟨j.val,hj⟩ else p.nonzero
  booleanDAGSplice p.graph r (booleanWordAndDAG w)

/-- Select the masked width `w` quotient followed by the width `2*w` remainder from the division
graph. -/
def booleanWordDivSelect (w : ℕ) :
    Fin (3*w) → Fin (2*w+((booleanWordDivProgram w).nodes+w)) := fun j =>
  if hj : j.val < w then ⟨2*w+(booleanWordDivProgram w).nodes+j.val,by omega⟩
  else Fin.castLE (by omega) ((booleanWordDivProgram w).remainder
    ⟨j.val-w,by have := j.isLt; omega⟩)

/-- Evaluate the selected quotient and remainder output bits on two packed unsigned input words. -/
def booleanWordDivResult (w : ℕ) (a b : Reg w) : Reg (3*w) := fun j =>
  booleanDAGValue (booleanWordDivDAG w) (booleanWordAdderInput w a b)
    (booleanWordDivSelect w j)

/-- Extract the width `w` quotient word from the evaluated division result. -/
def booleanWordDivQuotient (w : ℕ) (a b : Reg w) : Reg w := fun j =>
  booleanWordDivResult w a b ⟨j.val,by have := j.isLt; omega⟩

/-- Extract the width `2*w` remainder word from the evaluated division result. -/
def booleanWordDivRemainder (w : ℕ) (a b : Reg w) : Reg (2*w) := fun j =>
  booleanWordDivResult w a b ⟨w+j.val,by have := j.isLt; omega⟩

/-- Interpret the highest `i` bits of a width `w` word as a little-endian unsigned word of width
`i`. -/
def booleanWordHighValue (w i : ℕ) (hi : i ≤ w) (a : Reg w) : ℕ :=
  booleanWordLSBValue i (fun j => a ⟨w-i+j.val,by have := j.isLt; omega⟩)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
