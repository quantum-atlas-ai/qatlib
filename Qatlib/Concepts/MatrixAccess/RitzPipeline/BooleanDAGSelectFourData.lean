/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedAdditionData

/-!
# Boolean DAG constructions for four-way selection

`booleanSelectFourDAG` combines two multiplexers controlled by the low selector bit and a final
multiplexer controlled by the high bit. `booleanSelectFourRow` encodes the chosen row as
`2*high+low`.

The module defines the source maps, output wires, input packing, and evaluated result used to
verify this construction. The circuit background is described in [KitaevShenVyalyi2002].

## Main statements

* `booleanSelectFourDAG`, `booleanSelectFourOutput`: graph and output wires.
* `booleanSelectFourInput`, `booleanSelectFourWord`: input packing and row extraction.
* `booleanSelectFourRow`: row index determined by two Boolean selectors.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- Pack two source words and one control source in the input layout of a word multiplexer. -/
def booleanMuxSources {α : Type*} (H : ℕ) (a b : Fin H → α) (c : α) : Fin (2*H+1) → α :=
  fun j => if hj : j.val < H then a ⟨j.val,hj⟩
    else if hk : j.val < 2*H then b ⟨j.val-H,by omega⟩ else c

/-- Locate bit `j` of one of the four raw input words in a graph with `K` appended nodes. -/
def booleanSelectFourRaw (H K : ℕ) (row : Fin 4) (j : Fin H) : Fin (4*H+2+K) :=
  ⟨row.val*H+j.val,by have := row.isLt; have := j.isLt; nlinarith⟩
/-- Locate the high selector input after the four word blocks. -/
def booleanSelectFourHigh (H K : ℕ) : Fin (4*H+2+K) := ⟨4*H,by omega⟩
/-- Locate the low selector input immediately after the high selector input. -/
def booleanSelectFourLow (H K : ℕ) : Fin (4*H+2+K) := ⟨4*H+1,by omega⟩

/-- Route rows one and zero, together with the low selector, into the first multiplexer. -/
def booleanSelectFourFirstInputs (H : ℕ) : Fin (2*H+1) → Fin (4*H+2+0) :=
  booleanMuxSources H (booleanSelectFourRaw H 0 1) (booleanSelectFourRaw H 0 0) (booleanSelectFourLow H 0)
/-- Build the first multiplexer, selecting between rows one and zero using the low selector. -/
def booleanSelectFourFirst (H : ℕ) : BooleanDAG (4*H+2) (0+3*H) :=
  booleanDAGSplice .nil (booleanSelectFourFirstInputs H) (booleanWordMuxDAG H)
/-- Route rows three and two, together with the low selector, into the second multiplexer. -/
def booleanSelectFourSecondInputs (H : ℕ) : Fin (2*H+1) → Fin (4*H+2+(0+3*H)) :=
  booleanMuxSources H (booleanSelectFourRaw H (0+3*H) 3) (booleanSelectFourRaw H (0+3*H) 2)
    (booleanSelectFourLow H (0+3*H))
/-- Append the second multiplexer to select between rows three and two using the low selector. -/
def booleanSelectFourSecond (H : ℕ) : BooleanDAG (4*H+2) ((0+3*H)+3*H) :=
  booleanDAGSplice (booleanSelectFourFirst H) (booleanSelectFourSecondInputs H) (booleanWordMuxDAG H)

/-- Route the second and first multiplexer outputs, together with the high selector, into the
final multiplexer. -/
def booleanSelectFourFinalInputs (H : ℕ) : Fin (2*H+1) → Fin (4*H+2+((0+3*H)+3*H)) :=
  booleanMuxSources H
    (fun j => booleanSpliceSource (booleanSelectFourSecondInputs H) (booleanWordMuxSelect H j))
    (fun j => Fin.castLE (by omega)
      (booleanSpliceSource (booleanSelectFourFirstInputs H) (booleanWordMuxSelect H j)))
    (booleanSelectFourHigh H ((0+3*H)+3*H))
/-- Build the three-multiplexer graph selecting one of four width `H` words using two selector
bits. -/
def booleanSelectFourDAG (H : ℕ) : BooleanDAG (4*H+2) (((0+3*H)+3*H)+3*H) :=
  booleanDAGSplice (booleanSelectFourSecond H) (booleanSelectFourFinalInputs H) (booleanWordMuxDAG H)
/-- Select the final multiplexer's width `H` output wires. -/
def booleanSelectFourOutput (H : ℕ) : Fin H → Fin (4*H+2+(((0+3*H)+3*H)+3*H)) :=
  fun j => booleanSpliceSource (booleanSelectFourFinalInputs H) (booleanWordMuxSelect H j)

/-- Pack four width `H` words followed by the high and low selector bits into one input
register. -/
def booleanSelectFourInput (H : ℕ) (a : Fin 4 → Reg H) (high low : Bool) : Reg (4*H+2) :=
  fun j => if hj : j.val < 4*H then a ⟨j.val/H,by
    by_cases hh : H=0
    · subst H; omega
    · exact (Nat.div_lt_iff_lt_mul (Nat.pos_of_ne_zero hh)).mpr (by omega)⟩
      ⟨j.val%H,by
        by_cases hh : H=0
        · subst H; omega
        · exact Nat.mod_lt _ (Nat.pos_of_ne_zero hh)⟩
    else if j.val=4*H then high else low

/-- Extract one of the four width `H` words from the packed input register. -/
def booleanSelectFourWord (H : ℕ) (x : Reg (4*H+2)) (row : Fin 4) : Reg H :=
  fun j => x (booleanSelectFourRaw H 0 row j)
/-- Evaluate the four-way selection graph at its selected output wires. -/
def booleanSelectFourResult (H : ℕ) (x : Reg (4*H+2)) : Reg H :=
  fun j => booleanDAGValue (booleanSelectFourDAG H) x (booleanSelectFourOutput H j)
/-- Encode the two selector bits as a row index, with the high bit contributing two and the low
bit contributing one. -/
def booleanSelectFourRow (high low : Bool) : Fin 4 :=
  if high then (if low then 3 else 2) else (if low then 1 else 0)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
