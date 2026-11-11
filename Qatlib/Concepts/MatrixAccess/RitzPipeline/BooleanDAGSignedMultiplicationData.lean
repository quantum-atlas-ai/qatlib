/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedDivisionData

/-!
# Boolean DAG constructions for signed multiplication

`booleanWordSignedMulProgram` embeds the unsigned multiplier in a graph with two extra sign
inputs, then appends their XOR as the product sign. The selected output consists of `2*w`
magnitude bits and one sign bit.

The module defines input packing, operand views, result evaluation, and sign-magnitude decoding
for this graph. The circuit background is described in [KitaevShenVyalyi2002].

## Main statements

* `booleanWordSignedMulInput`, `booleanWordSignedMulLeft`, `booleanWordSignedMulRight`: input
  layout.
* `booleanWordSignedMulProgram`: unsigned multiplication followed by sign XOR.
* `booleanWordSignedMulMagnitude`, `booleanWordSignedMulSign`, `booleanWordSignedMulValue`:
  output interpretation.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- Pack two width `w` magnitude words followed by their respective negative flags. -/
def booleanWordSignedMulInput (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : Reg (2*w+2) :=
  Fin.snoc (Fin.snoc (booleanWordAdderInput w a b) negativeA) negativeB

/-- Extract the first magnitude word from a packed signed-multiplication input. -/
def booleanWordSignedMulLeft (w : ℕ) (x : Reg (2*w+2)) : Reg w :=
  booleanWordAdderLeft w (fun j => x j.castSucc.castSucc)

/-- Extract the second magnitude word from a packed signed-multiplication input. -/
def booleanWordSignedMulRight (w : ℕ) (x : Reg (2*w+2)) : Reg w :=
  booleanWordAdderRight w (fun j => x j.castSucc.castSucc)

/-- Build a signed multiplier by embedding unsigned multiplication and appending the XOR of the
two input sign bits. -/
def booleanWordSignedMulProgram (w : ℕ) : BooleanDAGWord (2*w+2) (2*w+1) :=
  let p := booleanWordMulProgram w
  let n₀ := 0+p.nodes
  let raw : Fin (2*w) → Fin (2*w+2+0) := fun j => j.castSucc.castSucc
  let g₀ : BooleanDAG (2*w+2) n₀ :=
    booleanDAGSplice (.nil : BooleanDAG (2*w+2) 0) raw p.graph
  let q : Fin (2*w) → Fin (2*w+2+n₀) := fun j =>
    booleanSpliceSource raw (booleanWordMulSelect w j)
  let g := g₀.snoc (.xor ⟨2*w,by omega⟩ ⟨2*w+1,by omega⟩)
  ⟨n₀+1,g,
    (fun j => if hj : j.val < 2*w then Fin.castLE (by omega) (q ⟨j.val,hj⟩)
      else ⟨2*w+2+n₀,by omega⟩),
    Fin.castLE (by omega) (booleanSpliceSource raw p.zero)⟩

/-- Evaluate the signed-multiplier output, consisting of `2*w` magnitude bits followed by one
sign bit. -/
def booleanWordSignedMulResult (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : Reg (2*w+1) :=
  fun j => booleanDAGValue (booleanWordSignedMulProgram w).graph
    (booleanWordSignedMulInput w a b negativeA negativeB) ((booleanWordSignedMulProgram w).output j)

/-- Extract the width `2*w` product magnitude from the signed-multiplication output. -/
def booleanWordSignedMulMagnitude (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : Reg (2*w) :=
  fun j => booleanWordSignedMulResult w a b negativeA negativeB j.castSucc

/-- Extract the final product sign bit from the signed-multiplication output. -/
def booleanWordSignedMulSign (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : Bool :=
  booleanWordSignedMulResult w a b negativeA negativeB (Fin.last (2*w))

/-- Decode the signed multiplication output magnitude and sign as an integer. -/
def booleanWordSignedMulValue (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : ℤ :=
  booleanWordSignedValue (2*w) (booleanWordSignedMulMagnitude w a b negativeA negativeB)
    (booleanWordSignedMulSign w a b negativeA negativeB)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
