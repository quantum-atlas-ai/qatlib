/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedMultiplicationData
import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGConditionalSubtractData

/-!
# Boolean DAG constructions for signed addition

`booleanWordMuxDAG` implements controlled selection between two words.
`booleanWordSignedAddProgram` computes a sum for equal signs and an absolute magnitude
difference for unequal signs, retaining the sign of the operand with larger magnitude and
choosing the first sign on ties.

The input consists of two width `w` magnitudes and two sign bits. The output contains `w+1`
magnitude bits followed by a sign bit. The circuit background is described in
[KitaevShenVyalyi2002].

## Main statements

* `booleanWordMuxInput`, `booleanWordMuxResult`: multiplexer interface.
* `booleanWordSignedAddProgram`: signed addition graph.
* `booleanWordSignedAddMagnitude`, `booleanWordSignedAddSign`, `booleanWordSignedAddValue`:
  output interpretation.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- Build the first `i` bits of a word multiplexer using three Boolean nodes per output bit. -/
def booleanWordMuxPrefix (w : ℕ) : (i : ℕ) → i ≤ w → BooleanDAG (2*w+1) (3*i)
  | 0, _ => .nil
  | i+1, hi =>
    let g₀ := booleanWordMuxPrefix w i (by omega)
    let g₁ := g₀.snoc (.xor ⟨i,by omega⟩ ⟨w+i,by omega⟩)
    let g₂ := g₁.snoc (.conj ⟨2*w+1+3*i,by omega⟩ ⟨2*w,by omega⟩)
    let g₃ := g₂.snoc (.xor ⟨w+i,by omega⟩ ⟨2*w+1+3*i+1,by omega⟩)
    by simpa only [Nat.mul_succ,Nat.add_assoc] using g₃

/-- Build the full multiplexer graph for two width `w` words and one control bit. -/
def booleanWordMuxDAG (w : ℕ) : BooleanDAG (2*w+1) (3*w) :=
  booleanWordMuxPrefix w w (Nat.le_refl w)

/-- Select the final XOR node producing each multiplexer output bit. -/
def booleanWordMuxSelect (w : ℕ) : Fin w → Fin (2*w+1+3*w) :=
  fun j => ⟨2*w+1+3*j.val+2,by have := j.isLt; omega⟩

/-- Pack two width `w` words followed by the Boolean selecting the first word. -/
def booleanWordMuxInput (w : ℕ) (a b : Reg w) (selectA : Bool) : Reg (2*w+1) :=
  Fin.snoc (booleanWordAdderInput w a b) selectA

/-- Evaluate the selected output word of the multiplexer graph on its packed operands and
control. -/
def booleanWordMuxResult (w : ℕ) (a b : Reg w) (selectA : Bool) : Reg w := fun j =>
  booleanDAGValue (booleanWordMuxDAG w) (booleanWordMuxInput w a b selectA) (booleanWordMuxSelect w j)

/-- Pack two width `w` magnitude words followed by their two negative flags. -/
def booleanWordSignedAddInput (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : Reg (2*w+2) :=
  booleanWordSignedMulInput w a b negativeA negativeB

/-- Build a sign-magnitude adder using unsigned addition, conditional subtraction in both
operand orders, sign selection, and magnitude multiplexing. -/
def booleanWordSignedAddProgram (w : ℕ) : BooleanDAGWord (2*w+2) (w+2) :=
  let g₀ : BooleanDAG (2*w+2) 1 := .snoc .nil (.constant false)
  let raw₀ : Fin (2*w) → Fin (2*w+2+1) := fun j => ⟨j.val,by have := j.isLt; omega⟩
  let nA := 1+(5*w+1)
  let gA : BooleanDAG (2*w+2) nA := booleanDAGSplice g₀ raw₀ (booleanWordAdderDAG w)
  let sum : Fin (w+1) → Fin (2*w+2+nA) := fun j =>
    booleanSpliceSource raw₀ (booleanWordAdderSelect w j)
  let nC := 7*w+1+3*w+1
  let rawA : Fin (2*w) → Fin (2*w+2+nA) := fun j => ⟨j.val,by have := j.isLt; omega⟩
  let nF := nA+nC
  let gF : BooleanDAG (2*w+2) nF := booleanDAGSplice gA rawA (booleanWordCondSubDAG w)
  let f : Fin (w+1) → Fin (2*w+2+nF) := fun j =>
    booleanSpliceSource rawA (booleanWordCondSubSelect w j)
  let reverse : Fin (2*w) → Fin (2*w+2+nF) := fun j =>
    if hj : j.val < w then ⟨w+j.val,by omega⟩ else ⟨j.val-w,by have := j.isLt; omega⟩
  let nR := nF+nC
  let gR : BooleanDAG (2*w+2) nR := booleanDAGSplice gF reverse (booleanWordCondSubDAG w)
  let r : Fin (w+1) → Fin (2*w+2+nR) := fun j =>
    booleanSpliceSource reverse (booleanWordCondSubSelect w j)
  let flag : Fin (2*w+2+nR) := Fin.castLE (by dsimp [nR]; omega) (f (Fin.last w))
  let g₁ := gR.snoc (.xor ⟨2*w,by omega⟩ ⟨2*w+1,by omega⟩)
  let g₂ := g₁.snoc (.conj ⟨2*w+2+nR,by omega⟩ (Fin.castLE (by omega) flag))
  let g₃ := g₂.snoc (.xor ⟨2*w+1,by omega⟩ ⟨2*w+2+nR+1,by omega⟩)
  let nS := nR+1+1+1
  let diffMap : Fin (2*w+1) → Fin (2*w+2+nS) := fun j =>
    if hj : j.val < w then Fin.castLE (by dsimp [nS,nR]; omega) (f (Fin.castSucc ⟨j.val,hj⟩))
    else if hk : j.val < 2*w then
      Fin.castLE (by dsimp [nS]; omega) (r (Fin.castSucc ⟨j.val-w,by omega⟩))
    else Fin.castLE (by dsimp [nS,nR]; omega) (f (Fin.last w))
  let nD := nS+3*w
  let gD : BooleanDAG (2*w+2) nD := booleanDAGSplice g₃ diffMap (booleanWordMuxDAG w)
  let diff : Fin w → Fin (2*w+2+nD) := fun j =>
    booleanSpliceSource diffMap (booleanWordMuxSelect w j)
  let zero : Fin (2*w+2+nD) := ⟨2*w+2,by dsimp [nD,nS,nR,nF,nA,nC]; omega⟩
  let finalMap : Fin (2*(w+1)+1) → Fin (2*w+2+nD) := fun j =>
    if hj : j.val < w+1 then
      if hk : j.val < w then diff ⟨j.val,hk⟩ else zero
    else if hk : j.val < 2*(w+1) then
      Fin.castLE (by dsimp [nD,nS,nR,nF]; omega) (sum ⟨j.val-(w+1),by omega⟩)
    else ⟨2*w+2+nR,by dsimp [nD,nS]; omega⟩
  let nT := nD+3*(w+1)
  let g : BooleanDAG (2*w+2) nT := booleanDAGSplice gD finalMap (booleanWordMuxDAG (w+1))
  let mag : Fin (w+1) → Fin (2*w+2+nT) := fun j =>
    booleanSpliceSource finalMap (booleanWordMuxSelect (w+1) j)
  ⟨nT,g,
    (fun j => if hj : j.val < w+1 then mag ⟨j.val,hj⟩
      else ⟨2*w+2+nR+2,by dsimp [nT,nD,nS]; omega⟩),
    Fin.castLE (by dsimp [nT]; omega) zero⟩

/-- Evaluate the signed-adder output, consisting of `w+1` magnitude bits followed by one sign
bit. -/
def booleanWordSignedAddResult (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : Reg (w+2) :=
  fun j => booleanDAGValue (booleanWordSignedAddProgram w).graph
    (booleanWordSignedAddInput w a b negativeA negativeB) ((booleanWordSignedAddProgram w).output j)

/-- Extract the width `w+1` magnitude word from the signed-addition output. -/
def booleanWordSignedAddMagnitude (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : Reg (w+1) :=
  fun j => booleanWordSignedAddResult w a b negativeA negativeB j.castSucc

/-- Extract the final sign bit from the signed-addition output. -/
def booleanWordSignedAddSign (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : Bool :=
  booleanWordSignedAddResult w a b negativeA negativeB (Fin.last (w+1))

/-- Decode the signed-addition magnitude and sign as an integer. -/
def booleanWordSignedAddValue (w : ℕ) (a b : Reg w) (negativeA negativeB : Bool) : ℤ :=
  booleanWordSignedValue (w+1) (booleanWordSignedAddMagnitude w a b negativeA negativeB)
    (booleanWordSignedAddSign w a b negativeA negativeB)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
