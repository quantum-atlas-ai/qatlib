/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedDotData

/-!
# Boolean graph data for a bilinear quotient

This module composes signed dot products, multiplication, and division into
`booleanWordBilinearQuotientProgram`. Sixteen signed input words encode a left vector, a 3 × 3
matrix, a right vector, and a scalar; the program scales the bilinear form and divides by a
scaled square of the scalar.

The wire selections and word layouts provide data for a reversible implementation in the circuit
framework of [NielsenChuang2010].

## Main statements

* `booleanWordBilinearForm`: defines the integer bilinear expression.
* `booleanWordBilinearQuotientProgram`: assembles the Boolean graph.
* `booleanWordBilinearQuotientValue`: decodes its signed output.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
open scoped BigOperators
set_option autoImplicit false

/-- Pads a signed word from magnitude width w to width v, retaining its sign and using the
supplied zero entry for new magnitude positions. -/
def booleanSignedWordPadTo {α : Type*} (w v : ℕ) (hw : w ≤ v) (zero : α)
    (a : Fin (w+1) → α) : Fin (v+1) → α := fun j =>
  booleanSignedWordPad w (v-w) zero a ⟨j.val,by have := j.isLt; omega⟩

/-- Shifts the magnitude entries of a signed word left by the specified number of positions,
inserts the supplied zero entry, and retains the sign. -/
def booleanSignedWordShift {α : Type*} (w shift : ℕ) (zero : α)
    (a : Fin (w+1) → α) : Fin (w+shift+1) → α := fun j =>
  if hlow : j.val < shift then zero
  else if hj : j.val < w+shift then a (Fin.castSucc ⟨j.val-shift,by omega⟩)
  else a (Fin.last w)

/-- Concatenates three signed-pair selections into the input layout of a three-term signed dot
product. -/
def booleanSignedTripleSelect {α : Type*} (w : ℕ)
    (a b : Fin 3 → Fin (w+1) → α) : Fin (3*(2*w+2)) → α := fun j =>
  if hj : j.val < 2*w+2 then booleanSignedPairSelect w (a 0) (b 0) ⟨j.val,hj⟩
  else if hk : j.val < 2*(2*w+2) then
    booleanSignedPairSelect w (a 1) (b 1) ⟨j.val-(2*w+2),by omega⟩
  else booleanSignedPairSelect w (a 2) (b 2) ⟨j.val-2*(2*w+2),by have := j.isLt; omega⟩

/-- Selects the bits of one of sixteen signed input slots within a graph with n additional
nodes. -/
def booleanWordBilinearRaw (w n : ℕ) (slot : Fin 16) : Fin (w+1) → Fin (16*(w+1)+n) :=
  fun j => ⟨slot.val*(w+1)+j.val,by have hs := slot.isLt; have hj := j.isLt; nlinarith⟩

/-- Maps a row and column of the three-by-three matrix to its input slot, starting at slot
three. -/
def booleanWordBilinearMatrixSlot (i j : Fin 3) : Fin 16 :=
  ⟨3+3*i.val+j.val,by have := i.isLt; have := j.isLt; omega⟩

/-- Selects the left-vector and matrix-column word pairs for the specified column dot product. -/
def booleanWordBilinearColumnInput (w n : ℕ) (j : Fin 3) :
    Fin (3*(2*w+2)) → Fin (16*(w+1)+n) :=
  booleanSignedTripleSelect w
    (fun i => booleanWordBilinearRaw w n ⟨i.val,by have := i.isLt; omega⟩)
    (fun i => booleanWordBilinearRaw w n (booleanWordBilinearMatrixSlot i j))

/-- The word program computing all three dot products of the left vector with the matrix
columns. -/
def booleanWordBilinearColumns (w : ℕ) : BooleanDAGWord (16*(w+1)) (3*(2*w+3)) :=
  let M := 16*(w+1)
  let dot := booleanWordSignedDotProgram w
  let p₀ := booleanDAGAppendWord (.nil : BooleanDAG M 0) (booleanWordBilinearColumnInput w 0 0) dot
  let p₁ := booleanDAGAppendWord p₀.graph (booleanWordBilinearColumnInput w p₀.nodes 1) dot
  let p₂ := booleanDAGAppendWord p₁.graph (booleanWordBilinearColumnInput w p₁.nodes 2) dot
  ⟨p₂.nodes,p₂.graph,(fun j =>
    if hj : j.val < 2*w+3 then
      Fin.castLE (by change M+p₀.nodes ≤ M+(p₀.nodes+dot.nodes+dot.nodes); omega) (p₀.output ⟨j.val,hj⟩)
    else if hk : j.val < 2*(2*w+3) then
      Fin.castLE (by change M+p₁.nodes ≤ M+(p₁.nodes+dot.nodes); omega)
        (p₁.output ⟨j.val-(2*w+3),by omega⟩)
    else p₂.output ⟨j.val-2*(2*w+3),by have := j.isLt; omega⟩),p₂.zero⟩

/-- The word program computing the dot product of the three column results with the padded
right-vector words. -/
def booleanWordBilinearProgram (w : ℕ) : BooleanDAGWord (16*(w+1)) (2*(2*w+2)+3) :=
  let p := booleanWordBilinearColumns w
  let q := 2*w+2
  let left : Fin 3 → Fin (q+1) → Fin (16*(w+1)+p.nodes) := fun i j =>
    p.output ⟨i.val*(2*w+3)+j.val,by have hi := i.isLt; have hj := j.isLt; dsimp only [q] at hj; nlinarith⟩
  let right : Fin 3 → Fin (q+1) → Fin (16*(w+1)+p.nodes) := fun i =>
    booleanSignedWordPadTo w q (by dsimp only [q]; omega) p.zero
      (booleanWordBilinearRaw w p.nodes ⟨12+i.val,by have := i.isLt; omega⟩)
  booleanDAGAppendWord p.graph (booleanSignedTripleSelect q left right) (booleanWordSignedDotProgram q)

/-- The common quotient magnitude width b + d + 4w + 6. -/
def booleanWordBilinearQuotientWidth (w b d : ℕ) : ℕ := b+d+4*w+6

/-- The program computing a bilinear form, squaring the final input word, shifting and padding
both quantities, and applying signed division. -/
def booleanWordBilinearQuotientProgram (w b d : ℕ) :
    BooleanDAGWord (16*(w+1)) (booleanWordBilinearQuotientWidth w b d+3) :=
  let M := 16*(w+1)
  let q := 2*w+2
  let p := booleanWordBilinearProgram w
  let rawK := booleanWordBilinearRaw w p.nodes 15
  let square :=
      booleanDAGAppendWord p.graph (booleanSignedPairSelect w rawK rawK)
      (booleanWordSignedMulProgram w)
  let bil : Fin (2*q+3) → Fin (M+square.nodes) := fun j =>
    Fin.castLE (by change M+p.nodes ≤ M+(p.nodes+(booleanWordSignedMulProgram w).nodes); omega) (p.output j)
  let V := booleanWordBilinearQuotientWidth w b d
  let num : Fin (V+1) → Fin (M+square.nodes) :=
    booleanSignedWordPadTo (2*q+2+b) V (by dsimp only [V,q,booleanWordBilinearQuotientWidth]; omega) square.zero
      (booleanSignedWordShift (2*q+2) b square.zero bil)
  let den : Fin (V+1) → Fin (M+square.nodes) :=
    booleanSignedWordPadTo (2*w+d) V (by dsimp only [V,booleanWordBilinearQuotientWidth]; omega) square.zero
      (booleanSignedWordShift (2*w) d square.zero square.output)
  let inputs : Fin (2*V+1) → Fin (M+square.nodes) := fun j =>
    if hj : j.val < V then num (Fin.castSucc ⟨j.val,hj⟩)
    else if hk : j.val < 2*V then den (Fin.castSucc ⟨j.val-V,by omega⟩)
    else num (Fin.last V)
  let final := booleanDAGAppendWord square.graph inputs (booleanWordSignedDivProgram V)
  ⟨final.nodes,final.graph,final.output,
    Fin.castLE (by change M+square.nodes ≤ M+(square.nodes+(booleanWordSignedDivProgram V).nodes); omega) square.zero⟩

/-- Packs sixteen words of w magnitude bits and one sign bit into a single input register. -/
def booleanWordBilinearInput (w : ℕ) (a : Fin 16 → Reg (w+1)) : Reg (16*(w+1)) := fun j =>
  a ⟨j.val/(w+1),by exact (Nat.div_lt_iff_lt_mul (by omega)).2 j.isLt⟩
    ⟨j.val%(w+1),Nat.mod_lt _ (by omega)⟩

/-- The signed integer value encoded by the specified slot of a bilinear input register. -/
def booleanWordBilinearInputValue (w : ℕ) (x : Reg (16*(w+1))) (s : Fin 16) : ℤ :=
  booleanWordSignedValue w
    (fun j => x (booleanWordBilinearRaw w 0 s j.castSucc))
    (x (booleanWordBilinearRaw w 0 s (Fin.last w)))

/-- The three-dimensional integer bilinear form given by the left vector, matrix, and right
vector stored in the input slots. -/
def booleanWordBilinearForm (w : ℕ) (x : Reg (16*(w+1))) : ℤ :=
  ∑ j : Fin 3, (∑ i : Fin 3,
    booleanWordBilinearInputValue w x ⟨i.val,by have := i.isLt; omega⟩ *
      booleanWordBilinearInputValue w x (booleanWordBilinearMatrixSlot i j)) *
    booleanWordBilinearInputValue w x ⟨12+j.val,by have := j.isLt; omega⟩

/-- The selected output word obtained by evaluating the bilinear quotient program. -/
def booleanWordBilinearQuotientResult (w b d : ℕ) (x : Reg (16*(w+1))) :
    Reg (booleanWordBilinearQuotientWidth w b d+3) := fun j =>
  booleanDAGValue (booleanWordBilinearQuotientProgram w b d).graph x
    ((booleanWordBilinearQuotientProgram w b d).output j)

/-- The signed integer decoded from the output word of the bilinear quotient program. -/
def booleanWordBilinearQuotientValue (w b d : ℕ) (x : Reg (16*(w+1))) : ℤ :=
  let V := booleanWordBilinearQuotientWidth w b d
  booleanWordSignedValue (V+2)
    (fun j => booleanWordBilinearQuotientResult w b d x j.castSucc)
    (booleanWordBilinearQuotientResult w b d x (Fin.last (V+2)))

end Qatlib.Concepts.MatrixAccess.RitzPipeline
