/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGDividerData

/-!
# Boolean DAG constructions for signed division

`booleanWordSignedValue` decodes a magnitude word and a negative flag as an integer.
`booleanWordSignedDivProgram` extends unsigned division with a remainder test and a conditional
increment for a negative numerator.

The input has two width `w` magnitudes and a numerator sign bit. The selected output has `w+2`
magnitude bits and the original sign bit. The circuit background is described in
[KitaevShenVyalyi2002].

## Main statements

* `booleanWordSignedValue`: sign-magnitude interpretation.
* `booleanWordSignedDivProgram`: unsigned quotient with a guarded rounding correction.
* `booleanWordSignedDivMagnitude`, `booleanWordSignedDivSign`, `booleanWordSignedDivValue`:
  output interpretation.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- Decode an unsigned magnitude word as its integer value, negated when `negative` is true. -/
def booleanWordSignedValue (w : ℕ) (a : Reg w) (negative : Bool) : ℤ :=
  if negative then -(booleanWordLSBValue w a : ℤ) else booleanWordLSBValue w a

/-- Pack numerator and denominator magnitude words followed by the numerator's negative flag. -/
def booleanWordSignedDivInput (w : ℕ) (a b : Reg w) (negative : Bool) : Reg (2*w+1) :=
  Fin.snoc (booleanWordAdderInput w a b) negative

/-- Extract the numerator magnitude word from a packed signed-division input. -/
def booleanWordSignedDivLeft (w : ℕ) (x : Reg (2*w+1)) : Reg w :=
  booleanWordAdderLeft w (fun j => x j.castSucc)

/-- Extract the unsigned denominator word from a packed signed-division input. -/
def booleanWordSignedDivRight (w : ℕ) (x : Reg (2*w+1)) : Reg w :=
  booleanWordAdderRight w (fun j => x j.castSucc)

/-- Build a signed divider by computing unsigned quotient and remainder, testing the remainder,
and conditionally incrementing the quotient magnitude for a negative numerator. -/
def booleanWordSignedDivProgram (w : ℕ) : BooleanDAGWord (2*w+1) (w+3) :=
  let p := booleanWordDivProgram w
  let n₀ := 0+(p.nodes+w)
  let raw : Fin (2*w) → Fin (2*w+1+0) := fun j => j.castSucc
  let g₀ := booleanDAGSplice (.nil : BooleanDAG (2*w+1) 0) raw (booleanWordDivDAG w)
  let q : Fin w → Fin (2*w+1+n₀) := fun j =>
    booleanSpliceSource raw (booleanWordDivSelect w ⟨j.val,by have := j.isLt; omega⟩)
  let r : Fin (2*w) → Fin (2*w+1+n₀) := fun j =>
    booleanSpliceSource raw (booleanWordDivSelect w ⟨w+j.val,by have := j.isLt; omega⟩)
  let zero : Fin (2*w+1+n₀) :=
    booleanSpliceSource raw (Fin.castLE (by dsimp only [p]; omega) p.zero)
  let dnz : Fin (2*w+1+n₀) :=
    booleanSpliceSource raw (Fin.castLE (by dsimp only [p]; omega) p.nonzero)
  let remMap : Fin (2*(2*w)) → Fin (2*w+1+n₀) := fun j =>
    if hj : j.val < 2*w then zero else r ⟨j.val-2*w,by have := j.isLt; omega⟩
  let g₁ := booleanDAGSplice g₀ remMap (booleanWordNonzeroPrefix (2*w) (2*w) (Nat.le_refl _))
  let rnz : Fin (2*w+1+(n₀+(3*(2*w)+1))) :=
    booleanSpliceSource remMap (⟨2*(2*w)+3*(2*w),by omega⟩ : Fin (2*(2*w)+(3*(2*w)+1)))
  let g₂ := g₁.snoc (.conj rnz (Fin.castLE (by dsimp only [n₀,p]; omega) dnz))
  let g₃ := g₂.snoc (.conj ⟨2*w+1+(n₀+(3*(2*w)+1)),by dsimp only [n₀,p]; omega⟩ ⟨2*w,by omega⟩)
  let n₃ := n₀+(3*(2*w)+1)+1+1
  let z : Fin (2*w+1+n₃) := Fin.castLE (by dsimp [n₃]; omega) zero
  let c : Fin (2*w+1+n₃) := ⟨2*w+1+(n₀+(3*(2*w)+1))+1,by dsimp [n₃]; omega⟩
  let left : Fin (w+1) → Fin (2*w+1+n₃) := fun j =>
    if hj : j.val < w then Fin.castLE (by dsimp [n₃]; omega) (q ⟨j.val,hj⟩) else z
  let right : Fin (w+1) → Fin (2*w+1+n₃) := fun j => if j.val = 0 then c else z
  let g := booleanDAGAppendAdder g₃ (w+1) left right
  let out := booleanDAGAppendAdderSelect (w+1) left right
  ⟨n₃+(5*(w+1)+1),g,
    (fun j => if hj : j.val < w+2 then out ⟨j.val,hj⟩ else ⟨2*w,by omega⟩),
    Fin.castLE (by omega) z⟩

/-- Evaluate the signed-divider output, consisting of `w+2` magnitude bits followed by the input
sign bit. -/
def booleanWordSignedDivResult (w : ℕ) (a b : Reg w) (negative : Bool) : Reg (w+3) :=
  fun j => booleanDAGValue (booleanWordSignedDivProgram w).graph
    (booleanWordSignedDivInput w a b negative) ((booleanWordSignedDivProgram w).output j)

/-- Extract the width `w+2` magnitude word from the signed-divider output. -/
def booleanWordSignedDivMagnitude (w : ℕ) (a b : Reg w) (negative : Bool) : Reg (w+2) :=
  fun j => booleanWordSignedDivResult w a b negative j.castSucc

/-- Extract the final sign bit from the signed-divider output. -/
def booleanWordSignedDivSign (w : ℕ) (a b : Reg w) (negative : Bool) : Bool :=
  booleanWordSignedDivResult w a b negative (Fin.last (w+2))

/-- Decode the signed-divider output magnitude and sign as an integer. -/
def booleanWordSignedDivValue (w : ℕ) (a b : Reg w) (negative : Bool) : ℤ :=
  booleanWordSignedValue (w+2) (booleanWordSignedDivMagnitude w a b negative)
    (booleanWordSignedDivSign w a b negative)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
