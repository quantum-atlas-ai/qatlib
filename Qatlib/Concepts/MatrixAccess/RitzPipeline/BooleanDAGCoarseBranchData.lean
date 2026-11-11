/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGBilinearQuotientData

/-!
# Boolean graph data for the coarse frequency branch

This module constructs `booleanWordCoarseProgram` from a bilinear quotient, a zero-frequency
test, a special entry-dependent division, and a multiplexer. The special branch uses a mask on
four entry bits and a divisor of either 12 or 24.

The input layouts, output selections, and signed-value decoders support reversible circuit
compilation in the framework of [NielsenChuang2010].

## Main statements

* `booleanZeroDetailProgram`: builds the special-branch quotient graph.
* `booleanWordCoarseProgram`: assembles both branches and the frequency-controlled multiplexer.
* `booleanWordCoarseFlag`: evaluates the selected frequency-test flag.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- The eleven-node graph computing entry-pair equality, the special-branch mask, a row
conjunction and its negation, and a true constant from five input bits. -/
def booleanZeroDetailFlags : BooleanDAG 5 11 :=
  let g₀ : BooleanDAG 5 0 := .nil
  let g₁ := g₀.snoc (.xor ⟨0,by omega⟩ ⟨2,by omega⟩)
  let g₂ := g₁.snoc (.xor ⟨1,by omega⟩ ⟨3,by omega⟩)
  let g₃ := g₂.snoc (.neg ⟨5,by omega⟩)
  let g₄ := g₃.snoc (.neg ⟨6,by omega⟩)
  let g₅ := g₄.snoc (.conj ⟨7,by omega⟩ ⟨8,by omega⟩)
  let g₆ := g₅.snoc (.xor ⟨0,by omega⟩ ⟨1,by omega⟩)
  let g₇ := g₆.snoc (.conj ⟨0,by omega⟩ ⟨1,by omega⟩)
  let g₈ := g₇.snoc (.xor ⟨10,by omega⟩ ⟨11,by omega⟩)
  let g₉ := g₈.snoc (.conj ⟨9,by omega⟩ ⟨12,by omega⟩)
  let g₁₀ := g₉.snoc (.neg ⟨11,by omega⟩)
  g₁₀.snoc (.constant true)

/-- Tests that the two entry-bit pairs agree and that the first pair contains at least one true
bit. -/
def booleanZeroDetailMask (e : Reg 4) : Bool :=
  ((e 0 == e 2) && (e 1 == e 3)) && (e 0 || e 1)
/-- The special-branch divisor, equal to 24 when both first-pair bits are true and 12 otherwise. -/
def booleanZeroDetailDivisor (e : Reg 4) : ℕ := if e 0 && e 1 then 24 else 12

/-- Appends signed division to the entry-flag graph, selecting a mask-weighted numerator at bit
b and an entry-dependent divisor; its fifth input supplies the false bit. -/
def booleanZeroDetailProgram (V b : ℕ) (_hb : b < V) (_hV : 5 ≤ V) : BooleanDAGWord 5 (V+3) :=
  let num : Fin V → Fin (5+11) := fun j => if j.val=b then ⟨13,by omega⟩ else ⟨4,by omega⟩
  let den : Fin V → Fin (5+11) := fun j =>
    if j.val=2 then ⟨14,by omega⟩ else if j.val=3 then ⟨15,by omega⟩
    else if j.val=4 then ⟨11,by omega⟩ else ⟨4,by omega⟩
  let inputs : Fin (2*V+1) → Fin (5+11) := fun j =>
    if hj : j.val < V then num ⟨j.val,hj⟩
    else if hk : j.val < 2*V then den ⟨j.val-V,by omega⟩ else ⟨4,by omega⟩
  let p := booleanDAGAppendWord booleanZeroDetailFlags inputs (booleanWordSignedDivProgram V)
  ⟨p.nodes,p.graph,p.output,⟨4,by omega⟩⟩

/-- The selected special-branch result word evaluated on four entry bits followed by false. -/
def booleanZeroDetailResult (V b : ℕ) (hb : b < V) (hV : 5 ≤ V) (e : Reg 4) : Reg (V+3) := fun j =>
  booleanDAGValue (booleanZeroDetailProgram V b hb hV).graph (Fin.snoc e false)
    ((booleanZeroDetailProgram V b hb hV).output j)
/-- The signed integer decoded from the special-branch result word. -/
def booleanZeroDetailValue (V b : ℕ) (hb : b < V) (hV : 5 ≤ V) (e : Reg 4) : ℤ :=
  booleanWordSignedValue (V+2) (fun j => booleanZeroDetailResult V b hb hV e j.castSucc)
    (booleanZeroDetailResult V b hb hV e (Fin.last (V+2)))

/-- The coarse-branch input width 16(w+1) + 2n + 4. -/
def booleanWordCoarseInputWidth (n w : ℕ) : ℕ := 16*(w+1)+2*n+4

/-- The graph computing the bilinear quotient, testing for zero frequency, computing the special
entry branch, and selecting the result with a multiplexer. -/
def booleanWordCoarseProgram (n w b d : ℕ) :
    BooleanDAGWord (booleanWordCoarseInputWidth n w) (booleanWordBilinearQuotientWidth w b d+3) :=
  let M := booleanWordCoarseInputWidth n w
  let V := booleanWordBilinearQuotientWidth w b d
  let old := booleanWordBilinearQuotientProgram w b d
  let raw : Fin (16*(w+1)) → Fin (M+0) := fun j =>
    ⟨j.val,by have := j.isLt; dsimp only [M,booleanWordCoarseInputWidth]; omega⟩
  let p := booleanDAGAppendWord (.nil : BooleanDAG M 0) raw old
  let nzInputs : Fin (2*(2*n)) → Fin (M+p.nodes) := fun j =>
    if hj : j.val < 2*n then p.zero else
      ⟨16*(w+1)+(j.val-2*n),by have := j.isLt; dsimp only [M,booleanWordCoarseInputWidth]; omega⟩
  let nNZ := p.nodes+(3*(2*n)+1)
  let gNZ :=
      booleanDAGSplice p.graph nzInputs (booleanWordNonzeroPrefix (2*n) (2*n) (Nat.le_refl _))
  let nz : Fin (M+nNZ) := booleanSpliceSource nzInputs
    (⟨2*(2*n)+3*(2*n),by omega⟩ : Fin (2*(2*n)+(3*(2*n)+1)))
  let gC := gNZ.snoc (.neg nz)
  let nC := nNZ+1
  let zero : Fin (M+nC) := Fin.castLE (by dsimp only [nC,nNZ]; omega) p.zero
  let zi : Fin 5 → Fin (M+nC) := fun j =>
    if hj : j.val < 4 then
      ⟨16*(w+1)+2*n+j.val,by dsimp only [M,booleanWordCoarseInputWidth]; omega⟩ else zero
  let z := booleanDAGAppendWord gC zi
    (booleanZeroDetailProgram V b (by dsimp only [V,booleanWordBilinearQuotientWidth]; omega)
      (by dsimp only [V,booleanWordBilinearQuotientWidth]; omega))
  let o := V+3
  let muxInputs : Fin (2*o+1) → Fin (M+z.nodes) := fun j =>
    if hj : j.val < o then z.output ⟨j.val,hj⟩
    else if hk : j.val < 2*o then
      Fin.castLE (by change M+p.nodes ≤ M+(nC+(booleanZeroDetailProgram V b _ _).nodes); dsimp only [nC,nNZ]; omega)
        (p.output ⟨j.val-o,by omega⟩)
    else Fin.castLE (by change M+nC ≤ M+(nC+(booleanZeroDetailProgram V b _ _).nodes); omega)
      (⟨M+nNZ,by dsimp only [nC]; omega⟩ : Fin (M+nC))
  let g := booleanDAGSplice z.graph muxInputs (booleanWordMuxDAG o)
  ⟨z.nodes+3*o,g,(fun j => booleanSpliceSource muxInputs (booleanWordMuxSelect o j)),
    Fin.castLE (by omega) z.zero⟩

/-- Selects the wire introduced by negating the frequency nonzero-test result within the full
coarse graph. -/
def booleanWordCoarseFlagSelect (n w b d : ℕ) :
    Fin (booleanWordCoarseInputWidth n w+(booleanWordCoarseProgram n w b d).nodes) :=
  ⟨booleanWordCoarseInputWidth n w+(0+(booleanWordBilinearQuotientProgram w b d).nodes)+(3*(2*n)+1),by
    dsimp only [booleanWordCoarseProgram,booleanDAGAppendWord]
    omega⟩
/-- The Boolean value of the selected frequency flag in the evaluated coarse graph. -/
def booleanWordCoarseFlag (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) : Bool :=
  booleanDAGValue (booleanWordCoarseProgram n w b d).graph x (booleanWordCoarseFlagSelect n w b d)

/-- Extracts the sixteen signed coefficient words from the beginning of the coarse input. -/
def booleanWordCoarseCoefficients (n w : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) : Reg (16*(w+1)) :=
  fun j => x ⟨j.val,by have := j.isLt; dsimp only [booleanWordCoarseInputWidth]; omega⟩
/-- Extracts the 2n frequency bits following the coefficient words. -/
def booleanWordCoarseFrequency (n w : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) : Reg (2*n) :=
  fun j => x ⟨16*(w+1)+j.val,by have := j.isLt; dsimp only [booleanWordCoarseInputWidth]; omega⟩
/-- Extracts the final four entry bits of the coarse input. -/
def booleanWordCoarseEntry (n w : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) : Reg 4 :=
  fun j => x ⟨16*(w+1)+2*n+j.val,by have := j.isLt; dsimp only [booleanWordCoarseInputWidth]; omega⟩

/-- Concatenates the coefficient register, frequency register, and four entry bits into the
coarse input layout. -/
def booleanWordCoarseInput (n w : ℕ) (a : Reg (16*(w+1))) (f : Reg (2*n)) (e : Reg 4) :
    Reg (booleanWordCoarseInputWidth n w) := fun j =>
  if hj : j.val < 16*(w+1) then a ⟨j.val,hj⟩
  else if hk : j.val < 16*(w+1)+2*n then f ⟨j.val-16*(w+1),by omega⟩
  else e ⟨j.val-(16*(w+1)+2*n),by have := j.isLt; dsimp only [booleanWordCoarseInputWidth] at this; omega⟩

/-- The selected output word obtained by evaluating the coarse-branch graph. -/
def booleanWordCoarseResult (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) :
    Reg (booleanWordBilinearQuotientWidth w b d+3) := fun j =>
  booleanDAGValue (booleanWordCoarseProgram n w b d).graph x ((booleanWordCoarseProgram n w b d).output j)
/-- The signed integer decoded from the coarse-branch output word. -/
def booleanWordCoarseValue (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) : ℤ :=
  let V := booleanWordBilinearQuotientWidth w b d
  booleanWordSignedValue (V+2) (fun j => booleanWordCoarseResult n w b d x j.castSucc)
    (booleanWordCoarseResult n w b d x (Fin.last (V+2)))

end Qatlib.Concepts.MatrixAccess.RitzPipeline
