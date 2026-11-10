/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGCoarseBranchData
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

def booleanWordLow (W m : ℕ) (hm : m ≤ W) (a : Reg W) : Reg m :=
  fun j => a (Fin.castLE hm j)

def booleanWordThresholdOffsetProgram (n w b d : ℕ) :
    BooleanDAGWord (booleanWordCoarseInputWidth n w) (booleanWordBilinearQuotientWidth w b d+4) :=
  let M := booleanWordCoarseInputWidth n w
  let V := booleanWordBilinearQuotientWidth w b d
  let p := booleanWordCoarseProgram n w b d
  let g := p.graph.snoc (.constant true)
  let old : Fin (V+3) → Fin (M+(p.nodes+1)) := fun j => Fin.castSucc (p.output j)
  let zero : Fin (M+(p.nodes+1)) := Fin.castSucc p.zero
  let one : Fin (M+(p.nodes+1)) := ⟨M+p.nodes,by omega⟩
  let offset : Fin (V+3) → Fin (M+(p.nodes+1)) := fun j =>
    if j.val=b+5 then one else zero
  booleanDAGAppendWord g (booleanSignedPairSelect (V+2) old offset)
    (booleanWordSignedAddProgram (V+2))

def booleanWordThresholdOffsetResult (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) :
    Reg (booleanWordBilinearQuotientWidth w b d+4) := fun j =>
  booleanDAGValue (booleanWordThresholdOffsetProgram n w b d).graph x
    ((booleanWordThresholdOffsetProgram n w b d).output j)

def booleanWordThresholdOffsetValue (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) : ℤ :=
  let V := booleanWordBilinearQuotientWidth w b d
  booleanWordSignedValue (V+3) (fun j => booleanWordThresholdOffsetResult n w b d x j.castSucc)
    (booleanWordThresholdOffsetResult n w b d x (Fin.last (V+3)))

def booleanWordThresholdProgram (n w b d : ℕ) :
    BooleanDAGWord (booleanWordCoarseInputWidth n w) (b+6) :=
  let p := booleanWordThresholdOffsetProgram n w b d
  ⟨p.nodes,p.graph,(fun j => p.output (Fin.castSucc ⟨(Fin.rev j).val,by
    have := (Fin.rev j).isLt
    dsimp only [booleanWordBilinearQuotientWidth]
    omega⟩)),p.zero⟩

def booleanWordThresholdResult (n w b d : ℕ) (x : Reg (booleanWordCoarseInputWidth n w)) : Reg (b+6) :=
  fun j => booleanDAGValue (booleanWordThresholdProgram n w b d).graph x
    ((booleanWordThresholdProgram n w b d).output j)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
