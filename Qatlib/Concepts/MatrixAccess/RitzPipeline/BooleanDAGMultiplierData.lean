/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSpliceData
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

structure BooleanDAGWord (m w : ℕ) where
  nodes : ℕ
  graph : BooleanDAG m nodes
  output : Fin w → Fin (m+nodes)
  zero : Fin (m+nodes)

def booleanWordAndPrefix (w : ℕ) : (n : ℕ) → n ≤ w → BooleanDAG (w+1) n
  | 0, _ => .nil
  | n+1, hn =>
    (booleanWordAndPrefix w n (by omega)).snoc
      (.conj ⟨n,by omega⟩ ⟨w,by omega⟩)

def booleanWordAndDAG (w : ℕ) : BooleanDAG (w+1) w :=
  booleanWordAndPrefix w w (Nat.le_refl w)

def booleanWordMulStart (w : ℕ) : BooleanDAGWord (2*w) w where
  nodes := 1
  graph := .snoc .nil (.constant false)
  output := fun _ => ⟨2*w,by omega⟩
  zero := ⟨2*w,by omega⟩

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

def booleanWordMulPrefix (w : ℕ) : (i : ℕ) → i ≤ w → BooleanDAGWord (2*w) (w+i)
  | 0, _ => booleanWordMulStart w
  | i+1, hi =>
    booleanWordMulRound w i (by omega) (booleanWordMulPrefix w i (by omega))

def booleanWordMulProgram (w : ℕ) : BooleanDAGWord (2*w) (w+w) :=
  booleanWordMulPrefix w w (Nat.le_refl w)

def booleanWordMulSelect (w : ℕ) :
    Fin (2*w) → Fin (2*w+(booleanWordMulProgram w).nodes) :=
  fun j => (booleanWordMulProgram w).output ⟨j.val,by have := j.isLt; omega⟩

def booleanWordMulResult (w : ℕ) (a b : Reg w) : Reg (2*w) := fun j =>
  booleanDAGValue (booleanWordMulProgram w).graph (booleanWordAdderInput w a b)
    (booleanWordMulSelect w j)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
