/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGSignedAdditionData
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

def booleanSignedWordPad {α : Type*} (w extra : ℕ) (zero : α)
    (a : Fin (w+1) → α) : Fin (w+extra+1) → α := fun j =>
  if hj : j.val < w then a (Fin.castSucc ⟨j.val,hj⟩)
  else if j.val < w+extra then zero else a (Fin.last w)

def booleanSignedPairSelect {α : Type*} (w : ℕ) (a b : Fin (w+1) → α) : Fin (2*w+2) → α :=
  fun j => if hj : j.val < w then a (Fin.castSucc ⟨j.val,hj⟩)
    else if hk : j.val < 2*w then b (Fin.castSucc ⟨j.val-w,by omega⟩)
    else if j.val = 2*w then a (Fin.last w) else b (Fin.last w)

def booleanDAGAppendWord {M K m o : ℕ} (g : BooleanDAG M K)
    (r : Fin m → Fin (M+K)) (h : BooleanDAGWord m o) : BooleanDAGWord M o :=
  ⟨K+h.nodes,booleanDAGSplice g r h.graph,
    (fun j => booleanSpliceSource r (h.output j)),booleanSpliceSource r h.zero⟩

def booleanWordSignedDotPair (w : ℕ) (i : Fin 3) : Fin (2*w+2) → Fin (3*(2*w+2)) :=
  fun j => ⟨i.val*(2*w+2)+j.val,by have hi := i.isLt; have hj := j.isLt; nlinarith⟩

def booleanWordSignedDotProgram (w : ℕ) : BooleanDAGWord (3*(2*w+2)) (2*w+3) :=
  let M := 3*(2*w+2)
  let mul := booleanWordSignedMulProgram w
  let p₀ := booleanDAGAppendWord (.nil : BooleanDAG M 0)
    (fun j => Fin.castLE (by omega) (booleanWordSignedDotPair w 0 j)) mul
  let p₁ := booleanDAGAppendWord p₀.graph
    (fun j => Fin.castLE (by omega) (booleanWordSignedDotPair w 1 j)) mul
  let p₂ := booleanDAGAppendWord p₁.graph
    (fun j => Fin.castLE (by omega) (booleanWordSignedDotPair w 2 j)) mul
  let first : Fin (2*w+1) → Fin (M+p₂.nodes) := fun j =>
    Fin.castLE (by change M+p₀.nodes ≤ M+(p₀.nodes+mul.nodes+mul.nodes); omega) (p₀.output j)
  let second : Fin (2*w+1) → Fin (M+p₂.nodes) := fun j =>
    Fin.castLE (by change M+p₁.nodes ≤ M+(p₁.nodes+mul.nodes); omega) (p₁.output j)
  let sum := booleanDAGAppendWord p₂.graph (booleanSignedPairSelect (2*w) first second)
    (booleanWordSignedAddProgram (2*w))
  let third : Fin (2*w+1) → Fin (M+sum.nodes) := fun j =>
    Fin.castLE (by change M+p₂.nodes ≤ M+(p₂.nodes+(booleanWordSignedAddProgram (2*w)).nodes); omega)
      (p₂.output j)
  booleanDAGAppendWord sum.graph
    (booleanSignedPairSelect (2*w+1) sum.output (booleanSignedWordPad (2*w) 1 sum.zero third))
    (booleanWordSignedAddProgram (2*w+1))

def booleanWordSignedDotView (w : ℕ) (x : Reg (3*(2*w+2))) (i : Fin 3) : Reg (2*w+2) :=
  fun j => x (booleanWordSignedDotPair w i j)

def booleanWordSignedDotResult (w : ℕ) (x : Reg (3*(2*w+2))) : Reg (2*w+3) := fun j =>
  booleanDAGValue (booleanWordSignedDotProgram w).graph x ((booleanWordSignedDotProgram w).output j)

def booleanWordSignedDotValue (w : ℕ) (x : Reg (3*(2*w+2))) : ℤ :=
  booleanWordSignedValue (2*w+2) (fun j => booleanWordSignedDotResult w x j.castSucc)
    (booleanWordSignedDotResult w x (Fin.last (2*w+2)))

end Qatlib.Concepts.MatrixAccess.RitzPipeline
