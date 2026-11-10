/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGData
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.CountedClusterSequence
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

def booleanWordLSBValue (w : ℕ) (a : Reg w) : ℕ :=
  (bitVecEquiv w (fun j => a (Fin.rev j))).val

def booleanWordAdderInput (w : ℕ) (a b : Reg w) : Reg (2*w) := fun i =>
  if h : i.val < w then a ⟨i.val,h⟩ else b ⟨i.val-w,by omega⟩

def booleanWordAdderLeft (w : ℕ) (x : Reg (2*w)) : Reg w := fun i =>
  x ⟨i.val,by have := i.isLt; omega⟩

def booleanWordAdderRight (w : ℕ) (x : Reg (2*w)) : Reg w := fun i =>
  x ⟨w+i.val,by have := i.isLt; omega⟩

def booleanWordAdderPrefix (w : ℕ) : (i : ℕ) → (i ≤ w) → BooleanDAG (2*w) (5*i+1)
  | 0, _ => .snoc .nil (.constant false)
  | i+1, hi =>
    let g₀ := booleanWordAdderPrefix w i (by omega)
    let g₁ := g₀.snoc (.xor ⟨i,by omega⟩ ⟨w+i,by omega⟩)
    let g₂ := g₁.snoc (.xor ⟨2*w+5*i+1,by omega⟩ ⟨2*w+5*i,by omega⟩)
    let g₃ := g₂.snoc (.conj ⟨i,by omega⟩ ⟨w+i,by omega⟩)
    let g₄ := g₃.snoc (.conj ⟨2*w+5*i+1,by omega⟩ ⟨2*w+5*i,by omega⟩)
    let g₅ := g₄.snoc (.xor ⟨2*w+5*i+3,by omega⟩ ⟨2*w+5*i+4,by omega⟩)
    by simpa only [Nat.mul_succ,Nat.add_assoc] using g₅

def booleanWordAdderDAG (w : ℕ) : BooleanDAG (2*w) (5*w+1) :=
  booleanWordAdderPrefix w w (Nat.le_refl w)

def booleanWordAdderSelect (w : ℕ) : Fin (w+1) → Fin ((2*w)+(5*w+1)) := fun j =>
  if h : j.val < w then ⟨2*w+5*j.val+2,by omega⟩
  else ⟨2*w+5*w,by omega⟩

def booleanWordAdderResult (w : ℕ) (a b : Reg w) : Reg (w+1) := fun j =>
  booleanDAGValue (booleanWordAdderDAG w) (booleanWordAdderInput w a b)
    (booleanWordAdderSelect w j)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
