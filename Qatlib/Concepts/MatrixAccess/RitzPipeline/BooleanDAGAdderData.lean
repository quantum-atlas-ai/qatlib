/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGData
import Qatlib.Concepts.ClusterPatterns.AdaptiveEuler.CountedClusterSequence

/-!
# Boolean graph data for unsigned word addition

This module defines unsigned words with the least significant bit first and constructs a
ripple-carry Boolean graph for addition. `booleanWordAdderDAG` has 5w + 1 nodes, and
`booleanWordAdderSelect` selects the w sum bits and final carry.

These data support reversible arithmetic in the circuit model of [NielsenChuang2010].

## Main statements

* `booleanWordLSBValue`: decodes an unsigned word.
* `booleanWordAdderPrefix`: builds a partial ripple-carry graph.
* `booleanWordAdderResult`: evaluates the selected sum and carry bits.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- The unsigned natural-number value of a word indexed with the least significant bit first. -/
def booleanWordLSBValue (w : ℕ) (a : Reg w) : ℕ :=
  (bitVecEquiv w (fun j => a (Fin.rev j))).val

/-- Concatenates two w-bit words into the 2w-bit input of the adder graph. -/
def booleanWordAdderInput (w : ℕ) (a b : Reg w) : Reg (2*w) := fun i =>
  if h : i.val < w then a ⟨i.val,h⟩ else b ⟨i.val-w,by omega⟩

/-- Extracts the first w-bit word from a combined adder input. -/
def booleanWordAdderLeft (w : ℕ) (x : Reg (2*w)) : Reg w := fun i =>
  x ⟨i.val,by have := i.isLt; omega⟩

/-- Extracts the second w-bit word from a combined adder input. -/
def booleanWordAdderRight (w : ℕ) (x : Reg (2*w)) : Reg w := fun i =>
  x ⟨w+i.val,by have := i.isLt; omega⟩

/-- The first i ripple-carry addition stages, with one initial false carry node and five nodes
per stage. -/
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

/-- The full Boolean graph for adding two w-bit words, containing 5w + 1 nodes. -/
def booleanWordAdderDAG (w : ℕ) : BooleanDAG (2*w) (5*w+1) :=
  booleanWordAdderPrefix w w (Nat.le_refl w)

/-- Selects the w sum bits followed by the final carry from the evaluated adder graph. -/
def booleanWordAdderSelect (w : ℕ) : Fin (w+1) → Fin ((2*w)+(5*w+1)) := fun j =>
  if h : j.val < w then ⟨2*w+5*j.val+2,by omega⟩
  else ⟨2*w+5*w,by omega⟩

/-- The w+1-bit word obtained by evaluating the selected outputs of the adder graph. -/
def booleanWordAdderResult (w : ℕ) (a b : Reg w) : Reg (w+1) := fun j =>
  booleanDAGValue (booleanWordAdderDAG w) (booleanWordAdderInput w a b)
    (booleanWordAdderSelect w j)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
