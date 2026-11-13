/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdderData

/-!
# Boolean graph data for conditional subtraction

This module constructs a ripple-borrow subtraction graph and then selects either the difference
or the original first word according to the final borrow. `booleanWordCondSubDAG` adds a flag
indicating that no borrow occurred, and `booleanWordCondSubResult` evaluates the selected word
and flag.

The graph supplies the arithmetic data for reversible compilation in the circuit setting of
[NielsenChuang2010].

## Main statements

* `booleanWordSubPrefix`: builds the subtraction stages.
* `booleanWordCondSubPrefix`: adds the conditional output-bit selections.
* `booleanWordCondSubSelect`: selects the result bits and no-borrow flag.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath

namespace Qatlib.Concepts.MatrixAccess.RitzPipeline
set_option autoImplicit false

/-- The first i ripple-borrow subtraction stages on two w-bit inputs, with a false initial
borrow and seven nodes per stage. -/
def booleanWordSubPrefix (w : ℕ) : (i : ℕ) → i ≤ w → BooleanDAG (2*w) (7*i+1)
  | 0, _ => .snoc .nil (.constant false)
  | i+1, hi =>
    let g₀ := booleanWordSubPrefix w i (by omega)
    let g₁ := g₀.snoc (.xor ⟨i,by omega⟩ ⟨w+i,by omega⟩)
    let g₂ := g₁.snoc (.xor ⟨2*w+7*i+1,by omega⟩ ⟨2*w+7*i,by omega⟩)
    let g₃ := g₂.snoc (.neg ⟨i,by omega⟩)
    let g₄ := g₃.snoc (.conj ⟨2*w+7*i+3,by omega⟩ ⟨w+i,by omega⟩)
    let g₅ := g₄.snoc (.neg ⟨2*w+7*i+1,by omega⟩)
    let g₆ := g₅.snoc (.conj ⟨2*w+7*i+5,by omega⟩ ⟨2*w+7*i,by omega⟩)
    let g₇ := g₆.snoc (.xor ⟨2*w+7*i+4,by omega⟩ ⟨2*w+7*i+6,by omega⟩)
    by simpa only [Nat.mul_succ,Nat.add_assoc] using g₇

/-- Extends the completed subtraction graph with i conditional bit selections, retaining the
first input on borrow and choosing the difference otherwise. -/
def booleanWordCondSubPrefix (w : ℕ) :
    (i : ℕ) → i ≤ w → BooleanDAG (2*w) (7*w+1+3*i)
  | 0, _ => booleanWordSubPrefix w w (Nat.le_refl w)
  | i+1, hi =>
    let g₀ := booleanWordCondSubPrefix w i (by omega)
    let g₁ := g₀.snoc (.xor ⟨i,by omega⟩ ⟨2*w+7*i+2,by omega⟩)
    let g₂ := g₁.snoc (.conj ⟨2*w+(7*w+1+3*i),by omega⟩ ⟨2*w+7*w,by omega⟩)
    let g₃ := g₂.snoc (.xor ⟨2*w+7*i+2,by omega⟩ ⟨2*w+(7*w+1+3*i)+1,by omega⟩)
    by simpa only [Nat.mul_succ,Nat.add_assoc] using g₃

/-- The complete conditional-subtraction graph, including all selected result bits and the
negation of the final borrow as a flag. -/
def booleanWordCondSubDAG (w : ℕ) : BooleanDAG (2*w) (7*w+1+3*w+1) :=
  (booleanWordCondSubPrefix w w (Nat.le_refl w)).snoc (.neg ⟨2*w+7*w,by omega⟩)

/-- Selects the w conditional result bits followed by the no-borrow flag from the evaluated
graph. -/
def booleanWordCondSubSelect (w : ℕ) : Fin (w+1) → Fin (2*w+(7*w+1+3*w+1)) := fun j =>
  if hj : j.val < w then ⟨2*w+(7*w+1+3*j.val)+2,by omega⟩
  else ⟨2*w+10*w+1,by omega⟩

/-- The w+1-bit result and flag obtained by evaluating the conditional-subtraction graph on the
two input words. -/
def booleanWordCondSubResult (w : ℕ) (a b : Reg w) : Reg (w+1) := fun j =>
  booleanDAGValue (booleanWordCondSubDAG w) (booleanWordAdderInput w a b)
    (booleanWordCondSubSelect w j)

end Qatlib.Concepts.MatrixAccess.RitzPipeline
