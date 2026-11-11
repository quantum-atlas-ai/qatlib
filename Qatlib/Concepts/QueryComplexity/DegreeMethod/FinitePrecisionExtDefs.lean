/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionEffective

/-!
# Encoded multiplication stack program

This module defines `frame`, a bit encoding with a false terminator, and `mulInput`, the
reversed concatenation of a framed multiplicand and a multiplier. The length identities give
explicit sizes for these encodings in the classical computational setting discussed in
[KitaevShenVyalyi2002].

The six-stack `program` parses the input, invokes the multiplication subroutine, clears the
multiplicand stack, and transfers the result to the output stack. The definition `sourceSteps`
records the combined source-step count for these phases.

## Main statements

* `frame` and `mulInput`: the encodings used by the multiplication program.
* `frame_length` and `mulInput_length`: exact encoding lengths.
* `program`: the parser, multiplication call, cleanup, and output instructions.
* `sourceSteps`: the combined source-step count.

## References

* [Kitaev, Shen, and Vyalyi, 2002][KitaevShenVyalyi2002]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false


open Qatlib.Concepts.BitWordCompiler.CanonicalCodec
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Cleanup
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.Increment
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM.TableCopy
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

namespace Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs

open Turing
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec (Bits binaryValue)
open Qatlib
open Qatlib.Concepts.BitWordCompiler.CanonicalCodec.TM

deriving instance Fintype for MulVar
instance : Inhabited MulVar := ⟨MulVar.init⟩

/-- The self-delimiting bit encoding that represents each payload bit by true followed by that
bit and terminates with false. -/
def frame : Bits → Bits
  | [] => [false]
  | b :: bs => true :: b :: frame bs

/-- The multiplication input obtained by reversing the concatenation of `frame x` and `y`. -/
def mulInput (x y : Bits) : Bits := (frame x ++ y).reverse

/-- The encoded word `frame x` has length `2 * x.length + 1`. -/
theorem frame_length (x : Bits) : (frame x).length = 2*x.length+1 := by
  induction x with
  | nil => rfl
  | cons b bs ih => simp only [frame,List.length_cons,ih]; omega

/-- The encoded multiplication input has length `2 * x.length + y.length + 1`. -/
theorem mulInput_length (x y : Bits) : (mulInput x y).length = 2*x.length+y.length+1 := by
  simp only [mulInput,List.length_reverse,List.length_append,frame_length]
  omega

/-- The control labels for parsing the two inputs, calling multiplication, clearing a stack, and
producing output. -/
inductive Label where
  | parse
  | payload
  | multiplier
  | multiply : MulLabel → Label
  | clear
  | output
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.parse⟩

/-- A six-stack program that decodes the framed multiplicand and multiplier, invokes
`mulProgram`, clears the multiplicand stack, and transfers the result to output. -/
def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label MulVar
  | .parse => .pop 5 MulVar.readMbit
      (.branch (fun v => v.mbit.getD false)
        (.goto (fun _ => .payload))
        (.load (fun _ => MulVar.init) (.goto (fun _ => .multiplier))))
  | .payload => .pop 5 MulVar.readMbit
      (.push 3 (fun v => v.mbit.getD false)
        (.load (fun _ => MulVar.init) (.goto (fun _ => .parse))))
  | .multiplier => .pop 5 MulVar.readMbit
      (.branch (fun v => v.mbit.isSome)
        (.push 4 (fun v => v.mbit.getD false)
          (.load (fun _ => MulVar.init) (.goto (fun _ => .multiplier))))
        (.load (fun _ => MulVar.init) (.goto (fun _ => .multiply .outer))))
  | .multiply l => StackCall.stmt id Label.multiply .clear id (fun _ v => v) (mulProgram l)
  | .clear => .pop 3 MulVar.readMbit
      (.branch (fun v => v.mbit.isSome)
        (.goto (fun _ => .clear))
        (.load (fun _ => MulVar.init) (.goto (fun _ => .output))))
  | .output => .pop 0 MulVar.readMbit
      (.branch (fun v => v.mbit.isSome)
        (.push 2 (fun v => v.mbit.getD false) (.goto (fun _ => .output)))
        (.load (fun _ => MulVar.init) .halt))

/-- The source-step count comprising input parsing, multiplication, multiplicand cleanup, and
result transfer. -/
def sourceSteps (x y : Bits) : ℕ :=
  (2*x.length+1)+(y.length+1)+(mulTotalTicks x y y.length+2)+
    (x.length+1)+((mulAcc x y y.length).length+1)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs
