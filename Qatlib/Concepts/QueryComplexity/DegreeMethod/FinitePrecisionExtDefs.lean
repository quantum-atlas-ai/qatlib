/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionEffective
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

def frame : Bits → Bits
  | [] => [false]
  | b :: bs => true :: b :: frame bs

def mulInput (x y : Bits) : Bits := (frame x ++ y).reverse

theorem frame_length (x : Bits) : (frame x).length = 2*x.length+1 := by
  induction x with
  | nil => rfl
  | cons b bs ih => simp only [frame,List.length_cons,ih]; omega

theorem mulInput_length (x y : Bits) : (mulInput x y).length = 2*x.length+y.length+1 := by
  simp only [mulInput,List.length_reverse,List.length_append,frame_length]
  omega

inductive Label where
  | parse
  | payload
  | multiplier
  | multiply : MulLabel → Label
  | clear
  | output
  deriving DecidableEq, Fintype

instance : Inhabited Label := ⟨.parse⟩

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

def sourceSteps (x y : Bits) : ℕ :=
  (2*x.length+1)+(y.length+1)+(mulTotalTicks x y y.length+2)+
    (x.length+1)+((mulAcc x y y.length).length+1)

end Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionExtDefs
