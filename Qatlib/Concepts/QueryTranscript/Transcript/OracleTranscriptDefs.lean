/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Foundations.PureStateMath.Qubit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.QueryTranscript.Transcript
open Qatlib

def runTrace {Query Output : Type} (A : Query → Bool) :
    BoolQueryTree Query Output → Output × List (Query × Bool)
  | .halt y => (y, [])
  | .ask a no yes =>
      let b := A a
      let r := if b then runTrace A yes else runTrace A no
      (r.1, (a, b) :: r.2)

def readdress {Query Target Output : Type} (f : Query → Target) :
    BoolQueryTree Query Output → BoolQueryTree Target Output
  | .halt y => .halt y
  | .ask a no yes => .ask (f a) (readdress f no) (readdress f yes)

def pairOracle {n : ℕ} (S U : Reg n → Bool) (a : Bool × Reg n) : Bool :=
  if a.1 then U a.2 else S a.2

def packAddress {n : ℕ} (a : Bool × Reg n) : Reg (n + 1) := Fin.cons a.1 a.2

def packedOracle {n : ℕ} (S U : Reg n → Bool) (a : Reg (n + 1)) : Bool :=
  if a 0 then U (fun i => a i.succ) else S (fun i => a i.succ)

end Qatlib.Concepts.QueryTranscript.Transcript
