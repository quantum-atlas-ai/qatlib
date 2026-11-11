/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.DegreeMethod.ClassicalQuery
import Qatlib.Foundations.PureStateMath.Qubit

/-!
# Boolean oracle transcript definitions

This module defines `runTrace`, which evaluates a Boolean query tree while recording its visited
query-answer pairs. It also defines query readdressing and the prefix encoding that combines two
Boolean oracles into one oracle on a register with one additional bit.

The mathematical background is described in [NielsenChuang2010].

## Main statements

* `runTrace`: output and ordered query-answer log.
* `readdress`: recursive relabeling of query addresses.
* `packedOracle`: a single oracle selected by a prefix bit.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib
open Qatlib

set_option autoImplicit false
namespace Qatlib.Concepts.QueryTranscript.Transcript
open Qatlib

/-- Executes a Boolean query tree and returns its output together with the ordered list of
queried addresses and oracle answers. -/
def runTrace {Query Output : Type} (A : Query → Bool) :
    BoolQueryTree Query Output → Output × List (Query × Bool)
  | .halt y => (y, [])
  | .ask a no yes =>
      let b := A a
      let r := if b then runTrace A yes else runTrace A no
      (r.1, (a, b) :: r.2)

/-- Relabels every query in a Boolean query tree by a given address map, preserving its
branching structure and outputs. -/
def readdress {Query Target Output : Type} (f : Query → Target) :
    BoolQueryTree Query Output → BoolQueryTree Target Output
  | .halt y => .halt y
  | .ask a no yes => .ask (f a) (readdress f no) (readdress f yes)

/-- Selects one of two Boolean oracles using the Boolean component of a tagged address. -/
def pairOracle {n : ℕ} (S U : Reg n → Bool) (a : Bool × Reg n) : Bool :=
  if a.1 then U a.2 else S a.2

/-- Packs a Boolean tag and an `n`-bit register into an `(n + 1)`-bit register by prefixing the
tag. -/
def packAddress {n : ℕ} (a : Bool × Reg n) : Reg (n + 1) := Fin.cons a.1 a.2

/-- Evaluates the oracle selected by the first address bit at the remaining register bits. -/
def packedOracle {n : ℕ} (S U : Reg n → Bool) (a : Reg (n + 1)) : Bool :=
  if a 0 then U (fun i => a i.succ) else S (fun i => a i.succ)

end Qatlib.Concepts.QueryTranscript.Transcript
