/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.List.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Nat.Bits

set_option autoImplicit false
namespace Qatlib.Foundations.FramedBits.FramedCodec
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

def framePrefix (n : ℕ) : List Bool := List.replicate n true++[false]
def frame (xs : List Bool) : List Bool := framePrefix xs.length++xs

def parseLength : List Bool→Option (ℕ×List Bool)
  | [] => none
  | false::rest => some (0,rest)
  | true::rest => (parseLength rest).map fun p => (p.1+1,p.2)

def parseFrame (xs : List Bool) : Option (List Bool×List Bool) := do
  let (n,rest) ← parseLength xs
  if n≤rest.length then some (rest.take n,rest.drop n) else none

def encodeList (xss : List (List Bool)) : List Bool := framePrefix xss.length++xss.flatMap frame

def parseMany : ℕ→List Bool→Option (List (List Bool)×List Bool)
  | 0,xs => some ([],xs)
  | n+1,xs => do
      let (x,rest) ← parseFrame xs
      let (ys,tail) ← parseMany n rest
      some (x::ys,tail)

def parseList (xs : List Bool) : Option (List (List Bool)×List Bool) := do
  let (n,rest) ← parseLength xs
  parseMany n rest

def ofBits : List Bool→ℕ
  | []=>0
  | b::bs=>(if b then 1 else 0)+2*ofBits bs

def magnitude (z : ℤ) : List Bool := Nat.bits z.natAbs
def encodeInt (z : ℤ) : List Bool := (decide (z < 0))::frame (magnitude z)

def parseInt (xs : List Bool) : Option (ℤ×List Bool) := do
  let sign ← xs.head?
  let (bs,rest) ← parseFrame xs.tail
  let n := ofBits bs
  if Nat.bits n=bs ∧ (sign=false ∨ n≠0) then
    some ((if sign then -(n:ℤ) else (n:ℤ)),rest)
  else none

end Qatlib.Foundations.FramedBits.FramedCodec
