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

/-!
# Length-framed bit strings, lists, and integers

This module defines a unary length prefix and uses it to frame bit strings and lists while
retaining unconsumed suffixes during parsing. The integer codec adds a sign bit to the framed
canonical binary magnitude.

The parser `parseInt` checks canonical magnitude digits and excludes negative zero. These
explicit finite encodings provide a classical data representation in the computational setting
of [KitaevShenVyalyi2002].

## Main statements

* `frame`: The payload preceded by the unary encoding of its length.
* `encodeList`: Encode a list of bit strings by a unary item count followed by the framed items.
* `parseInt`: Parse a sign and framed magnitude, requiring canonical binary digits and excluding
  negative zero, and return the integer with the remaining suffix.

## References

* [Kitaev et al., 2002][KitaevShenVyalyi2002]
-/

set_option autoImplicit false
namespace Qatlib.Foundations.FramedBits.FramedCodec
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The unary representation of `n` as `n` true bits followed by one false bit. -/
def framePrefix (n : ℕ) : List Bool := List.replicate n true++[false]
/-- The payload preceded by the unary encoding of its length. -/
def frame (xs : List Bool) : List Bool := framePrefix xs.length++xs

/-- Parse a unary length terminated by a false bit, returning the length and the remaining bits. -/
def parseLength : List Bool→Option (ℕ×List Bool)
  | [] => none
  | false::rest => some (0,rest)
  | true::rest => (parseLength rest).map fun p => (p.1+1,p.2)

/-- Parse a length-prefixed payload and return it with the remaining suffix, failing if the
payload is too short. -/
def parseFrame (xs : List Bool) : Option (List Bool×List Bool) := do
  let (n,rest) ← parseLength xs
  if n≤rest.length then some (rest.take n,rest.drop n) else none

/-- Encode a list of bit strings by a unary item count followed by the framed items. -/
def encodeList (xss : List (List Bool)) : List Bool := framePrefix xss.length++xss.flatMap frame

/-- Parse a specified number of framed bit strings and return the resulting list with the
remaining suffix. -/
def parseMany : ℕ→List Bool→Option (List (List Bool)×List Bool)
  | 0,xs => some ([],xs)
  | n+1,xs => do
      let (x,rest) ← parseFrame xs
      let (ys,tail) ← parseMany n rest
      some (x::ys,tail)

/-- Parse a unary item count followed by that many framed bit strings. -/
def parseList (xs : List Bool) : Option (List (List Bool)×List Bool) := do
  let (n,rest) ← parseLength xs
  parseMany n rest

/-- Decode a list of bits as a natural number in least-significant-bit-first order. -/
def ofBits : List Bool→ℕ
  | []=>0
  | b::bs=>(if b then 1 else 0)+2*ofBits bs

/-- The canonical binary digits of the absolute value of a signed integer. -/
def magnitude (z : ℤ) : List Bool := Nat.bits z.natAbs
/-- Encode an integer as a negativity bit followed by its framed canonical binary magnitude. -/
def encodeInt (z : ℤ) : List Bool := (decide (z < 0))::frame (magnitude z)

/-- Parse a sign and framed magnitude, requiring canonical binary digits and excluding negative
zero, and return the integer with the remaining suffix. -/
def parseInt (xs : List Bool) : Option (ℤ×List Bool) := do
  let sign ← xs.head?
  let (bs,rest) ← parseFrame xs.tail
  let n := ofBits bs
  if Nat.bits n=bs ∧ (sign=false ∨ n≠0) then
    some ((if sign then -(n:ℤ) else (n:ℤ)),rest)
  else none

end Qatlib.Foundations.FramedBits.FramedCodec
