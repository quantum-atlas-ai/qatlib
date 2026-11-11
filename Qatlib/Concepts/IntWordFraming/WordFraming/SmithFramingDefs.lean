/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.IntWordFraming.WordFraming.SmithNormalizationDefs

/-!
# Self-delimiting integer word encodings

This module defines `encodeInt` using a unary magnitude-length prefix, a false delimiter, a sign
bit, and binary magnitude bits. `decodeInt` returns the decoded value together with the unused
suffix; `encodeWords` and `decodeWords` extend this interface to lists. The encodings provide a
bit representation for integer presentation data in finite Abelian group computations
[CheungMosca2001].

## Main statements

* `encodeInt`: frame a signed integer as a Boolean list.
* `decodeWords`: decode a specified number of framed integers.

## References

* [Cheung and Mosca, 2001][CheungMosca2001]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.IntWordFraming.WordFraming

/-- Encode an integer by a unary magnitude-length prefix, a false delimiter, a sign bit, and its
binary magnitude. -/
def encodeInt (z : ℤ) : List Bool :=
  List.replicate z.natAbs.bits.length true ++ [false, decide (z < 0)] ++ z.natAbs.bits
/-- Decode one framed integer and return its unused suffix, failing if the delimiter, sign bit,
or magnitude payload is incomplete. -/
def decodeInt (bs : List Bool) : Option (ℤ × List Bool) :=
  let (header, rest) := bs.span id
  match rest with
  | false :: sign :: tail =>
      if header.length ≤ tail.length then
        some (smithDecodeInteger (sign,tail.take header.length),tail.drop header.length)
      else none
  | _ => none
/-- Concatenate the framed encodings of a list of integers. -/
def encodeWords (zs : List ℤ) : List Bool := zs.flatMap encodeInt
/-- Decode the specified number of framed integers, returning their list and the unused suffix
when all decodings succeed. -/
def decodeWords : ℕ → List Bool → Option (List ℤ × List Bool)
  | 0, bs => some ([],bs)
  | n+1, bs => do
      let (z,rest) ← decodeInt bs
      let (zs,tail) ← decodeWords n rest
      pure (z::zs,tail)
end Qatlib.Concepts.IntWordFraming.WordFraming
