/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.IntWordFraming.WordFraming.SmithNormalizationDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
namespace Qatlib.Concepts.IntWordFraming.WordFraming
open Qatlib.Concepts.IntWordFraming.WordFraming

def encodeInt (z : ℤ) : List Bool :=
  List.replicate z.natAbs.bits.length true ++ [false, decide (z < 0)] ++ z.natAbs.bits
def decodeInt (bs : List Bool) : Option (ℤ × List Bool) :=
  let (header, rest) := bs.span id
  match rest with
  | false :: sign :: tail =>
      if header.length ≤ tail.length then
        some (smithDecodeInteger (sign,tail.take header.length),tail.drop header.length)
      else none
  | _ => none
def encodeWords (zs : List ℤ) : List Bool := zs.flatMap encodeInt
def decodeWords : ℕ → List Bool → Option (List ℤ × List Bool)
  | 0, bs => some ([],bs)
  | n+1, bs => do
      let (z,rest) ← decodeInt bs
      let (zs,tail) ← decodeWords n rest
      pure (z::zs,tail)
end Qatlib.Concepts.IntWordFraming.WordFraming
