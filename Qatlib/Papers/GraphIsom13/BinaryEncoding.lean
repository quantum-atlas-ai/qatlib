/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphIsom13.GiCost
import Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryWords

/-!
# Binary encoding of graph-isomorphism strings

This module groups a flat Boolean register into fixed-width blocks and parses each block into an
integer-string entry. The equivalence `parseEquiv` transports the graph-isomorphism cost of
[GaitanClark2014] to `bitCost` without changing whether a zero-cost witness exists.

## Main statements

* `parse_value`: the positional binary value of each parsed block.
* `bitCost_zero_iff`: zero binary cost characterizes graph isomorphism.

## References

* [Gaitan and Clark, 2014][GaitanClark2014]
-/

set_option warningAsError false

namespace Qatlib.Papers.GraphIsom13.BinaryEncoding
set_option autoImplicit false
noncomputable section
open Qatlib.Papers.GraphIsom13.GiCost
open Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryWords

/-- The Boolean register of length `N * encBits N` used to encode an integer string. -/
abbrev Bits (N : ℕ) := Fin (N * encBits N) → Bool

/-- Regroup a flat Boolean register into `N` blocks of `encBits N` bits. -/
def splitEquiv (N : ℕ) : Bits N ≃ (Fin N → Fin (encBits N) → Bool) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl Bool)).trans (Equiv.curry _ _ _)

/-- The equivalence parsing each fixed-width bit block as an integer-string entry. -/
def parseEquiv (N : ℕ) : Bits N ≃ IntStr N :=
  (splitEquiv N).trans (Equiv.piCongrRight fun _ => blockEquiv (encBits N))

/-- The bit at block position `(i, j)` is the flat bit at the corresponding product index. -/
theorem split_address (N : ℕ) (b : Bits N) (i : Fin N) (j : Fin (encBits N)) :
    splitEquiv N b i j = b (finProdFinEquiv (i,j)) := rfl

/-- Each parsed entry is the sum of its bits weighted by powers `2^j`, with bit position `j` as
the binary exponent [GaitanClark2014]. -/
theorem parse_value (N : ℕ) (b : Bits N) (i : Fin N) :
    (parseEquiv N b i).val = ∑ j : Fin (encBits N),
      bitValue (b (finProdFinEquiv (i,j))) * 2^j.val := blockEquiv_value _ _

/-- Parsing the Boolean register into an integer string is bijective. -/
theorem parse_bijective (N : ℕ) : Function.Bijective (parseEquiv N) := (parseEquiv N).bijective

/-- The graph-isomorphism cost of the integer string parsed from a Boolean register. -/
def bitCost {N : ℕ} (G G' : SimpleGraph (Fin N)) [DecidableRel G.Adj] [DecidableRel G'.Adj]
    (b : Bits N) : ℕ := cost G G' (parseEquiv N b)

/-- A zero-cost Boolean register exists if and only if the two graphs are isomorphic. -/
theorem bitCost_zero_iff {N : ℕ} (G G' : SimpleGraph (Fin N))
    [DecidableRel G.Adj] [DecidableRel G'.Adj] :
    (∃ b : Bits N, bitCost G G' b = 0) ↔ Nonempty (G ≃g G') := by
  rw [← gi_cop_zero_iff G G']
  constructor
  · rintro ⟨b,hb⟩; exact ⟨parseEquiv N b,hb⟩
  · rintro ⟨s,hs⟩
    exact ⟨(parseEquiv N).symm s,by simpa [bitCost] using hs⟩
end
end Qatlib.Papers.GraphIsom13.BinaryEncoding
