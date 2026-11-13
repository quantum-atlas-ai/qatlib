/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MatrixAccess.RitzPipeline.BooleanDAGAdder

/-!
# Low-bit truncation of Boolean words

`booleanWordLow` restricts a Boolean word to its least significant positions. The value theorem
identifies this restriction with reduction modulo a power of two, providing a word-arithmetic
identity for the PRN circuit implementation associated with [KanekoEtAl2020].

## Main statements

* `boolean_word_low_value`: identifies low-bit extraction with reduction modulo `2 ^ m`.

## References

* [Kaneko et al., 2020][KanekoEtAl2020]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MatrixAccess.RitzPipeline
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
namespace Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
open Matrix
open scoped Classical BigOperators
set_option autoImplicit false

/-- Restrict a word of width `W` to its first `m` bit positions, assuming `m ≤ W`. -/
def booleanWordLow (W m : ℕ) (hm : m ≤ W) (a : Reg W) : Reg m := fun j => a (Fin.castLE hm j)

/-- The unsigned little-endian value of the low `m` bits equals the full word value modulo `2 ^
m`. -/
theorem boolean_word_low_value (W m : ℕ) (hm : m ≤ W) (a : Reg W) :
    booleanWordLSBValue m (booleanWordLow W m hm a) = booleanWordLSBValue W a % 2^m := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hm
  let low := booleanWordLSBValue m (booleanWordLow (m+k) m hm a)
  let high := booleanWordLSBValue k (fun j => a (Fin.natAdd m j))
  have hlt : low < 2^m := (bitVecEquiv m (fun j => booleanWordLow (m+k) m hm a (Fin.rev j))).isLt
  have hs : booleanWordLSBValue (m+k) a = low + 2^m*high := by
    rw [boolean_word_lsb_value,Fin.sum_univ_add]
    change _ = booleanWordLSBValue m (booleanWordLow (m+k) m hm a)+
      2^m*booleanWordLSBValue k (fun j => a (Fin.natAdd m j))
    rw [boolean_word_lsb_value,boolean_word_lsb_value,Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    simp only [Fin.val_natAdd,pow_add]
    ring
  change low = _
  simp only [hs,Nat.add_mod,Nat.mul_mod_right,Nat.add_zero,Nat.mod_eq_of_lt hlt]
end Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
