/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CurveGroups.AffineAdd.NativeCurve
import Mathlib.GroupTheory.Perm.ViaEmbedding
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.BitVec
import Mathlib.Data.FinEnum
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Fin

/-!
# Field encodings and reversible arithmetic oracles

This module defines `FieldEncoding`, which embeds field elements into fixed width bit vectors
and preserves zero. It transports field permutations to bit vectors, defines XOR computation and
uncomputation, and specifies the affine point addition register schedule `xorPointRun`. The
schedule is motivated by [RoettelerEtAl2017].

## Main statements

* `encodedPerm_apply`: transported permutations agree on encoded values.
* `xorBits_uncompute`: XOR erases a matching encoded value.
* `xorPointRun`: the register computation for affine addition.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

/-- An embedding of a field into width `w` bit vectors with a decoding left inverse and an
encoding that preserves zero. -/
structure FieldEncoding (K : Type*) [Field K] (w : ℕ) where

  encode : K ↪ BitVec w

  decode : BitVec w → K

  decode_encode : ∀ x, decode (encode x) = x

  encode_zero : encode 0 = 0

variable {K : Type*} [Field K] {w : ℕ}

/-- Extend a field permutation along its bit encoding to a permutation of all width `w` bit
vectors. -/
noncomputable def encodedPerm (E : FieldEncoding K w) (p : Equiv.Perm K) :
    Equiv.Perm (BitVec w) := p.viaEmbedding E.encode

/-- The extended permutation maps an encoded field value to the encoding of its image. -/
theorem encodedPerm_apply (E : FieldEncoding K w) (p : Equiv.Perm K) (x : K) :
    encodedPerm E p (E.encode x) = E.encode (p x) :=
  Equiv.Perm.viaEmbedding_apply p E.encode x

/-- The bit vector permutation extending field translation by `c`. -/
noncomputable def shiftBits (E : FieldEncoding K w) (c : K) : Equiv.Perm (BitVec w) :=
  encodedPerm E (Equiv.addRight c)

/-- Translation on encoded values agrees with encoding the field sum `x + c`. -/
theorem shiftBits_apply (E : FieldEncoding K w) (c x : K) :
    shiftBits E c (E.encode x) = E.encode (x + c) :=
  encodedPerm_apply E (Equiv.addRight c) x

/-- The bit vector permutation extending field negation. -/
noncomputable def negateBits (E : FieldEncoding K w) : Equiv.Perm (BitVec w) :=
  encodedPerm E (Equiv.neg K)

/-- Bit negation on an encoded value yields the encoding of its field negative. -/
theorem negateBits_apply (E : FieldEncoding K w) (x : K) :
    negateBits E (E.encode x) = E.encode (-x) :=
  encodedPerm_apply E (Equiv.neg K) x

/-- The involutive bit vector permutation that XORs with the encoding of `f`. -/
def xorBits (E : FieldEncoding K w) (f : K) : Equiv.Perm (BitVec w) where
  toFun y := E.encode f ^^^ y
  invFun y := E.encode f ^^^ y
  left_inv y := by
    dsimp only
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  right_inv y := by
    dsimp only
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

/-- XOR with the encoding of `f` computes that encoding from encoded zero. -/
theorem xorBits_clean (E : FieldEncoding K w) (f : K) :
    xorBits E f (E.encode 0) = E.encode f := by
  simp [xorBits, E.encode_zero]

/-- XOR with the encoding of `f` computes that encoding from the zero bit vector. -/
theorem xorBits_zero (E : FieldEncoding K w) (f : K) :
    xorBits E f 0 = E.encode f := by
  simp [xorBits]

/-- XOR with the encoding of `f` erases that same encoding to encoded zero. -/
theorem xorBits_uncompute (E : FieldEncoding K w) (f : K) :
    xorBits E f (E.encode f) = E.encode 0 := by
  simp [xorBits, E.encode_zero]

/-- Four width `w` bit vector registers for the two coordinates, slope, and temporary value. -/
structure BitRegisters (w : ℕ) where

  x : BitVec w

  y : BitVec w

  lam : BitVec w

  temp : BitVec w
  deriving DecidableEq, Fintype

/-- Execute the encoded affine addition schedule with zero initial slope and temporary
registers. -/
noncomputable def xorPointRun (E : FieldEncoding K w) (x2 y2 : K)
    (x1 y1 : BitVec w) : BitRegisters w :=
  let x := shiftBits E (-x2) x1
  let y := shiftBits E (-y2) y1
  let t := xorBits E (E.decode x)⁻¹ 0
  let l := xorBits E (E.decode y * E.decode t) 0
  let y := xorBits E (E.decode l * E.decode x) y
  let t := xorBits E (E.decode x)⁻¹ t
  let t := xorBits E (E.decode l ^ 2) t
  let x := shiftBits E (-E.decode t) x
  let x := shiftBits E (3 * x2) x
  let t := xorBits E (E.decode l ^ 2) t
  let y := xorBits E (E.decode l * E.decode x) y
  let t := xorBits E (E.decode x)⁻¹ t
  let l := xorBits E (E.decode t * E.decode y) l
  let t := xorBits E (E.decode x)⁻¹ t
  let x := negateBits E x
  let y := shiftBits E (-y2) y
  let x := shiftBits E x2 x
  ⟨x, y, l, t⟩

end Qatlib.Concepts.CurveGroups.AffineAdd
