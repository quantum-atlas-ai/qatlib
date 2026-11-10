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

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

structure FieldEncoding (K : Type*) [Field K] (w : ℕ) where

  encode : K ↪ BitVec w

  decode : BitVec w → K

  decode_encode : ∀ x, decode (encode x) = x

  encode_zero : encode 0 = 0

variable {K : Type*} [Field K] {w : ℕ}

noncomputable def encodedPerm (E : FieldEncoding K w) (p : Equiv.Perm K) :
    Equiv.Perm (BitVec w) := p.viaEmbedding E.encode

theorem encodedPerm_apply (E : FieldEncoding K w) (p : Equiv.Perm K) (x : K) :
    encodedPerm E p (E.encode x) = E.encode (p x) :=
  Equiv.Perm.viaEmbedding_apply p E.encode x

noncomputable def shiftBits (E : FieldEncoding K w) (c : K) : Equiv.Perm (BitVec w) :=
  encodedPerm E (Equiv.addRight c)

theorem shiftBits_apply (E : FieldEncoding K w) (c x : K) :
    shiftBits E c (E.encode x) = E.encode (x + c) :=
  encodedPerm_apply E (Equiv.addRight c) x

noncomputable def negateBits (E : FieldEncoding K w) : Equiv.Perm (BitVec w) :=
  encodedPerm E (Equiv.neg K)

theorem negateBits_apply (E : FieldEncoding K w) (x : K) :
    negateBits E (E.encode x) = E.encode (-x) :=
  encodedPerm_apply E (Equiv.neg K) x

def xorBits (E : FieldEncoding K w) (f : K) : Equiv.Perm (BitVec w) where
  toFun y := E.encode f ^^^ y
  invFun y := E.encode f ^^^ y
  left_inv y := by
    dsimp only
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  right_inv y := by
    dsimp only
    rw [← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]

theorem xorBits_clean (E : FieldEncoding K w) (f : K) :
    xorBits E f (E.encode 0) = E.encode f := by
  simp [xorBits, E.encode_zero]

theorem xorBits_zero (E : FieldEncoding K w) (f : K) :
    xorBits E f 0 = E.encode f := by
  simp [xorBits]

theorem xorBits_uncompute (E : FieldEncoding K w) (f : K) :
    xorBits E f (E.encode f) = E.encode 0 := by
  simp [xorBits, E.encode_zero]

structure BitRegisters (w : ℕ) where

  x : BitVec w

  y : BitVec w

  lam : BitVec w

  temp : BitVec w
  deriving DecidableEq, Fintype

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
