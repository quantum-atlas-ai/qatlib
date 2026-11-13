/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CurveGroups.AffineAdd.XorSchedule

/-!
# Prime field bit encoding

This module constructs `primeFieldEncoding` for `ZMod p` when `p ≤ 2 ^ w`. It supplies the field
encoding used by reversible affine arithmetic in the elliptic curve setting of
[RoettelerEtAl2017].

## Main statements

* `primeFieldEncoding`: encode prime field residues into sufficiently wide bit vectors.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

/-- Encode `ZMod p` into width `w` bit vectors using canonical residue values when `p ≤ 2 ^ w`,
with a decoding left inverse and zero preservation. -/
def primeFieldEncoding (p w : ℕ) [Fact p.Prime] (hp : p ≤ 2^w) :
    FieldEncoding (ZMod p) w where
  encode := ⟨fun x => BitVec.ofNat w x.val, by
    intro x y h
    apply ZMod.val_injective p
    have hh := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((ZMod.val_lt x).trans_le hp),
      Nat.mod_eq_of_lt ((ZMod.val_lt y).trans_le hp)] using hh⟩
  decode x := (x.toNat : ZMod p)
  decode_encode x := by
    dsimp
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((ZMod.val_lt x).trans_le hp)]
    exact ZMod.natCast_zmod_val x
  encode_zero := by
    apply BitVec.eq_of_toNat_eq
    simp

end Qatlib.Concepts.CurveGroups.AffineAdd
