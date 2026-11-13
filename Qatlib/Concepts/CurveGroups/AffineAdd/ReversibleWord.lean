/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CurveGroups.AffineAdd.PrimeEncoding

/-!
# Reversible word for affine addition

This module lifts permutations of individual bit vector registers to `BitRegisters` and
assembles the seventeen step word `sourceWord`. Its composite agrees with `xorPointRun` on clean
auxiliary registers, connecting the arithmetic schedule to the reversible implementation setting
of [RoettelerEtAl2017].

## Main statements

* `sourcePermutation_clean_apply`: the word implements the clean register schedule.
* `sourceWord_length`: the word has seventeen register permutations.

## References

* [Roetteler et al., 2017][RoettelerEtAl2017]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Concepts.CurveGroups.AffineAdd

variable {K : Type*} [Field K] {w : ℕ}

/-- Apply a permutation to the X register, parameterized by the other three registers, while
preserving those registers. -/
def xGate (p : BitVec w → BitVec w → BitVec w → Equiv.Perm (BitVec w)) :
    Equiv.Perm (BitRegisters w) where
  toFun r := {r with x := p r.y r.lam r.temp r.x}
  invFun r := {r with x := (p r.y r.lam r.temp).symm r.x}
  left_inv r := by cases r; simp
  right_inv r := by cases r; simp

/-- Apply a permutation to the Y register, parameterized by the other three registers, while
preserving those registers. -/
def yGate (p : BitVec w → BitVec w → BitVec w → Equiv.Perm (BitVec w)) :
    Equiv.Perm (BitRegisters w) where
  toFun r := {r with y := p r.x r.lam r.temp r.y}
  invFun r := {r with y := (p r.x r.lam r.temp).symm r.y}
  left_inv r := by cases r; simp
  right_inv r := by cases r; simp

/-- Apply a permutation to the slope register, parameterized by the other three registers, while
preserving those registers. -/
def lamGate (p : BitVec w → BitVec w → BitVec w → Equiv.Perm (BitVec w)) :
    Equiv.Perm (BitRegisters w) where
  toFun r := {r with lam := p r.x r.y r.temp r.lam}
  invFun r := {r with lam := (p r.x r.y r.temp).symm r.lam}
  left_inv r := by cases r; simp
  right_inv r := by cases r; simp

/-- Apply a permutation to the temporary register, parameterized by the other three registers,
while preserving those registers. -/
def tempGate (p : BitVec w → BitVec w → BitVec w → Equiv.Perm (BitVec w)) :
    Equiv.Perm (BitRegisters w) where
  toFun r := {r with temp := p r.x r.y r.lam r.temp}
  invFun r := {r with temp := (p r.x r.y r.lam).symm r.temp}
  left_inv r := by cases r; simp
  right_inv r := by cases r; simp

/-- The seventeen register permutations forming the encoded affine point addition schedule. -/
noncomputable def sourceWord (E : FieldEncoding K w) (x2 y2 : K) :
    List (Equiv.Perm (BitRegisters w)) :=
  [xGate (fun _ _ _ => shiftBits E (-x2)),
   yGate (fun _ _ _ => shiftBits E (-y2)),
   tempGate (fun x _ _ => xorBits E (E.decode x)⁻¹),
   lamGate (fun _ y t => xorBits E (E.decode y * E.decode t)),
   yGate (fun x l _ => xorBits E (E.decode l * E.decode x)),
   tempGate (fun x _ _ => xorBits E (E.decode x)⁻¹),
   tempGate (fun _ _ l => xorBits E (E.decode l ^ 2)),
   xGate (fun _ _ t => shiftBits E (-E.decode t)),
   xGate (fun _ _ _ => shiftBits E (3*x2)),
   tempGate (fun _ _ l => xorBits E (E.decode l ^ 2)),
   yGate (fun x l _ => xorBits E (E.decode l * E.decode x)),
   tempGate (fun x _ _ => xorBits E (E.decode x)⁻¹),
   lamGate (fun _ y t => xorBits E (E.decode t * E.decode y)),
   tempGate (fun x _ _ => xorBits E (E.decode x)⁻¹),
   xGate (fun _ _ _ => negateBits E),
   yGate (fun _ _ _ => shiftBits E (-y2)),
   xGate (fun _ _ _ => shiftBits E x2)]

/-- The composite permutation of the affine addition word in execution order. -/
noncomputable def sourcePermutation (E : FieldEncoding K w) (x2 y2 : K) :
    Equiv.Perm (BitRegisters w) :=
  (sourceWord E x2 y2).foldl Equiv.trans (Equiv.refl _)

/-- On zero slope and temporary registers, the composite word equals `xorPointRun`. -/
theorem sourcePermutation_clean_apply (E : FieldEncoding K w) (x2 y2 : K)
    (x y : BitVec w) :
    sourcePermutation E x2 y2 ⟨x,y,0,0⟩ = xorPointRun E x2 y2 x y := by
  rfl

/-- The affine addition source word contains exactly seventeen register permutations. -/
theorem sourceWord_length (E : FieldEncoding K w) (x2 y2 : K) :
    (sourceWord E x2 y2).length = 17 := rfl

end Qatlib.Concepts.CurveGroups.AffineAdd
