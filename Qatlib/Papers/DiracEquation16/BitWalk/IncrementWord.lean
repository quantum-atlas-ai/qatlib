/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryShift

@[expose] public section

/-!
# Three-bit controlled increment word

Figure 2 of [FillionGourdeauMacLeanLaflamme2017] implements the conditional translations of
Eqs. (47)-(52) by a cascade of controlled bit flips. On a three-bit cyclic register the cascade
consists of three steps applied from the least significant bit upwards: flip the lowest bit, flip
the middle bit when the lowest bit is clear, and flip the highest bit when both lower bits are
clear. In the paper's drawing these are the white (zero) controlled `X` gates of the increment
cascade.

This module records that gate word as an explicit `8 × 8` matrix over `ZMod 8` and proves that it
coincides with the conditional translation
`Qatlib.Concepts.TensorRegisters.RegisterModel.BinaryShift.stream` at unit shift. Consequently the
permutation semantics of the streaming matrices is realized by a gate-level word for three-bit
registers.

## Main statements

* `incrementWord3_eq_stream`: the three controlled flips compose to the unit conditional
  translation on `ZMod 8`.

## References

* [Fillion-Gourdeau et al., 2017][FillionGourdeauMacLeanLaflamme2017]
-/

set_option autoImplicit false

open Matrix

namespace Qatlib.Papers.DiracEquation16.BitWalk

open Qatlib.Concepts.TensorRegisters.RegisterModel

/-- The increment step on bit `k` of a numeric three-bit value: toggle bit `k` exactly when all
lower bits vanish. -/
def stepNat (k : ℕ) (x : ℕ) : ℕ :=
  if x % 2 ^ k = 0 then (if x / 2 ^ k % 2 = 1 then x - 2 ^ k else x + 2 ^ k) else x

/-- The numeric increment step keeps three-bit values in range. -/
theorem stepNat_lt (k : Fin 3) : ∀ x : Fin 8, stepNat (k : ℕ) x.val < 8 := by
  fin_cases k <;> decide

/-- The numeric increment step is an involution on three-bit values. -/
theorem stepNat_involutive (k : Fin 3) :
    ∀ x : Fin 8, stepNat (k : ℕ) (stepNat (k : ℕ) x.val) = x.val := by
  fin_cases k <;> decide

/-- The cascade of numeric increment steps adds one modulo eight. -/
theorem stepNat_cascade :
    ∀ x : Fin 8, stepNat 2 (stepNat 1 (stepNat 0 x.val)) = (x.val + 1) % 8 := by
  decide

/-- The reversed cascade of numeric increment steps subtracts one modulo eight. -/
theorem stepNat_cascade_reverse :
    ∀ x : Fin 8, stepNat 0 (stepNat 1 (stepNat 2 x.val)) = (x.val + 7) % 8 := by
  decide

/-- The increment step on bit `k` of the three-bit cyclic register. -/
def incrementStep (k : Fin 3) (i : ZMod 8) : ZMod 8 := (stepNat (k : ℕ) i.val : ZMod 8)

/-- The value of an increment step is the numeric increment step of the register value. -/
theorem incrementStep_val (k : Fin 3) (i : ZMod 8) :
    (incrementStep k i).val = stepNat (k : ℕ) i.val := by
  rw [incrementStep, ZMod.val_natCast, Nat.mod_eq_of_lt]
  exact stepNat_lt k ⟨i.val, ZMod.val_lt i⟩

/-- Every increment step is an involution of the register values. -/
theorem incrementStep_involutive (k : Fin 3) (i : ZMod 8) :
    incrementStep k (incrementStep k i) = i := by
  apply ZMod.val_injective 8
  rw [incrementStep_val, incrementStep_val]
  exact stepNat_involutive k ⟨i.val, ZMod.val_lt i⟩

/-- The value of one in the register. -/
theorem val_one_zmod_eight : (1 : ZMod 8).val = 1 := by
  rw [← Nat.cast_one, ZMod.val_natCast]

/-- The increment cascade adds one to the register value. -/
theorem incrementStep_cascade (i : ZMod 8) :
    incrementStep 2 (incrementStep 1 (incrementStep 0 i)) = i + 1 := by
  apply ZMod.val_injective 8
  rw [incrementStep_val, incrementStep_val, incrementStep_val, ZMod.val_add, val_one_zmod_eight]
  exact stepNat_cascade ⟨i.val, ZMod.val_lt i⟩

/-- The reversed increment cascade subtracts one from the register value. -/
theorem incrementStep_cascade_reverse (i : ZMod 8) :
    incrementStep 0 (incrementStep 1 (incrementStep 2 i)) = i - 1 := by
  apply ZMod.val_injective 8
  rw [incrementStep_val, incrementStep_val, incrementStep_val, sub_eq_add_neg, ZMod.val_add,
    ZMod.val_neg_one]
  exact stepNat_cascade_reverse ⟨i.val, ZMod.val_lt i⟩

/-- The increment step on bit `k`, as a permutation of the register values. -/
def incrementPerm (k : Fin 3) : Equiv.Perm (ZMod 8) where
  toFun := incrementStep k
  invFun := incrementStep k
  left_inv := incrementStep_involutive k
  right_inv := incrementStep_involutive k

/-- The single-bit controlled flip of the increment cascade, as a register matrix. -/
def incrementGate (k : Fin 3) : Matrix (ZMod 8) (ZMod 8) ℂ :=
  BinaryShift.permU (incrementPerm k)

/-- The three-bit controlled increment word of Fig. 2, with the least significant bit flipped
first. -/
def incrementWord3 : Matrix (ZMod 8) (ZMod 8) ℂ :=
  incrementGate 2 * incrementGate 1 * incrementGate 0

/-- Lifting a product of permutations to conditional translations is multiplicative. -/
theorem permU_mul {I : Type*} [Fintype I] [DecidableEq I] (σ τ : Equiv.Perm I) :
    BinaryShift.permU (σ * τ) = BinaryShift.permU σ * BinaryShift.permU τ := by
  rw [BinaryShift.permU, BinaryShift.permU, BinaryShift.permU,
    show (σ * τ).symm = τ.symm * σ.symm from rfl, Matrix.permMatrix_mul]

/-- The entries of a conditional translation form the indicator of the inverse permutation. -/
theorem permU_apply {I : Type*} [Fintype I] [DecidableEq I] (e : Equiv.Perm I) (i j : I) :
    BinaryShift.permU e i j = if e.symm i = j then (1 : ℂ) else 0 := by
  show (PEquiv.toMatrix (Equiv.toPEquiv e.symm) : Matrix I I ℂ) i j = _
  rw [PEquiv.toMatrix_apply, Equiv.toPEquiv_apply]
  simp [eq_comm]

/-- The conditional translation of the paper's Fig. 2 is the three-bit controlled increment word.
-/
theorem incrementWord3_eq_stream :
    incrementWord3 =
      (BinaryShift.stream (S := Unit) (G := ZMod 8) (fun _ => true) 1).submatrix
        (fun g => ((), g)) (fun g => ((), g)) := by
  have hinv (k : Fin 3) : (incrementPerm k).symm = incrementPerm k := rfl
  have hsymm : (incrementPerm 2 * incrementPerm 1 * incrementPerm 0).symm =
      incrementPerm 0 * (incrementPerm 1 * incrementPerm 2) := by
    rw [show (incrementPerm 2 * incrementPerm 1 * incrementPerm 0).symm =
        (incrementPerm 0).symm * (incrementPerm 2 * incrementPerm 1).symm from rfl,
      show (incrementPerm 2 * incrementPerm 1).symm =
        (incrementPerm 1).symm * (incrementPerm 2).symm from rfl,
      hinv, hinv, hinv]
  have hperm : ∀ i : ZMod 8,
      (incrementPerm 0 * (incrementPerm 1 * incrementPerm 2)) i =
        incrementStep 0 (incrementStep 1 (incrementStep 2 i)) := by
    intro i
    rfl
  have hdown : ∀ i : ZMod 8,
      (incrementPerm 2 * incrementPerm 1 * incrementPerm 0).symm i = i - 1 := by
    intro i
    rw [hsymm, hperm i, incrementStep_cascade_reverse i]
  have hshift : ∀ i : ZMod 8,
      (BinaryShift.shift (fun _ : Unit => true) (G := ZMod 8) 1).symm ((), i) =
        ((), i - 1) := by
    intro i
    rfl
  rw [incrementWord3, incrementGate, incrementGate, incrementGate, ← permU_mul, ← permU_mul]
  rw [show BinaryShift.stream (S := Unit) (G := ZMod 8) (fun _ => true) 1 =
      BinaryShift.permU (BinaryShift.shift (fun _ : Unit => true) 1) from rfl]
  ext i j
  rw [permU_apply, Matrix.submatrix_apply, permU_apply, hdown i, hshift i]
  simp [eq_comm]

end Qatlib.Papers.DiracEquation16.BitWalk
