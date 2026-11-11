/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.PauliClifford.ExactRank.BooleanCharacters

/-!
# Boolean register coordinates for characters

This module identifies Boolean registers with vectors over `ZMod 2`. The equivalence sends
`false` to zero and `true` to one, so coordinatewise conjunction becomes multiplication and the
Boolean dot product becomes a sum of conjunction bits. These identities connect register
notation with the character notation used for finite Fourier transforms.

The computational basis and Boolean Hadamard transform provide the quantum-computing background
in [NielsenChuang2010].

## Key declarations

* `boolZModEquiv` and `regBooleanEquiv` give the scalar and register equivalences.
* `boolZModEquiv_and_mul` and `booleanDot_regBooleanEquiv` translate Boolean operations into
  arithmetic modulo two.
* `booleanCharacter_regBooleanEquiv_apply` and its conjugate form express character evaluation
  through the standard additive character.

## References

* [Nielsen and Chuang, 2010][NielsenChuang2010]
-/

set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.WalshMoment.Forrelation

open scoped ComplexConjugate Classical

/-- The equivalence from Boolean values to `ZMod 2`, sending `false` to zero and `true` to one. -/
def boolZModEquiv : Bool ≃ ZMod 2 :=
  Qatlib.Foundations.PureStateMath.boolEquivFin2.trans (ZMod.finEquiv 2)

/-- The Boolean value `false` maps to zero under `boolZModEquiv`. -/
@[simp] theorem boolZModEquiv_false : boolZModEquiv false = 0 := by
  simp [boolZModEquiv, Qatlib.Foundations.PureStateMath.boolEquivFin2,
    Qatlib.Concepts.QuditTeleport.TeleportCore.finEquiv_apply_val]

/-- The Boolean value `true` maps to one under `boolZModEquiv`. -/
@[simp] theorem boolZModEquiv_true : boolZModEquiv true = 1 := by
  simp [boolZModEquiv, Qatlib.Foundations.PureStateMath.boolEquivFin2,
    Qatlib.Concepts.QuditTeleport.TeleportCore.finEquiv_apply_val]

/-- The coordinatewise equivalence between `n`-bit registers and vectors of length `n` over
`ZMod 2`, induced by `boolZModEquiv`. -/
def regBooleanEquiv (n : ℕ) : Qatlib.Foundations.PureStateMath.Reg n ≃ BooleanVec n where
  toFun x i := boolZModEquiv (x i)
  invFun a i := boolZModEquiv.symm (a i)
  left_inv x := by
    funext i
    exact boolZModEquiv.left_inv (x i)
  right_inv a := by
    funext i
    exact boolZModEquiv.right_inv (a i)

/-- Each coordinate of `regBooleanEquiv n x` is obtained by applying `boolZModEquiv` to the
corresponding bit of `x`. -/
@[simp] theorem regBooleanEquiv_apply {n : ℕ} (x : Qatlib.Foundations.PureStateMath.Reg n) (i : Fin n) :
    regBooleanEquiv n x i = boolZModEquiv (x i) := rfl

/-- The inverse register equivalence applies `boolZModEquiv.symm` to each coordinate. -/
@[simp] theorem regBooleanEquiv_symm_apply {n : ℕ} (a : BooleanVec n) (i : Fin n) :
    (regBooleanEquiv n).symm a i = boolZModEquiv.symm (a i) := rfl

/-- Under `boolZModEquiv`, Boolean conjunction becomes multiplication in `ZMod 2`. -/
theorem boolZModEquiv_and_mul (a b : Bool) :
    boolZModEquiv (a && b) = boolZModEquiv a * boolZModEquiv b := by
  cases a <;> cases b <;> simp

/-- The Boolean dot product of the converted registers is the sum in `ZMod 2` of their
coordinatewise conjunction bits. -/
theorem booleanDot_regBooleanEquiv {n : ℕ} (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    booleanDot (regBooleanEquiv n y) (regBooleanEquiv n z) =
      ∑ i, boolZModEquiv (y i && z i) := by
  unfold booleanDot
  apply Finset.sum_congr rfl
  intro i _
  exact (boolZModEquiv_and_mul (y i) (z i)).symm

/-- The character indexed by the converted register `y`, evaluated at the converted register
`z`, equals the standard additive character of the sum of conjunction bits. -/
theorem booleanCharacter_regBooleanEquiv_apply {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    booleanCharacter (regBooleanEquiv n y) (regBooleanEquiv n z) =
      ZMod.stdAddChar (∑ i, boolZModEquiv (y i && z i)) := by
  rw [booleanCharacter_apply, booleanDot_regBooleanEquiv]

/-- The conjugate Boolean character value equals the conjugate standard additive character
evaluated at the sum of coordinatewise conjunction bits. -/
theorem conj_booleanCharacter_regBooleanEquiv_apply {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    conj (booleanCharacter (regBooleanEquiv n y) (regBooleanEquiv n z)) =
      conj (ZMod.stdAddChar (∑ i, boolZModEquiv (y i && z i))) := by
  rw [booleanCharacter_regBooleanEquiv_apply]

end Qatlib.Concepts.WalshMoment.Forrelation
