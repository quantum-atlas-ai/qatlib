/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.PauliClifford.ExactRank.BooleanCharacters
set_option warningAsError false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.PauliClifford.ExactRank

namespace Qatlib.Concepts.WalshMoment.Forrelation

open scoped ComplexConjugate Classical

def boolZModEquiv : Bool ≃ ZMod 2 :=
  Qatlib.Foundations.PureStateMath.boolEquivFin2.trans (ZMod.finEquiv 2)

@[simp] theorem boolZModEquiv_false : boolZModEquiv false = 0 := by
  simp [boolZModEquiv, Qatlib.Foundations.PureStateMath.boolEquivFin2,
    Qatlib.Concepts.QuditTeleport.TeleportCore.finEquiv_apply_val]

@[simp] theorem boolZModEquiv_true : boolZModEquiv true = 1 := by
  simp [boolZModEquiv, Qatlib.Foundations.PureStateMath.boolEquivFin2,
    Qatlib.Concepts.QuditTeleport.TeleportCore.finEquiv_apply_val]

def regBooleanEquiv (n : ℕ) : Qatlib.Foundations.PureStateMath.Reg n ≃ BooleanVec n where
  toFun x i := boolZModEquiv (x i)
  invFun a i := boolZModEquiv.symm (a i)
  left_inv x := by
    funext i
    exact boolZModEquiv.left_inv (x i)
  right_inv a := by
    funext i
    exact boolZModEquiv.right_inv (a i)

@[simp] theorem regBooleanEquiv_apply {n : ℕ} (x : Qatlib.Foundations.PureStateMath.Reg n) (i : Fin n) :
    regBooleanEquiv n x i = boolZModEquiv (x i) := rfl

@[simp] theorem regBooleanEquiv_symm_apply {n : ℕ} (a : BooleanVec n) (i : Fin n) :
    (regBooleanEquiv n).symm a i = boolZModEquiv.symm (a i) := rfl

theorem boolZModEquiv_and_mul (a b : Bool) :
    boolZModEquiv (a && b) = boolZModEquiv a * boolZModEquiv b := by
  cases a <;> cases b <;> simp

theorem booleanDot_regBooleanEquiv {n : ℕ} (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    booleanDot (regBooleanEquiv n y) (regBooleanEquiv n z) =
      ∑ i, boolZModEquiv (y i && z i) := by
  unfold booleanDot
  apply Finset.sum_congr rfl
  intro i _
  exact (boolZModEquiv_and_mul (y i) (z i)).symm

theorem booleanCharacter_regBooleanEquiv_apply {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    booleanCharacter (regBooleanEquiv n y) (regBooleanEquiv n z) =
      ZMod.stdAddChar (∑ i, boolZModEquiv (y i && z i)) := by
  rw [booleanCharacter_apply, booleanDot_regBooleanEquiv]

theorem conj_booleanCharacter_regBooleanEquiv_apply {n : ℕ}
    (y z : Qatlib.Foundations.PureStateMath.Reg n) :
    conj (booleanCharacter (regBooleanEquiv n y) (regBooleanEquiv n z)) =
      conj (ZMod.stdAddChar (∑ i, boolZModEquiv (y i && z i))) := by
  rw [booleanCharacter_regBooleanEquiv_apply]

end Qatlib.Concepts.WalshMoment.Forrelation
