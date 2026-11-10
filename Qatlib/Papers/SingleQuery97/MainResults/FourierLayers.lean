/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.LinearCodeProgram
import Qatlib.Papers.SingleQuery97.MainResults.CharacterSum
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.FourierLayers

open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalshMoment.Forrelation
open LinearCodeProgram FourierReadout
open scoped ComplexConjugate

theorem normalization_product (A m : ℕ) [NeZero A] :
    fourierScale (Fin m → ZMod A) = ((Real.sqrt (A:ℝ):ℂ)⁻¹)^m := by
  have hs : Real.sqrt ((A:ℝ)^m) = (Real.sqrt (A:ℝ))^m := by
    induction m with
    | zero => simp
    | succ m ih => rw [pow_succ,Real.sqrt_mul (by positivity),ih,pow_succ]
  simp only [fourierScale,Fintype.card_fun,Fintype.card_fin,ZMod.card,Nat.cast_pow,
    hs,Complex.ofReal_pow,inv_pow]

theorem positiveFourier_product (A m : ℕ) [NeZero A]
    (z s : Fin m → ZMod A) :
    positiveFourier A m z s = ∏ i, zmodQFTGate (N:=A) (z i) (s i) := by
  change fourierScale (Fin m → ZMod A) *
    conj ((-dotCharacter z) s) = _
  rw [AddChar.neg_apply,AddChar.map_neg_eq_conj,Complex.conj_conj]
  simp only [dotCharacter,AddChar.compAddMonoidHom_apply,dotHom,
    AddMonoidHom.coe_mk,ZeroHom.coe_mk]
  rw [CharacterSum.map_finsetSum_eq_prod]
  simp only [zmodQFTGate_apply]
  rw [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,
    normalization_product]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  rw [mul_comm]

theorem binary_character_one : ZMod.stdAddChar (1:ZMod 2) = (-1:ℂ) := by
  have h : ZMod.stdAddChar (1:ZMod 2) =
      Complex.exp (2*(Real.pi:ℂ)*Complex.I/2) := by
    simpa using ZMod.stdAddChar_coe (N:=2) (1:ℤ)
  calc
    _ = Complex.exp ((Real.pi:ℂ)*Complex.I) := by
      rw [h]
      congr 1
      ring
    _ = -1 := Complex.exp_pi_mul_I

noncomputable def binaryLabel : Bool ≃ ZMod 2 := Equiv.ofBijective
  (fun b => if b then 1 else 0) (by decide)

theorem binary_factor_hadamard (x y : Bool) :
    zmodQFTGate (N:=2) (binaryLabel x) (binaryLabel y) =
      Qatlib.Foundations.PureStateMath.Hadamard x y := by
  cases x <;> cases y <;>
    simp [binaryLabel,zmodQFTGate_apply,
      Qatlib.Foundations.PureStateMath.Hadamard,binary_character_one]

theorem binary_layer_hadamard (m : ℕ)
    (z s : Qatlib.Foundations.PureStateMath.Reg m) :
    positiveFourier 2 m (fun i => binaryLabel (z i)) (fun i => binaryLabel (s i)) =
      Qatlib.Foundations.PureStateMath.HadamardN m z s := by
  rw [positiveFourier_product]
  simp only [binary_factor_hadamard,
    Qatlib.Foundations.PureStateMath.HadamardN,Matrix.of_apply]

end Qatlib.Papers.SingleQuery97.MainResults.FourierLayers
