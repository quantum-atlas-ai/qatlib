/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.CyclicRecovery.AlgebraicOracle
import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Qatlib.Papers.QComplexity97.XorSeparation.ParityOracleSeparationRestricted
set_option warningAsError false
set_option autoImplicit false
namespace Qatlib.Papers.SingleQuery97.MainResults.ActualQuery
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore

theorem one_query_character_kickback {I R : Type} [Fintype I] [DecidableEq I]
    [Fintype R] [DecidableEq R] [AddCommGroup R] (f : I → R)
    (χ : AddChar R ℂ) (c : ℂ) (ψ : QState I) :
    Run (AddOracle f) [Step.query] (TensorState ψ (fun b => c*χ b)) =
      TensorState (fun x => χ (-f x)*ψ x) (fun b => c*χ b) := by
  funext p
  rcases p with ⟨x,b⟩
  simp only [run_addOracle_query, applyGate_addOracle, TensorState,
    sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

theorem cyclic_answer_kickback {I : Type} [Fintype I] [DecidableEq I]
    (A : ℕ) [NeZero A] (f : I → ZMod A) (ψ : QState I) :
    Run (AddOracle f) [Step.query] (TensorState ψ (charState (1:ZMod A))) =
      TensorState (fun x => ZMod.stdAddChar (-f x)*ψ x) (charState (1:ZMod A)) := by
  have hη : charState (1:ZMod A) = (fun b : ZMod A =>
      (Real.sqrt (A:ℝ):ℂ)⁻¹ * ZMod.stdAddChar b) := by
    funext b
    rw [charState_apply, one_mul]
  rw [hη]
  exact one_query_character_kickback f (ZMod.stdAddChar (N:=A))
      (Real.sqrt (A:ℝ):ℂ)⁻¹ ψ

theorem cyclic_negative_phase_readout (A : ℕ) [NeZero A] (z : ZMod A) :
    ApplyGate (zmodQFTGate (N:=A)) (charState (-z)) = Ket z := by
  rw [applyGate_zmodQFTGate, zmodQFT_charState, neg_neg]

theorem cyclic_negative_phase_born (A : ℕ) [NeZero A] (z out : ZMod A) :
    BornProb (ApplyGate (zmodQFTGate (N:=A)) (charState (-z))) out =
      if out=z then 1 else 0 := by
  rw [cyclic_negative_phase_readout]
  exact bornProb_ket z out

theorem binary_actual_recovery (n : ℕ) (y : Reg n) :
    Run (Qatlib.Concepts.QueryWordCore.QueryMachinery.BitOracleOn
      (Qatlib.Concepts.UniformBqp.BvParityBound.bvCharBit y))
      (Qatlib.Concepts.UniformBqp.BvParityBound.bvOneCallCircuit n)
      (TensorState (Ket (ZeroStr n)) Minus) = TensorState (Ket y) Minus ∧
    QueryCount (Qatlib.Concepts.UniformBqp.BvParityBound.bvOneCallCircuit n)=1 :=
  Qatlib.Papers.QComplexity97.XorSeparation.bv_one_query_recovery n y

section KnownEncoding
variable {S X R : Type} [Fintype S] [DecidableEq S]
  [Fintype X] [DecidableEq X] [AddCommGroup X]
  [Fintype R] [DecidableEq R] [AddCommGroup R]

noncomputable def encodedQueryWord (encode : S → X) : Circuit ((S × X) × R) :=
  [Step.gate (TensorGate (AddOracle encode) 1), Step.query,
   Step.gate (TensorGate (AddOracle (-encode)) 1)]

omit [AddCommGroup R] in

theorem encodedQueryWord_unitary (encode : S → X) : IsUnitaryCircuit (encodedQueryWord (R:=R) encode) := by
  simp only [encodedQueryWord, isUnitaryCircuit_gate, isUnitaryCircuit_query, isUnitaryCircuit_nil,
    and_true]
  exact ⟨tensorGate_unitary (addOracle_unitary encode) (Matrix.unitaryGroup R ℂ).one_mem,
    tensorGate_unitary (addOracle_unitary (-encode)) (Matrix.unitaryGroup R ℂ).one_mem⟩

omit [Fintype S] [Fintype X] [Fintype R] [AddCommGroup R] in

theorem encodedQueryWord_resources (encode : S → X) :
    QueryCount (encodedQueryWord (R:=R) encode)=1 ∧ GateCount (encodedQueryWord (R:=R) encode)=2 := by
  constructor <;> rfl

theorem encodedQueryWord_clean (encode : S → X) (hidden : X → R)
    (χ : AddChar R ℂ) (c : ℂ) (ψ : QState S) :
    Run (AddOracle (fun p : S × X => hidden p.2)) (encodedQueryWord encode)
      (TensorState (TensorState ψ (Ket (0:X))) (fun b => c*χ b)) =
    TensorState (TensorState (fun s => χ (-hidden (encode s))*ψ s) (Ket (0:X)))
      (fun b => c*χ b) := by
  have hkick := one_query_character_kickback (fun p : S × X => hidden p.2) χ c
    (ApplyGate (AddOracle encode) (TensorState ψ (Ket (0:X))))
  simp only [run_addOracle_query] at hkick
  simp only [encodedQueryWord, Run, applyGate_tensorGate, applyGate_one]
  rw [hkick, applyGate_tensorGate, applyGate_one]
  apply congrArg (fun φ => TensorState φ (fun b => c*χ b))
  funext p
  rcases p with ⟨s,x⟩
  simp only [applyGate_addOracle, TensorState, Ket, Pi.neg_apply,
    sub_neg_eq_add, add_sub_cancel_right]
  by_cases hx : x=0 <;> simp [hx]
end KnownEncoding

end Qatlib.Papers.SingleQuery97.MainResults.ActualQuery
