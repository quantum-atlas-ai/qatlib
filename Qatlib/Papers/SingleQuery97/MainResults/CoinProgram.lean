/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SingleQuery97.MainResults.LinearCodeProgram
import Qatlib.Papers.SingleQuery97.MainResults.CoinWeighing
import Qatlib.Papers.SingleQuery97.MainResults.ParityRecovery
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

namespace Qatlib.Papers.SingleQuery97.MainResults.CoinProgram

open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.HspRecovery.CyclicRecovery
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalshMoment.Forrelation
open Qatlib.Papers.QComplexity97.XorSeparation
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open DatabaseDefs CoinWeighing ParityRecovery

noncomputable def alternating (n : ℕ) : AddChar (ZMod (registerN n)) ℂ where
  toFun := bAmplitude n
  map_zero_eq_one' := by simp [bAmplitude]
  map_add_eq_mul' := bAmplitude_add n

noncomputable def answerState (n : ℕ) : QState (ZMod (registerN n)) :=
  characterState (alternating n)

theorem answerState_normalized (n : ℕ) : Normalized (answerState n) :=
  normalized_characterState _

theorem alternating_neg (n : ℕ) (b : ZMod (registerN n)) :
    alternating n (-b) = bAmplitude n b := by
  rw [AddChar.map_neg_eq_conj]
  simp only [alternating, AddChar.coe_mk, bAmplitude, signOfParity]
  split_ifs <;> simp

def weighing {n : ℕ} (y x : Reg n) : ZMod (registerN n) := weight (wedge x y)

theorem weighing_phase {n : ℕ} (y x : Reg n) :
    alternating n (-weighing y x) =
      if Qatlib.Concepts.UniformBqp.BvParityBound.bvCharBit y x then (-1:ℂ) else 1 := by
  rw [alternating_neg, weighing, bAmplitude_natCast, weight_wedge_eq_dot,
    signOfParity_dot_eq_bvCharBit_phase]

noncomputable def answerFourier (n : ℕ) :
    Matrix (ZMod (registerN n)) (ZMod (registerN n)) ℂ :=
  fourierGate (dualLabeling (ZMod (registerN n)))

noncomputable def answerLabel (n : ℕ) : ZMod (registerN n) :=
  (dualLabeling (ZMod (registerN n))).symm (alternating n)

theorem prepare_answerState (n : ℕ) :
    ApplyGate (answerFourier n)ᴴ (Ket (answerLabel n)) = answerState n := by
  have hread : ApplyGate (answerFourier n) (answerState n) = Ket (answerLabel n) := by
    funext b
    simp only [answerFourier, applyGate_fourierGate, answerState, fourier_characterState]
    simp [Qatlib.Foundations.PureStateMath.Ket, answerLabel, Equiv.eq_symm_apply]
  have hi := (Matrix.mem_unitaryGroup_iff').mp
    (fourierGate_unitary (dualLabeling (ZMod (registerN n))))
  rw [Matrix.star_eq_conjTranspose] at hi
  change (answerFourier n)ᴴ * answerFourier n = 1 at hi
  rw [← hread, ← applyGate_mul, hi, applyGate_one]

noncomputable def word (n : ℕ) : Circuit (Reg n × ZMod (registerN n)) :=
  [Step.gate (TensorGate 1 (answerFourier n)ᴴ),
   Step.gate (TensorGate (HadamardN n) 1), Step.query,
   Step.gate (TensorGate (HadamardN n) 1)]

theorem word_unitary (n : ℕ) : IsUnitaryCircuit (word n) := by
  have hH := tensorGate_unitary (hadamardN_unitary n)
    (Matrix.unitaryGroup (ZMod (registerN n)) ℂ).one_mem
  simp only [word, isUnitaryCircuit_gate, isUnitaryCircuit_query, isUnitaryCircuit_nil, and_true]
  exact ⟨tensorGate_unitary (Matrix.unitaryGroup _ ℂ).one_mem
    (conjTranspose_mem_unitaryGroup (fourierGate_unitary _)), hH, hH⟩

theorem word_resources (n : ℕ) : QueryCount (word n) = 1 ∧ GateCount (word n) = 3 := by
  constructor <;> rfl

theorem run_word (n : ℕ) (y : Reg n) :
    Run (AddOracle (weighing y)) (word n)
      (TensorState (Ket (ZeroStr n)) (Ket (answerLabel n))) =
      TensorState (Ket y) (answerState n) := by
  have hk := ActualQuery.one_query_character_kickback (weighing y) (alternating n)
    (fourierScale (ZMod (registerN n))) (Uniform (Reg n))
  change Run (AddOracle (weighing y)) [Step.query]
    (TensorState (Uniform (Reg n)) (answerState n)) = _ at hk
  have hp : (fun x : Reg n => alternating n (-weighing y x) * Uniform (Reg n) x) =
      ApplyGate (HadamardN n) (Ket y) := by
    rw [← bv_phase_prepares_secret]
    funext x
    rw [applyGate_phaseOracle, weighing_phase]
  rw [hp] at hk
  simp only [word, Run, applyGate_tensorGate, applyGate_one,
    prepare_answerState, applyGate_hadamardN_ket_zero]
  rw [show ApplyGate (AddOracle (weighing y))
      (TensorState (Uniform (Reg n)) (answerState n)) = _ from hk]
  rw [applyGate_tensorGate, applyGate_one, ← applyGate_mul, bv_hadamard_square, applyGate_one]
  rfl

theorem recovery_probability (n : ℕ) (y : Reg n) :
    MeasureProb (Run (AddOracle (weighing y)) (word n)
      (TensorState (Ket (ZeroStr n)) (Ket (answerLabel n))))
      ({y} ×ˢ Finset.univ) = 1 := by
  rw [run_word, measureProb_tensorState_left (answerState_normalized n)]
  simp [MeasureProb, bornProb_ket]

end Qatlib.Papers.SingleQuery97.MainResults.CoinProgram
