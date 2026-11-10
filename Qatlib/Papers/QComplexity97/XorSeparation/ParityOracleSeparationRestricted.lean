/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.UniformBqp.BvParityBound.ParityClassicalLowerBound
import Qatlib.Concepts.BlockEncoding.LinearCombination
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestricted
import Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestrictedDefs
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.BvParityBound

namespace Qatlib.Papers.QComplexity97.XorSeparation

open Matrix

theorem bv_character_phase {n : ℕ} (k x : Reg n) :
    (if bvCharBit k x then (-1 : ℂ) else 1) =
      ∏ i, if k i && x i then (-1 : ℂ) else 1 := by
  classical
  rw [← Finset.prod_filter]
  simp only [Finset.prod_const]
  rw [neg_one_pow_eq_pow_mod_two]
  unfold bvCharBit
  have hm := Nat.mod_lt (Finset.univ.filter fun i => k i && x i).card (by omega : 0 < 2)
  interval_cases h : (Finset.univ.filter fun i => k i && x i).card % 2 <;> simp

theorem bv_phase_prepares_secret {n : ℕ} (k : Reg n) :
    ApplyGate (PhaseOracle (bvCharBit k)) (Uniform (Reg n)) =
      ApplyGate (HadamardN n) (Ket k) := by
  funext x
  rw [applyGate_phaseOracle, bv_character_phase]
  change _ = (HadamardN n *ᵥ Ket k) x
  rw [mulVec_ket_apply, hadamardN_apply]
  have hc := congrFun (applyGate_hadamardN_ket_zero n) x
  change (HadamardN n *ᵥ Ket (ZeroStr n)) x = Uniform (Reg n) x at hc
  rw [mulVec_ket_apply, hadamardN_apply_zero_right] at hc
  rw [← hc]
  simp only [Bool.and_comm (k _) (x _)]
  ring

theorem bv_hadamard_square (n : ℕ) : HadamardN n * HadamardN n = 1 := by
  have hh : (HadamardN n)ᴴ = HadamardN n := by
    ext x y
    simp only [Matrix.conjTranspose_apply, RCLike.star_def, hadamardN_conj]
    rw [hadamardN_apply, hadamardN_apply]
    simp only [Bool.and_comm (y _) (x _)]
  have hu := hadamardN_unitary n
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh] at hu
  exact hu

theorem bv_one_query_recovery (n : ℕ) (k : Reg n) :
    Run (BitOracleOn (bvCharBit k)) (bvOneCallCircuit n)
      (TensorState (Ket (ZeroStr n)) Minus) = TensorState (Ket k) Minus ∧
      QueryCount (bvOneCallCircuit n) = 1 := by
  refine ⟨?_, rfl⟩
  simp only [bvOneCallCircuit, Run, bvMainGate, applyGate_tensorGate, applyGate_one]
  rw [applyGate_hadamardN_ket_zero, applyGate_bitOracleOn_tensorState_minus,
    bv_phase_prepares_secret, applyGate_tensorGate, applyGate_one,
    ← applyGate_mul, bv_hadamard_square, applyGate_one]

theorem bv_tensor_diagonal {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (a : I → ℂ) (b : J → ℂ) :
    TensorGate (Matrix.diagonal a) (Matrix.diagonal b) =
      Matrix.diagonal (fun p : I × J => a p.1 * b p.2) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hi : i = k <;> by_cases hj : j = l <;>
    simp [TensorGate, hi, hj]

theorem bv_target_phase_apply (n : ℕ) (ψ : QState (Reg n × Bool))
    (p : Reg n × Bool) :
    ApplyGate (bvTgtGate n PauliZ) ψ p = (if p.2 then (-1 : ℂ) else 1) * ψ p := by
  unfold bvTgtGate PauliZ
  rw [← Matrix.diagonal_one, bv_tensor_diagonal]
  simp only [one_mul, ApplyGate, Matrix.mulVec_diagonal]

theorem bv_two_query_phase (n : ℕ) (f : Reg n → Bool) (ψ : QState (Reg n × Bool)) :
    Run (BitOracleOn f) (bvTwoCallWord n) ψ =
      ApplyGate (TensorGate (PhaseOracle f) PauliZ) ψ ∧
      QueryCount (bvTwoCallWord n) = 2 := by
  refine ⟨?_, rfl⟩
  funext p
  simp only [bvTwoCallWord, Run, applyGate_bitOracleOn, bv_target_phase_apply]
  unfold PhaseOracle PauliZ
  rw [bv_tensor_diagonal]
  simp only [ApplyGate, Matrix.mulVec_diagonal]
  rcases p with ⟨x, b⟩
  cases hf : f x <;> cases b <;> simp [BitFlip, hf]

theorem parityOracleSeparationRestricted : ParityOracleSeparationRestricted :=
  ⟨bv_one_query_recovery, bv_two_query_phase, bv_classical_zero_error_lower_bound⟩

end Qatlib.Papers.QComplexity97.XorSeparation
