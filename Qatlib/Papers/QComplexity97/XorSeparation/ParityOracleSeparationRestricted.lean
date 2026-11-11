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

/-!
# Exact restricted parity-oracle separation

This module proves explicit circuit identities for the parity-oracle separation associated with
[BernsteinVazirani1997]. The phase identity `bv_phase_prepares_secret` and the involution
`bv_hadamard_square` yield `bv_one_query_recovery`, which recovers the hidden parity secret
while preserving the minus-state target.

The identity `bv_two_query_phase` computes the action of a two-call word on an arbitrary state.
The theorem `parityOracleSeparationRestricted` packages these identities together with the
deterministic classical lower bound.

## Main statements

* `bv_one_query_recovery`: exactly recovers the secret using one bit-oracle call.
* `bv_two_query_phase`: implements `TensorGate (PhaseOracle f) PauliZ` using two bit-oracle
  calls.
* `parityOracleSeparationRestricted`: combines the two quantum identities with the classical
  `n`-query lower bound.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.BlockEncoding.LinearCombination
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.BvParityBound

namespace Qatlib.Papers.QComplexity97.XorSeparation

open Matrix

/-- The sign of the parity character `bvCharBit k x` equals the product of the coordinate signs
determined by `k i && x i`. -/
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

/-- Applying the phase oracle of the parity character with secret `k` to the uniform state gives
the Hadamard transform of `Ket k`. -/
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

/-- The `n`-qubit Hadamard matrix multiplied by itself is the identity. -/
theorem bv_hadamard_square (n : ℕ) : HadamardN n * HadamardN n = 1 := by
  have hh : (HadamardN n)ᴴ = HadamardN n := by
    ext x y
    simp only [Matrix.conjTranspose_apply, RCLike.star_def, hadamardN_conj]
    rw [hadamardN_apply, hadamardN_apply]
    simp only [Bool.and_comm (y _) (x _)]
  have hu := hadamardN_unitary n
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh] at hu
  exact hu

/-- The one-call circuit maps the zero-register/minus-state input to `TensorState (Ket k) Minus`
for the parity oracle with secret `k`, and its query count is `1` [BernsteinVazirani1997]. -/
theorem bv_one_query_recovery (n : ℕ) (k : Reg n) :
    Run (BitOracleOn (bvCharBit k)) (bvOneCallCircuit n)
      (TensorState (Ket (ZeroStr n)) Minus) = TensorState (Ket k) Minus ∧
      QueryCount (bvOneCallCircuit n) = 1 := by
  refine ⟨?_, rfl⟩
  simp only [bvOneCallCircuit, Run, bvMainGate, applyGate_tensorGate, applyGate_one]
  rw [applyGate_hadamardN_ket_zero, applyGate_bitOracleOn_tensorState_minus,
    bv_phase_prepares_secret, applyGate_tensorGate, applyGate_one,
    ← applyGate_mul, bv_hadamard_square, applyGate_one]

/-- The tensor product of two diagonal gates is diagonal, with entries equal to the products of
their respective diagonal entries. -/
theorem bv_tensor_diagonal {I J : Type} [Fintype I] [DecidableEq I]
    [Fintype J] [DecidableEq J] (a : I → ℂ) (b : J → ℂ) :
    TensorGate (Matrix.diagonal a) (Matrix.diagonal b) =
      Matrix.diagonal (fun p : I × J => a p.1 * b p.2) := by
  ext ⟨i, j⟩ ⟨k, l⟩
  by_cases hi : i = k <;> by_cases hj : j = l <;>
    simp [TensorGate, hi, hj]

/-- Applying Pauli Z to the target multiplies the amplitude at `(x, b)` by `-1` when `b` is true
and by `1` otherwise. -/
theorem bv_target_phase_apply (n : ℕ) (ψ : QState (Reg n × Bool))
    (p : Reg n × Bool) :
    ApplyGate (bvTgtGate n PauliZ) ψ p = (if p.2 then (-1 : ℂ) else 1) * ψ p := by
  unfold bvTgtGate PauliZ
  rw [← Matrix.diagonal_one, bv_tensor_diagonal]
  simp only [one_mul, ApplyGate, Matrix.mulVec_diagonal]

/-- For any Boolean oracle function and input state, the two-call word acts as `TensorGate
(PhaseOracle f) PauliZ`, and its query count is `2`. -/
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

/-- Establishes the conjunction of exact one-query parity-secret recovery, the two-query
phase-gate identity, and the deterministic classical `n`-query recovery lower bound
[BernsteinVazirani1997]. -/
theorem parityOracleSeparationRestricted : ParityOracleSeparationRestricted :=
  ⟨bv_one_query_recovery, bv_two_query_phase, bv_classical_zero_error_lower_bound⟩

end Qatlib.Papers.QComplexity97.XorSeparation
