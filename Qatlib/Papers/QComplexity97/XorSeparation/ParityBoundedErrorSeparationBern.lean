/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QComplexity97.XorSeparation.ParityBoundedErrorSeparationStat
import Qatlib.Concepts.UniformBqp.BvParityBound.ParityAverageSuccessBoundBern
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestrictedDefs

/-!
# Bounded-error parity-oracle separation

This module proves `parityBoundedErrorSeparation` for the parity-secret recovery task associated
with [BernsteinVazirani1997]. The classical part uses the average-success bound for randomized
query trees; the quantum part uses the explicit one-query circuit and its exact recovery
identity.

## Main statements

* `parityBoundedErrorSeparation`: success probability at least `2 / 3` for every secret requires
  a classical query bound of at least `n`, while the specified unitary quantum circuit recovers
  every secret with probability `1` using one query.

## References

* [Bernstein and Vazirani, 1997][BernsteinVazirani1997]
-/

set_option warningAsError false

open Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UniformBqp.BvParityBound
open Qatlib.Concepts.QueryComplexity.DegreeMethod

set_option autoImplicit false
namespace Qatlib.Papers.QComplexity97.XorSeparation
open Matrix
open scoped BigOperators

/-- Establishes the bounded-error parity-secret separation: a randomized classical query tree
distribution with success at least `2 / 3` on every secret needs query bound at least `n`,
whereas the specified normalized unitary quantum circuit recovers every secret with
probability `1` using one query [BernsteinVazirani1997]. -/
theorem parityBoundedErrorSeparation : ParityBoundedErrorSeparation := by
  classical
  constructor
  · intro n T P hT hS
    have hu := parityAverageSuccessBound n T P hT
    have hl : (2 : ℝ) ^ n * (2 / 3) ≤
        ∑ k : Reg n, (BoolQueryTree.SuccessProb P (bvCharBit k) (fun output => output = k)).toReal := by
      calc
        _ = ∑ _ : Reg n, (2 : ℝ) / 3 := by simp [nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum fun k _ => hS k
    by_contra hn
    have ht : T + 1 ≤ n := by omega
    have hp := pow_le_pow_right₀ (by norm_num : 1 ≤ (2 : ℝ)) ht
    rw [pow_succ] at hp
    nlinarith [pow_pos (by norm_num : 0 < (2 : ℝ)) T]
  · intro n
    have hgate : bvMainGate n (HadamardN n) ∈ Matrix.unitaryGroup (Reg n × Bool) ℂ :=
      tensorGate_unitary (hadamardN_unitary n) (by exact one_mem _)
    refine ⟨?_, normalized_tensorState (normalized_ket _) normalized_minus,
      (bv_one_query_recovery n (ZeroStr n)).2, ?_⟩
    · simp only [bvOneCallCircuit, isUnitaryCircuit_gate, isUnitaryCircuit_query,
        isUnitaryCircuit_nil, and_true]
      exact ⟨hgate, hgate⟩
    · intro k
      rw [(bv_one_query_recovery n k).1, measureProb_tensorState_prod,
        measureProb_univ normalized_minus, mul_one]
      simp only [MeasureProb, Finset.sum_singleton, bornProb_ket, if_true]

end Qatlib.Papers.QComplexity97.XorSeparation
