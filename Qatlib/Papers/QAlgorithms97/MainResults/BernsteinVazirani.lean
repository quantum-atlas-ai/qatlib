/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAlgorithms97.MainResults.OracleInterfaces
import Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestricted
import Qatlib.Papers.QComplexity97.XorSeparation.ParityOracleSeparationRestricted

/-!
# Bernstein-Vazirani and affine parity queries

The Bernstein-Vazirani circuit recovers a binary parity secret with one bit-oracle query; adding
a constant affine offset changes only the final global phase. This module records exact circuit
states, deterministic readout, and classical query-tree lower bounds in the oracle framework of
[CleveEtAl1998].

## Main statements

* `bernstein_vazirani_single_query`: exact recovery with one query.
* `affine_bernstein_vazirani_readout`: one-query readout for affine parity.
* `parity_classical_zero_error_lower_bound`: the classical query-tree lower bound.

## References

* [Cleve et al., 1998][CleveEtAl1998]
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.UniformBqp.BvParityBound

namespace Qatlib.Papers.QAlgorithms97.MainResults.BernsteinVazirani

/-- The one-query Bernstein-Vazirani circuit maps the zero register and minus ancilla to the
secret basis state and the same ancilla [Cleve et al., Section 3][CleveEtAl1998]. -/
theorem bernstein_vazirani_single_query (n : ℕ) (a : Reg n) :
    Run (BitOracleOn (bvCharBit a)) (bvOneCallCircuit n)
        (TensorState (Ket (ZeroStr n)) Minus) = TensorState (Ket a) Minus ∧
      QueryCount (bvOneCallCircuit n) = 1 := by
  have h : Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestricted :=
    Qatlib.Papers.QComplexity97.XorSeparation.parityOracleSeparationRestricted
  exact h.1 n a

/-- The two-query word implements the tensor product of the phase oracle and Pauli Z on any
input state, using exactly two queries. -/
theorem bernstein_vazirani_two_query_phase (n : ℕ) (f : Reg n → Bool)
    (ψ : QState (Reg n × Bool)) :
    Run (BitOracleOn f) (bvTwoCallWord n) ψ =
        ApplyGate (TensorGate (PhaseOracle f) PauliZ) ψ ∧
      QueryCount (bvTwoCallWord n) = 2 := by
  have h : Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestricted :=
    Qatlib.Papers.QComplexity97.XorSeparation.parityOracleSeparationRestricted
  exact h.2.1 n f ψ

/-- Any Boolean query tree that recovers every length-`n` parity secret exactly has maximum
query count at least `n` [CleveEtAl1998]. -/
theorem parity_classical_zero_error_lower_bound (n : ℕ)
    (T : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree (Reg n) (Reg n))
    (hT : ∀ a : Reg n,
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run
        (bvCharBit a) T).1 = a) :
    n ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries T := by
  have h : Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestricted :=
    Qatlib.Papers.QComplexity97.XorSeparation.parityOracleSeparationRestricted
  exact h.2.2 n T hT

/-- The restricted parity-oracle separation combines one-query secret recovery, the two-query
phase identity, and the `n`-query lower bound for exact classical Boolean query trees. -/
theorem parity_oracle_separation_restricted :
    Qatlib.Concepts.UniformBqp.BvParityBound.ParityOracleSeparationRestricted :=
  Qatlib.Papers.QComplexity97.XorSeparation.parityOracleSeparationRestricted

/-- The parity function with secret `a` and constant Boolean offset `b`. -/
def affineParity {n : ℕ} (a : Reg n) (b : Bool) (x : Reg n) : Bool := bvCharBit a x != b

/-- The affine parity phase oracle sends the uniform state to the Hadamard image of the secret
basis state, with sign determined by the offset. -/
theorem affine_phase_prepares_secret {n : ℕ} (a : Reg n) (b : Bool) :
    ApplyGate (PhaseOracle (affineParity a b)) (Uniform (Reg n)) =
      (if b then (-1 : ℂ) else 1) • ApplyGate (HadamardN n) (Ket a) := by
  rw [← Qatlib.Papers.QComplexity97.XorSeparation.bv_phase_prepares_secret]
  funext x
  simp only [Pi.smul_apply, smul_eq_mul, OracleInterfaces.phaseOracle_apply]
  cases b <;> cases h : bvCharBit a x <;> simp [affineParity, h]

/-- The one-query circuit for affine parity prepares the secret basis state with an
offset-dependent sign and leaves the minus ancilla unchanged. -/
theorem affine_bernstein_vazirani_run (n : ℕ) (a : Reg n) (b : Bool) :
    Run (BitOracleOn (affineParity a b)) (bvOneCallCircuit n)
      (TensorState (Ket (ZeroStr n)) Minus) =
        TensorState (fun z => (if b then (-1 : ℂ) else 1) * Ket a z) Minus := by
  simp only [bvOneCallCircuit, Run, bvMainGate, applyGate_tensorGate, applyGate_one]
  rw [applyGate_hadamardN_ket_zero, OracleInterfaces.bitOracle_minus,
    applyGate_tensorGate, applyGate_one, affine_phase_prepares_secret]
  change TensorState ((HadamardN n).mulVec ((if b then (-1 : ℂ) else 1) • _)) Minus = _
  rw [Matrix.mulVec_smul]
  change TensorState ((if b then (-1 : ℂ) else 1) •
    ApplyGate (HadamardN n) (ApplyGate (HadamardN n) (Ket a))) Minus = _
  rw [← applyGate_mul, Qatlib.Papers.QComplexity97.XorSeparation.bv_hadamard_square,
    applyGate_one]
  rfl

/-- The affine Bernstein-Vazirani circuit reads out the secret with probability one using
exactly one query. -/
theorem affine_bernstein_vazirani_readout (n : ℕ) (a : Reg n) (b : Bool) :
    MeasureProb (Run (BitOracleOn (affineParity a b)) (bvOneCallCircuit n)
      (TensorState (Ket (ZeroStr n)) Minus)) ({a} ×ˢ (Finset.univ : Finset Bool)) = 1 ∧
      QueryCount (bvOneCallCircuit n) = 1 := by
  constructor
  · rw [affine_bernstein_vazirani_run, measureProb_tensorState_left normalized_minus]
    cases b <;> simp [MeasureProb, BornProb, Qatlib.Foundations.PureStateMath.Ket]
  · rfl

/-- A Boolean query tree recovering the secret for every affine parity function has maximum
query count at least `n`. -/
theorem affine_classical_lower_bound (n : ℕ)
    (T : Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree (Reg n) (Reg n))
    (hT : ∀ (a : Reg n) (b : Bool),
      (Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.Run (affineParity a b) T).1 = a) :
    n ≤ Qatlib.Concepts.QueryComplexity.DegreeMethod.BoolQueryTree.MaxQueries T := by
  apply parity_classical_zero_error_lower_bound n T
  intro a
  have hf : affineParity a false = bvCharBit a := by
    funext x
    simp [affineParity]
  simpa only [hf] using hT a false

end Qatlib.Papers.QAlgorithms97.MainResults.BernsteinVazirani
