/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CircuitImpl.ReflectionCompile.LocalPreparedAmplification
import Mathlib.Tactic
import Qatlib.Papers.GroverSearch96.MainResults.Theorem1Decomposition
import Qatlib.Papers.GroverSearch96.MainResults.SearchBounds

/-!
# Local implementation and readout of Grover search

The prepared amplitude amplification construction is identified with the source Grover oracle,
reflection, and state. The local circuit realizes this state in a clean ancillary embedding and
has explicit query and gate counts.

`measure_clean_embed` and `local_source_readout` transfer marked measurement probabilities to
the enlarged register. `local_source_singleton_algorithm` combines these identities with
normalization and a singleton search success bound. See [Grover1996].

## Main statements

* `local_source_grover_state_and_cost`: The local circuit with the lifted set oracle produces
  the embedded Grover state, uses exactly `k` queries and at most `(34*k+1)*n` gates, and is
  unitary.
* `local_source_readout`: The marked data readout of the local circuit equals the success
  probability of `GroverState S k`.
* `local_source_singleton_algorithm`: For `n ≥ 1`, a unitary local singleton search circuit uses
  `k ≤ (π/4) * sqrt (2^n)` queries and at most `(34*k+1)*n` gates, with normalized input and
  outputs and success probability at least `1/2` for every target.

## References

* [Grover, 1996][Grover1996]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation Qatlib.Concepts.CircuitImpl.ReflectionCompile

open Matrix
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.QueryWordCore.QueryMachinery
namespace Qatlib.Papers.GroverSearch96.MainResults

/-- The prepared marking operator for `S` equals the source set oracle `SetOracle S`. -/
theorem prepared_mark_eq_source_oracle (n : ℕ) (S : Finset (Reg n)) :
    preparedMark S = SetOracle S := by
  ext x y
  simp only [preparedMark, SetOracle, PhaseOracle, Qatlib.Foundations.InstrumentCore.Measurement.Projector, Matrix.sub_apply,
    Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hxy : x=y
  · subst y
    by_cases hx : x∈S <;> norm_num [hx]
  · simp [hxy]

/-- Reflection about the zero basis state equals `ZeroPhaseReflection n`. -/
theorem zero_ket_reflection_eq_source (n : ℕ) :
    ReflectionAbout (outerProduct (Ket (ZeroStr n))) = ZeroPhaseReflection n := by
  ext x y
  simp only [ReflectionAbout, outerProduct, Qatlib.Foundations.PureStateMath.Ket, ZeroPhaseReflection,
    Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.diagonal_apply,
    Matrix.of_apply, smul_eq_mul]
  by_cases hxy : x=y <;> by_cases hx : x=ZeroStr n <;>
    by_cases hy : y=ZeroStr n <;> simp_all
  all_goals norm_num

/-- The tensor Hadamard operator `HadamardN n` is self adjoint. -/
theorem source_hadamard_adjoint (n : ℕ) : (HadamardN n)ᴴ = HadamardN n := by
  ext x y
  simp only [Matrix.conjTranspose_apply, RCLike.star_def, hadamardN_conj]
  simp [HadamardN, Hadamard, and_comm]

/-- Prepared amplitude amplification using `HadamardN n` and the zero basis state produces
`GroverState S k`. -/
theorem prepared_aa_eq_source_grover (n k : ℕ) (S : Finset (Reg n)) :
    Run (preparedMark S) (preparedAACircuit (HadamardN n) (ZeroStr n) k)
      (Ket (ZeroStr n)) = GroverState S k := by
  have hword : preparedAACircuit (HadamardN n) (ZeroStr n) k =
      [Step.gate (HadamardN n)] ++ ExpandedCircuit n k := by
    simp only [preparedAACircuit, source_hadamard_adjoint,
      zero_ket_reflection_eq_source, ExpandedCircuit, ExpandedStep, DiffusionCircuit]
  rw [hword, run_append, run_gate, run_nil, applyGate_hadamardN_ket_zero,
    prepared_mark_eq_source_oracle, run_expandedCircuit]
  rfl

/-- The local prepared circuit realizes the embedded prepared state, uses `k` queries and
`(2*k+1)*n + k*localReflectionCost n` gates, and is unitary; its gate count is at most
`(34*k+1)*n`. -/
theorem local_grover_actual_state_and_cost (n k : ℕ) (S : Finset (Reg n)) :
    Run (reflectionLift n (preparedMark S))
      (localPreparedAACircuit n (localHadamardReflectionSteps n) k)
      (reflectionEmbed n (Ket (fun _ => false))) =
      reflectionEmbed n (Run (preparedMark S)
        (preparedAACircuit (HadamardN n) (fun _ => false) k) (Ket (fun _ => false))) ∧
    QueryCount (localPreparedAACircuit n (localHadamardReflectionSteps n) k) = k ∧
    GateCount (localPreparedAACircuit n (localHadamardReflectionSteps n) k) =
      (2*k+1)*n+k*localReflectionCost n ∧
    GateCount (localPreparedAACircuit n (localHadamardReflectionSteps n) k) ≤ (34*k+1)*n ∧
    IsUnitaryCircuit (localPreparedAACircuit n (localHadamardReflectionSteps n) k) := by
  have h := local_prepared_aa_actual_state_and_three_counts n k
    (localHadamardReflectionSteps n) S (localHadamardReflectionSteps_legal n)
  dsimp only at h
  rw [localHadamardReflectionSteps_matrix] at h
  rw [localHadamardReflectionSteps_length] at h
  refine ⟨h.1,h.2.1,h.2.2,?_,
    localPreparedAACircuit_unitary n k _ (localHadamardReflectionSteps_legal n)⟩
  rw [h.2.2]
  have hc : localReflectionCost n ≤ 32*n := by
    unfold localReflectionCost
    split_ifs <;> omega
  calc
    (2*k+1)*n+k*localReflectionCost n ≤ (2*k+1)*n+k*(32*n) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left k hc) _
    _ = (34*k+1)*n := by ring

/-- The local circuit with the lifted set oracle produces the embedded Grover state, uses
exactly `k` queries and at most `(34*k+1)*n` gates, and is unitary. See [Grover1996]. -/
theorem local_source_grover_state_and_cost (n k : ℕ) (S : Finset (Reg n)) :
    Run (reflectionLift n (SetOracle S))
      (localPreparedAACircuit n (localHadamardReflectionSteps n) k)
      (reflectionEmbed n (Ket (ZeroStr n))) = reflectionEmbed n (GroverState S k) ∧
    QueryCount (localPreparedAACircuit n (localHadamardReflectionSteps n) k) = k ∧
    GateCount (localPreparedAACircuit n (localHadamardReflectionSteps n) k) ≤ (34*k+1)*n ∧
    IsUnitaryCircuit (localPreparedAACircuit n (localHadamardReflectionSteps n) k) := by
  obtain ⟨h,hq,_,hg,hu⟩ := local_grover_actual_state_and_cost n k S
  have hs := h.trans (congrArg (reflectionEmbed n) (prepared_aa_eq_source_grover n k S))
  rw [prepared_mark_eq_source_oracle] at hs
  exact ⟨hs,hq,hg,hu⟩

/-- Measuring the data component of a clean ancillary embedding gives the same probability for
`S` as measuring the original state. -/
theorem measure_clean_embed (n : ℕ) (ψ : QState (Reg n)) (S : Finset (Reg n)) :
    MeasureProb (reflectionEmbed n ψ)
      (Finset.univ.filter (fun z => (reflectionSplit n z).1 ∈ S)) = MeasureProb ψ S := by
  classical
  unfold MeasureProb
  rw [Finset.sum_filter]
  calc
    (∑ z : Reg (n+(n-1)), if (reflectionSplit n z).1 ∈ S then
      BornProb (reflectionEmbed n ψ) z else 0) =
      ∑ p : Reg n × Reg (n-1), if p.2 = (fun _ => false) then
        (if p.1 ∈ S then BornProb ψ p.1 else 0) else 0 := by
      apply Fintype.sum_equiv (reflectionSplit n)
      intro z
      simp only [BornProb, reflectionEmbed]
      split_ifs <;> simp_all
    _ = ∑ x ∈ S, BornProb ψ x := by
      rw [Fintype.sum_prod_type]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      rw [← Finset.sum_filter]
      simp

/-- The marked data readout of the local circuit equals the success probability of `GroverState
S k`. See [Grover1996]. -/
theorem local_source_readout (n k : ℕ) (S : Finset (Reg n)) :
    MeasureProb (Run (reflectionLift n (SetOracle S))
      (localPreparedAACircuit n (localHadamardReflectionSteps n) k)
      (reflectionEmbed n (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n))))
      (Finset.univ.filter (fun z => (reflectionSplit n z).1 ∈ S)) =
      MeasureProb (GroverState S k) S := by
  rw [(local_source_grover_state_and_cost n k S).1, measure_clean_embed]

/-- A clean ancillary embedding of a normalized state is normalized. -/
theorem normalized_clean_embed (n : ℕ) (ψ : QState (Reg n)) (hψ : Normalized ψ) :
    Normalized (reflectionEmbed n ψ) := by
  have hmass : MeasureProb ψ Finset.univ = 1 := by
    simpa [MeasureProb, BornProb, Normalized] using hψ
  have h := (measure_clean_embed n ψ Finset.univ).trans hmass
  simpa [MeasureProb, BornProb, Normalized] using h

/-- For `n ≥ 1`, a unitary local singleton search circuit uses `k ≤ (π/4) * sqrt (2^n)` queries
and at most `(34*k+1)*n` gates, with normalized input and outputs and success probability at
least `1/2` for every target. See [Grover1996]. -/
theorem local_source_singleton_algorithm (n : ℕ) (hn : 1 ≤ n) :
    ∃ k : ℕ, (k : ℝ) ≤ Real.pi/4 * Real.sqrt (2^n : ℝ) ∧
      QueryCount (localPreparedAACircuit n (localHadamardReflectionSteps n) k) = k ∧
      GateCount (localPreparedAACircuit n (localHadamardReflectionSteps n) k) ≤ (34*k+1)*n ∧
      IsUnitaryCircuit (localPreparedAACircuit n (localHadamardReflectionSteps n) k) ∧
      Normalized (reflectionEmbed n (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n))) ∧
      ∀ w : Reg n,
        Normalized (Run (reflectionLift n (SetOracle {w}))
          (localPreparedAACircuit n (localHadamardReflectionSteps n) k)
          (reflectionEmbed n (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n)))) ∧
        (1/2 : ℝ) ≤ MeasureProb (Run (reflectionLift n (SetOracle {w}))
          (localPreparedAACircuit n (localHadamardReflectionSteps n) k)
          (reflectionEmbed n (Qatlib.Foundations.PureStateMath.Ket (ZeroStr n))))
          (Finset.univ.filter (fun z => (reflectionSplit n z).1 = w)) := by
  have hN : 2 ≤ Fintype.card (Reg n) := by
    rw [card_reg]
    calc 2 = 2^1 := by norm_num
         _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) hn
  let k := groverIterations (knownCountAngle ((1 : ℝ)/Fintype.card (Reg n)))
  have hcost := local_source_grover_state_and_cost n k ∅
  refine ⟨k,?_,hcost.2.1,hcost.2.2.1,hcost.2.2.2,
    normalized_clean_embed n _ (normalized_ket _),?_⟩
  · have hb := knownCount_query_budget (I := Reg n) (m := 1)
      (by norm_num) (by omega : 1 < Fintype.card (Reg n))
    simp only [Nat.cast_one] at hb
    rw [budget_rewrite] at hb
    exact hb
  · intro w
    constructor
    · rw [(local_source_grover_state_and_cost n k {w}).1]
      exact normalized_clean_embed n _ (normalized_groverState Fintype.card_pos {w} k)
    · have hs := knownCount_success (I := Reg n) Fintype.card_pos ({w} : Finset (Reg n))
        (m := 1) (by simp) (by norm_num) (by omega : 1 < Fintype.card (Reg n))
      simp only [Nat.cast_one] at hs
      have hq : (1 : ℝ)/Fintype.card (Reg n) ≤ 1/2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by norm_num)
        exact_mod_cast hN
      have hread := local_source_readout n k ({w} : Finset (Reg n))
      simp only [Finset.mem_singleton] at hread
      rw [hread]
      exact (show (1/2 : ℝ) ≤ 1 - (1 : ℝ)/Fintype.card (Reg n) by linarith).trans hs

end Qatlib.Papers.GroverSearch96.MainResults
