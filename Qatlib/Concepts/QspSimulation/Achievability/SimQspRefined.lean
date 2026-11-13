/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.JacobiAnger.SimQspDefs
import Qatlib.Concepts.RandCompile.ChannelBudget.QspSimulation
import Qatlib.Concepts.QspSimulation.Achievability.ComputedSignalConsumers

/-!
# Refined endpoints for QSP Hamiltonian simulation

This module exposes certificates connecting computed phase packets, Jacobi-Anger degree
selection, resource accounting, and noisy-oracle execution. `clause11_endpoint` combines the
near-optimal truncation count with the identities identifying the synthesized cosine and sine
packets and a comparison of the declared analytic and exhaustive phase costs. The truncation
estimate is in the Hamiltonian-simulation setting of [LowChuang2017].

`clause12_endpoint` combines time continuity and rational time reads with the fields of
`simQspLedger` and a norm bound for the output of `computedSignalWord`. For a unitary oracle
within distance `δ` of the encoded oracle, `simQsp_single_output_error` adds the dyadic
truncation error to the query count times `δ`.

## Main statements

* `analyticCosinePacket_exhaustive` and `analyticSinePacket_exhaustive` identify the outputs of
  finite phase synthesis.
* `simJaCount_near_optimal` gives the two-sided degree comparison and the factorial truncation
  bound.
* `hamiltonianEvolution_time_lipschitz` bounds time perturbations by the time difference times
  the Hamiltonian norm.
* `simQspLedger_spec` identifies the declared qubit, gate, query, perturbation, and truncation
  quantities.
* `simQsp_single_output_error` bounds the error on the framed input state.
* `clause11_endpoint` and `clause12_endpoint` assemble the synthesis and execution certificates.

## References

* [Low and Chuang, 2017][LowChuang2017]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

/-- Finite phase synthesis for the computed cosine coefficients returns the selected analytic
cosine phase packet. -/
theorem analyticCosinePacket_exhaustive (t : ℚ) (k : ℕ) :
    (finitePhaseSynthesis (computedCosCoefficients (t / (computedSignalSegments t : ℚ))
      (computedSignalCutoff t k)) (2 * computedSignalCutoff t k)
      (computedSignalTolerance t k)).value
      = some (analyticPhasePacket t k true) := by
  have h := Qatlib.Concepts.QspSimulation.JacobiAnger.computed_signal_synthesized_packets t k
  have h1 := (Classical.choose_spec (Classical.choose_spec h)).1
  dsimp only [analyticPhasePacket]
  exact h1

/-- Finite phase synthesis for the computed sine coefficients returns the selected analytic sine
phase packet. -/
theorem analyticSinePacket_exhaustive (t : ℚ) (k : ℕ) :
    (finitePhaseSynthesis (computedSinCoefficients (t / (computedSignalSegments t : ℚ))
      (computedSignalCutoff t k)) (2 * computedSignalCutoff t k + 1)
      (computedSignalTolerance t k)).value
      = some (analyticPhasePacket t k false) := by
  have h := Qatlib.Concepts.QspSimulation.JacobiAnger.computed_signal_synthesized_packets t k
  have h2 := (Classical.choose_spec (Classical.choose_spec h)).2.1
  dsimp only [analyticPhasePacket]
  exact h2

/-- When the computed cutoff is at least one, the declared analytic phase cost is strictly less
than the exhaustive phase cost. -/
theorem analyticPhaseCost_lt_exhaustive (t : ℚ) (k : ℕ) (hk : 1 ≤ computedSignalCutoff t k) :
    analyticPhaseCost t k < exhaustivePhaseCost t k := by
  have hpc : 1 ≤ phaseConstant (2 * computedSignalCutoff t k + 1) := by
    have := phaseConstant_pos (2 * computedSignalCutoff t k + 1)
    omega
  have hclog : 1 ≤ Nat.clog 2 (32 * phaseConstant (2 * computedSignalCutoff t k + 1)) := by
    have h1 : 2 ≤ 32 * phaseConstant (2 * computedSignalCutoff t k + 1) := by omega
    by_contra h
    have h2 : Nat.clog 2 (32 * phaseConstant (2 * computedSignalCutoff t k + 1)) ≤ 0 := by omega
    rw [Nat.clog_le_iff_le_pow (by omega : (1 : ℕ) < 2)] at h2
    have h2' : 32 * phaseConstant (2 * computedSignalCutoff t k + 1) ≤ 1 := by simpa using! h2
    omega
  have hr1 : 1 ≤ Qatlib.Concepts.QspSimulation.JacobiAnger.phaseGridBits (2 * computedSignalCutoff t k + 1)
      (Qatlib.Concepts.QspSimulation.JacobiAnger.phaseToleranceBits (computedSignalTolerance t k)) := by
    unfold Qatlib.Concepts.QspSimulation.JacobiAnger.phaseGridBits Qatlib.Concepts.NativeNumerics.PhaseSynthesis.phaseGridBits
    omega
  have hpow : 2 ≤ 2 ^ Qatlib.Concepts.QspSimulation.JacobiAnger.phaseGridBits (2 * computedSignalCutoff t k + 1)
      (Qatlib.Concepts.QspSimulation.JacobiAnger.phaseToleranceBits (computedSignalTolerance t k)) := by
    have hh := Nat.one_lt_two_pow (by
      omega : Qatlib.Concepts.QspSimulation.JacobiAnger.phaseGridBits (2 * computedSignalCutoff t k + 1)
        (Qatlib.Concepts.QspSimulation.JacobiAnger.phaseToleranceBits (computedSignalTolerance t k)) ≠ 0)
    omega
  have hlt : (2 * computedSignalCutoff t k + 1) + 1 < 2 ^ (2 * computedSignalCutoff t k + 2) := by
    have hall : ∀ m : ℕ, m + 1 < 2 ^ (m + 1) := by
      intro m
      induction m with
      | zero => simp
      | succ n ih =>
        have hh : 2 ^ (n + 2) = 2 ^ (n + 1) * 2 := by rw [pow_succ]
        omega
    exact hall (2 * computedSignalCutoff t k + 1)
  have hexp : 2 ^ (2 * computedSignalCutoff t k + 2)
      ≤ (2 ^ Qatlib.Concepts.QspSimulation.JacobiAnger.phaseGridBits (2 * computedSignalCutoff t k + 1)
        (Qatlib.Concepts.QspSimulation.JacobiAnger.phaseToleranceBits (computedSignalTolerance t k))) ^ (2 * computedSignalCutoff t k + 2) :=
    Nat.pow_le_pow_left hpow _
  show computedSignalCutoff t k + 1 <
      (2 ^ Qatlib.Concepts.QspSimulation.JacobiAnger.phaseGridBits (2 * computedSignalCutoff t k + 1)
        (Qatlib.Concepts.QspSimulation.JacobiAnger.phaseToleranceBits (computedSignalTolerance t k))) ^ (2 * computedSignalCutoff t k + 2)
  omega

/-- On `JaDomain`, the Jacobi-Anger count lies between the ideal shape and eleven times that
shape, and its factorial remainder bound is at most `ε / 8`. This expresses the truncation
scale used in [LowChuang2017]. -/
theorem simJaCount_near_optimal (τ ε : ℝ) (h : JaDomain τ ε) :
    jaIdealShape τ ε ≤ (jaCount τ ε : ℝ) ∧
      (jaCount τ ε : ℝ) ≤ 11 * jaIdealShape τ ε ∧
      4 * τ ^ (jaCount τ ε : ℝ) /
          (2 ^ (jaCount τ ε : ℝ) * (jaCount τ ε).factorial : ℝ) ≤ ε / 8 :=
  Qatlib.Concepts.RandCompile.ChannelBudget.jaCount_near_optimal τ ε h

/-- For a Hermitian Hamiltonian, the operator-norm distance between evolutions at two times is
at most the absolute time difference times the Hamiltonian norm. -/
theorem hamiltonianEvolution_time_lipschitz (D : ℕ) (H : Operator D) (t₁ t₂ : ℝ)
    (hH : H.IsHermitian) :
    ‖HamiltonianEvolution H t₁ - HamiltonianEvolution H t₂‖ ≤ |t₁ - t₂| * ‖H‖ := by
  have hsplit : HamiltonianEvolution H t₁
      = HamiltonianEvolution H t₂ * HamiltonianEvolution H (t₁ - t₂) := by
    rw [← hamiltonianEvolution_add H t₂ (t₁ - t₂)]
    congr 1
    ring
  rw [hsplit]
  have hnorm : ‖HamiltonianEvolution H t₂‖ ≤ 1 :=
    l2_norm_unitary_le_one (hamiltonianEvolution_unitary hH t₂)
  have hrem := (hamiltonian_exponential_lipschitz_and_quadratic D H (t₁ - t₂) hH).1
  calc ‖HamiltonianEvolution H t₂ * HamiltonianEvolution H (t₁ - t₂) - HamiltonianEvolution H t₂‖
      = ‖HamiltonianEvolution H t₂ * (HamiltonianEvolution H (t₁ - t₂) - 1)‖ := by
        rw [Matrix.mul_sub]
        simp only [Matrix.mul_one]
    _ ≤ ‖HamiltonianEvolution H t₂‖ * ‖HamiltonianEvolution H (t₁ - t₂) - 1‖ :=
        norm_mul_le _ _
    _ ≤ 1 * (|t₁ - t₂| * ‖H‖) := by
        calc ‖HamiltonianEvolution H t₂‖ * ‖HamiltonianEvolution H (t₁ - t₂) - 1‖
            ≤ 1 * ‖HamiltonianEvolution H (t₁ - t₂) - 1‖ :=
              mul_le_mul_of_nonneg_right hnorm (norm_nonneg _)
          _ ≤ 1 * (|t₁ - t₂| * ‖H‖) := by
              exact mul_le_mul_of_nonneg_left hrem (by norm_num)
    _ = |t₁ - t₂| * ‖H‖ := by ring

/-- A certified rational time read at precision `k` has absolute error at most `2⁻ᵏ`. -/
theorem simQspTimeRead_certified {x : ℝ} {q : ℕ → ℚ} (h : simQspTimeRead x q) (k : ℕ) :
    |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k := h k

/-- Identifies the ledger's qubit count, fixed-gate count, and oracle-query count, together with
query count times `δ` and the dyadic truncation error. -/
theorem simQspLedger_spec {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (F : Matrix H I ℂ) (t : ℚ) (k : ℕ) (δ : ℝ) :
    (simQspLedger F t k δ).qubits = hostingQubits (Fintype.card H) ∧
    (simQspLedger F t k δ).fixedGates = adjointGateCount (computedSignalWord F t k) ∧
    (simQspLedger F t k δ).oracleQueries = adjointQueryCount (computedSignalWord F t k) ∧
    (simQspLedger F t k δ).failureRate = (adjointQueryCount (computedSignalWord F t k) : ℝ) * δ ∧
    (simQspLedger F t k δ).truncationError = (1 / 2 : ℝ) ^ k := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl

/-- For a Hermitian encoded matrix and a unitary oracle within distance `δ` of the exact oracle,
the computed word's framed output error is at most the ledger's truncation error plus query
perturbation budget, multiplied by the input norm. -/
theorem simQsp_single_output_error :
    ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      (A : Matrix I I ℂ) (U V : Matrix H H ℂ) (F : Matrix H I ℂ) (t : ℚ) (k : ℕ) (δ : ℝ),
      A.IsHermitian → ProjectedUnitaryEncoding A U F F → V ∈ Matrix.unitaryGroup H ℂ →
      0 ≤ δ → ‖V - U‖ ≤ δ →
      let cs := computedSignalWord F t k
      let O := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J := Bool) V))
      ∀ ψ : QState I,
        ‖toEuclidean_fromVec (evaluate O cs *ᵥ (scaleEightFrame (hamiltonianFrame F) *ᵥ ψ) -
          scaleEightFrame (hamiltonianFrame F) *ᵥ (hamiltonianEvolution A (t : ℝ) *ᵥ ψ))‖ ≤
          ((simQspLedger F t k δ).truncationError + (simQspLedger F t k δ).failureRate) *
            ‖toEuclidean_fromVec ψ‖ := by
  intro H I _ _ _ _ A U V F t k δ hA h hV hδ hVU
  (try dsimp only)
  have h := computed_signal_oracle_noise_and_inverse H I A U V F t k δ hA h hV hδ hVU
  intro ψ
  have hbound := h.2.2 ψ
  simp only [simQspLedger] at hbound ⊢
  exact hbound

/-- The rational read program evaluates to the sum of segment count, cutoff, dyadic target
error, and computed phase tolerance. -/
theorem simQspReadProgram_eval (t : ℚ) (k : ℕ) :
    ratEval (simQspReadProgram t k) =
      (computedSignalSegments t : ℚ) + (computedSignalCutoff t k : ℚ) +
        ((1 / 2 : ℚ) ^ k) + computedSignalTolerance t k := by
  unfold simQspReadProgram ratAdd ratLit ratEval
  simp only [Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs.RatProgram.eval]
  ring

/-- Combines the Jacobi-Anger degree and remainder bounds with the finite-synthesis packet
identities and strict comparison of declared analytic and exhaustive phase costs. The
approximation component is in the setting of [LowChuang2017]. -/
theorem clause11_endpoint : ∀ (τ ε : ℝ), JaDomain τ ε →
    (jaIdealShape τ ε ≤ (jaCount τ ε : ℝ) ∧
      (jaCount τ ε : ℝ) ≤ 11 * jaIdealShape τ ε ∧
      4 * τ ^ (jaCount τ ε : ℝ) /
          (2 ^ (jaCount τ ε : ℝ) * (jaCount τ ε).factorial : ℝ) ≤ ε / 8) ∧
    (∀ (t : ℚ) (k : ℕ),
      (finitePhaseSynthesis (computedCosCoefficients (t / (computedSignalSegments t : ℚ))
        (computedSignalCutoff t k)) (2 * computedSignalCutoff t k)
        (computedSignalTolerance t k)).value
        = some (analyticPhasePacket t k true) ∧
      (finitePhaseSynthesis (computedSinCoefficients (t / (computedSignalSegments t : ℚ))
        (computedSignalCutoff t k)) (2 * computedSignalCutoff t k + 1)
        (computedSignalTolerance t k)).value
        = some (analyticPhasePacket t k false)) ∧
    (∀ (t : ℚ) (k : ℕ), 1 ≤ computedSignalCutoff t k →
      analyticPhaseCost t k < exhaustivePhaseCost t k) := by
  intro τ ε h
  refine ⟨simJaCount_near_optimal τ ε h, ?_, ?_⟩
  · intro t k
    exact ⟨analyticCosinePacket_exhaustive t k, analyticSinePacket_exhaustive t k⟩
  · intro t k hk
    exact analyticPhaseCost_lt_exhaustive t k hk

/-- Collects Hamiltonian time continuity, certified rational time reads, the resource-ledger
identities, the noisy-oracle output bound, and evaluation of the rational read program. -/
theorem clause12_endpoint : ∀ (H I : Type) [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (U V : Matrix H H ℂ) (F : Matrix H I ℂ) (t : ℚ) (k : ℕ) (δ : ℝ),
    A.IsHermitian → ProjectedUnitaryEncoding A U F F → V ∈ Matrix.unitaryGroup H ℂ →
    0 ≤ δ → ‖V - U‖ ≤ δ →
    (∀ (D : ℕ) (H : Operator D) (t₁ t₂ : ℝ), H.IsHermitian →
      ‖HamiltonianEvolution H t₁ - HamiltonianEvolution H t₂‖ ≤ |t₁ - t₂| * ‖H‖) ∧
    (∀ (x : ℝ) (q : ℕ → ℚ), simQspTimeRead x q → ∀ k, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k) ∧
    (simQspLedger F t k δ).qubits = hostingQubits (Fintype.card H) ∧
    (simQspLedger F t k δ).fixedGates = adjointGateCount (computedSignalWord F t k) ∧
    (simQspLedger F t k δ).oracleQueries = adjointQueryCount (computedSignalWord F t k) ∧
    (simQspLedger F t k δ).failureRate = (adjointQueryCount (computedSignalWord F t k) : ℝ) * δ ∧
    (simQspLedger F t k δ).truncationError = (1 / 2 : ℝ) ^ k ∧
    (let cs := computedSignalWord F t k
     let O := TensorGate (1 : Matrix Bool Bool ℂ) (controlOracle (parallelOracle (J := Bool) V))
     ∀ ψ : QState I,
       ‖toEuclidean_fromVec (evaluate O cs *ᵥ (scaleEightFrame (hamiltonianFrame F) *ᵥ ψ) -
         scaleEightFrame (hamiltonianFrame F) *ᵥ (hamiltonianEvolution A (t : ℝ) *ᵥ ψ))‖ ≤
         ((simQspLedger F t k δ).truncationError + (simQspLedger F t k δ).failureRate) *
           ‖toEuclidean_fromVec ψ‖) ∧
    (∀ (t : ℚ) (k : ℕ),
      ratEval (simQspReadProgram t k) =
        (computedSignalSegments t : ℚ) + (computedSignalCutoff t k : ℚ) +
          ((1 / 2 : ℚ) ^ k) + computedSignalTolerance t k) := by
  intro H I _ _ _ _ A U V F t k δ hA h hV hδ hVU
  have hL : ∀ (D : ℕ) (H : Operator D) (t₁ t₂ : ℝ), H.IsHermitian →
      ‖HamiltonianEvolution H t₁ - HamiltonianEvolution H t₂‖ ≤ |t₁ - t₂| * ‖H‖ :=
    fun D H t₁ t₂ hH => hamiltonianEvolution_time_lipschitz D H t₁ t₂ hH
  have hT : ∀ (x : ℝ) (q : ℕ → ℚ), simQspTimeRead x q →
      ∀ k, |x - (q k : ℝ)| ≤ (1 / 2 : ℝ) ^ k := by
    intro x q hx k
    exact simQspTimeRead_certified hx k
  obtain ⟨hq, hf, ho, hfr, ht⟩ := simQspLedger_spec F t k δ
  have hE := simQsp_single_output_error H I A U V F t k δ hA h hV hδ hVU
  refine ⟨hL, hT, hq, hf, ho, hfr, ht, ?_, ?_⟩
  · exact hE
  · intro t' k'
    exact simQspReadProgram_eval t' k'

end Qatlib.Concepts.QspSimulation.Achievability
