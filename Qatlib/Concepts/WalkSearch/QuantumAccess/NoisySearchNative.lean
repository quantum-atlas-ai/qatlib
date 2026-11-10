/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.QuantumAccess.ResidualDiagnosticContracts
import Mathlib.Tactic.Linarith
import Qatlib.Concepts.QsvtCore.QueryLowerBound.SubroutineExpansion
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false

namespace Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.WalkSearch.Primitives
open Qatlib.Concepts.WalkSearch.QuantumAccess.Walk
open Qatlib.Concepts.WalkSearch.WalkAlgorithms

theorem noisySearch_native_empty_obstruction (ncs : NoisySearch) :
    ¬ NoisySearch.NativeRealized ncs := by
  intro h
  obtain ⟨_circuit, start, _unitary, hnorm, _queries, _born⟩ :=
    h 0 (fun _ => false) (fun _ => false) 0 0 (by simp)
  have hn := hnorm (Classical.choice ncs.seedNe)
  simp [Normalized] at hn

theorem noisySearchNative_obstruction : ¬ NoisySearchNative := by
  intro h
  obtain ⟨ncs, _hexp, _hκ, hnative⟩ := h 3 (by decide)
  exact noisySearch_native_empty_obstruction ncs hnative

theorem false_test_is_sound {N : ℕ} (marked : Fin N → Bool) :
    ∀ v, (false : Bool) = true → marked v = true := by
  simp

theorem sound_test_without_completeness_obstruction (C : Circuit (Fin 2))
    (hC : IsUnitaryCircuit C) (ψ : QState (Fin 2)) (hψ : Normalized ψ)
    (ε : ℝ) (hε : ε < 1 / 2) :
    ¬ (1 - ε ≤ MeasureProb (Run (1 : Matrix (Fin 2) (Fin 2) ℂ) C ψ) {0} ∧
      1 - ε ≤ MeasureProb (Run (1 : Matrix (Fin 2) (Fin 2) ℂ) C ψ) {1}) := by
  intro h
  have hn := normalized_run (1 : Matrix (Fin 2) (Fin 2) ℂ) (by simp) C hC hψ
  change ∑ i : Fin 2, BornProb (Run (1 : Matrix (Fin 2) (Fin 2) ℂ) C ψ) i = 1 at hn
  rw [Fin.sum_univ_two] at hn
  simp only [MeasureProb, Finset.sum_singleton] at h
  linarith [h.1, h.2]

open Qatlib.Concepts.QueryWordCore.AdjointCircuits Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Classical BigOperators

variable {I : Type} [Fintype I] [DecidableEq I]

noncomputable def coherentTestTemplate (j : I) (accept : Finset I) (k : ℕ) : List (AdjointStep I) :=
  repeatAdjointWord [.forward, .gate (ReflectionAbout (outerProduct (Ket j))),
    .backward, .gate (preparedMark accept)] k ++ [.forward]

noncomputable def coherentTestAmplifier (body : List (AdjointStep I))
    (j : I) (accept : Finset I) (k : ℕ) : List (AdjointStep I) :=
  substituteAdjointCircuit body (coherentTestTemplate j accept k)

theorem coherentTestTemplate_actual (A : Matrix I I ℂ) (j : I) (accept : Finset I) (k : ℕ) :
    evaluate A (coherentTestTemplate j accept k) =
      (preparedAAIterate A j accept) ^ k * A ∧
    adjointQueryCount (coherentTestTemplate j accept k) = 2 * k + 1 ∧
    adjointGateCount (coherentTestTemplate j accept k) = 2 * k ∧
    WellFormedAdjointCircuit (coherentTestTemplate j accept k) := by
  have hrep := repeat_adjoint_word_semantics_cost A
    ([.forward, .gate (ReflectionAbout (outerProduct (Ket j))),
      .backward, .gate (preparedMark accept)] : List (AdjointStep I)) k
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [coherentTestTemplate, evaluate_append, hrep.1]
    simp [evaluate, instructionMatrix, preparedAAIterate, Matrix.mul_assoc]
  · simp [coherentTestTemplate, hrep.2.1, adjointQueryCount]
    omega
  · simp [coherentTestTemplate, hrep.2.2.1, adjointGateCount, Nat.mul_comm]
  · apply WellFormedAdjointCircuit.append
    · apply hrep.2.2.2
      simp only [WellFormedAdjointCircuit.forward_cons_iff,
        WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.backward_cons_iff,
        WellFormedAdjointCircuit.nil, and_true]
      exact ⟨outerProduct_reflection_unitary (normalized_ket j),
        (prepared_aa_reflection_and_access (1 : Matrix I I ℂ) j accept (Submonoid.one_mem _)).1⟩
    · simp

theorem coherentTestAmplifier_evaluate_and_cost (O : Matrix I I ℂ)
    (body : List (AdjointStep I)) (j : I) (accept : Finset I) (k : ℕ) :
    evaluate O (coherentTestAmplifier body j accept k) =
      (preparedAAIterate (evaluate O body) j accept) ^ k * evaluate O body ∧
    adjointQueryCount (coherentTestAmplifier body j accept k) =
      (2 * k + 1) * adjointQueryCount body ∧
    adjointGateCount (coherentTestAmplifier body j accept k) =
      2 * k + (2 * k + 1) * adjointGateCount body ∧
    (WellFormedAdjointCircuit body →
      WellFormedAdjointCircuit (coherentTestAmplifier body j accept k)) := by
  have hs := substitute_adjoint_evaluate_cost O body (coherentTestTemplate j accept k)
  have ht := coherentTestTemplate_actual (evaluate O body) j accept k
  exact ⟨hs.1.trans ht.1, by rw [coherentTestAmplifier, hs.2.1, ht.2.1],
    by rw [coherentTestAmplifier, hs.2.2.1, ht.2.2.1, ht.2.1],
    fun hb => hs.2.2.2 hb ht.2.2.2⟩

theorem coherentTestAmplifier_born (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (body : List (AdjointStep I)) (hb : WellFormedAdjointCircuit body)
    (j : I) (accept : Finset I) (k : ℕ) :
    ApplyGate (evaluate O (coherentTestAmplifier body j accept k)) (Ket j) =
      Run (preparedMark accept) (preparedAACircuit (evaluate O body) j k) (Ket j) := by
  have hA := hb.evaluate_unitary hO
  rw [(coherentTestAmplifier_evaluate_and_cost O body j accept k).1,
    (prepared_aa_actual_circuit (evaluate O body) j accept k hA).2.2.2]
  exact applyGate_mul _ _ _

theorem coherentTestAmplifier_success (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (body : List (AdjointStep I)) (hb : WellFormedAdjointCircuit body)
    (j : I) (accept : Finset I) (k : ℕ) (θ : ℝ)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2)
    (hmass : MeasureProb (preparedAAState (evaluate O body) j) accept = (Real.sin θ) ^ 2) :
    MeasureProb (ApplyGate (evaluate O (coherentTestAmplifier body j accept k)) (Ket j)) accept =
      (Real.sin ((2 * (k : ℝ) + 1) * θ)) ^ 2 := by
  rw [coherentTestAmplifier_born O hO body hb j accept k]
  exact prepared_aa_born_success (evaluate O body) j accept θ k
    (hb.evaluate_unitary hO) hθ0 hθ1 hmass

theorem coherentTestAmplifier_zero (O : Matrix I I ℂ) (hO : O ∈ Matrix.unitaryGroup I ℂ)
    (body : List (AdjointStep I)) (hb : WellFormedAdjointCircuit body)
    (j : I) (accept : Finset I) (k : ℕ)
    (hmass : MeasureProb (preparedAAState (evaluate O body) j) accept = 0) :
    MeasureProb (ApplyGate (evaluate O (coherentTestAmplifier body j accept k)) (Ket j)) accept = 0 := by
  rw [coherentTestAmplifier_born O hO body hb j accept k,
    (prepared_aa_endpoint_states (evaluate O body) j accept k (hb.evaluate_unitary hO)).1 hmass]
  exact hmass

theorem coherentTestAmplifier_queries_positive (body : List (AdjointStep I))
    (j : I) (accept : Finset I) (k : ℕ) (hq : 0 < adjointQueryCount body) :
    0 < adjointQueryCount (coherentTestAmplifier body j accept k) := by
  rw [(coherentTestAmplifier_evaluate_and_cost (1 : Matrix I I ℂ) body j accept k).2.1]
  positivity

end Qatlib.Concepts.WalkSearch.QuantumAccess
