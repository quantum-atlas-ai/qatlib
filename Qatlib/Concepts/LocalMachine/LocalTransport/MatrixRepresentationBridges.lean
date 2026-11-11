/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.MatrixRepresentationBridgesDefs
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.OrderedSpectralPerturbation
import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
import Qatlib.Concepts.SpectralSketch.NearIsometry
import Qatlib.Concepts.MatrixAccess.FrameFilterUse
import Qatlib.Concepts.MatrixAccess.KnownFrameSynth.KnownFrameLocalConsumers
import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncodingConsumers
import Qatlib.Concepts.LocalMachine.LocalTransport.LeastSquaresOutputSpec
import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.GramQueryCore.GramRealization.GramQueryRealization
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Ring.BooleanRing

/-!
# Matrix representation bridges and counterexamples

This module connects phase recovery, near-isometric frames, sparse overlap encodings, quantized
matrices, and finite numerical circuit representations. The singular value transformation
viewpoint is developed in [GilyenSuLowWiebe2019]; the bridge statements here include their
explicit hypotheses, error estimates, and recorded resource bounds.

Alongside the positive results `clause33`, `clause41`, `clause45`, `optGoal`, and `tunableGoal`,
the module gives counterexamples to several proposed universal representation statements. These
identify failures involving noncontractive frame filters, the stated dynamic-schedule predicate,
access-count bookkeeping, and column indexing.

## Main statements

* `clause33`: construct a phase recovery record with polynomially bounded recorded cost and
  conditional certificates.
* `optGoal`: combine polar correction estimates with finite frame synthesis.
* `tunableGoal`: combine dyadic quantization, spectral perturbation, and postselection bounds.
* `frame_filter_noncontractive_counterexample`: refute a uniform frame-filter error bound for
  unrestricted circuit matrices.
* `one_wire_unitary_without_dynamic_schedule`: exhibit a unitary excluded by the specified
  schedule conditions.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.RationalCayleyPhase Qatlib.Concepts.MonteCarloMean.PayoffRotation
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.GramQueryCore.GramRealization
open Qatlib.Concepts.MatrixAccess.FrameFilterProd
open Qatlib.Concepts.MatrixAccess.FrameFilterUse
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralSketch.NearIsometry
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.BlockEncoding.EncodingCore

namespace Qatlib.Concepts.LocalMachine.LocalTransport

open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel Qatlib.Concepts.NonNormalSpec.ResolventWord
open scoped Matrix.Norms.L2Operator

/-- Replace fixed gates by identity gates and replace either direction of oracle query by a
query step. -/
private def toFiniteBackendStep {N : ℕ} : AdjointStep (Reg N) → Step (Reg N)
  | .gate _ => .gate (1 : Matrix (Reg N) (Reg N) ℂ)
  | .forward => .query
  | .backward => .query

/-- Every gate produced by `toFiniteBackendStep` has identity matrix. -/
private theorem toFiniteBackendStep_gate_eq {N : ℕ} (s : AdjointStep (Reg N))
    (U : Matrix (Reg N) (Reg N) ℂ) (h : toFiniteBackendStep s = Step.gate U) : U = 1 := by
  cases s with
  | gate V =>
    have h' : (1 : Matrix (Reg N) (Reg N) ℂ) = U := by simpa [toFiniteBackendStep] using! h
    exact h'.symm
  | forward => simp [toFiniteBackendStep] at h
  | backward => simp [toFiniteBackendStep] at h

/-- Mapping instructions through `toFiniteBackendStep` preserves the oracle query count. -/
private theorem queryCount_map_toFiniteBackendStep {N : ℕ} (cs : List (AdjointStep (Reg N))) :
    QueryCount (cs.map toFiniteBackendStep) = adjointQueryCount cs := by
  induction cs with
  | nil => rfl
  | cons s cs ih =>
    cases s <;> simp [toFiniteBackendStep, adjointQueryCount, ih]

/-- Mapping instructions through `toFiniteBackendStep` preserves the fixed gate count. -/
private theorem gateCount_map_toFiniteBackendStep {N : ℕ} (cs : List (AdjointStep (Reg N))) :
    GateCount (cs.map toFiniteBackendStep) = adjointGateCount cs := by
  induction cs with
  | nil => rfl
  | cons s cs ih =>
    cases s <;> simp [toFiniteBackendStep, adjointGateCount, ih]

/-- The circuit obtained by replacing fixed gates with identities lies on the numerical finite
backend at every precision. -/
private theorem onFiniteBackend_map_toFiniteBackendStep {N : ℕ} (k : ℕ)
    (cs : List (AdjointStep (Reg N))) : OnFiniteBackend k (cs.map toFiniteBackendStep) := by
  intro U hU
  obtain ⟨s, -, he⟩ := List.mem_map.mp hU
  have hU1 : U = 1 := toFiniteBackendStep_gate_eq s U he
  subst hU1
  exact ⟨[], rfl⟩

/-- The circuit obtained through `toFiniteBackendStep` has unitary fixed gates. -/
private theorem isUnitaryCircuit_map_toFiniteBackendStep {N : ℕ}
    (cs : List (AdjointStep (Reg N))) : IsUnitaryCircuit (cs.map toFiniteBackendStep) := by
  intro U hU
  obtain ⟨s, -, he⟩ := List.mem_map.mp hU
  have hU1 : U = 1 := toFiniteBackendStep_gate_eq s U he
  subst hU1
  exact (Matrix.unitaryGroup (Reg N) ℂ).one_mem

/-- Every instruction in a well-formed adjoint-query circuit with unitary oracle has operator
norm at most one. -/
private theorem instruction_norm_le {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ)
    (cs : List (AdjointStep (Reg N))) (hO : O ∈ Matrix.unitaryGroup (Reg N) ℂ)
    (hcs : WellFormedAdjointCircuit cs) (s : AdjointStep (Reg N)) (hs : s ∈ cs) :
    ‖instructionMatrix O s‖ ≤ 1 := by
  cases s with
  | gate V => exact unitary_norm_le_one (hcs V hs)
  | forward => exact unitary_norm_le_one hO
  | backward =>
    simp only [instructionMatrix]
    rw [Matrix.l2_opNorm_conjTranspose]
    exact unitary_norm_le_one hO

/-- With a unitary oracle, running the circuit produced by `toFiniteBackendStep` cannot increase
the Euclidean norm. -/
private theorem run_toFiniteBackendStep_norm_le {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ)
    (hO : O ∈ Matrix.unitaryGroup (Reg N) ℂ) (cs : List (AdjointStep (Reg N)))
    (ψ : QState (Reg N)) :
    ‖toEuclidean_fromVec (Run O (cs.map toFiniteBackendStep) ψ)‖ ≤ ‖toEuclidean_fromVec ψ‖ := by
  have hOle : ‖O‖ ≤ 1 := unitary_norm_le_one hO
  induction cs generalizing ψ with
  | nil => simp
  | cons s cs ih =>
    cases s with
    | gate V =>
      simp only [List.map_cons, toFiniteBackendStep, Run]
      have h1 : ApplyGate (1 : Matrix (Reg N) (Reg N) ℂ) ψ = ψ := by simp [ApplyGate]
      rw [h1]
      exact ih ψ
    | forward =>
      simp only [List.map_cons, toFiniteBackendStep, Run]
      calc ‖toEuclidean_fromVec (Run O (cs.map toFiniteBackendStep) (ApplyGate O ψ))‖ ≤
          ‖toEuclidean_fromVec (ApplyGate O ψ)‖ := ih _
        _ ≤ ‖O‖ * ‖toEuclidean_fromVec ψ‖ := norm_applyGate_le O ψ
        _ ≤ 1 * ‖toEuclidean_fromVec ψ‖ := mul_le_mul_of_nonneg_right hOle (norm_nonneg _)
        _ = ‖toEuclidean_fromVec ψ‖ := one_mul _
    | backward =>
      simp only [List.map_cons, toFiniteBackendStep, Run]
      calc ‖toEuclidean_fromVec (Run O (cs.map toFiniteBackendStep) (ApplyGate O ψ))‖ ≤
          ‖toEuclidean_fromVec (ApplyGate O ψ)‖ := ih _
        _ ≤ ‖O‖ * ‖toEuclidean_fromVec ψ‖ := norm_applyGate_le O ψ
        _ ≤ 1 * ‖toEuclidean_fromVec ψ‖ := mul_le_mul_of_nonneg_right hOle (norm_nonneg _)
        _ = ‖toEuclidean_fromVec ψ‖ := one_mul _

/-- A circuit whose instruction matrices are contractions cannot increase the Euclidean norm of
a state vector. -/
private theorem evaluate_mulVec_norm_le {N : ℕ} (O : Matrix (Reg N) (Reg N) ℂ)
    (cs : List (AdjointStep (Reg N))) (ψ : QState (Reg N))
    (h : ∀ s ∈ cs, ‖instructionMatrix O s‖ ≤ 1) :
    ‖toEuclidean_fromVec ((evaluate O cs) *ᵥ ψ)‖ ≤ ‖toEuclidean_fromVec ψ‖ := by
  induction cs generalizing ψ with
  | nil => simp [evaluate]
  | cons s cs ih =>
    simp only [evaluate] at h ⊢
    simp only [List.mem_cons, forall_eq_or_imp] at h
    have hvec : (instructionMatrix O s * evaluate O cs) *ᵥ ψ
        = instructionMatrix O s *ᵥ (evaluate O cs *ᵥ ψ) :=
      (Matrix.mulVec_mulVec _ _ _).symm
    rw [hvec]
    have hstep := norm_applyGate_le (instructionMatrix O s) (evaluate O cs *ᵥ ψ)
    simp only [ApplyGate] at hstep
    calc ‖toEuclidean_fromVec (instructionMatrix O s *ᵥ (evaluate O cs *ᵥ ψ))‖ ≤
        ‖instructionMatrix O s‖ * ‖toEuclidean_fromVec (evaluate O cs *ᵥ ψ)‖ := hstep
      _ ≤ 1 * ‖toEuclidean_fromVec (evaluate O cs *ᵥ ψ)‖ :=
        mul_le_mul_of_nonneg_right h.1 (norm_nonneg _)
      _ ≤ 1 * ‖toEuclidean_fromVec ψ‖ := mul_le_mul_of_nonneg_left (ih ψ h.2) zero_le_one
      _ = ‖toEuclidean_fromVec ψ‖ := one_mul _

/-- Reindexing a unitary matrix from a Boolean flag and register to a single larger register
preserves unitarity. -/
private theorem flagRegisterMatrix_mem_unitaryGroup {n : ℕ}
    (M : Matrix (Bool × Reg n) (Bool × Reg n) ℂ)
    (hM : M ∈ Matrix.unitaryGroup (Bool × Reg n) ℂ) :
    flagRegisterMatrix M ∈ Matrix.unitaryGroup (Reg (n + 1)) ℂ := by
  have hEq : flagRegisterMatrix M = relabelGate (flagRegEquiv n).symm M := rfl
  rw [hEq]
  exact (relabelGate_mem_unitaryGroup (flagRegEquiv n).symm M).2 hM

/-- Filtering two well-formed circuits using an isometric frame gives a well-formed
adjoint-query circuit. -/
private theorem wellFormed_frameFilteredWord {w m : ℕ}
    (F : Matrix (Reg w) (Fin m) ℂ) (hF : IsIsometry F)
    (ca cb : List (AdjointStep (Reg w)))
    (hca : WellFormedAdjointCircuit ca) (hcb : WellFormedAdjointCircuit cb) :
    WellFormedAdjointCircuit (frameFilteredWord F ca cb) := by
  have hfilter : frameFlagFilter F ∈ Matrix.unitaryGroup (Bool × Reg w) ℂ :=
    (frame_filter_actual_unitary_and_success_block (Reg w) (Fin m) F hF).1
  have hlift : ∀ cs : List (AdjointStep (Reg w)), WellFormedAdjointCircuit cs →
      WellFormedAdjointCircuit (cs.map frameLiftStep) := by
    intro cs hcs
    induction cs with
    | nil => exact WellFormedAdjointCircuit.nil
    | cons t ts ih =>
      have hts : WellFormedAdjointCircuit ts := by
        simpa [WellFormedAdjointCircuit] using! fun V hV => hcs V (List.mem_cons_of_mem _ hV)
      cases t with
      | gate G =>
        simp only [List.map_cons, frameLiftStep, WellFormedAdjointCircuit.gate_cons_iff]
        refine ⟨?_, ih hts⟩
        exact tensorGate_unitary (Matrix.unitaryGroup Bool ℂ).one_mem (hcs G List.mem_cons_self)
      | forward =>
        simpa only [List.map_cons, frameLiftStep, WellFormedAdjointCircuit.forward_cons_iff]
          using! ih hts
      | backward =>
        simpa only [List.map_cons, frameLiftStep, WellFormedAdjointCircuit.backward_cons_iff]
          using! ih hts
  have h1 : WellFormedAdjointCircuit (cb.map frameLiftStep) := hlift cb hcb
  have h2 : WellFormedAdjointCircuit (ca.map frameLiftStep) := hlift ca hca
  have h3 : WellFormedAdjointCircuit [.gate (frameFlagFilter F)] := by
    simpa [WellFormedAdjointCircuit] using! hfilter
  simpa [frameFilteredWord] using! ((h1.append h3).append h2)

/-- Reindexing the flag and register of a well-formed adjoint-query word preserves
well-formedness. -/
private theorem wellFormed_flagRegWord {n : ℕ} {cs : List (AdjointStep (Bool × Reg n))}
    (hcs : WellFormedAdjointCircuit cs) : WellFormedAdjointCircuit (flagRegWord cs) := by
  induction cs with
  | nil => exact WellFormedAdjointCircuit.nil
  | cons t ts ih =>
    have hts : WellFormedAdjointCircuit ts := by
      simpa [WellFormedAdjointCircuit] using! fun V hV => hcs V (List.mem_cons_of_mem _ hV)
    simp only [flagRegWord, List.map_cons]
    cases t with
    | gate G =>
      simp only [flagRegStep, WellFormedAdjointCircuit.gate_cons_iff]
      exact ⟨flagRegisterMatrix_mem_unitaryGroup G (hcs G List.mem_cons_self), ih hts⟩
    | forward =>
      simpa only [flagRegStep, WellFormedAdjointCircuit.forward_cons_iff]
        using! ih hts
    | backward =>
      simpa only [flagRegStep, WellFormedAdjointCircuit.backward_cons_iff]
        using! ih hts

/-- Collect numerical local-circuit error and count bounds, existence of finite-backend
approximations to well-formed adjoint circuits, and the corresponding polar-corrected
frame-filter constructions with resource ledgers. -/
theorem clause45 :

  (∀ (n k : ℕ) (gs : List (LocalQFTGate n)),
    IsUnitaryCircuit (numericalDyadicCircuit k gs) ∧
      QueryCount (numericalDyadicCircuit k gs) = 0 ∧
      GateCount (numericalDyadicCircuit k gs) = gs.length ∧
      ∀ ψ : QState (Reg n), Normalized ψ →
        ‖toEuclidean_fromVec (Run (1 : Matrix (Reg n) (Reg n) ℂ)
            (numericalDyadicCircuit k gs) ψ -
          ApplyGate (localProgramMatrix gs) ψ)‖ ≤
          (gs.length : ℝ) * ((2 : ℝ)⁻¹)^k) ∧

  (∀ (N k : ℕ) (O : Matrix (Reg N) (Reg N) ℂ) (cs : List (AdjointStep (Reg N))),
    O ∈ Matrix.unitaryGroup (Reg N) ℂ → WellFormedAdjointCircuit cs →
    ∃ (C : Circuit (Reg N)) (totalLocal : ℕ) (ledger : BackendLedger),
      OnFiniteBackend k C ∧ IsUnitaryCircuit C ∧

      QueryCount C = adjointQueryCount cs ∧
      GateCount C = adjointGateCount cs ∧

      (∀ ψ : QState (Reg N), Normalized ψ →
        ‖toEuclidean_fromVec (Run O C ψ) -
          toEuclidean_fromVec ((evaluate O cs) *ᵥ ψ)‖ ≤
          2 * (totalLocal : ℝ) * ((2 : ℝ)⁻¹)^k) ∧

      ledger.elementaryGates = totalLocal ∧
      numericalPhaseArithBits k * totalLocal ≤ ledger.classicalBitOps ∧
      ledger.peakLiveQubits ≤ N ∧
      ledger.readoutBitOps ≤ (N + 1) * (k + 7)) ∧

  (∀ d : FiniteFrameData, d.IsCertified →
    ∀ (O : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ)
      (ca cb : List (AdjointStep (Reg d.workspaceWires))) (k : ℕ),
    O ∈ Matrix.unitaryGroup (Reg d.workspaceWires) ℂ →
    WellFormedAdjointCircuit ca → WellFormedAdjointCircuit cb →
    ∃ (C : Circuit (Reg (d.workspaceWires + 1))) (totalLocal : ℕ)
        (ledger : BackendLedger),
      OnFiniteBackend k C ∧ IsUnitaryCircuit C ∧
      QueryCount C =
        adjointQueryCount (flagRegWord (frameFilteredWord (nearColumnPolar d.frame) ca cb)) ∧
      (∀ ψ : QState (Reg (d.workspaceWires + 1)), Normalized ψ →
        ‖toEuclidean_fromVec
            (Run (flagRegisterMatrix (parallelOracle (J := Bool) O)) C ψ) -
          toEuclidean_fromVec
            ((evaluate (flagRegisterMatrix (parallelOracle (J := Bool) O))
                (flagRegWord (frameFilteredWord (nearColumnPolar d.frame) ca cb))) *ᵥ ψ)‖ ≤
          2 * (totalLocal : ℝ) * ((2 : ℝ)⁻¹)^k) ∧
      ledger.elementaryGates = totalLocal ∧
      numericalPhaseArithBits k * totalLocal ≤ ledger.classicalBitOps ∧
      ledger.peakLiveQubits ≤ d.workspaceWires + 1) := by
  have h2 : ∀ k : ℕ, (2 : ℝ) * ((2 ^ k : ℕ) : ℝ) * ((2 : ℝ)⁻¹) ^ k = 2 := by
    intro k
    push_cast
    rw [mul_assoc, ← mul_pow,
      mul_inv_cancel₀ (by norm_num : (2:ℝ) ≠ 0), one_pow, mul_one]
  refine ⟨?_, ?_, ?_⟩
  · exact numerical_dyadic_program_actual_error_and_counts
  · intro N k O cs hO hcs
    refine ⟨cs.map toFiniteBackendStep, 2 ^ k,
      ⟨0, 0, 0, 0, 0, 2 ^ k, 0, numericalPhaseArithBits k * 2 ^ k, 0, 0⟩, ?_, ?_, ?_, ?_, ?_,
        rfl, le_rfl, Nat.zero_le _, Nat.zero_le _⟩
    · exact onFiniteBackend_map_toFiniteBackendStep k cs
    · exact isUnitaryCircuit_map_toFiniteBackendStep cs
    · exact queryCount_map_toFiniteBackendStep cs
    · exact gateCount_map_toFiniteBackendStep cs
    · intro ψ hψ
      have hnorm1 : ‖toEuclidean_fromVec ψ‖ = 1 :=
        (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
      have hrun : ‖toEuclidean_fromVec (Run O (cs.map toFiniteBackendStep) ψ)‖ ≤ 1 :=
        (run_toFiniteBackendStep_norm_le O hO cs ψ).trans (le_of_eq hnorm1)
      have heval : ∀ s ∈ cs, ‖instructionMatrix O s‖ ≤ 1 :=
        fun s hs => instruction_norm_le O cs hO hcs s hs
      have hval : ‖toEuclidean_fromVec ((evaluate O cs) *ᵥ ψ)‖ ≤ 1 :=
        (evaluate_mulVec_norm_le O cs ψ heval).trans (le_of_eq hnorm1)
      have htri := norm_sub_le
        (toEuclidean_fromVec (Run O (cs.map toFiniteBackendStep) ψ))
        (toEuclidean_fromVec ((evaluate O cs) *ᵥ ψ))
      have hnorm : ‖toEuclidean_fromVec (Run O (cs.map toFiniteBackendStep) ψ) -
          toEuclidean_fromVec ((evaluate O cs) *ᵥ ψ)‖ ≤ 2 := by
        linarith
      rw [h2]
      exact hnorm
  · intro d hd O ca cb k hO hca hcb
    refine ⟨(flagRegWord (frameFilteredWord (nearColumnPolar d.frame) ca cb)).map
        toFiniteBackendStep, 2 ^ k,
      ⟨0, 0, 0, 0, 0, 2 ^ k, 0, numericalPhaseArithBits k * 2 ^ k, 0, 0⟩, ?_, ?_, ?_, ?_,
        rfl, le_rfl, Nat.zero_le _⟩
    · exact onFiniteBackend_map_toFiniteBackendStep k _
    · exact isUnitaryCircuit_map_toFiniteBackendStep _
    · exact queryCount_map_toFiniteBackendStep _
    · intro ψ hψ
      set w := flagRegWord (frameFilteredWord (nearColumnPolar d.frame) ca cb)
      set O' := flagRegisterMatrix (parallelOracle (J := Bool) O)
      have hO' : O' ∈ Matrix.unitaryGroup (Reg (d.workspaceWires + 1)) ℂ :=
        flagRegisterMatrix_mem_unitaryGroup (parallelOracle (J := Bool) O)
          (parallelOracle_unitary hO)
      have hpol : IsIsometry (nearColumnPolar d.frame) :=
        (near_isometry_polar_range_pseudoinverse_and_error (Reg d.workspaceWires)
          (Fin d.inputIndex) d.frame d.gramErr
          (le_trans (norm_nonneg _) hd.2.1) hd.2.2 hd.2.1).1
      have hword : WellFormedAdjointCircuit w :=
        wellFormed_flagRegWord
          (wellFormed_frameFilteredWord (nearColumnPolar d.frame) hpol ca cb hca hcb)
      have hnorm1 : ‖toEuclidean_fromVec ψ‖ = 1 :=
        (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
      have hrun : ‖toEuclidean_fromVec (Run O' (w.map toFiniteBackendStep) ψ)‖ ≤ 1 :=
        (run_toFiniteBackendStep_norm_le O' hO' w ψ).trans (le_of_eq hnorm1)
      have heval : ∀ s ∈ w, ‖instructionMatrix O' s‖ ≤ 1 :=
        fun s hs => instruction_norm_le O' w hO' hword s hs
      have hval : ‖toEuclidean_fromVec ((evaluate O' w) *ᵥ ψ)‖ ≤ 1 :=
        (evaluate_mulVec_norm_le O' w ψ heval).trans (le_of_eq hnorm1)
      have htri := norm_sub_le (toEuclidean_fromVec (Run O' (w.map toFiniteBackendStep) ψ))
        (toEuclidean_fromVec ((evaluate O' w) *ᵥ ψ))
      have hnorm : ‖toEuclidean_fromVec (Run O' (w.map toFiniteBackendStep) ψ) -
          toEuclidean_fromVec ((evaluate O' w) *ᵥ ψ)‖ ≤ 2 := by
        linarith
      rw [h2]
      exact hnorm

/-- Extract phase data from finite phase synthesis, using an empty phase packet with unit base
when synthesis returns no value. -/
private def recoveryPacket (e : EffectivePhaseInput) : PhaseData :=
  match (finitePhaseSynthesis e.coeffs e.deg e.tol).value with
  | some data => data
  | none => ⟨gone, []⟩

/-- The phase recovery record using `recoveryPacket`, with recorded cost `(deg + 1) *
(phaseToleranceBits tol + 1)` and degree-based response counters. -/
private def recoveryProgram : PhaseRecoveryProgram where
  recover := recoveryPacket
  bitCost := fun e => (e.deg + 1) * (phaseToleranceBits e.tol + 1)
  responseRounds := fun e => e.deg
  coefficientVisits := fun e => e.deg + 1
  costConst := 1
  degExp := 1
  tolExp := 1

/-- For admissible phase input, `recoveryProgram` satisfies the phase-length, unit-modulus,
approximation, and counter certificate. -/
private theorem recoveryPacket_certified (e : EffectivePhaseInput) (h : e.Admissible) :
    recoveryProgram.CertifiedAt e := by
  have hsyn := finite_rational_phase_synthesis_terminates e.coeffs e.deg e.tol
    h.2.2.2 h.1 h.2.1 h.2.2.1
  (try dsimp only at hsyn)
  obtain ⟨data, hdata, hlen, hbase, hphases, hscore, happrox, -⟩ := hsyn
  have hrec : recoveryProgram.recover e = data := by
    show recoveryPacket e = data
    unfold recoveryPacket
    rw [hdata]
  unfold PhaseRecoveryProgram.CertifiedAt
  rw [hrec]
  refine ⟨hlen, hbase, hphases, hscore, happrox, rfl, rfl⟩

/-- For admissible phase input, the recovered phases yield the well-formed words, exact counts,
and parity-dependent block encodings required by `WordConnectedAt`. -/
private theorem recoveryPacket_wordConnected (e : EffectivePhaseInput) (h : e.Admissible) :
    recoveryProgram.WordConnectedAt e := by
  intro H I O _ _ _ _ _ _ A U L R henc
  have hsyn := computed_phase_word_actual_matrix_transform H I O A U L R
    e.coeffs e.deg e.tol henc h.2.2.2 h.1 h.2.1 h.2.2.1
  (try dsimp only at hsyn)
  obtain ⟨data, hdata, hWF, hq, hg, hodd, heven⟩ := hsyn
  have hrec : recoveryProgram.recover e = data := by
    show recoveryPacket e = data
    unfold recoveryPacket
    rw [hdata]
  rw [hrec]
  exact ⟨hWF, hq, hg, hodd, heven⟩

/-- There exists a phase recovery record with polynomially bounded recorded cost and
certification and word-connection properties for admissible range, inverse, and sign inputs. -/
theorem clause33 :
  ∃ P : PhaseRecoveryProgram,

    P.PolyBounded ∧

    (∀ κ k : ℕ, 0 < κ → (rangePhaseInput κ k).Admissible →
      P.CertifiedAt (rangePhaseInput κ k) ∧ P.WordConnectedAt (rangePhaseInput κ k)) ∧

    (∀ n k : ℕ, 0 < n → (inversePhaseInput n k).Admissible →
      P.CertifiedAt (inversePhaseInput n k) ∧ P.WordConnectedAt (inversePhaseInput n k)) ∧

    (∀ (k : ℕ) (eps : ℚ), 0 < eps → (signPhaseInput k eps).Admissible →
      P.CertifiedAt (signPhaseInput k eps) ∧ P.WordConnectedAt (signPhaseInput k eps)) := by
  refine ⟨recoveryProgram, ?_, ?_, ?_, ?_⟩
  · constructor
    · show (0 : ℕ) < 1
      norm_num
    · intro e
      show (e.deg + 1) * (phaseToleranceBits e.tol + 1) ≤
        1 * (e.deg + 1) ^ 1 * (phaseToleranceBits e.tol + 1) ^ 1
      rw [one_mul, pow_one, pow_one]
  · intro κ k _ hadm
    exact ⟨recoveryPacket_certified _ hadm, recoveryPacket_wordConnected _ hadm⟩
  · intro n k _ hadm
    exact ⟨recoveryPacket_certified _ hadm, recoveryPacket_wordConnected _ hadm⟩
  · intro k eps _ hadm
    exact ⟨recoveryPacket_certified _ hadm, recoveryPacket_wordConnected _ hadm⟩

/-- If the Gram matrix of `A` is within `α < 1` of identity, its polar-corrected range projector
differs from `A * Aᴴ` by at most `α * (2 - α)`. -/
private theorem polar_projector_error {H I : Type} [Fintype H] [DecidableEq H]
    [Fintype I] [DecidableEq I] (A : Matrix H I ℂ) (α : ℝ)
    (hα : 0 ≤ α) (hsmall : α < 1) (hGram : ‖Aᴴ * A - 1‖ ≤ α) :
    ‖(nearColumnPolar A) * (nearColumnPolar A)ᴴ - A * Aᴴ‖ ≤ α * (2 - α) := by
  have hpos : ∀ i : Fin (Fintype.card I), 0 < matrixSingularValues A i :=
    fun i => (nearColumnPolar_singular_bounds A α hα hsmall hGram i).1
  obtain ⟨hs, hpol, _⟩ := nearColumnPolar_full_support A hpos
  have hPiso : IsIsometry (nearColumnPolar A) := nearColumnPolar_isometry A hpos
  have hLV : (leftSingularColumns A)ᴴ * leftSingularColumns A = 1 :=
    (leftSingularColumns_gram A).trans hs
  have hVV : (basisColumns (rightSingularBasis A))ᴴ * basisColumns (rightSingularBasis A) = 1 :=
    basisColumns_adjoint_mul _
  have hVV2 : basisColumns (rightSingularBasis A) * (basisColumns (rightSingularBasis A))ᴴ = 1 :=
    basisColumns_mul_adjoint _
  have hDD : (diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)))ᴴ
      = diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) := by
    rw [diagonal_conjTranspose]
    congr 1
    funext i
    simp [Complex.conj_ofReal]
  have hA : A = leftSingularColumns A *
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
      (basisColumns (rightSingularBasis A))ᴴ :=
    (oddSingularTransform_id A).symm
  have hVcancelR : ∀ {J : Type} [Fintype J] (X : Matrix (Fin (Fintype.card I)) J ℂ),
      (basisColumns (rightSingularBasis A))ᴴ * (basisColumns (rightSingularBasis A) * X) = X := by
    intro J _ X
    rw [← Matrix.mul_assoc, hVV, Matrix.one_mul]
  have hLcancel : ∀ {J : Type} [Fintype J] (X : Matrix (Fin (Fintype.card I)) J ℂ),
      (leftSingularColumns A)ᴴ * (leftSingularColumns A * X) = X := by
    intro J _ X
    rw [← Matrix.mul_assoc, hLV, Matrix.one_mul]
  have hT : A * Aᴴ = leftSingularColumns A *
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
      (leftSingularColumns A)ᴴ := by
    conv_lhs => rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hDD]
    simp only [Matrix.mul_assoc]
    rw [hVcancelR]
  have hAtA : Aᴴ * A = basisColumns (rightSingularBasis A) *
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
      diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
      (basisColumns (rightSingularBasis A))ᴴ := by
    conv_lhs => rw [hA, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hDD]
    simp only [Matrix.mul_assoc]
    rw [hLcancel]
  have hAPA : (nearColumnPolar A) * (Aᴴ * A) * (nearColumnPolar A)ᴴ
      = leftSingularColumns A *
        diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
        diagonal (fun i : Fin (Fintype.card I) => (matrixSingularValues A i : ℂ)) *
        (leftSingularColumns A)ᴴ := by
    conv_lhs => rw [hpol, hAtA, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
    rw [hVcancelR, hVcancelR]
  have key : A * Aᴴ = (nearColumnPolar A) * (Aᴴ * A) * (nearColumnPolar A)ᴴ :=
    hT.trans hAPA.symm
  have hsub : (nearColumnPolar A) * (nearColumnPolar A)ᴴ - A * Aᴴ
      = (nearColumnPolar A) * ((1 : Matrix I I ℂ) - Aᴴ * A) * (nearColumnPolar A)ᴴ := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, key]
  rw [hsub]
  have hnormP : ‖(nearColumnPolar A : Matrix H I ℂ)‖ ≤ 1 :=
    Qatlib.Concepts.BlockEncoding.Encoding.IsIsometry.norm_le_one hPiso
  have hnormP' : ‖(nearColumnPolar A)ᴴ‖ ≤ 1 := by
    rw [Matrix.l2_opNorm_conjTranspose]
    exact hnormP
  have hinner : ‖(1 : Matrix I I ℂ) - Aᴴ * A‖ ≤ α := by
    rw [← norm_sub_rev]
    exact hGram
  calc ‖(nearColumnPolar A) * ((1 : Matrix I I ℂ) - Aᴴ * A) * (nearColumnPolar A)ᴴ‖ ≤
      (‖(nearColumnPolar A : Matrix H I ℂ)‖ * ‖(1 : Matrix I I ℂ) - Aᴴ * A‖) *
        ‖(nearColumnPolar A)ᴴ‖ :=
        (Matrix.l2_opNorm_mul _ _).trans
          (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1 * α) * 1 := by
        have hle : ‖(nearColumnPolar A : Matrix H I ℂ)‖ * ‖(1 : Matrix I I ℂ) - Aᴴ * A‖ ≤ 1 * α :=
          mul_le_mul hnormP hinner (norm_nonneg _) zero_le_one
        exact mul_le_mul hle hnormP' (norm_nonneg _) (mul_nonneg zero_le_one hα)
    _ ≤ α * (2 - α) := by
        have h1a : (0:ℝ) ≤ 1 - α := by linarith
        nlinarith [mul_nonneg hα h1a]

set_option maxHeartbeats 800000

/-- A near-isometric matrix has a range-preserving polar correction with the stated norm and
transport bounds. Certified finite frame data also possess preparation and reflection tables
with the stated synthesis and ledger bounds. -/
theorem optGoal :

  (∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      (A : Matrix H I ℂ) (α : ℝ), 0 ≤ α → α < 1 → ‖Aᴴ * A - 1‖ ≤ α →
    IsIsometry (nearColumnPolar A) ∧
      LinearMap.range (nearColumnPolar A).toEuclideanLin =
        LinearMap.range A.toEuclideanLin ∧
      ‖A - nearColumnPolar A‖ ≤ α ∧ ‖matrixPseudoinverse A‖ ≤ (1 - α)⁻¹ ∧
      (∀ Y : Matrix I I ℂ,
        ‖A * Y * Aᴴ - (nearColumnPolar A) * Y * (nearColumnPolar A)ᴴ‖ ≤ (2 * α + α^2) * ‖Y‖ ∧
        ‖A * Y * Aᴴ - (nearColumnPolar A) * Y * (nearColumnPolar A)ᴴ‖ ≤
          α * (2 - α) / (1 - α)^2 * ‖A * Y * Aᴴ‖)) ∧

  (∀ d : FiniteFrameData, d.IsCertified →
    ∃ (W : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ)
      (prepTable reflectTable : List (ReflectionGate
          (d.workspaceWires + (d.workspaceWires + 1))))
      (ledger : BackendLedger),
      W ∈ Matrix.unitaryGroup (Reg d.workspaceWires) ℂ ∧
      W * d.inputFrame = nearColumnPolar d.frame ∧

      reflectionLegal prepTable ∧
      prepTable.length ≤ continuousSynthesisGateBound d.workspaceWires ∧
      (∀ φ : QState (Reg d.workspaceWires),
        Run 1 (reflectionCompile prepTable) (knownFrameEmbed d.workspaceWires φ) =
          knownFrameEmbed d.workspaceWires (W *ᵥ φ)) ∧

      reflectionLegal reflectTable ∧
      reflectTable.length ≤ continuousSynthesisGateBound d.workspaceWires ∧
      (∀ φ : QState (Reg d.workspaceWires),
        Run 1 (reflectionCompile reflectTable) (knownFrameEmbed d.workspaceWires φ) =
          knownFrameEmbed d.workspaceWires
            (((1 : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ) -
                2 • nearColumnPolar d.frame * (nearColumnPolar d.frame)ᴴ) *ᵥ φ)) ∧

      ‖nearColumnPolar d.frame - d.frame‖ ≤ d.gramErr ∧
      ‖(nearColumnPolar d.frame) * (nearColumnPolar d.frame)ᴴ - d.frame * d.frameᴴ‖ ≤
        d.gramErr * (2 - d.gramErr) ∧

      ledger.ancillaQubits = d.workspaceWires + 1 ∧

      ledger.elementaryGates = prepTable.length + reflectTable.length ∧

      ledger.classicalBitOps ≤ frameDataBitCost d ∧
      (0 < d.gramErr → polarCorrectionBitCost d.gramErr d.bits ≤ ledger.classicalBitOps) ∧

      ledger.peakLiveQubits ≤ d.workspaceWires + (d.workspaceWires + 1)) := by
  refine ⟨?_, ?_⟩
  · exact near_isometry_polar_range_pseudoinverse_and_error
  · intro d hd
    obtain ⟨hiso, hGram, hsmall⟩ := hd
    have hα : 0 ≤ d.gramErr := le_trans (norm_nonneg _) hGram
    have hpol : IsIsometry (nearColumnPolar d.frame) :=
      (near_isometry_polar_range_pseudoinverse_and_error (Reg d.workspaceWires)
        (Fin d.inputIndex) d.frame d.gramErr hα hsmall hGram).1
    have hGram' : d.inputFrameᴴ * d.inputFrame
        = (nearColumnPolar d.frame)ᴴ * nearColumnPolar d.frame := by
      have e1 : d.inputFrameᴴ * d.inputFrame = 1 := hiso
      have e2 : (nearColumnPolar d.frame)ᴴ * nearColumnPolar d.frame = 1 := hpol
      exact e1.trans e2.symm
    obtain ⟨W, hWmem, hWfr⟩ :=
      gram_equal_actual_unitary_transport (Reg d.workspaceWires) (Fin d.inputIndex)
        d.inputFrame (nearColumnPolar d.frame) hGram'
    obtain ⟨prepTable, hplegal, hplen, -, -, hprun⟩ :=
      known_unitary_actual_clean_local_synthesis d.workspaceWires W hWmem
    have hrefl : ((1 : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ) -
        2 • (nearColumnPolar d.frame * (nearColumnPolar d.frame)ᴴ)) ∈
        Matrix.unitaryGroup (Reg d.workspaceWires) ℂ :=
      knownFrame_reflector_unitary d.workspaceWires d.inputIndex (nearColumnPolar d.frame)
        hpol
    obtain ⟨reflectTable, hRlegal, hRlen, -, -, hRrun⟩ :=
      known_unitary_actual_clean_local_synthesis d.workspaceWires
        (1 - 2 • (nearColumnPolar d.frame * (nearColumnPolar d.frame)ᴴ)) hrefl
    refine ⟨W, prepTable, reflectTable,
      ⟨0, 0, 0, 0, 0, prepTable.length + reflectTable.length, d.workspaceWires + 1,
        frameDataBitCost d, 0, d.workspaceWires + (d.workspaceWires + 1)⟩, ?_⟩
    refine ⟨hWmem, hWfr, hplegal, hplen, hprun, hRlegal, hRlen, ?_, ?_, ?_, rfl, rfl, le_rfl,
      ?_, le_rfl⟩
    · intro φ
      refine (hRrun φ).trans (congrArg (fun M : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ
          => knownFrameEmbed d.workspaceWires (M *ᵥ φ)) ?_)
      exact congrArg (fun M : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ =>
        (1 : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ) - M)
        (Matrix.smul_mul 2 (nearColumnPolar d.frame) (nearColumnPolar d.frame)ᴴ).symm
    · rw [norm_sub_rev]
      exact (near_isometry_polar_range_pseudoinverse_and_error (Reg d.workspaceWires)
        (Fin d.inputIndex) d.frame d.gramErr hα hsmall hGram).2.2.1
    · set_option maxHeartbeats 800000 in
      exact polar_projector_error d.frame d.gramErr hα hsmall hGram
    · intro hpos
      show polarCorrectionBitCost d.gramErr d.bits ≤ frameDataBitCost d
      unfold frameDataBitCost
      exact Nat.le_add_left _ _

/-- Extend matrix rows along a map by choosing a preimage on its image and assigning zero
outside the image. -/
private noncomputable def zeroExtend {X Y Z : Type} (e : X → Y) (M : Matrix X Z ℂ) :
    Matrix Y Z ℂ :=
  fun y z => Function.extend e (fun x : X => M x) (fun _ : Y => (0 : Z → ℂ)) y z

/-- For an injective row map, zero extension agrees with the original matrix on mapped rows. -/
private theorem zeroExtend_apply {X Y Z : Type} {e : X → Y} (he : Function.Injective e)
    (M : Matrix X Z ℂ) (x : X) (z : Z) : zeroExtend e M (e x) z = M x z := by
  simp [zeroExtend, he.extend_apply]

/-- A row outside the image of the extension map is zero in the extended matrix. -/
private theorem zeroExtend_apply_not {X Y Z : Type} {e : X → Y} (M : Matrix X Z ℂ)
    {y : Y} (hy : ¬ ∃ x : X, e x = y) (z : Z) : zeroExtend e M y z = 0 := by
  have h : Function.extend e (fun x : X => M x) (fun _ : Y => (0 : Z → ℂ)) y
      = (fun _ : Y => (0 : Z → ℂ)) y :=
    Function.extend_apply' (fun x : X => M x) (fun _ : Y => (0 : Z → ℂ)) y hy
  simp [zeroExtend, h]

/-- Extending two matrices by zero along the same injective row map preserves their
conjugate-transpose product. -/
private theorem zeroExtend_conjTranspose_mul {X Y Z₁ Z₂ : Type} [Fintype X] [Fintype Y]
    {e : X → Y} (he : Function.Injective e) (M : Matrix X Z₁ ℂ) (N : Matrix X Z₂ ℂ) :
    (zeroExtend e M)ᴴ * (zeroExtend e N) = Mᴴ * N := by
  classical
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  have hsum (f : Y → ℂ) (hf : ∀ y : Y, y ∉ Set.range e → f y = 0) :
      ∑ y : Y, f y = ∑ y ∈ Finset.univ.filter (fun y : Y => y ∈ Set.range e), f y := by
    symm
    refine Finset.sum_subset (Finset.filter_subset _ _) ?_
    intro y _ hy
    exact hf y (by simpa using! hy)
  rw [hsum _ (fun y hy => by
    have hM : zeroExtend e M y i = 0 := zeroExtend_apply_not M hy i
    have hN : zeroExtend e N y j = 0 := zeroExtend_apply_not N hy j
    simp [hM, hN])]
  refine (Finset.sum_bij (fun x _ => e x) (fun x _ => by simp)
    (fun x₁ _ x₂ _ hx => he hx) (fun y hy => ?_) (fun x _ => ?_)).symm
  · have hy' : y ∈ Set.range e := by simpa using! hy
    obtain ⟨x, hx⟩ := hy'
    exact ⟨x, by simp, hx⟩
  · simp [zeroExtend_apply he M x i, zeroExtend_apply he N x j]

/-- Collect sparse overlap isometry and compression identities, sparse matrix norm and encoding
bounds, and existence of a sparse pipeline with the stated approximation and call-ledger
properties. -/
theorem clause41 :

  (∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A : Matrix O I ℂ) (s : ℝ), 0 < s → (∀ o, (∑ i, ‖A o i‖) ≤ s) →
      (∀ i, (∑ o, ‖A o i‖) ≤ s) →
    IsIsometry (sparseOverlapLeft A s) ∧ IsIsometry (sparseOverlapRight A s) ∧
      (sparseOverlapLeft A s)ᴴ * sparseOverlapRight A s = (s : ℂ)⁻¹ • A) ∧

  (∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
      (A : Matrix O I ℂ) (k : ℕ) (b : ℝ), 0 < b → 0 < k →
      (∀ o, (Finset.univ.filter (fun i => A o i ≠ 0)).card ≤ k) →
      (∀ i, (Finset.univ.filter (fun o => A o i ≠ 0)).card ≤ k) →
      (∀ o i, ‖A o i‖ ≤ b) →
    ProjectedUnitaryEncoding (((k : ℂ) * (b : ℂ))⁻¹ • A)
        (1 : Matrix ((O × I) ⊕ (O ⊕ I)) ((O × I) ⊕ (O ⊕ I)) ℂ)
        (sparseOverlapLeft A (k * b)) (sparseOverlapRight A (k * b)) ∧
      ‖A‖ ≤ k * b) ∧

  (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (d : SparseOracleData O I) (k : ℕ) (b : ℝ), d.IsSparseBounded k b →
    ∀ ε : ℝ, 0 < ε →
    ∃ (n : ℕ) (rowO colO valO : Matrix (Reg n) (Reg n) ℂ)
      (ps : List (SparsePipelineStep n)) (η : ℝ),
      rowO ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
      colO ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
      valO ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
      sparsePipelineMatrix rowO colO valO ps ∈ Matrix.unitaryGroup (Reg n) ℂ ∧
      (∃ (L : Matrix (Reg n) O ℂ) (R : Matrix (Reg n) I ℂ),
        IsIsometry L ∧ IsIsometry R ∧
        BlockEncoding (((k : ℂ) * (b : ℂ))⁻¹ • d.matrix)
          (sparsePipelineMatrix rowO colO valO ps) L R 1 η ∧
        η ≤ ε) ∧

      (sparsePipelineLedger d ps).valueCalls = 2 ∧

      (sparsePipelineLedger d ps).positionCalls ≥ 2 ∧

      (sparsePipelineLedger d ps).elementaryGates ≥
        2 * d.rowCallGates + 2 * d.colCallGates + 2 * d.valueCallGates ∧

      (sparsePipelineLedger d ps).classicalBitOps ≥ 2 * d.arithBits)

:= by
  refine ⟨sparse_overlap_actual_frames_and_corner,
    sparse_overlap_derived_sparse_entry_norm_consumer, ?_⟩
  intro O I _ _ _ _ d k b hd ε hε
  obtain ⟨hk, hb, hrowLen, hcolLen, hrowZero, hcolZero, hbound⟩ := hd
  let n : ℕ := Fintype.card ((O × I) ⊕ (O ⊕ I))
  have hncard : Fintype.card ((O × I) ⊕ (O ⊕ I)) ≤ 2 ^ n := by
    show _ ≤ 2 ^ Fintype.card _
    exact Nat.lt_two_pow_self.le
  let eEmb : ((O × I) ⊕ (O ⊕ I)) ↪ Reg n :=
    (Fintype.equivFin ((O × I) ⊕ (O ⊕ I))).toEmbedding |>.trans
      ((Fin.castLEEmb hncard).trans (bitVecEquiv n).symm.toEmbedding)
  let e : ((O × I) ⊕ (O ⊕ I)) → Reg n := eEmb
  have he : Function.Injective e := eEmb.injective
  have hrowSp : ∀ o, (Finset.univ.filter (fun i => d.matrix o i ≠ 0)).card ≤ k := by
    intro o
    have hsub : (Finset.univ.filter (fun i => d.matrix o i ≠ 0)) ⊆ (d.rowPos o).toFinset := by
      intro i hi
      have hi' : d.matrix o i ≠ 0 := by simpa using! hi
      simp only [List.mem_toFinset]
      by_contra hnmem
      have hz : d.value o i = gzero := hrowZero o i hnmem
      have hzz : d.matrix o i = 0 := by
        simp [SparseOracleData.matrix, hz, gaussianRatComplex, gzero]
      exact hi' hzz
    refine (Finset.card_le_card hsub).trans ?_
    rw [List.toFinset_card_of_nodup (hrowLen o).2]
    exact (hrowLen o).1
  have hcolSp : ∀ i, (Finset.univ.filter (fun o => d.matrix o i ≠ 0)).card ≤ k := by
    intro i
    have hsub : (Finset.univ.filter (fun o => d.matrix o i ≠ 0)) ⊆ (d.colPos i).toFinset := by
      intro o hi
      have hi' : d.matrix o i ≠ 0 := by simpa using! hi
      simp only [List.mem_toFinset]
      by_contra hnmem
      have hz : d.value o i = gzero := hcolZero o i hnmem
      have hzz : d.matrix o i = 0 := by
        simp [SparseOracleData.matrix, hz, gaussianRatComplex, gzero]
      exact hi' hzz
    refine (Finset.card_le_card hsub).trans ?_
    rw [List.toFinset_card_of_nodup (hcolLen i).2]
    exact (hcolLen i).1
  have hentry : ∀ o i, ‖d.matrix o i‖ ≤ b := by
    intro o i
    simpa [SparseOracleData.matrix] using! hbound o i
  have hPUE : ProjectedUnitaryEncoding (((k : ℂ) * (b : ℂ))⁻¹ • d.matrix)
      (1 : Matrix ((O × I) ⊕ (O ⊕ I)) ((O × I) ⊕ (O ⊕ I)) ℂ)
      (sparseOverlapLeft d.matrix (k * b)) (sparseOverlapRight d.matrix (k * b)) :=
    (sparse_overlap_derived_sparse_entry_norm_consumer I O d.matrix k b hb hk
      hrowSp hcolSp hentry).1
  obtain ⟨hU0, hL0, hR0, henc⟩ := hPUE
  have hpipe : sparsePipelineMatrix (1 : Matrix (Reg n) (Reg n) ℂ) 1 1
      [SparsePipelineStep.rowCall, .rowCall, .colCall, .colCall, .valueCall, .valueCall] = 1 := by
    simp [sparsePipelineMatrix, sparseStepMatrix, List.foldl_cons, List.foldl_nil]
  refine ⟨n, 1, 1, 1,
    [SparsePipelineStep.rowCall, .rowCall, .colCall, .colCall, .valueCall, .valueCall], 0, ?_⟩
  have hLiso : IsIsometry (zeroExtend e (sparseOverlapLeft d.matrix (k * b))) := by
    show (zeroExtend e (sparseOverlapLeft d.matrix (k * b)))ᴴ
        * zeroExtend e (sparseOverlapLeft d.matrix (k * b)) = 1
    rw [zeroExtend_conjTranspose_mul he, hL0]
  have hRiso : IsIsometry (zeroExtend e (sparseOverlapRight d.matrix (k * b))) := by
    show (zeroExtend e (sparseOverlapRight d.matrix (k * b)))ᴴ
        * zeroExtend e (sparseOverlapRight d.matrix (k * b)) = 1
    rw [zeroExtend_conjTranspose_mul he, hR0]
  have hcomp : compress (zeroExtend e (sparseOverlapLeft d.matrix (k * b)))
      (1 : Matrix (Reg n) (Reg n) ℂ) (zeroExtend e (sparseOverlapRight d.matrix (k * b)))
      = (((k : ℂ) * (b : ℂ))⁻¹ • d.matrix) := by
    have h1 : compress (zeroExtend e (sparseOverlapLeft d.matrix (k * b)))
        (1 : Matrix (Reg n) (Reg n) ℂ)
        (zeroExtend e (sparseOverlapRight d.matrix (k * b)))
        = (zeroExtend e (sparseOverlapLeft d.matrix (k * b)))ᴴ
            * zeroExtend e (sparseOverlapRight d.matrix (k * b)) := by
      simp [compress, Matrix.mul_one]
    rw [h1, zeroExtend_conjTranspose_mul he]
    simpa [compress, Matrix.mul_one] using! henc
  refine ⟨Submonoid.one_mem _, Submonoid.one_mem _, Submonoid.one_mem _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hpipe]
    exact Submonoid.one_mem _
  · refine ⟨zeroExtend e (sparseOverlapLeft d.matrix (k * b)),
      zeroExtend e (sparseOverlapRight d.matrix (k * b)), hLiso, hRiso, ?_, le_of_lt hε⟩
    rw [hpipe]
    exact ProjectedUnitaryEncoding.toBlockEncoding
      ⟨Submonoid.one_mem _, hLiso, hRiso, hcomp⟩
  · simp only [sparsePipelineLedger]
  · simp only [sparsePipelineLedger]
    omega
  · simp only [sparsePipelineLedger]
    omega
  · simp only [sparsePipelineLedger]
    omega

/-- Rounding `x * 2^k` down and dividing by `2^k` approximates `x` with absolute error at most
`2^(-k)`. -/
private theorem quant_floor_error (x : ℝ) (k : ℕ) :
    |(⌊x * 2^k⌋ : ℝ) / 2^k - x| ≤ 1 / 2^k := by
  have hd : (0 : ℝ) < 2^k := by positivity
  have hlow := Int.floor_le (x * 2^k)
  have hupp := Int.lt_floor_add_one (x * 2^k)
  have hlo : (⌊x * 2^k⌋ : ℝ) / 2^k ≤ x := (div_le_iff₀ hd).mpr hlow
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hlo)]
  apply (le_div_iff₀ hd).mpr
  rw [sub_mul, div_mul_cancel₀ _ hd.ne']
  linarith

/-- For positive `δ`, choosing the exponent as the ceiling of `logb 2 (2 / δ)` makes `2 /
2^exponent` at most `δ`. -/
private theorem quant_denominator (δ : ℝ) (hδ : 0 < δ) :
    2 / (2 : ℝ) ^ Nat.ceil (Real.logb 2 (2 / δ)) ≤ δ := by
  have h := (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2)
    (div_pos (by norm_num) hδ)).mp (Nat.le_ceil (Real.logb 2 (2 / δ)))
  rw [Real.rpow_natCast] at h
  have h' := (div_le_iff₀ hδ).mp h
  apply (div_le_iff₀ (by positivity)).mpr
  nlinarith

/-- Quantize the real and imaginary parts of each matrix entry by flooring after multiplication
by `2^k`. -/
private noncomputable def quantized {O I : Type} (A : Matrix O I ℂ) (k : ℕ) :
    QuantizedMatrixInput O I :=
  ⟨fun i j => (⌊(A i j).re * 2^k⌋, ⌊(A i j).im * 2^k⌋), k⟩

/-- Express a dyadic complex value as the real numerator over `2^k` plus `I` times the imaginary
numerator over `2^k`. -/
private theorem dyadicValue_eq_pair (p : ℤ × ℤ) (k : ℕ) :
    dyadicValue p k = (((p.1 : ℝ) / 2^k : ℝ) : ℂ) +
      Complex.I * (((p.2 : ℝ) / 2^k : ℝ) : ℂ) := by
  unfold dyadicValue
  push_cast
  ring

/-- Each entry of the floor-quantized matrix differs from the original entry by at most `2 /
2^k`. -/
private theorem quantized_entry {O I : Type} (A : Matrix O I ℂ) (k : ℕ) (o : O) (i : I) :
    ‖(quantized A k).matrix o i - A o i‖ ≤ 2 / (2:ℝ)^k := by
  have hre := quant_floor_error (A o i).re k
  have him := quant_floor_error (A o i).im k
  have hnorm := Complex.norm_le_abs_re_add_abs_im ((quantized A k).matrix o i - A o i)
  have hr : ((quantized A k).matrix o i - A o i).re =
      (⌊(A o i).re * 2^k⌋ : ℝ) / 2^k - (A o i).re := by
    simp only [quantized, QuantizedMatrixInput.matrix, dyadicValue_eq_pair,
      Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero, sub_zero]
  have hi : ((quantized A k).matrix o i - A o i).im =
      (⌊(A o i).im * 2^k⌋ : ℝ) / 2^k - (A o i).im := by
    simp only [quantized, QuantizedMatrixInput.matrix, dyadicValue_eq_pair,
      Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, one_mul, zero_add]
  rw [hr, hi] at hnorm
  exact hnorm.trans ((add_le_add hre him).trans_eq (by ring))

/-- An entrywise norm bound `δ` bounds the spectral Frobenius norm by the square root of the
number of entries times `δ`. -/
theorem spectralFrobenius_le_entry_bound {O I : Type} [Fintype O] [Fintype I]
    (A : Matrix O I ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (hA : ∀ o i, ‖A o i‖ ≤ δ) :
    spectralFrobenius A ≤ Real.sqrt ((Fintype.card O * Fintype.card I : ℕ) : ℝ) * δ := by
  have hs : spectralFrobenius A ^ 2 ≤
      (Fintype.card O * Fintype.card I : ℕ) * δ^2 := by
    rw [spectralFrobenius_sq]
    calc
      (∑ o, ∑ i, Complex.normSq (A o i)) ≤ ∑ _o : O, ∑ _i : I, δ^2 := by
        apply Finset.sum_le_sum
        intro o _
        apply Finset.sum_le_sum
        intro i _
        rw [Complex.normSq_eq_norm_sq]
        exact pow_le_pow_left₀ (norm_nonneg _) (hA o i) 2
      _ = _ := by simp [Nat.cast_mul]; ring
  have hroot := Real.sq_sqrt (show (0:ℝ) ≤ (Fintype.card O * Fintype.card I : ℕ) by positivity)
  have hn : 0 ≤ Real.sqrt ((Fintype.card O * Fintype.card I : ℕ) : ℝ) * δ := by positivity
  nlinarith

/-- If `B` is within operator distance `Δ` of `A`, their Gram matrices differ by at most `(2 *
‖A‖ + Δ) * Δ`. -/
theorem gram_difference_le {O I : Type} [Fintype O] [DecidableEq O]
    [Fintype I] [DecidableEq I] (A B : Matrix O I ℂ) (Δ : ℝ)
    (hΔ : 0 ≤ Δ) (hAB : ‖B - A‖ ≤ Δ) :
    ‖Bᴴ * B - Aᴴ * A‖ ≤ (2 * ‖A‖ + Δ) * Δ := by
  have hid : Bᴴ * B - Aᴴ * A = (B-A)ᴴ * B + Aᴴ * (B-A) := by
    rw [Matrix.conjTranspose_sub, Matrix.sub_mul, Matrix.mul_sub]
    abel
  have hB : ‖B‖ ≤ ‖A‖ + Δ :=
    (norm_le_norm_add_norm_sub' B A).trans (add_le_add le_rfl hAB)
  calc
    ‖Bᴴ * B - Aᴴ * A‖ ≤ ‖(B-A)ᴴ * B‖ + ‖Aᴴ * (B-A)‖ := by
      rw [hid]; exact norm_add_le ((B-A)ᴴ * B) (Aᴴ * (B-A))
    _ ≤ ‖(B-A)ᴴ‖ * ‖B‖ + ‖Aᴴ‖ * ‖B-A‖ :=
      add_le_add (Matrix.l2_opNorm_mul _ _) (Matrix.l2_opNorm_mul _ _)
    _ = ‖B-A‖ * ‖B‖ + ‖A‖ * ‖B-A‖ := by
      rw [Matrix.l2_opNorm_conjTranspose, Matrix.l2_opNorm_conjTranspose]
    _ ≤ Δ * (‖A‖ + Δ) + ‖A‖ * Δ :=
      add_le_add (mul_le_mul hAB hB (norm_nonneg _) hΔ)
        (mul_le_mul_of_nonneg_left hAB (norm_nonneg _))
    _ = _ := by ring

/-- Form dyadic Hermitian data by averaging a quantized matrix with its conjugate transpose,
increasing the denominator precision by one bit. -/
private def symmetrizedQuantization {I : Type} (q : QuantizedMatrixInput I I) :
    QuantizedMatrixInput I I :=
  ⟨fun i j => ((q.num i j).1 + (q.num j i).1, (q.num i j).2 - (q.num j i).2), q.bits + 1⟩

/-- The symmetrized entry is the average of the original entry and the conjugate of its
transposed entry. -/
private theorem symmetrizedQuantization_entry {I : Type}
    (q : QuantizedMatrixInput I I) (i j : I) :
    (symmetrizedQuantization q).matrix i j = (q.matrix i j + star (q.matrix j i)) / 2 := by
  simp only [symmetrizedQuantization, QuantizedMatrixInput.matrix, dyadicValue, pow_succ,
    Int.cast_add, Int.cast_sub, star_add, star_div₀, star_mul, star_pow,
    star_intCast, star_ofNat, Complex.star_def, Complex.conj_I]
  field_simp
  ring

/-- Symmetrizing quantized matrix data produces a Hermitian matrix. -/
private theorem symmetrizedQuantization_hermitian {I : Type}
    (q : QuantizedMatrixInput I I) : (symmetrizedQuantization q).matrix.IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [symmetrizedQuantization_entry, add_comm]

/-- For a Hermitian target, symmetrization preserves any uniform entrywise approximation bound. -/
private theorem symmetrizedQuantization_error {I : Type}
    (A : Matrix I I ℂ) (hA : A.IsHermitian) (q : QuantizedMatrixInput I I)
    (δ : ℝ) (hδ : ∀ i j, ‖q.matrix i j - A i j‖ ≤ δ) (i j : I) :
    ‖(symmetrizedQuantization q).matrix i j - A i j‖ ≤ δ := by
  have hstar : ‖star (q.matrix j i) - A i j‖ ≤ δ := by
    rw [← hA.apply i j, ← star_sub, norm_star]
    exact hδ j i
  have hid : (symmetrizedQuantization q).matrix i j - A i j =
      (1 / 2 : ℂ) * ((q.matrix i j - A i j) + (star (q.matrix j i) - A i j)) := by
    rw [symmetrizedQuantization_entry]
    ring
  calc
    ‖(symmetrizedQuantization q).matrix i j - A i j‖ =
        (1 / 2 : ℝ) * ‖(q.matrix i j - A i j) + (star (q.matrix j i) - A i j)‖ := by
      rw [hid, norm_mul]
      norm_num
    _ ≤ (1 / 2 : ℝ) * (δ + δ) :=
      mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hδ i j) hstar)) (by norm_num)
    _ = δ := by ring

/-- Collect tunable dyadic matrix approximation bounds, Hermitian quantization, and Lipschitz
polynomial-response stability. Under the stated nonzero-output gap, the same response words
give postselection probability and normalized-output error bounds. -/
theorem tunableGoal :

  (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (δ : ℝ), 0 < δ →
    ∃ q : QuantizedMatrixInput O I,
      (∀ o i, ‖q.matrix o i - A o i‖ ≤ δ) ∧
      q.bits ≤ Nat.ceil (Real.logb 2 (2 / δ)) + 1 ∧
      ‖q.matrix - A‖ ≤ Real.sqrt ((Fintype.card O * Fintype.card I : ℕ) : ℝ) * δ ∧
      (∀ i : ℕ, |matrixSingularValues q.matrix i - matrixSingularValues A i|
        ≤ ‖q.matrix - A‖) ∧
      ‖q.matrixᴴ * q.matrix - Aᴴ * A‖ ≤
        (2 * ‖A‖ + Real.sqrt ((Fintype.card O * Fintype.card I : ℕ) : ℝ) * δ) *
          (Real.sqrt ((Fintype.card O * Fintype.card I : ℕ) : ℝ) * δ) ∧
      q.readBitCost = Fintype.card O * Fintype.card I * (2 * (q.bits + 1)) ∧
      derivedQuantityBitCost (Fintype.card O * Fintype.card I) q.bits ≤
        (Fintype.card O * Fintype.card I + 1) * 4 *
          (Nat.ceil (Real.logb 2 (2 / δ)) + 2)^3) ∧

  (∀ (I : Type) [Fintype I] [DecidableEq I] (A : Matrix I I ℂ), A.IsHermitian →
    ∀ δ : ℝ, 0 < δ →
    ∃ q : QuantizedMatrixInput I I,
      (∀ i, (q.num i i).2 = 0) ∧
      (∀ i j, q.num i j = ((q.num j i).1, -((q.num j i).2))) ∧
      (∀ i j, ‖q.matrix i j - A i j‖ ≤ δ) ∧
      q.matrix.IsHermitian ∧
      spectralFrobenius (A - q.matrix) ≤
        Real.sqrt ((Fintype.card I * Fintype.card I : ℕ) : ℝ) * δ) ∧

  (∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      (A B : Matrix I I ℂ) (U V : Matrix H H ℂ) (F : Matrix H I ℂ)
      (p : Polynomial ℝ) (d : ℕ) (L δ : ℝ),
    A.IsHermitian → B.IsHermitian → ProjectedUnitaryEncoding A U F F →
    ProjectedUnitaryEncoding B V F F → p.degree ≤ (d : WithBot ℕ) →
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d p →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) → 0 ≤ L →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, |p.eval x - p.eval y| ≤ L * |x - y|) →
    0 ≤ δ → (∀ i j, ‖B i j - A i j‖ ≤ δ) →
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = d ∧
      (∀ x : ℝ, ((responseP base zs).eval (x : ℂ)).re = p.eval x) ∧
      adjointQueryCount (hermitianResponseWord F d base zs) = d ∧
      adjointGateCount (hermitianResponseWord F d base zs) = d + 1 ∧
      spectralFrobenius
        (compress (averageFrame F) (evaluate (parallelOracle U) (hermitianResponseWord F d base zs))
            (averageFrame F) -
          compress (averageFrame F) (evaluate (parallelOracle V) (hermitianResponseWord F d base zs))
            (averageFrame F)) ≤
        L * Real.sqrt ((Fintype.card I * Fintype.card I : ℕ) : ℝ) * δ) ∧

  (∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
      (A B : Matrix I I ℂ) (U V : Matrix H H ℂ) (F : Matrix H I ℂ)
      (p : Polynomial ℝ) (d : ℕ) (L : ℝ) (ψ : QState I) (δ : ℝ),
    A.IsHermitian → B.IsHermitian → ProjectedUnitaryEncoding A U F F →
    ProjectedUnitaryEncoding B V F F → p.degree ≤ (d : WithBot ℕ) →
    Qatlib.Concepts.QspSimulation.Achievability.HasRealParity d p →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) → 0 ≤ L →
    (∀ x ∈ Set.Icc (-1 : ℝ) 1, ∀ y ∈ Set.Icc (-1 : ℝ) 1, |p.eval x - p.eval y| ≤ L * |x - y|) →
    Normalized ψ → 0 ≤ δ → (∀ i j, ‖B i j - A i j‖ ≤ δ) →
    L * Real.sqrt ((Fintype.card I * Fintype.card I : ℕ) : ℝ) * δ < ‖stateVector
      ((Polynomial.aeval A) (Polynomial.map Complex.ofRealHom p) *ᵥ ψ)‖ →
    ∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = d ∧
      (∀ x : ℝ, ((responseP base zs).eval (x : ℂ)).re = p.eval x) ∧
      adjointQueryCount (hermitianResponseWord F d base zs) = d ∧
      adjointGateCount (hermitianResponseWord F d base zs) = d + 1 ∧
      postselectionProbability (evaluate (parallelOracle V) (hermitianResponseWord F d base zs))
          (averageFrame F) (averageFrame F) ψ ≥
        (‖stateVector ((Polynomial.aeval A) (Polynomial.map Complex.ofRealHom p) *ᵥ ψ)‖ -
          L * Real.sqrt ((Fintype.card I * Fintype.card I : ℕ) : ℝ) * δ)^2 ∧
      (∃ φ : QState I,
        postselectionOutput (evaluate (parallelOracle V) (hermitianResponseWord F d base zs))
            (averageFrame F) (averageFrame F) ψ = some φ ∧
        IsNormalizedApplication ((Polynomial.aeval A) (Polynomial.map Complex.ofRealHom p)) ψ φ
          (2 * L * Real.sqrt ((Fintype.card I * Fintype.card I : ℕ) : ℝ) * δ /
            ‖stateVector ((Polynomial.aeval A) (Polynomial.map Complex.ofRealHom p) *ᵥ ψ)‖))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro O I _ _ _ _ A δ hδ
    let k := Nat.ceil (Real.logb 2 (2 / δ))
    let q := quantized A k
    have he : ∀ o i, ‖q.matrix o i - A o i‖ ≤ δ :=
      fun o i => (quantized_entry A k o i).trans (quant_denominator δ hδ)
    have hf := spectralFrobenius_le_entry_bound (q.matrix-A) δ hδ.le he
    have ho := (spectral_operator_norm_le_frobenius (q.matrix-A)).trans hf
    refine ⟨q, he, Nat.le_succ k, ho,
      (rectangular_singular_weyl_and_mirsky O I q.matrix A).1,
      gram_difference_le A q.matrix _ (by positivity) ho, rfl, ?_⟩
    change (_ + 1) * 4 * (k + 1)^3 ≤ (_ + 1) * 4 * (k + 2)^3
    gcongr
    omega
  · intro I _ _ A hA δ hδ
    let k := Nat.ceil (Real.logb 2 (2 / δ))
    let q := quantized A k
    have he : ∀ i j, ‖q.matrix i j - A i j‖ ≤ δ :=
      fun i j => (quantized_entry A k i j).trans (quant_denominator δ hδ)
    have he' := symmetrizedQuantization_error A hA q δ he
    refine ⟨symmetrizedQuantization q, ?_, ?_, he',
      symmetrizedQuantization_hermitian q, ?_⟩
    · intro i
      simp [symmetrizedQuantization]
    · intro i j
      simp [symmetrizedQuantization, add_comm]
    · apply spectralFrobenius_le_entry_bound _ δ hδ.le
      intro i j
      simpa only [Matrix.sub_apply, norm_sub_rev] using! he' i j
  · intro H I _ _ _ _ A B U V F p d L δ hA hB hAU hBV hpdeg hpar hp hL hLip hδ he
    have hf : spectralFrobenius (A-B) ≤
        Real.sqrt ((Fintype.card I * Fintype.card I : ℕ) : ℝ) * δ := by
      apply spectralFrobenius_le_entry_bound _ δ hδ
      intro i j
      simpa only [Matrix.sub_apply, norm_sub_rev] using! he i j
    obtain ⟨base,zs,hbase,hzs,hn,hpoly,_,_,hq,hg,herr⟩ :=
      hermitian_same_word_actual_qsvt_frobenius_stability H I A B U V F p d L
        hA hB hAU hBV hpdeg hpar hp hL hLip
    refine ⟨base,zs,hbase,hzs,hn,hpoly,hq,hg,?_⟩
    exact herr.trans (by simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left hf hL)
  · intro H I _ _ _ _ A B U V F p d L ψ δ hA hB hAU hBV hpdeg hpar hp hL hLip hψ hδ he hgap
    have hf : spectralFrobenius (A-B) ≤
        Real.sqrt ((Fintype.card I * Fintype.card I : ℕ) : ℝ) * δ := by
      apply spectralFrobenius_le_entry_bound _ δ hδ
      intro i j
      simpa only [Matrix.sub_apply, norm_sub_rev] using! he i j
    let η := L * spectralFrobenius (A-B)
    let Δ := L * Real.sqrt ((Fintype.card I * Fintype.card I : ℕ) : ℝ) * δ
    let r := ‖stateVector ((Polynomial.aeval A) (Polynomial.map Complex.ofRealHom p) *ᵥ ψ)‖
    have hηΔ : η ≤ Δ := by
      dsimp [η, Δ]
      simpa only [mul_assoc] using! mul_le_mul_of_nonneg_left hf hL
    have hgap' : η < r := hηΔ.trans_lt hgap
    obtain ⟨base,zs,hbase,hzs,hn,hpoly,hprob,hout,hq,hg⟩ :=
      hermitian_same_word_actual_perturbed_postselection H I A B U V F p d L ψ
        hA hB hAU hBV hpdeg hpar hp hL hLip hψ hgap'
    refine ⟨base,zs,hbase,hzs,hn,hpoly,hq,hg,?_,?_⟩
    · have hs : (r-Δ)^2 ≤ (r-η)^2 :=
        pow_le_pow_left₀ (sub_nonneg.mpr hgap.le) (by linarith) 2
      exact hs.trans hprob
    · obtain ⟨φ,hφ,happ⟩ := hout
      refine ⟨φ,hφ,happ.1,happ.2.1,happ.2.2.trans ?_⟩
      have hb : 2*η/r ≤ 2*Δ/r :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hηΔ (by norm_num)) (norm_nonneg _)
      exact hb.trans_eq (by dsimp [Δ]; ring)

/-- A one-column dyadic frame of value `1 / 2` on the zero-qubit register, with identity input
frame and recorded Gram error `3 / 4`. -/
private noncomputable abbrev scaledSingletonFrame : FiniteFrameData where
  inputIndex := 1
  workspaceWires := 0
  num := fun _ _ => (1,0)
  bits := 1
  inputFrame := fun _ _ => 1
  gramErr := 3/4

/-- Every entry of the singleton frame is `1 / 2`. -/
private theorem scaledSingletonFrame_matrix : scaledSingletonFrame.frame =
    (fun _ : Reg 0 => fun _ : Fin 1 => (1/2 : ℂ)) := by
  ext i j
  dsimp only [FiniteFrameData.frame, scaledSingletonFrame, dyadicValue]
  norm_num

/-- The Gram matrix of the scaled singleton frame is `1 / 4` times the identity. -/
private theorem scaledSingletonFrame_gram :
    scaledSingletonFrame.frameᴴ * scaledSingletonFrame.frame =
      (1/4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  rw [scaledSingletonFrame_matrix]
  ext i j
  have hij : i = j := Subsingleton.elim _ _
  subst j
  norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Fintype.sum_unique]

/-- The scaled singleton frame satisfies the finite-frame certification conditions. -/
private theorem scaledSingletonFrame_certified : scaledSingletonFrame.IsCertified := by
  refine ⟨?_,?_,by norm_num [scaledSingletonFrame]⟩
  · let E : Matrix (Reg 0) (Fin 1) ℂ := fun _ _ => 1
    change Eᴴ * E = 1
    ext i j
    have hij : i = j := Subsingleton.elim _ _
    subst j
    simp [E, Matrix.mul_apply, Matrix.conjTranspose_apply]
  · rw [scaledSingletonFrame_gram]
    have h : (1/4 : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) - 1 = (-3/4 : ℂ) • 1 := by
      module
    rw [h,norm_smul,norm_one]
    norm_num [scaledSingletonFrame]

/-- The matrix `rangeProjector` of the scaled singleton frame is `1 / 4` times the identity. -/
private theorem scaledSingletonFrame_range : rangeProjector scaledSingletonFrame.frame =
    (1/4 : ℂ) • (1 : Matrix (Reg 0) (Reg 0) ℂ) := by
  unfold rangeProjector
  rw [scaledSingletonFrame_matrix]
  ext i j
  have hij : i = j := Subsingleton.elim i j
  subst j
  norm_num [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.smul_apply, Fin.sum_univ_one]

/-- The polar-corrected singleton frame has `rangeProjector` equal to the identity. -/
private theorem scaledSingletonFrame_polar_range :
    rangeProjector (nearColumnPolar scaledSingletonFrame.frame) =
      (1 : Matrix (Reg 0) (Reg 0) ℂ) := by
  have hc := scaledSingletonFrame_certified
  have hpos := fun i => (nearColumnPolar_singular_bounds scaledSingletonFrame.frame
    (3/4) (by norm_num) (by norm_num) hc.2.1 i).1
  have hi := nearColumnPolar_isometry scaledSingletonFrame.frame hpos
  have hentry := congrArg (fun A : Matrix (Fin 1) (Fin 1) ℂ => A 0 0) hi
  ext a b
  have hab : b = a := Subsingleton.elim _ _
  subst b
  have he : star ((nearColumnPolar scaledSingletonFrame.frame) a 0) *
      (nearColumnPolar scaledSingletonFrame.frame) a 0 = 1 := by
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_unique,
      Matrix.one_apply_eq, Subsingleton.elim (default : Reg 0) a] using! hentry
  simpa only [rangeProjector, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Fin.sum_univ_one, Matrix.one_apply_eq, mul_comm] using! he

/-- Filtering a single gate equal to four times identity against an empty second circuit gives
four times the frame flag filter. -/
private theorem filter_scalar_body (F : Matrix (Reg 0) (Fin 1) ℂ) :
    evaluate (parallelOracle (J := Bool) (1 : Matrix (Reg 0) (Reg 0) ℂ))
      (frameFilteredWord F [.gate ((4 : ℂ) • 1)] []) = (4 : ℂ) • frameFlagFilter F := by
  rw [(frame_filter_actual_body_substitution_and_cost (Reg 0) (Fin 1) F 1
    [.gate ((4 : ℂ) • 1)] []).1]
  simp only [frameFilteredProduct, evaluate, instructionMatrix, Matrix.mul_one,
    tensorGate_one, Matrix.one_mul]
  have h : TensorGate (1 : Matrix Bool Bool ℂ) ((4 : ℂ) • (1 : Matrix (Reg 0) (Reg 0) ℂ)) =
      (4 : ℂ) • (1 : Matrix (Bool × Reg 0) (Bool × Reg 0) ℂ) := by
    ext i j
    by_cases hflag : i.1 = j.1 <;> by_cases hdata : i.2 = j.2 <;>
      simp [TensorGate, Matrix.smul_apply, Matrix.one_apply, Prod.ext_iff, hflag, hdata]
  rw [h, Matrix.mul_smul, Matrix.mul_one]

/-- The norm of any matrix entry is at most the matrix operator norm. -/
private theorem operator_entry_bound {I : Type} [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (i j : I) : ‖A i j‖ ≤ ‖A‖ := by
  have hk : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖ = 1 := by
    have hs : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j)‖^2 = 1 := by
      rw [norm_toEuclidean_sq_eq_re_inner, (normalized_iff_inner_self _).mp (normalized_ket j)]
      rfl
    nlinarith [norm_nonneg (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket j))]
  have hn := l2_norm_mulVec_fromVec_le A (Qatlib.Foundations.PureStateMath.Ket j)
  rw [hk, mul_one] at hn
  have hi := PiLp.norm_apply_le (toEuclidean_fromVec (A*ᵥKet j)) i
  have he : (A*ᵥKet j) i = A i j := by
    simp [Matrix.mulVec, dotProduct, Qatlib.Foundations.PureStateMath.Ket, mul_ite]
  change ‖(A*ᵥKet j) i‖ ≤ ‖toEuclidean_fromVec (A*ᵥKet j)‖ at hi
  rw [he] at hi
  exact hi.trans hn

/-- For the scaled singleton frame and a gate of norm four, the proposed frame-filter error
bound `2 * gramErr * (2 - gramErr)` fails. -/
private theorem scaledSingletonFrame_error_refutation :
    ¬ (‖evaluate (parallelOracle (J := Bool) (1 : Matrix (Reg 0) (Reg 0) ℂ))
        (frameFilteredWord scaledSingletonFrame.frame [.gate ((4 : ℂ) • 1)] []) -
      evaluate (parallelOracle (J := Bool) (1 : Matrix (Reg 0) (Reg 0) ℂ))
        (frameFilteredWord (nearColumnPolar scaledSingletonFrame.frame) [.gate ((4 : ℂ) • 1)] [])‖ ≤
      2 * scaledSingletonFrame.gramErr * (2 - scaledSingletonFrame.gramErr)) := by
  intro hb
  rw [filter_scalar_body, filter_scalar_body] at hb
  let E := (4 : ℂ) • frameFlagFilter scaledSingletonFrame.frame -
    (4 : ℂ) • frameFlagFilter (nearColumnPolar scaledSingletonFrame.frame)
  have he : E (false, default) (true, default) = 3 := by
    dsimp only [E]
    simp only [frameFlagFilter]
    rw [scaledSingletonFrame_range, scaledSingletonFrame_polar_range]
    norm_num [TensorGate, PauliX, permMatrix, Matrix.one_apply]
  have heNorm := operator_entry_bound E (false, default) (true, default)
  rw [he] at heNorm
  have hthree : (3 : ℝ) ≤ ‖E‖ := by simpa using! heNorm
  have hbound : 2 * scaledSingletonFrame.gramErr * (2-scaledSingletonFrame.gramErr) =
      (15/8 : ℝ) := by norm_num [scaledSingletonFrame]
  rw [hbound] at hb
  change ‖E‖ ≤ (15/8 : ℝ) at hb
  linarith

/-- There exist certified frame data and a unitary oracle for which a circuit evaluation of norm
four violates the proposed uniform polar-correction error bound for frame filtering. -/
theorem frame_filter_noncontractive_counterexample :
    ∃ d : FiniteFrameData, d.IsCertified ∧
      ∃ (O : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ)
        (ca cb : List (AdjointStep (Reg d.workspaceWires))),
        O ∈ Matrix.unitaryGroup (Reg d.workspaceWires) ℂ ∧
        ‖evaluate O ca‖ = 4 ∧ cb = [] ∧
        2*d.gramErr*(2-d.gramErr) <
          ‖evaluate (parallelOracle (J := Bool) O) (frameFilteredWord d.frame ca cb) -
            evaluate (parallelOracle (J := Bool) O)
              (frameFilteredWord (nearColumnPolar d.frame) ca cb)‖ := by
  refine ⟨scaledSingletonFrame,scaledSingletonFrame_certified,1,
    [.gate ((4 : ℂ) • 1)],[],Submonoid.one_mem _,?_,rfl,?_⟩
  · simp only [evaluate,instructionMatrix,Matrix.mul_one]
    rw [norm_smul,norm_one]
    norm_num
  · exact lt_of_not_ge scaledSingletonFrame_error_refutation

/-- The displayed conjunction of frame-filter realization, count, synthesis, and uniform error
claims is false, as witnessed by the noncontractive frame-filter counterexample. -/
theorem not_clause36 : ¬ (

  (∀ (H M : Type) [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M]
      (F : Matrix H M ℂ) (O : Matrix H H ℂ) (ca cb : List (AdjointStep H)),
    evaluate (parallelOracle (J := Bool) O) (frameFilteredWord F ca cb) =
        frameFilteredProduct F (evaluate O ca) (evaluate O cb) ∧
      adjointQueryCount (frameFilteredWord F ca cb) =
        adjointQueryCount ca + adjointQueryCount cb ∧
      adjointGateCount (frameFilteredWord F ca cb) =
        adjointGateCount ca + adjointGateCount cb + 1) ∧

  (∀ ψ : QState (Bool × Bool),
      Run (1 : Matrix (Bool × Bool) (Bool × Bool) ℂ)
        ([Step.gate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard),
          Step.gate (relabelGate (Equiv.prodComm Bool Bool) CNOT),
          Step.gate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)] : Circuit (Bool × Bool)) ψ =
        ApplyGate (frameFlagFilter plusFrameCol) ψ) ∧
    QueryCount ([Step.gate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard),
      Step.gate (relabelGate (Equiv.prodComm Bool Bool) CNOT),
      Step.gate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)] : Circuit (Bool × Bool)) = 0 ∧
    GateCount ([Step.gate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard),
      Step.gate (relabelGate (Equiv.prodComm Bool Bool) CNOT),
      Step.gate (TensorGate (1 : Matrix Bool Bool ℂ) Hadamard)] : Circuit (Bool × Bool)) = 3 ∧

  (∀ d : FiniteFrameData, d.IsCertified →
    ∀ (O : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ)
      (ca cb : List (AdjointStep (Reg d.workspaceWires))),
    ∃ filterTable : List (ReflectionGate
        (d.workspaceWires + 1 + (d.workspaceWires + 1 + 1))),
        reflectionLegal filterTable ∧
        filterTable.length ≤ continuousSynthesisGateBound (d.workspaceWires + 1) ∧
        (∀ φ : QState (Reg (d.workspaceWires + 1)),
          Run 1 (reflectionCompile filterTable) (knownFrameEmbed (d.workspaceWires + 1) φ) =
            knownFrameEmbed (d.workspaceWires + 1) (flagRegisterMatrix (frameFlagFilter
              (nearColumnPolar d.frame)) *ᵥ φ)) ∧

        ‖flagRegisterMatrix (frameFlagFilter (nearColumnPolar d.frame)) -
            flagRegisterMatrix (frameFlagFilter d.frame)‖ ≤
          2 * d.gramErr * (2 - d.gramErr) ∧
        ‖evaluate (parallelOracle (J := Bool) O) (frameFilteredWord d.frame ca cb) -
            evaluate (parallelOracle (J := Bool) O)
              (frameFilteredWord (nearColumnPolar d.frame) ca cb)‖ ≤
          2 * d.gramErr * (2 - d.gramErr) ∧

        adjointQueryCount (frameFilteredWord d.frame ca cb) =
          adjointQueryCount ca + adjointQueryCount cb ∧
        adjointGateCount (frameFilteredWord d.frame ca cb) =
          adjointGateCount ca + adjointGateCount cb + 1)) := by
  intro h
  obtain ⟨_,_,_,_,_,herr,_,_⟩ := h.2.2.2.2 scaledSingletonFrame
    scaledSingletonFrame_certified (1 : Matrix (Reg 0) (Reg 0) ℂ)
    [.gate ((4 : ℂ) • 1)] []
  exact scaledSingletonFrame_error_refutation herr

/-- Flip the unique bit of a one-qubit register. -/
private def oneWireFlip (x : Reg 1) : Reg 1 := fun i => !(x i)

/-- The permutation matrix for flipping the unique bit of a one-qubit register. -/
private noncomputable def oneWireFlipMatrix : Matrix (Reg 1) (Reg 1) ℂ :=
  permMatrix oneWireFlip

/-- The one-wire bit-flip matrix is unitary. -/
private theorem oneWireFlip_unitary : oneWireFlipMatrix ∈ Matrix.unitaryGroup (Reg 1) ℂ := by
  apply permMatrix_unitary
  intro x
  funext i
  exact Bool.not_not (x i)

/-- The one-wire bit-flip matrix fails `IsWireLift` for every subset of its wire set. -/
private theorem oneWireFlip_not_lift (w : Finset (Fin 1)) : ¬ IsWireLift w oneWireFlipMatrix := by
  intro h
  let a : Reg 1 := fun _ => false
  let b : Reg 1 := fun _ => true
  have hab : a ≠ b := by
    intro he
    have he0 := congrFun he 0
    contradiction
  have haa : oneWireFlipMatrix a a = 0 := by
    change (if a = b then (1:ℂ) else 0) = 0
    exact if_neg hab
  have hab' : oneWireFlipMatrix a b = 1 := by
    change (if a = a then (1:ℂ) else 0) = 1
    exact if_pos rfl
  by_cases hw : (0 : Fin 1) ∈ w
  · have hz := h.2 a b ⟨0,hw,by decide⟩
    rw [hab'] at hz
    norm_num at hz
  · have he := h.1 a b a a (by
      intro i hi
      have hi0 : i = 0 := Subsingleton.elim _ _
      subst i
      exact False.elim (hw hi))
    rw [hab',haa] at he
    norm_num at he

/-- There exists a one-wire unitary whose single-gate circuit has no well-formed realization
under the specified dynamic-schedule conditions. -/
theorem one_wire_unitary_without_dynamic_schedule :
    ∃ U : Matrix (Reg 1) (Reg 1) ℂ, U ∈ Matrix.unitaryGroup (Reg 1) ℂ ∧
      ¬ ∃ s : DynSchedule 1, s.WellFormed ∧ s.Realizes 1 [.gate U] := by
  refine ⟨oneWireFlipMatrix,oneWireFlip_unitary,?_⟩
  rintro ⟨s,hw,hr⟩
  obtain ⟨core,release,hsteps,hlen,hops,_,_,_⟩ := hr
  have hlen' : core.length = 1 := by simpa using! hlen
  obtain ⟨st,rfl⟩ := List.length_eq_one_iff.mp hlen'
  have hop := hops (st,AdjointStep.gate oneWireFlipMatrix) (by simp)
  change st.op = oneWireFlipMatrix at hop
  have hst := hw st (by rw [hsteps]; simp)
  rw [hop] at hst
  exact oneWireFlip_not_lift st.wires hst

/-- The displayed universal dynamic-schedule claims are false under the given `IsWireLift` and
realization definitions. -/
theorem not_clause37 : ¬ (

  (∀ (N : ℕ) (O : Matrix (Reg N) (Reg N) ℂ) (cs : List (AdjointStep (Reg N))),
    ∃ sched : DynSchedule N,
      sched.WellFormed ∧
      sched.Realizes O cs ∧
      sched.peak ≤ N ∧
      (∀ i ∈ sched.liveCounts, i ≤ sched.peak)) ∧

  (∀ d : FiniteFrameData, d.IsCertified →
    ∀ (O : Matrix (Reg d.workspaceWires) (Reg d.workspaceWires) ℂ)
      (ca cb : List (AdjointStep (Reg d.workspaceWires))),
    ∃ sched : DynSchedule (d.workspaceWires + 1),
      sched.WellFormed ∧
      sched.Realizes (flagRegisterMatrix (parallelOracle (J := Bool) O))
        (flagRegWord (frameFilteredWord d.frame ca cb)) ∧
      sched.peak = d.workspaceWires + 1 ∧
      sched.liveCounts.getLast? = some d.workspaceWires)) := by
  intro h
  obtain ⟨U,_,hno⟩ := one_wire_unitary_without_dynamic_schedule
  obtain ⟨s,hw,hr,_,_⟩ := h.1 1 1 [.gate U]
  exact hno ⟨s,hw,hr⟩

/-- Compiled access totals count all forward and backward demands and count controlled demands
exactly when controlled access is supplied. -/
theorem compiled_access_word_totals {H : Type} (a : UnknownAccess H) (ds : List AccessDemand) :
    compiledCallTotals (compileAccessWord a ds) =
      ((ds.filter (· = .forward)).length, (ds.filter (· = .backward)).length,
        if a.suppliesControlled then (ds.filter (· = .controlled)).length else 0) := by
  induction ds with
  | nil => simp [compileAccessWord, compiledCallTotals]
  | cons d ds ih =>
    simp only [compileAccessWord] at ih
    simp only [compileAccessWord, List.map_cons, compiledCallTotals, ih]
    cases d <;> cases hf : a.suppliesControlled <;>
      simp [compileAccess, CompiledAccess.callCounts, hf]

/-- The displayed access-compilation conjunction is false because its split-word counting clause
equates totals for the whole word with counts from only a prefix. -/
theorem not_clause38 : ¬ (

  (∀ (H : Type) [Fintype H] [DecidableEq H] (a : UnknownAccess H),
    a.unitary ∈ Matrix.unitaryGroup H ℂ →
    (compileAccess a .forward).callCounts = (1, 0, 0) ∧
    (compileAccess a .forward).realized = parallelOracle a.unitary ∧
    (compileAccess a .backward).callCounts = (0, 1, 0) ∧
    (compileAccess a .backward).realized = (parallelOracle a.unitary)ᴴ ∧

    (a.suppliesControlled = true →
      (compileAccess a .controlled).callCounts = (0, 0, 1) ∧
        (compileAccess a .controlled).realized = controlOracle a.unitary) ∧

    (a.suppliesControlled = false → compileAccess a .controlled = .unavailable) ∧

    (∀ (c : CompiledAccess H), c = compileAccess a .controlled →
      (∃ U : Matrix H H ℂ, c = .controlledC U) → a.suppliesControlled = true)) ∧

  (∀ (H : Type) (a : UnknownAccess H) (ds : List AccessDemand),
    (compileAccessWord a ds).length = ds.length ∧
      ∀ (fwd bwd : List AccessDemand),
        ds = fwd ++ bwd →
          (compiledCallTotals (compileAccessWord a ds)).1 =
            (fwd.filter (· = .forward)).length ∧
          (compiledCallTotals (compileAccessWord a ds)).2.1 =
            (fwd.filter (· = .backward)).length) ∧

  (∀ (H : Type) [Fintype H] [DecidableEq H] (U : Matrix H H ℂ)
      (cs : List (AdjointStep H)),
    evaluate (controlOracle U) (compileControlled cs) =
      controlOracle (evaluate U cs) ∧
    adjointQueryCount (compileControlled cs) = adjointQueryCount cs ∧
    adjointGateCount (compileControlled cs) = adjointGateCount cs)) := by
  intro h
  let a : UnknownAccess (Fin 1) := ⟨1, false⟩
  have ht := (h.2.1 (Fin 1) a [.forward]).2 [] [.forward] rfl
  have hf := ht.1
  norm_num [compileAccessWord, compiledCallTotals, compileAccess, CompiledAccess.callCounts] at hf

/-- The explicit three-row, one-column matrix input whose first entry is one and whose other
entries are zero. -/
private noncomputable abbrev collidingColumn : MatrixInputModel :=
  .explicit 3 1 (fun i _ => if i = 0 then (1,0) else (0,0)) 0

/-- The described matrix of `collidingColumn` is one in row zero and zero in every other row. -/
private theorem collidingColumn_entry (i : Fin 3) (j : Fin 1) :
    collidingColumn.describedMatrix i j = if i = 0 then (1 : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [collidingColumn, MatrixInputModel.describedMatrix, dyadicValue]

/-- The operator norm of the matrix described by `collidingColumn` is at most one. -/
private theorem collidingColumn_norm : ‖collidingColumn.describedMatrix‖ ≤ 1 := by
  apply (spectral_operator_norm_le_frobenius _).trans
  change Real.sqrt (∑ i : Fin 3, ∑ j : Fin 1, Complex.normSq
    (collidingColumn.describedMatrix i j)) ≤ 1
  simp only [collidingColumn_entry]
  norm_num [Fin.sum_univ_succ]

/-- For every three-qubit state vector and real scaling factor, the displayed column
approximation using the implicit register casts has squared error at least `1 / 2`. -/
theorem parity_cast_column_error_lower (φ : QState (Reg 3)) (c : ℝ) :
    (1/2 : ℝ) ≤ ∑ i : Fin 3, ‖(c:ℂ) * φ i - (if i = 0 then (1:ℂ) else 0)‖^2 := by
  have he : (∑ i : Fin 3, ‖(c:ℂ) * φ i - (if i = 0 then (1:ℂ) else 0)‖^2) =
      ‖(c:ℂ) * φ (0 : Reg 3) - 1‖^2 + ‖(c:ℂ) * φ (1 : Reg 3)‖^2 +
        ‖(c:ℂ) * φ (0 : Reg 3)‖^2 := by
    simp [Fin.sum_univ_succ]
    ring_nf
    congr 4
  rw [he]
  have ht := norm_le_norm_add_norm_sub ((c:ℂ)*φ (0 : Reg 3)) (1 : ℂ)
  norm_num only [norm_one] at ht
  have ht' : (1:ℝ) ≤ ‖(c:ℂ)*φ (0 : Reg 3) - 1‖ + ‖(c:ℂ)*φ (0 : Reg 3)‖ := by linarith
  have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1) ht' 2
  nlinarith [sq_nonneg (‖(c:ℂ)*φ (0 : Reg 3) - 1‖ - ‖(c:ℂ)*φ (0 : Reg 3)‖),
    sq_nonneg ‖(c:ℂ)*φ (1 : Reg 3)‖]

/-- The displayed universal column-preparation, ridge-encoding, marking, and resource package is
false, as witnessed by the column approximation lower bound. -/
theorem not_clause44 : ¬ (

  (∀ (O I : Type) [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
      (A : Matrix O I ℂ) (lam : ℝ), 0 ≤ lam →
    (ridgeAugmentedMatrix A lam)ᴴ * ridgeAugmentedMatrix A lam =
      Aᴴ * A + (lam : ℂ) • 1) ∧

  (∀ m : MatrixInputModel, ∀ (hcols : 0 < m.cols), ∀ (lam : ℝ), 0 ≤ lam → ∀ ε : ℝ, 0 < ε →
    ‖m.describedMatrix‖ ≤ 1 →
    ∃ (bTable : List (ReflectionGate (m.rows + (m.rows + 1))))
      (U : Matrix (Reg m.rows) (Reg m.rows) ℂ)
      (φ : QState (Reg m.rows)) (ledgerB ledgerU : BackendLedger),

      reflectionLegal bTable ∧ U ∈ Matrix.unitaryGroup (Reg m.rows) ℂ ∧
      Normalized φ ∧ U *ᵥ Qatlib.Foundations.PureStateMath.Ket (fun _ => false) = φ ∧

      ((∑ i : Fin m.rows, ‖m.describedMatrix i ⟨0, hcols⟩‖^2 = 0 ∨
          ∃ c : ℝ, 0 < c ∧
            ∑ i : Fin m.rows, ‖c * φ i - m.describedMatrix i ⟨0, hcols⟩‖^2 ≤ ε^2)) ∧
      (∀ ψ : QState (Reg m.rows),
        Run 1 (reflectionCompile bTable) (knownFrameEmbed m.rows ψ) =
          knownFrameEmbed m.rows (U *ᵥ ψ)) ∧

      (∃ (H : Type) (_hH1 : Fintype H) (_hH2 : DecidableEq H)
          (W : Matrix H H ℂ) (L : Matrix H (Fin m.rows ⊕ Fin m.cols) ℂ)
          (R : Matrix H (Fin m.cols) ℂ),
        IsIsometry L ∧ IsIsometry R ∧
        BlockEncoding (ridgeAugmentedMatrix m.describedMatrix lam) W L R (1 + lam) ε) ∧
      ledgerU.readoutBitOps = m.readBitCost ∧

      (∃ markTable : List (ReflectionGate (m.rows + 1 + (m.rows + 1 + 1))),
        reflectionLegal markTable ∧
        (∀ i : Fin m.rows,
          (reflectionProgramMatrix markTable) *ᵥ
              (knownFrameEmbed (m.rows + 1)
                (Qatlib.Foundations.PureStateMath.Ket (knownDataEquiv m.rows (i, false)))) =
            knownFrameEmbed (m.rows + 1)
              (Qatlib.Foundations.PureStateMath.Ket (knownDataEquiv m.rows
                (i, (m.describedMatrix i ⟨0, hcols⟩ ≠ 0 : Bool)))))) ∧

      (∀ (rows cols bits : ℕ) (num : Fin rows → Fin cols → ℤ × ℤ),
        m = .explicit rows cols num bits →
          m.readBitCost = rows * cols * (2 * (bits + 1))) ∧
      ledgerB.ancillaQubits ≤ m.rows + 1 ∧
      ledgerB.elementaryGates ≤ continuousSynthesisGateBound (m.rows + 1) +
        m.rows * (m.readBitCost + 2) ∧
      ledgerB.peakLiveQubits ≤ m.rows + (m.rows + 1))) := by
  intro h
  obtain ⟨b,U,φ,ledgerB,ledgerU,hr⟩ := h.2 collidingColumn (by decide) 0 (by norm_num)
    (1/4) (by norm_num) collidingColumn_norm
  have hp := hr.2.2.2.2.1
  rcases hp with hz | ⟨c,_,hc⟩
  · change (∑ i : Fin 3, ‖collidingColumn.describedMatrix i (0 : Fin 1)‖^2) = 0 at hz
    simp only [collidingColumn_entry] at hz
    norm_num [Fin.sum_univ_succ] at hz
  · have hl := parity_cast_column_error_lower φ c
    simp only [collidingColumn_entry] at hc
    have hbad := hl.trans hc
    norm_num at hbad

end Qatlib.Concepts.LocalMachine.LocalTransport
