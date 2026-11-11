/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Lean.Elab.Tactic.NormCast
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SimpRw
import Mathlib.Tactic.SplitIfs
import Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
import Qatlib.Concepts.HhlErrorBridge.FilterStability
import Qatlib.Concepts.NativeNumerics.LayeredMean.CountedHHLProgram
import Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.NearGridHHLOutput
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.LchsSimulation.StaticLchs.PreparedAmplitudeAmplification

/-!
# Sine-envelope HHL circuits and postselection estimates

This module defines the sine-envelope phase-estimation and HHL words and proves their legality,
resource counts, and spectral action. It implements the filtering and postselection analysis of
[HarrowHassidimLloyd2009] with explicit resolution constants.

The corrected well event selects the three-level success flag. Kernel estimates control
full-workspace error, relative flag mass, normalized well-state error, and
amplitude-amplification success.

## Main statements

* `sin_envelope_word_legality_and_counts`: circuit unitarity and exact instruction counts.
* `sin_envelope_hhl_full_workspace_error`: error at most `η` at resolution `21/(d*η)`.
* `sin_envelope_conditional_well_output_error`: normalized well-branch accuracy.
* `sin_envelope_aa_success_and_cost`: constant success probability with a bounded iteration
  count.

## References

* [Harrow et al., 2009][HarrowHassidimLloyd2009]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false


open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.HhlAlgorithms.GridExactHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlErrorBridge.FilterStability
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram
open Qatlib.Concepts.BlockEncoding.Postselection

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers

open Matrix Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Real

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Decode a phase label as `z/M` up to the midpoint and as `z/M - 1` above it. -/
noncomputable def sinEnvelopeDecode (M : ℕ) (z : Fin M) : ℝ :=
  if 2 * (z.val : ℕ) ≤ M then (z.val : ℝ) / (M : ℝ) else (z.val : ℝ) / (M : ℝ) - 1

/-- The phase-estimation circuit consisting of sine-envelope preparation, the phase-threshold
loop, and inverse Fourier transform. -/
noncomputable def sinEnvelopePhaseCircuit (M : ℕ) (hM : 2 ≤ M) :
    Circuit (Fin M × (Bool × I)) :=
  [Step.gate (TensorGate (sinEnvelopePrep M hM)
      (1 : Matrix (Bool × I) (Bool × I) ℂ))] ++
    phaseThresholdLoop M (M - 1) ++
    [Step.gate (TensorGate (QFTMatrix M)ᴴ (1 : Matrix (Bool × I) (Bool × I) ℂ))]

/-- The reversed adjoint-step encoding of the sine-envelope phase circuit. -/
noncomputable def sinEnvelopeForwardWord (M : ℕ) (hM : 2 ≤ M) :
    List (AdjointStep (Fin M × (Bool × I))) :=
  ((sinEnvelopePhaseCircuit (I := I) M hM).map stepToAdjoint).reverse

/-- The register equivalence moving the Boolean sector coordinate behind the phase coordinate. -/
def sinEnvelopeSectorEquiv (D M : ℕ) :
    Bool × (Fin M × (Fin 3 × Fin D)) ≃ Fin M × (Bool × (Fin 3 × Fin D)) :=
  (Equiv.prodComm Bool (Fin M × (Fin 3 × Fin D))).trans
    ((Equiv.prodAssoc (Fin M) (Fin 3 × Fin D) Bool).trans
      (Equiv.prodCongr (Equiv.refl (Fin M)) (Equiv.prodComm (Fin 3 × Fin D) Bool)))

/-- Extend a gate to act identically in each Boolean sector, with the workspace coordinates
relabeled. -/
noncomputable def sinEnvelopeLiftGate {D M : ℕ}
    (G : Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ) :
    Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ :=
  relabelGate (sinEnvelopeSectorEquiv D M) (TensorGate (1 : Matrix Bool Bool ℂ) G)

/-- Lift a data oracle to a controlled oracle on the Boolean register, preserving the phase and
three-level flag registers. -/
noncomputable def sinEnvelopeOracleLift {D M : ℕ} (U : Operator D) :
    Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ :=
  TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
    (controlOracle (TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U))

/-- The phase-label-controlled three-level flag rotation, tensored with the identity on the data
register. -/
noncomputable def sinEnvelopeFlagGate {D M : ℕ} (d : ℝ) :
    Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ :=
  relabelGate (Equiv.prodAssoc (Fin M) (Fin 3) (Fin D))
    (TensorGate (BlockDiag (fun z : Fin M =>
      sinEnvelopeFlagRotation d (sinEnvelopeDecode M z))) (1 : Operator D))

/-- Apply input preparation `B` to the data register while preserving the phase and three-level
flag registers. -/
noncomputable def sinEnvelopePrepMain {D M : ℕ} (B : Operator D) :
    Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ :=
  relabelGate (Equiv.prodAssoc (Fin M) (Fin 3) (Fin D))
    (TensorGate (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
      (1 : Matrix (Fin 3) (Fin 3) ℂ)) B)

/-- The HHL word combining input preparation, forward phase estimation, flag rotation, and
adjoint uncomputation. -/
noncomputable def sinEnvelopeHHLWord {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (d : ℝ)
    (B : Operator D) :
    List (AdjointStep (Fin M × (Bool × (Fin 3 × Fin D)))) :=
  adjointCircuit (sinEnvelopeForwardWord M hM) ++
    [AdjointStep.gate (sinEnvelopeLiftGate (sinEnvelopeFlagGate d))] ++
    sinEnvelopeForwardWord M hM ++
    [AdjointStep.gate (sinEnvelopeLiftGate (sinEnvelopePrepMain B))]

/-- Evaluate the HHL word on a basis input with phase, Boolean, and three-level flag registers
initialized to zero. -/
noncomputable def sinEnvelopeHHLRun {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U : Operator D)
    (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  evaluate (sinEnvelopeOracleLift U) (sinEnvelopeHHLWord M hM d B) *ᵥ
    TensorState (Ket (⟨0, by omega⟩ : Fin M))
      (TensorState (Ket false) (TensorState (Ket (0 : Fin 3)) (Ket j)))

/-- The ideal spectral filter output, with the phase and Boolean registers reset to their
initial states. -/
noncomputable def sinEnvelopeHHLIdeal {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V : Operator D) (d : ℝ) (B : Operator D) (j : Fin D) :
    QState (Fin M × (Bool × (Fin 3 × Fin D))) :=
  TensorState (Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Ket false)
    (fun p : Fin 3 × Fin D =>
      ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
        (B *ᵥ Ket j)) p.2))

/-- The spectrally weighted sum of the ideal combined flag mass, weighted by squared
prepared-input coefficients. -/
noncomputable def sinEnvelopeIdealMass {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) : ℝ :=
  ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖ ^ 2 * sinEnvelopeFlagMass d (eig i)

/-- The sum weighted by spectral coefficients and phase-kernel masses of the combined flag mass
at decoded labels. -/
noncomputable def sinEnvelopeActualMass {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) : ℝ :=
  ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖ ^ 2 *
    ∑ z, ‖sinEnvelopeKernel M (eig i) z‖ ^ 2 *
      sinEnvelopeFlagMass d (sinEnvelopeDecode M z)

/-- The spectral kernel state with three-level flag one and no success-filter amplitude factor. -/
noncomputable def sinEnvelopeActualWellState {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) :
    QState (Fin M × (Fin 3 × Fin D)) :=
  ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i • ∑ z, sinEnvelopeKernel M (eig i) z •
    TensorState (Ket z) (TensorState (Ket (1 : Fin 3)) (V *ᵥ Ket i))

/-- The spectral kernel state with flag one, weighted by the success filter at each decoded
phase label. -/
noncomputable def sinEnvelopeActualWellStateCorrected {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) :
    QState (Fin M × (Fin 3 × Fin D)) :=
  ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i • ∑ z, sinEnvelopeKernel M (eig i) z •
    (sinEnvelopeFilterF d (sinEnvelopeDecode M z) : ℂ) •
      TensorState (Ket z) (TensorState (Ket (1 : Fin 3)) (V *ᵥ Ket i))

/-- The spectral kernel state with flag one, weighted by the success filter at each exact
eigenphase. -/
noncomputable def sinEnvelopeIdealWellState {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ) :
    QState (Fin M × (Fin 3 × Fin D)) :=
  ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i • (sinEnvelopeFilterF d (eig i) : ℂ) •
    ∑ z, sinEnvelopeKernel M (eig i) z •
      TensorState (Ket z) (TensorState (Ket (1 : Fin 3)) (V *ᵥ Ket i))

/-- Scale a finite state by the reciprocal of its Euclidean norm; the zero state remains zero. -/
noncomputable def sinEnvelopeConditionalOutput {I : Type} [Fintype I] [DecidableEq I]
    (v : QState I) : QState I :=
  (Real.sqrt (∑ p, ‖v p‖ ^ 2))⁻¹ • v

/-- The workspace event where the Boolean control coordinate is true. -/
def sinEnvelopeWellSet (D M : ℕ) :
    Finset (Fin M × (Bool × (Fin 3 × Fin D))) :=
  Finset.univ.filter (fun p => p.2.1 = 1)

/-- The workspace event where the three-level flag coordinate equals one. -/
def sinEnvelopeWellSetCorrected (D M : ℕ) :
    Finset (Fin M × (Bool × (Fin 3 × Fin D))) :=
  Finset.univ.filter (fun p => p.2.2.1 = 1)

/-- The matrix evaluating the base sine-envelope HHL word, used as the preparation operator for
amplitude amplification. -/
noncomputable def sinEnvelopeAmplifiedWord {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (U : Operator D) (d : ℝ) (B : Operator D) :
    Matrix (Fin M × (Bool × (Fin 3 × Fin D)))
      (Fin M × (Bool × (Fin 3 × Fin D))) ℂ :=
  evaluate (sinEnvelopeOracleLift U) (sinEnvelopeHHLWord M hM d B)

/-- The workspace basis point with phase zero, Boolean control false, three-level flag zero, and
data label `j`. -/
def sinEnvelopeCleanInputPoint {D M : ℕ} (hM : 2 ≤ M) (j : Fin D) :
    Fin M × (Bool × (Fin 3 × Fin D)) :=
  (⟨0, by omega⟩, false, (0, j))

/-- On eigenphases at least `2*d`, the ideal success-filter operator equals the spectral
reciprocal filter with coefficients `d/eig i`. See [HarrowHassidimLloyd2009]. -/
theorem sin_envelope_ideal_well_output_direction {D : ℕ} (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ)
    (heig : ∀ i, 2 * d ≤ eig i) :
    (V * Matrix.diagonal (fun i => (sinEnvelopeFilterF d (eig i) : ℂ)) * Vᴴ) *ᵥ
        (B *ᵥ Ket j) =
      (V * Matrix.diagonal (fun i => ((d / eig i : ℝ) : ℂ)) * Vᴴ) *ᵥ
        (B *ᵥ Ket j) := by
  have hf : (fun i => (sinEnvelopeFilterF d (eig i) : ℂ)) =
      (fun i => ((d / eig i : ℝ) : ℂ)) := by
    funext i
    simp [sinEnvelopeFilterF, heig i]
  rw [hf]

/-- The sine-envelope phase circuit has unitary gate instructions. -/
theorem sin_envelope_phase_circuit_unitary (M : ℕ) (hM : 2 ≤ M) :
    IsUnitaryCircuit (sinEnvelopePhaseCircuit (I := I) M hM) := by
  intro G hG
  simp only [sinEnvelopePhaseCircuit, List.mem_append, List.mem_singleton,
    Step.gate.injEq] at hG
  rcases hG with (rfl | hG) | rfl
  · exact tensorGate_unitary (sin_envelope_state_normalized_and_prep M hM).2.1
      (Submonoid.one_mem _)
  · exact (phaseThresholdLoop_resources (I := I) M (M-1)).2.2 _ hG
  · exact tensorGate_unitary (Qatlib.Concepts.Execution.WorkspaceCP.adjoint_unitary (qftMatrix_unitary (by omega)))
      (Submonoid.one_mem _)

/-- The forward word uses `M-1` oracle queries and `2*(M-1)+2` gates. -/
theorem sin_envelope_forward_word_counts (M : ℕ) (hM : 2 ≤ M) :
    adjointQueryCount (sinEnvelopeForwardWord (I := I) M hM) = M-1 ∧
      adjointGateCount (sinEnvelopeForwardWord (I := I) M hM) = 2*(M-1)+2 := by
  have ht := phaseThresholdLoop_resources (I := I) M (M-1)
  constructor
  · rw [sinEnvelopeForwardWord, adjointQueryCount_reverse, adjointQueryCount_map_stepToAdjoint]
    simp [sinEnvelopePhaseCircuit, queryCount_append, QueryCount, ht.1]
  · rw [sinEnvelopeForwardWord, adjointGateCount_reverse, adjointGateCount_map_stepToAdjoint]
    simp [sinEnvelopePhaseCircuit, gateCount_append, GateCount, ht.2.1]

/-- Lifting a unitary gate to the Boolean sectors preserves unitarity. -/
private theorem sin_envelope_lift_gate_unitary {D M : ℕ}
    {G : Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ}
    (hG : G ∈ Matrix.unitaryGroup _ ℂ) :
    sinEnvelopeLiftGate G ∈ Matrix.unitaryGroup _ ℂ :=
  (relabelGate_mem_unitaryGroup _ _).2
    (tensorGate_unitary (Submonoid.one_mem _) hG)

/-- The phase-controlled flag gate is unitary for positive `d`. -/
private theorem sin_envelope_flag_gate_unitary (D M : ℕ) (d : ℝ) (hd : 0 < d) :
    sinEnvelopeFlagGate (D := D) (M := M) d ∈ Matrix.unitaryGroup _ ℂ :=
  (relabelGate_mem_unitaryGroup _ _).2
    (tensorGate_unitary (blockDiag_unitary _ fun z =>
      (sin_envelope_flag_rotation_unitary_and_column d (sinEnvelopeDecode M z) hd).1)
      (Submonoid.one_mem _))

/-- For positive `d` and unitary preparation and oracle matrices, the HHL word is well formed
and evaluates to a unitary, with `2*(M-1)` queries and `4*(M-1)+6` gates. See
[HarrowHassidimLloyd2009]. -/
theorem sin_envelope_word_legality_and_counts (D M : ℕ) (hM : 2 ≤ M) (d : ℝ)
    (hd : 0 < d) (B U : Operator D)
    (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    WellFormedAdjointCircuit (sinEnvelopeHHLWord M hM d B) ∧
      evaluate (sinEnvelopeOracleLift (D := D) (M := M) U) (sinEnvelopeHHLWord M hM d B)
        ∈ Matrix.unitaryGroup _ ℂ ∧
      adjointQueryCount (sinEnvelopeHHLWord M hM d B) = 2*(M-1) ∧
      adjointGateCount (sinEnvelopeHHLWord M hM d B) = 4*(M-1)+6 := by
  have hf : WellFormedAdjointCircuit (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) :=
    wellFormedAdjointCircuit_stepToAdjoint_reverse _ (sin_envelope_phase_circuit_unitary M hM)
  have hp : sinEnvelopePrepMain (M := M) B ∈ Matrix.unitaryGroup _ ℂ :=
    (relabelGate_mem_unitaryGroup _ _).2
      (tensorGate_unitary (tensorGate_unitary (Submonoid.one_mem _) (Submonoid.one_mem _)) hB)
  have hw : WellFormedAdjointCircuit (sinEnvelopeHHLWord M hM d B) := by
    simp only [sinEnvelopeHHLWord, WellFormedAdjointCircuit.append_iff,
      WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact ⟨⟨⟨hf.adjointCircuit,
      sin_envelope_lift_gate_unitary (sin_envelope_flag_gate_unitary D M d hd)⟩, hf⟩,
      sin_envelope_lift_gate_unitary hp⟩
  have ho : sinEnvelopeOracleLift (D := D) (M := M) U ∈ Matrix.unitaryGroup _ ℂ :=
    tensorGate_unitary (Submonoid.one_mem _)
      (controlOracle_unitary (tensorGate_unitary (Submonoid.one_mem _) hU))
  refine ⟨hw, hw.evaluate_unitary ho, ?_, ?_⟩
  · simp [sinEnvelopeHHLWord, adjointQueryCount,
      (sin_envelope_forward_word_counts (I := Fin 3 × Fin D) M hM).1]
    omega
  · simp [sinEnvelopeHHLWord, adjointGateCount,
      (sin_envelope_forward_word_counts (I := Fin 3 × Fin D) M hM).2]
    omega

/-- On an oracle eigenstate, the phase circuit produces the corresponding sine-envelope kernel
and a false Boolean flag. -/
theorem sin_envelope_forward_eigenstate (M : ℕ) (hM : 2 ≤ M) (U : Matrix I I ℂ)
    (ψ : QState I) (φ : ℝ)
    (hψ : U *ᵥ ψ = Complex.exp (2*Real.pi*Complex.I*φ) • ψ) :
    Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle U))
        (sinEnvelopePhaseCircuit M hM)
        (TensorState (Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Ket false) ψ)) =
      phaseFlagEmbed M (TensorState (sinEnvelopeKernel M φ) ψ) := by
  have hi : TensorState (Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Ket false) ψ) =
      phaseFlagEmbed M (TensorState (Ket (⟨0, by omega⟩ : Fin M)) ψ) := by
    ext p
    rcases p with ⟨x,b,i⟩
    cases b <;> simp [TensorState, phaseFlagEmbed, Ket]
  have he (n : ℕ) : (Complex.exp (2*Real.pi*Complex.I*φ))^n =
      Complex.exp (2*Real.pi*Complex.I*((n : ℝ)*φ)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hp : (fun p : Fin M × I =>
      ApplyGate (U ^ min (M-1) p.1.val)
        (fun i => TensorState (sinEnvelopeState M) ψ (p.1,i)) p.2) =
      TensorState (fun τ : Fin M =>
        Complex.exp (2*Real.pi*Complex.I*((τ.val : ℝ)*φ)) * sinEnvelopeState M τ) ψ := by
    ext p
    rcases p with ⟨x,i⟩
    rw [Nat.min_eq_right (by omega)]
    change (U^x.val *ᵥ ((sinEnvelopeState M x) • ψ)) i = _
    rw [Matrix.mulVec_smul, mulVec_pow_of_eigen hψ, he]
    simp [TensorState, Pi.smul_apply, smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]
  have hprep : ApplyGate (sinEnvelopePrep M hM) (Ket (⟨0, by omega⟩ : Fin M)) =
      sinEnvelopeState M := (sin_envelope_state_normalized_and_prep M hM).2.2
  rw [sinEnvelopePhaseCircuit, run_append, run_append, hi]
  simp only [Run]
  rw [phaseFlagEmbed_phaseGate, applyGate_tensorGate, applyGate_one,
    hprep,
    phaseThresholdLoop_action, hp, phaseFlagEmbed_phaseGate,
    applyGate_tensorGate, applyGate_one]
  rfl

/-- The corrected actual well-state amplitude is zero outside flag one and otherwise equals the
stated spectrally filtered kernel sum. -/
private theorem sin_envelope_actual_well_apply {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (p : Fin M × (Fin 3 × Fin D)) :
    sinEnvelopeActualWellStateCorrected M hM eig V B j d p =
      if p.2.1 = 1 then
        (V *ᵥ (fun i => (Vᴴ *ᵥ (B *ᵥ Ket j)) i * sinEnvelopeKernel M (eig i) p.1 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M p.1) : ℂ))) p.2.2 else 0 := by
  by_cases hp : p.2.1 = 1
  · simp [sinEnvelopeActualWellStateCorrected, TensorState, Ket, Finset.sum_apply,
      Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, hp]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp [sinEnvelopeActualWellStateCorrected, TensorState, Ket, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, hp]

/-- The squared norm of the corrected actual well state equals the spectrally weighted sum of
kernel-weighted squared success-filter values. -/
theorem sin_envelope_actual_well_mass_formula {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ p, ‖sinEnvelopeActualWellStateCorrected M hM eig V B j d p‖^2) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ∑ z, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 := by
  rw [Fintype.sum_prod_type]
  have hs (z : Fin M) :
      (∑ q : Fin 3 × Fin D,
        ‖sinEnvelopeActualWellStateCorrected M hM eig V B j d (z,q)‖^2) =
      ∑ k : Fin D, ‖(V *ᵥ (fun i => (Vᴴ *ᵥ (B *ᵥ Ket j)) i * sinEnvelopeKernel M (eig i) z *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) : ℂ))) k‖^2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [sin_envelope_actual_well_apply]
    rw [Fin.sum_univ_succ (n := 2), Fin.sum_univ_succ (n := 1), Fin.sum_univ_succ (n := 0)]
    simp
  rw [Finset.sum_congr rfl (fun z _ => hs z)]
  simp only [← Complex.normSq_eq_norm_sq]
  simp_rw [sum_normSq_mulVec_of_mem_unitaryGroup hV]
  simp only [Complex.normSq_eq_norm_sq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  ring

/-- The amplitude-amplification query expression is bounded by substituting the stated upper
bound on the iteration count. -/
theorem sin_envelope_aa_query_budget (M : ℕ) (hM : 2 ≤ M) (d : ℝ) (k : ℕ)
    (hk : k ≤ Nat.ceil (1/(5*d))+1) :
    (2*(k : ℝ)+1)*(2*((M : ℝ)-1))+(k : ℝ) ≤
      (2*((Nat.ceil (1/(5*d)) : ℝ)+1)+1)*(2*(M : ℝ))+
        ((Nat.ceil (1/(5*d)) : ℝ)+1) := by
  have hkr : (k : ℝ) ≤ (Nat.ceil (1/(5*d)) : ℝ)+1 := by exact_mod_cast hk
  have hmr : (2:ℝ) ≤ M := by exact_mod_cast hM
  have hc : (0:ℝ) ≤ Nat.ceil (1/(5*d)) := Nat.cast_nonneg _
  have hp := mul_le_mul_of_nonneg_right (show 2*(k : ℝ)+1 ≤
    2*((Nat.ceil (1/(5*d)) : ℝ)+1)+1 by linarith)
    (show 0 ≤ 2*((M : ℝ)-1) by linarith)
  have hq := mul_le_mul_of_nonneg_left (show 2*((M : ℝ)-1) ≤ 2*(M : ℝ) by linarith)
    (show 0 ≤ 2*((Nat.ceil (1/(5*d)) : ℝ)+1)+1 by linarith)
  linarith

/-- For `x ∈ [0, 1/4]` and `y ∈ [-1/2, 1/2]`, absolute difference is at most three times
circular phase distance. -/
private theorem signed_phase_distance (x y : ℝ) (hx : 0 ≤ x) (hx' : x ≤ 1/4)
    (hy : -1/2 ≤ y) (hy' : y ≤ 1/2) :
    |x-y| ≤ 3*phaseDistance x y := by
  let n : ℤ := ⌊x-y+1/2⌋
  have hn₀ : 0 ≤ n := Int.floor_nonneg.mpr (by linarith only [hx,hy'])
  have hn₁ : n < 2 := Int.floor_lt.mpr (by norm_num; linarith only [hx',hy])
  have hh := Int.floor_le (x-y+1/2)
  have he : n = 0 ∨ n = 1 := by omega
  unfold phaseDistance
  change |x-y| ≤ 3*|x-y-(n:ℝ)|
  rcases he with h|h
  · rw [h]; norm_num only [Int.cast_zero,sub_zero]
    nlinarith only [abs_nonneg (x-y)]
  · have hlo : 1/2 ≤ x-y := by dsimp [n] at h; rw [h] at hh; norm_num at hh; linarith only [hh]
    rw [h]; norm_num only [Int.cast_one]
    rw [abs_of_nonneg (by linarith only [hlo]),abs_of_nonpos (by linarith only [hx',hy])]
    linarith only [hx',hy]

/-- For `M ≥ 2`, the signed decoded phase belongs to `[-1/2, 1/2]`. -/
private theorem decode_bounded (M : ℕ) (z : Fin M) (hM : 2 ≤ M) :
    -1/2 ≤ sinEnvelopeDecode M z ∧ sinEnvelopeDecode M z ≤ 1/2 := by
  have hm0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hz0 : (0:ℝ) ≤ z.val := by positivity
  have hz1 : (z.val:ℝ) < M := by exact_mod_cast z.isLt
  unfold sinEnvelopeDecode
  split_ifs with h
  · have hh : 2*(z.val:ℝ) ≤ M := by exact_mod_cast h
    constructor
    · have hz := div_nonneg hz0 hm0.le; linarith only [hz]
    · apply (div_le_iff₀ hm0).mpr; linarith only [hh]
  · have hh : (M:ℝ) < 2*(z.val:ℝ) := by exact_mod_cast (show M < 2*z.val by omega)
    have hzlo : (1/2:ℝ) ≤ (z.val:ℝ)/(M:ℝ) := (le_div_iff₀ hm0).mpr (by linarith only [hh])
    have hzup : (z.val:ℝ)/(M:ℝ) < 1 := (div_lt_one hm0).mpr hz1
    constructor <;> linarith only [hzlo,hzup]

/-- Subtracting one from the second phase preserves circular phase distance. -/
private theorem phaseDistance_sub_one_right (x y : ℝ) : phaseDistance x (y-1) = phaseDistance x y := by
  unfold phaseDistance
  have he : x-(y-1)+1/2 = (x-y+1/2)+(1:ℤ) := by push_cast; ring
  rw [he,Int.floor_add_intCast]
  push_cast
  congr 1
  ring

/-- Signed decoding preserves circular distance to the corresponding phase grid point. -/
private theorem decode_distance (M : ℕ) (φ : ℝ) (z : Fin M) :
    phaseDistance φ (sinEnvelopeDecode M z) = phaseDistance φ ((z.val:ℝ)/(M:ℝ)) := by
  unfold sinEnvelopeDecode
  split_ifs
  · rfl
  · exact phaseDistance_sub_one_right _ _

/-- For positive `d` and `η`, phase in `[0, 1/4]`, and `M ≥ 21/(d*η)`, the kernel-weighted
squared error of the flag vector is at most `η^2`. -/
theorem sin_envelope_decoded_flag_error (M : ℕ) (hM : 2 ≤ M) (φ d η : ℝ)
    (hφ : 0 ≤ φ) (hφ' : φ ≤ 1/4) (hd : 0 < d) (hη : 0 < η)
    (hbudget : 21/(d*η) ≤ (M:ℝ)) :
    (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      ∑ s : Fin 3, ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
        sinEnvelopeHVector d φ s‖^2) ≤ η^2 := by
  have hm0 : (0:ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  let e (z : Fin M) := ∑ s : Fin 3,
    ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s-sinEnvelopeHVector d φ s‖^2
  let r (z : Fin M) := phaseDistance φ ((z.val:ℝ)/(M:ℝ))
  have he (z : Fin M) : e z ≤ (9/d^2)*(r z)^2 := by
    have hh := sin_envelope_h_lipschitz d (sinEnvelopeDecode M z) φ hd
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr hh
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun _ _ => sq_nonneg _)),mul_pow,sq_abs] at hs
    have hc := signed_phase_distance φ (sinEnvelopeDecode M z) hφ hφ'
      (decode_bounded M z hM).1 (decode_bounded M z hM).2
    rw [decode_distance] at hc
    have hcc := pow_le_pow_left₀ (abs_nonneg _) hc 2
    rw [sq_abs,mul_pow] at hcc
    have hmul := mul_le_mul_of_nonneg_left hcc (show 0 ≤ (1/d)^2 by positivity)
    change e z ≤ _
    have heq : (9/d^2)*(r z)^2 = (1/d)^2*(9*(r z)^2) := by ring
    rw [heq]
    have hab : (sinEnvelopeDecode M z-φ)^2 = (φ-sinEnvelopeDecode M z)^2 := by ring
    rw [hab] at hs
    exact hs.trans (by simpa only [r,show (3:ℝ)^2=9 by norm_num] using! hmul)
  have hc := sin_envelope_kernel_second_moment M φ hM
  have hconst : 4*Real.pi^2+40*Real.pi^4/3 ≤ 196*Real.pi^2 := by
    have hp : Real.pi^2 ≤ 10 := by nlinarith only [Real.pi_lt_d2,Real.pi_pos]
    have hh := mul_le_mul_of_nonneg_right hp (sq_nonneg Real.pi)
    nlinarith only [hh,sq_nonneg Real.pi]
  have hsum : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*(r z)^2) ≤
      49/(M:ℝ)^2 := by
    have heq : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*(2*Real.pi*(M:ℝ)*r z)^2) =
        (4*Real.pi^2*(M:ℝ)^2)*(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*(r z)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    change (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*(2*Real.pi*(M:ℝ)*r z)^2) ≤ _ at hc
    rw [heq] at hc
    have hh := hc.trans hconst
    have hh' : (M:ℝ)^2*(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*(r z)^2) ≤ 49 := by
      nlinarith only [hh,Real.pi_pos,sq_pos_of_pos Real.pi_pos]
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith only [hh']
  calc
    _ ≤ ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*((9/d^2)*(r z)^2) := by
      exact Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (he z) (sq_nonneg _))
    _ = (9/d^2)*(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*(r z)^2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ ≤ (9/d^2)*(49/(M:ℝ)^2) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ η^2 := by
      have hb := (div_le_iff₀ (by positivity : 0 < d*η)).mp hbudget
      have hs := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 21) hb 2
      have heq : (9/d^2)*(49/(M:ℝ)^2) = 441/(d^2*(M:ℝ)^2) := by ring
      rw [heq]
      apply (div_le_iff₀ (by positivity : (0:ℝ) < d^2*(M:ℝ)^2)).mpr
      nlinarith only [hs]

/-- The Euclidean norm of a finite state is the square root of its total squared amplitude. -/
private theorem se_normVec_sqrt {I : Type} [Fintype I] [DecidableEq I] (v : QState I) :
    ‖toEuclidean_fromVec v‖ = (∑ p, ‖v p‖ ^ 2).sqrt := by
  rw [← Real.sqrt_sq (norm_nonneg _), norm_toEuclidean_fromVec_sq]

/-- If the state error is smaller than the ideal norm, the error between normalized states is at
most twice the error divided by the ideal norm. -/
private theorem se_conditional_output_error {I : Type} [Fintype I] [DecidableEq I]
    (a i : QState I)
    (hx : (∑ p, ‖(a - i) p‖ ^ 2).sqrt < (∑ p, ‖i p‖ ^ 2).sqrt) :
    ‖toEuclidean_fromVec (sinEnvelopeConditionalOutput a -
        sinEnvelopeConditionalOutput i)‖ ≤
      2 * (∑ p, ‖(a - i) p‖ ^ 2).sqrt / (∑ p, ‖i p‖ ^ 2).sqrt := by
  have hgap : ‖toEuclidean_fromVec a - toEuclidean_fromVec i‖ <
      ‖toEuclidean_fromVec i‖ := by
    change ‖toEuclidean_fromVec (a - i)‖ < ‖toEuclidean_fromVec i‖
    simpa only [se_normVec_sqrt] using! hx
  have herr := (Qatlib.Concepts.BlockEncoding.Postselection.normalize_error_of_gap (le_refl _) hgap).2
  have hnormalize (v : QState I) :
      toEuclidean_fromVec (sinEnvelopeConditionalOutput v) =
        NormedSpace.normalize (toEuclidean_fromVec v) := by
    change (Real.sqrt (∑ p, ‖v p‖ ^ 2))⁻¹ • toEuclidean_fromVec v =
      ‖toEuclidean_fromVec v‖⁻¹ • toEuclidean_fromVec v
    rw [se_normVec_sqrt]
  change ‖toEuclidean_fromVec (sinEnvelopeConditionalOutput a) -
    toEuclidean_fromVec (sinEnvelopeConditionalOutput i)‖ ≤ _
  rw [hnormalize a, hnormalize i]
  change ‖NormedSpace.normalize (toEuclidean_fromVec a) -
    NormedSpace.normalize (toEuclidean_fromVec i)‖ ≤
      2 * ‖toEuclidean_fromVec (a - i)‖ / ‖toEuclidean_fromVec i‖ at herr
  simpa only [se_normVec_sqrt] using! herr

/-- Circular phase distance equals absolute difference when that difference is at most `1/2`. -/
private theorem se_phase_dist_eq_abs_of_le_half {x y : ℝ} (h : |x - y| ≤ 1/2) :
    phaseDistance x y = |x - y| := by
  have hlo : (0:ℝ) ≤ x - y + 1/2 := by
    have := abs_le.mp h |>.1
    linarith
  rcases lt_or_ge (x - y + 1/2) 1 with hlt | hge
  · have hf : ⌊x - y + 1/2⌋ = 0 := by
      rw [Int.floor_eq_iff]
      constructor <;> linarith
    unfold phaseDistance
    rw [hf]
    push_cast
    simp
  · have heq : x - y + 1/2 = 1 := le_antisymm (by
        have := abs_le.mp h |>.2
        linarith) hge
    have hf : ⌊x - y + 1/2⌋ = 1 := by rw [heq]; norm_num
    have hx : x - y = 1/2 := by linarith
    unfold phaseDistance
    rw [hf]
    push_cast
    rw [hx]
    norm_num

/-- When the absolute decoded phase difference is at most `1/2`, its square equals the squared
circular distance to the grid label. -/
private theorem se_near_label_eq (M : ℕ) (φ : ℝ) (z : Fin M)
    (h : |φ - sinEnvelopeDecode M z| ≤ 1/2) :
    (φ - sinEnvelopeDecode M z)^2 = phaseDistance φ ((z.val:ℝ)/(M:ℝ))^2 := by
  rw [← decode_distance, se_phase_dist_eq_abs_of_le_half h, sq_abs]

/-- If a decoded phase differs from a phase in `[0, 1/4]` by more than `1/2`, the corresponding
circular grid distance is at least `1/4`. -/
private theorem se_wrap_r_ge (M : ℕ) (φ : ℝ) (z : Fin M) (hM : 2 ≤ M)
    (hφ : 0 ≤ φ) (hφ' : φ ≤ 1/4)
    (h : 1/2 < |φ - sinEnvelopeDecode M z|) :
    1/4 ≤ phaseDistance φ ((z.val:ℝ)/(M:ℝ)) := by
  have hd := decode_bounded M z hM
  have h34 : |φ - sinEnvelopeDecode M z| ≤ 3/4 := by
    apply abs_le.mpr
    constructor <;> linarith
  have hkey : 1/4 ≤ phaseDistance φ (sinEnvelopeDecode M z) := by
    unfold phaseDistance
    by_cases hneg : φ - sinEnvelopeDecode M z < 0
    · rw [abs_of_neg hneg] at h h34
      have hf : ⌊φ - sinEnvelopeDecode M z + 1/2⌋ = -1 := by
        rw [Int.floor_eq_iff]
        constructor <;> linarith
      rw [hf]
      push_cast
      rw [abs_of_nonneg (by linarith)]
      linarith
    · have hge : 0 ≤ φ - sinEnvelopeDecode M z := le_of_not_gt hneg
      rw [abs_of_nonneg hge] at h h34
      have hf : ⌊φ - sinEnvelopeDecode M z + 1/2⌋ = 1 := by
        rw [Int.floor_eq_iff]
        constructor <;> linarith
      rw [hf]
      push_cast
      rw [abs_of_nonpos (by linarith)]
      linarith
  rw [← decode_distance]
  exact hkey

/-- For `M ≥ 4` and phase in `[0, 1/4]`, the decoded phase's kernel-weighted second moment is at
most `(1 + 10*π^2/3)/M^2 + 1440/M^3`. -/
private theorem se_kernel_e2 (M : ℕ) (hM : 2 ≤ M) (φ d : ℝ) (hd : 0 < d)
    (hφ : 0 ≤ φ) (hφ' : φ ≤ 1/4) (hM4 : 4 ≤ M) :
    ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 * (φ - sinEnvelopeDecode M z)^2 ≤
      (1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3 := by
  classical
  have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set s : Finset (Fin M) := Finset.univ.filter
    (fun z : Fin M => |φ - sinEnvelopeDecode M z| ≤ 1/2) with hsdef
  rw [← Finset.sum_add_sum_compl s]
  have hnear : (∑ z ∈ s, ‖sinEnvelopeKernel M φ z‖^2 *
      (φ - sinEnvelopeDecode M z)^2) ≤
      (1 + 10*Real.pi^2/3)/(M:ℝ)^2 := by
    have hterm : ∀ z ∈ s, ‖sinEnvelopeKernel M φ z‖^2 * (φ - sinEnvelopeDecode M z)^2 =
        ‖sinEnvelopeKernel M φ z‖^2 * phaseDistance φ ((z.val:ℝ)/(M:ℝ))^2 := by
      intro z hz
      rw [se_near_label_eq M φ z ((Finset.mem_filter.mp hz).2)]
    rw [Finset.sum_congr rfl (fun z hz => hterm z hz)]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
      (fun z _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))) ?_
    have hsm := sin_envelope_kernel_second_moment M φ hM
    have heq : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (2*Real.pi*(M:ℝ)*phaseDistance φ ((z.val:ℝ)/(M:ℝ)))^2) =
        (4*Real.pi^2*(M:ℝ)^2)*(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          phaseDistance φ ((z.val:ℝ)/(M:ℝ))^2) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => by ring
    rw [heq] at hsm
    refine (le_div_iff₀ (by positivity : (0:ℝ) < (M:ℝ)^2)).mpr ?_
    refine le_of_mul_le_mul_left ?_ (by positivity : (0:ℝ) < 4*Real.pi^2)
    calc 4*Real.pi^2*((∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          phaseDistance φ ((z.val:ℝ)/(M:ℝ))^2) * (M:ℝ)^2) =
          (4*Real.pi^2*(M:ℝ)^2)*(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            phaseDistance φ ((z.val:ℝ)/(M:ℝ))^2) := by ring
      _ ≤ 4*Real.pi^2+40*Real.pi^4/3 := hsm
      _ = 4*Real.pi^2*(1 + 10*Real.pi^2/3) := by ring
  have hwrap : (∑ z ∈ sᶜ, ‖sinEnvelopeKernel M φ z‖^2 *
      (φ - sinEnvelopeDecode M z)^2) ≤ 1440/(M:ℝ)^3 := by
    have hper : ∀ z ∈ sᶜ, ‖sinEnvelopeKernel M φ z‖^2 *
        (φ - sinEnvelopeDecode M z)^2 ≤ 1440/(M:ℝ)^4 := by
      intro z hz
      have hgt : 1/2 < |φ - sinEnvelopeDecode M z| := by
        refine not_le.mp ?_
        intro hle
        exact (Finset.mem_compl.mp hz) (Finset.mem_filter.mpr ⟨Finset.mem_univ z, hle⟩)
      have hr := se_wrap_r_ge M φ z hM hφ hφ' hgt
      have hfar : 1/(M:ℝ) ≤ phaseDistance φ ((z.val:ℝ)/(M:ℝ)) := by
        refine le_trans ?_ hr
        rw [div_le_div_iff₀ hMpos (by norm_num : (0:ℝ) < 4)]
        norm_num
        exact_mod_cast hM4
      have htail := sin_envelope_kernel_far_label_tail M φ z hM hfar
      have hd2 := decode_bounded M z hM
      have hq : (φ - sinEnvelopeDecode M z)^2 ≤ 9/16 := by
        have h34 : |φ - sinEnvelopeDecode M z| ≤ 3/4 := by
          apply abs_le.mpr
          constructor <;> linarith
        have hac := sq_abs (φ - sinEnvelopeDecode M z)
        nlinarith [h34]
      have hr4 : (1/4)^4 ≤ phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4 :=
        pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/4) hr 4
      have hfracnn : (0:ℝ) ≤ 10/((M:ℝ)^4 * phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4) :=
        div_nonneg (by norm_num)
          (mul_nonneg (pow_nonneg (Nat.cast_nonneg M) 4)
            (pow_nonneg (abs_nonneg _) 4))
      calc ‖sinEnvelopeKernel M φ z‖^2 * (φ - sinEnvelopeDecode M z)^2 ≤
          (10/((M:ℝ)^4 * phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4)) * (φ - sinEnvelopeDecode M z)^2 :=
            mul_le_mul_of_nonneg_right htail (sq_nonneg _)
        _ ≤ (10/((M:ℝ)^4 * phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4)) * (9/16) :=
            mul_le_mul_of_nonneg_left hq hfracnn
        _ ≤ (10/((M:ℝ)^4 * (1/4)^4)) * (9/16) := by
            refine mul_le_mul_of_nonneg_right ?_ (by norm_num : (0:ℝ) ≤ 9/16)
            apply (div_le_div_iff₀ (by positivity : (0:ℝ) <
              (M:ℝ)^4 * phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4)
              (by positivity : (0:ℝ) < (M:ℝ)^4 * (1/4)^4)).mpr
            calc 10 * ((M:ℝ)^4 * (1/4)^4) = (M:ℝ)^4 * ((1/4)^4 * 10) := by ring
              _ ≤ (M:ℝ)^4 * (phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4 * 10) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hr4 (by norm_num)) (by positivity)
              _ = 10 * ((M:ℝ)^4 * phaseDistance φ ((z.val:ℝ)/(M:ℝ))^4) := by ring
        _ = 1440/(M:ℝ)^4 := by
            have hMne : ((M:ℝ)^4) ≠ 0 := pow_ne_zero 4 hMpos.ne'
            field_simp
            norm_num
    have hcard : ∑ z ∈ sᶜ, (1440/(M:ℝ)^4) ≤ ∑ z : Fin M, (1440/(M:ℝ)^4) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ sᶜ)
        (fun z _ _ => div_nonneg (by norm_num)
          (pow_nonneg (Nat.cast_nonneg M) 4))
    have huniv : ∑ z : Fin M, (1440/(M:ℝ)^4) = 1440/(M:ℝ)^3 := by
      have hmul : ∑ z : Fin M, (1440/(M:ℝ)^4) = (M:ℝ) * (1440/(M:ℝ)^4) := by simp
      rw [hmul]
      field_simp
    calc (∑ z ∈ sᶜ, ‖sinEnvelopeKernel M φ z‖^2 * (φ - sinEnvelopeDecode M z)^2) ≤
        ∑ z ∈ sᶜ, (1440/(M:ℝ)^4) := Finset.sum_le_sum hper
      _ ≤ ∑ z : Fin M, (1440/(M:ℝ)^4) := hcard
      _ = 1440/(M:ℝ)^3 := huniv
  linarith

/-- For nonnegative weights summing to one, the square of the weighted mean is bounded by the
weighted second moment. -/
private theorem se_weighted_variance {ι : Type*} [Fintype ι] (w f : ι → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1) :
    (∑ i, w i * f i)^2 ≤ ∑ i, w i * f i^2 := by
  have hnn : 0 ≤ ∑ i, w i * (f i - ∑ j, w j * f j)^2 :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (sq_nonneg _))
  have hexp : ∀ i, w i * (f i - ∑ j, w j * f j)^2 =
      w i * f i^2 - 2 * (w i * f i) * (∑ j, w j * f j) +
        w i * (∑ j, w j * f j)^2 := by
    intro i; ring
  rw [Finset.sum_congr rfl (fun i _ => hexp i), Finset.sum_add_distrib,
    Finset.sum_sub_distrib] at hnn
  have h1 : ∑ i, 2 * (w i * f i) * (∑ j, w j * f j) =
      2 * (∑ i, w i * f i) * (∑ i, w i * f i) := by
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have h2 : ∑ i, w i * (∑ j, w j * f j)^2 =
      (∑ i, w i) * (∑ i, w i * f i)^2 := by
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [h1, h2, hsum] at hnn
  nlinarith [hnn]

/-- The square of a two-term real dot product is bounded by the product of the two squared
Euclidean norms. -/
private theorem se_two_dim_cs (a b x y : ℝ) : (a*x + b*y)^2 ≤ (a^2 + b^2) * (x^2 + y^2) := by
  nlinarith [sq_nonneg (a*y - b*x)]

/-- The combined flag mass is `1/4` for `d > 0` and `x ≤ 2*d`. -/
private theorem se_flag_mass_low (d x : ℝ) (hd : 0 < d) (hx : x ≤ 2*d) :
    sinEnvelopeFlagMass d x = 1/4 := by
  by_cases he : x = 2*d
  · rw [he]
    unfold sinEnvelopeFlagMass
    rw [(sin_envelope_filter_branch_values d hd).1,
      (sin_envelope_filter_branch_values d hd).2.1]
    norm_num
  · have hw : ¬ 2*d ≤ x := by intro h; exact he (le_antisymm hx h)
    unfold sinEnvelopeFlagMass sinEnvelopeFilterF sinEnvelopeFilterG
    simp only [if_neg hw]
    by_cases hl : d ≤ x
    · have hsin := Real.sin_sq_add_cos_sq (Real.pi/2*(x-d)/d)
      simp only [if_pos hl]
      nlinarith [hsin]
    · simp only [if_neg hl]
      norm_num

set_option maxHeartbeats 2000000 in

/-- The kernel-averaged flag mass differs from its ideal value by at most `47/(d*M)` times that
value under the stated phase and resolution hypotheses. -/
private theorem se_kernel_mass_stability (M : ℕ) (hM : 2 ≤ M) (φ d η : ℝ) (hd : 0 < d)
    (hφ : 0 ≤ φ) (hφ' : φ ≤ 1/4) (hη : 0 < η) (hη1 : η ≤ 1)
    (hbudget : 21 / (d * η) ≤ (M : ℝ)) :
    |(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        sinEnvelopeFlagMass d (sinEnvelopeDecode M z)) - sinEnvelopeFlagMass d φ| ≤
      (47 / (d * (M : ℝ))) * sinEnvelopeFlagMass d φ := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hDM : 21 ≤ d * (M:ℝ) := by
    have h1 : 21 / (d * η) * (d * η) ≤ (M:ℝ) * (d * η) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    rw [div_mul_cancel₀ _ (mul_pos hd hη).ne'] at h1
    nlinarith [h1, hη1, mul_nonneg hMpos.le hd.le]
  by_cases hd14 : 1/4 ≤ d
  · have hmσ : ∀ z : Fin M, sinEnvelopeFlagMass d (sinEnvelopeDecode M z) = 1/4 := by
      intro z
      apply se_flag_mass_low d _ hd
      have := (decode_bounded M z hM).2
      linarith
    have hmφ : sinEnvelopeFlagMass d φ = 1/4 :=
      se_flag_mass_low d φ hd (by linarith)
    rw [Finset.sum_congr rfl (fun z _ => by rw [hmσ z]), hmφ,
      ← Finset.sum_mul, (sin_envelope_kernel_normalized M φ hM), one_mul, sub_self]
    simp
    positivity
  · have hdlt : d < 1/4 := lt_of_not_ge hd14
    have hM84 : (84:ℝ) < M := by
      have h2 : 4 * (M * d) < M := by
        nlinarith [mul_lt_mul_of_pos_left hdlt hMpos]
      nlinarith [hDM, h2]
    have hw1 : ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 = 1 :=
      sin_envelope_kernel_normalized M φ hM
    have hwnn : ∀ z : Fin M, 0 ≤ ‖sinEnvelopeKernel M φ z‖^2 := fun z => sq_nonneg _
    have hmass : 0 ≤ sinEnvelopeFlagMass d φ :=
      add_nonneg (sq_nonneg _) (sq_nonneg _)
    have hE2 := se_kernel_e2 M hM φ d hd hφ hφ' (by
      have h4 : (4:ℝ) < M := by linarith
      have h4' : (4:ℕ) < M := by exact_mod_cast h4
      omega)
    have hpi : Real.pi^2 ≤ 10 := by nlinarith only [Real.pi_lt_d2, Real.pi_pos]
    have hE2nn : (0:ℝ) ≤ (1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3 :=
      add_nonneg (div_nonneg (by positivity) (pow_nonneg hMpos.le 2))
        (div_nonneg (by norm_num) (pow_nonneg hMpos.le 3))
    have hXeq : 2*Real.pi^2*(1/(2*d))^2 * (d*(M:ℝ))^2 = (Real.pi^2/2) * (M:ℝ)^2 := by
      field_simp
    have hX : 2*Real.pi^2*(1/(2*d))^2 * (d*(M:ℝ))^2 ≤ 5 * (M:ℝ)^2 := by
      rw [hXeq]
      exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
    have hnum : ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) * (M:ℝ)^2 ≤ 1081/21 := by
      have heq2 : (1440/(M:ℝ)^3) * (M:ℝ)^2 = 1440/(M:ℝ) := by
        field_simp
      have h1 : 1 + 10*Real.pi^2/3 ≤ 103/3 := by nlinarith [hpi]
      have h2 : 1440/(M:ℝ) ≤ 120/7 := by
        apply (div_le_iff₀ hMpos).mpr
        calc (1440:ℝ) = (120/7) * 84 := by norm_num
          _ ≤ (120/7) * M := mul_le_mul_of_nonneg_left (by linarith)
            (by norm_num : (0:ℝ) ≤ 120/7)
      rw [add_mul, div_mul_cancel₀ _ (pow_ne_zero 2 hMpos.ne'), heq2]
      linarith
    have hper : ∀ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
         (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2) ≤
        ‖sinEnvelopeKernel M φ z‖^2 *
        (2*Real.pi^2*(1/(2*d))^2 * (φ - sinEnvelopeDecode M z)^2 *
          sinEnvelopeFlagMass d φ) := by
      intro z
      have hst := sin_envelope_filter_stability d φ (sinEnvelopeDecode M z) hd hφ hφ'
        (decode_bounded M z hM).1 (decode_bounded M z hM).2
      have hsymm :
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
          (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2 =
          (sinEnvelopeFilterF d φ - sinEnvelopeFilterF d (sinEnvelopeDecode M z))^2 +
          (sinEnvelopeFilterG d φ - sinEnvelopeFilterG d (sinEnvelopeDecode M z))^2 := by
        have h1 : sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ =
            -(sinEnvelopeFilterF d φ - sinEnvelopeFilterF d (sinEnvelopeDecode M z)) := by
          ring
        have h2 : sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ =
            -(sinEnvelopeFilterG d φ - sinEnvelopeFilterG d (sinEnvelopeDecode M z)) := by
          ring
        rw [h1, h2]
        ring
      rw [hsymm]
      exact mul_le_mul_of_nonneg_left hst (hwnn z)
    have hsum : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
         (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) ≤
        (2*Real.pi^2*(1/(2*d))^2) * sinEnvelopeFlagMass d φ *
        ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) := by
      calc (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
             (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) ≤
          ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            (2*Real.pi^2*(1/(2*d))^2 * (φ - sinEnvelopeDecode M z)^2 *
              sinEnvelopeFlagMass d φ) := Finset.sum_le_sum (fun z _ => hper z)
        _ = (2*Real.pi^2*(1/(2*d))^2) * sinEnvelopeFlagMass d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (φ - sinEnvelopeDecode M z)^2) := by
            have hterm : ∀ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
                (2*Real.pi^2*(1/(2*d))^2 * (φ - sinEnvelopeDecode M z)^2 *
                  sinEnvelopeFlagMass d φ) =
                (2*Real.pi^2*(1/(2*d))^2 * sinEnvelopeFlagMass d φ) *
                (‖sinEnvelopeKernel M φ z‖^2 * (φ - sinEnvelopeDecode M z)^2) := by
              intro z; ring
            rw [Finset.sum_congr rfl (fun z _ => hterm z), ← Finset.mul_sum]
        _ ≤ (2*Real.pi^2*(1/(2*d))^2) * sinEnvelopeFlagMass d φ *
            ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) :=
            mul_le_mul_of_nonneg_left hE2 (by positivity)
    have hQ : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
         (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) *
        (d*(M:ℝ))^2 ≤ 258 * sinEnvelopeFlagMass d φ := by
      have hmid : (2*Real.pi^2*(1/(2*d))^2 * sinEnvelopeFlagMass d φ *
          ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3)) * (d*(M:ℝ))^2 ≤
          (5*(M:ℝ)^2) * sinEnvelopeFlagMass d φ *
          ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) := by
        have hrw : (2*Real.pi^2*(1/(2*d))^2 * sinEnvelopeFlagMass d φ *
            ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3)) * (d*(M:ℝ))^2 =
            (2*Real.pi^2*(1/(2*d))^2 * (d*(M:ℝ))^2) * sinEnvelopeFlagMass d φ *
            ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) := by ring
        rw [hrw]
        calc (2*Real.pi^2*(1/(2*d))^2 * (d*(M:ℝ))^2) * sinEnvelopeFlagMass d φ *
            ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) =
            ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) *
            (2*Real.pi^2*(1/(2*d))^2 * (d*(M:ℝ))^2 * sinEnvelopeFlagMass d φ) := by ring
          _ ≤ ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) *
            (5*(M:ℝ)^2 * sinEnvelopeFlagMass d φ) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hX hmass) hE2nn
          _ = (5*(M:ℝ)^2) * sinEnvelopeFlagMass d φ *
            ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) := by ring
      calc (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
             (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) *
            (d*(M:ℝ))^2 ≤
          (2*Real.pi^2*(1/(2*d))^2 * sinEnvelopeFlagMass d φ *
            ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3)) * (d*(M:ℝ))^2 :=
            mul_le_mul_of_nonneg_right hsum (sq_nonneg _)
        _ ≤ (5*(M:ℝ)^2) * sinEnvelopeFlagMass d φ *
            ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) := hmid
        _ = 5 * sinEnvelopeFlagMass d φ *
            (((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) * (M:ℝ)^2) := by ring
        _ ≤ 5 * sinEnvelopeFlagMass d φ * (1081/21) :=
            mul_le_mul_of_nonneg_left hnum (by positivity)
        _ ≤ 258 * sinEnvelopeFlagMass d φ := by
            nlinarith [hmass]
    have hmean : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        sinEnvelopeFlagMass d (sinEnvelopeDecode M z)) - sinEnvelopeFlagMass d φ =
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) +
        2*(sinEnvelopeFilterF d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
          sinEnvelopeFilterG d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))) := by
      have hper2 : ∀ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          sinEnvelopeFlagMass d (sinEnvelopeDecode M z) -
          ‖sinEnvelopeKernel M φ z‖^2 * sinEnvelopeFlagMass d φ =
          ‖sinEnvelopeKernel M φ z‖^2 *
            ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
             (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2) +
          2*‖sinEnvelopeKernel M φ z‖^2 *
            (sinEnvelopeFilterF d φ *
              (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ) +
             sinEnvelopeFilterG d φ *
              (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)) := by
        intro z
        unfold sinEnvelopeFlagMass
        ring
      have hmassum : sinEnvelopeFlagMass d φ = ∑ z : Fin M,
          ‖sinEnvelopeKernel M φ z‖^2 * sinEnvelopeFlagMass d φ := by
        calc sinEnvelopeFlagMass d φ =
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2) * sinEnvelopeFlagMass d φ := by
              rw [hw1, one_mul]
          _ = ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 * sinEnvelopeFlagMass d φ :=
              Finset.sum_mul Finset.univ (fun z : Fin M => ‖sinEnvelopeKernel M φ z‖^2) _
      have hsplit5 : (∑ z : Fin M, 2*‖sinEnvelopeKernel M φ z‖^2 *
            (sinEnvelopeFilterF d φ *
              (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ) +
             sinEnvelopeFilterG d φ *
              (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))) =
          2*(sinEnvelopeFilterF d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
          sinEnvelopeFilterG d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))) := by
        calc (∑ z : Fin M, 2*‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterF d φ *
                (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ) +
               sinEnvelopeFilterG d φ *
                (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))) =
            ∑ z : Fin M, (2*sinEnvelopeFilterF d φ*(‖sinEnvelopeKernel M φ z‖^2 *
                (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
              2*sinEnvelopeFilterG d φ*(‖sinEnvelopeKernel M φ z‖^2 *
                (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))) :=
              Finset.sum_congr rfl (fun z _ => by ring)
          _ = (∑ z : Fin M, 2*sinEnvelopeFilterF d φ*(‖sinEnvelopeKernel M φ z‖^2 *
                (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ))) +
              (∑ z : Fin M, 2*sinEnvelopeFilterG d φ*(‖sinEnvelopeKernel M φ z‖^2 *
                (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))) :=
              Finset.sum_add_distrib
          _ = 2*(sinEnvelopeFilterF d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
                (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
              sinEnvelopeFilterG d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
                (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))) := by
              rw [← Finset.mul_sum, ← Finset.mul_sum]; ring
      rw [hmassum, ← Finset.sum_sub_distrib,
        Finset.sum_congr rfl (fun z _ => hper2 z),
        Finset.sum_add_distrib, hsplit5]

    have hvarF : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ))^2 ≤
        ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 :=
      se_weighted_variance _ _ hwnn hw1
    have hvarG : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))^2 ≤
        ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2 :=
      se_weighted_variance _ _ hwnn hw1
    have hQpos : (0:ℝ) ≤ (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
         (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) :=
      Finset.sum_nonneg (fun z _ => mul_nonneg (hwnn z)
        (add_nonneg (sq_nonneg _) (sq_nonneg _)))
    have hcs : (sinEnvelopeFilterF d φ *
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
        sinEnvelopeFilterG d φ *
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)))^2 ≤
        sinEnvelopeFlagMass d φ *
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) := by
      refine (se_two_dim_cs _ _ _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hmass
      have hsplit3 : ∀ z : Fin M, (‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) +
          ‖sinEnvelopeKernel M φ z‖^2 *
            (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2 =
          ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2) := by
        intro z; ring
      have hsplit3sum : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) +
          (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2) =
          ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2) := by
        rw [← Finset.sum_add_distrib,
          Finset.sum_congr rfl (fun z _ => hsplit3 z)]
      linarith [hvarF, hvarG, hsplit3sum]

    have hQ13 : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
         (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) ≤
        13 * sinEnvelopeFlagMass d φ / (d*(M:ℝ)) := by
      apply (le_div_iff₀ (by positivity : (0:ℝ) < d*(M:ℝ))).mpr
      have hQ' : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) *
          (d*(M:ℝ)) * (d*(M:ℝ)) ≤ 258 * sinEnvelopeFlagMass d φ := by
        rw [mul_assoc, ← pow_two]
        exact hQ
      have hmul : ((∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) *
          (d*(M:ℝ))) * 21 ≤
          (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) *
          (d*(M:ℝ)) * (d*(M:ℝ)) :=
        mul_le_mul_of_nonneg_left hDM (by positivity)
      nlinarith [hQ', hmul, sq_nonneg (sinEnvelopeFlagMass d φ)]
    have hsqrt : (sinEnvelopeFlagMass d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
         (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2))).sqrt ≤
        17 * sinEnvelopeFlagMass d φ / (d*(M:ℝ)) := by
      have hkey : sinEnvelopeFlagMass d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) *
          (d*(M:ℝ))^2 ≤ (17 * sinEnvelopeFlagMass d φ)^2 := by
        calc sinEnvelopeFlagMass d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
               (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) *
              (d*(M:ℝ))^2 =
            sinEnvelopeFlagMass d φ * ((∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
               (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) *
              (d*(M:ℝ))^2) := by ring
          _ ≤ sinEnvelopeFlagMass d φ * (258 * sinEnvelopeFlagMass d φ) :=
              mul_le_mul_of_nonneg_left hQ hmass
          _ ≤ (17 * sinEnvelopeFlagMass d φ)^2 := by
              have hsq258 : sinEnvelopeFlagMass d φ * (258 * sinEnvelopeFlagMass d φ) =
                  258 * sinEnvelopeFlagMass d φ^2 := by ring
              have hsq289 : (17 * sinEnvelopeFlagMass d φ)^2 =
                  289 * sinEnvelopeFlagMass d φ^2 := by ring
              rw [hsq258, hsq289]
              exact mul_le_mul_of_nonneg_right (by norm_num) (sq_nonneg _)
      have hkey2 : sinEnvelopeFlagMass d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) ≤
          (17 * sinEnvelopeFlagMass d φ / (d*(M:ℝ)))^2 := by
        rw [div_pow]
        exact (le_div_iff₀ (by positivity : (0:ℝ) < (d*(M:ℝ))^2)).mpr hkey
      calc (sinEnvelopeFlagMass d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2))).sqrt ≤
          Real.sqrt ((17 * sinEnvelopeFlagMass d φ / (d*(M:ℝ)))^2) :=
            Real.sqrt_le_sqrt hkey2
        _ = 17 * sinEnvelopeFlagMass d φ / (d*(M:ℝ)) :=
            Real.sqrt_sq (div_nonneg (mul_nonneg (by norm_num) hmass)
              (mul_nonneg hd.le hMpos.le))

    have habslin : |sinEnvelopeFilterF d φ *
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
        sinEnvelopeFilterG d φ *
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))| ≤
        (sinEnvelopeFlagMass d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2))).sqrt := by
      calc |sinEnvelopeFilterF d φ *
          (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
          sinEnvelopeFilterG d φ *
          (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))| =
          Real.sqrt (|sinEnvelopeFilterF d φ *
          (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
          sinEnvelopeFilterG d φ *
          (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
            (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))|^2) :=
            (Real.sqrt_sq (abs_nonneg _)).symm
        _ ≤ (sinEnvelopeFlagMass d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2))).sqrt :=
            Real.sqrt_le_sqrt (by rw [sq_abs]; exact hcs)
    rw [hmean]
    have hstep : |(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) +
        2*(sinEnvelopeFilterF d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
          sinEnvelopeFilterG d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)))| ≤
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) +
        2*((sinEnvelopeFlagMass d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2))).sqrt) := by
      have htri : |(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) +
        2*(sinEnvelopeFilterF d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
          sinEnvelopeFilterG d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)))| ≤
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) +
        2*|sinEnvelopeFilterF d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
          sinEnvelopeFilterG d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))| := by
        have h2 := abs_add_le (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2))
          (2*(sinEnvelopeFilterF d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
          sinEnvelopeFilterG d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ))))
        rw [abs_of_nonneg hQpos, abs_mul, abs_two] at h2
        exact h2
      exact htri.trans (add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left habslin (by norm_num)))
    calc |(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) +
        2*(sinEnvelopeFilterF d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) +
          sinEnvelopeFilterG d φ *
            (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
              (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)))| ≤
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2)) +
        2*((sinEnvelopeFlagMass d φ * (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
           (sinEnvelopeFilterG d (sinEnvelopeDecode M z) - sinEnvelopeFilterG d φ)^2))).sqrt) := hstep
      _ ≤ 13 * sinEnvelopeFlagMass d φ / (d*(M:ℝ)) +
          2*(17 * sinEnvelopeFlagMass d φ / (d*(M:ℝ))) := by
          exact add_le_add hQ13
            (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
      _ = (47 / (d * (M:ℝ))) * sinEnvelopeFlagMass d φ := by
          field_simp
          ring

/-- The kernel-weighted squared success-filter error, multiplied by `(d*M)^2`, is at most `174`
times the ideal squared success filter under the stated well-phase and resolution
hypotheses. -/
private theorem se_kernel_wellF_error (M : ℕ) (hM : 2 ≤ M) (φ d η : ℝ) (hd : 0 < d)
    (hφ : 2*d ≤ φ) (hφ' : φ ≤ 1/4) (hη : 0 < η) (hη1 : η ≤ 1)
    (hbudget : 420 / (d * η) ≤ (M : ℝ)) :
    (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) *
      (d * (M : ℝ))^2 ≤ 174 * sinEnvelopeFilterF d φ^2 := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hDM : (420:ℝ) ≤ d * (M:ℝ) := by
    have h1 : 420 / (d * η) * (d * η) ≤ (M:ℝ) * (d * η) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    rw [div_mul_cancel₀ _ (mul_pos hd hη).ne'] at h1
    nlinarith [h1, hη1, mul_nonneg hMpos.le hd.le]
  have hd18 : d ≤ 1/8 := by linarith
  have h3360 : (3360:ℝ) ≤ M := by
    have h8 : (3360:ℝ) * d ≤ 420 :=
      calc (3360:ℝ) * d ≤ 3360 * (1/8) :=
            mul_le_mul_of_nonneg_left hd18 (by norm_num)
        _ = 420 := by norm_num
    nlinarith [h8, hDM, hd]
  have hφ0 : (0:ℝ) ≤ φ := by linarith
  have hE2 := se_kernel_e2 M hM φ d hd hφ0 hφ' (by
    have h4 : (4:ℝ) < M := by linarith
    have h4' : (4:ℕ) < M := by exact_mod_cast h4
    omega)
  have hG : sinEnvelopeFilterG d φ = 0 :=
    (sin_envelope_filter_branch_values d hd).2.2.2.2.2.2.2.2 φ hφ |>.2
  have hper : ∀ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 ≤
      ‖sinEnvelopeKernel M φ z‖^2 *
      (2*Real.pi^2*(1/(2*d))^2*(φ - sinEnvelopeDecode M z)^2*sinEnvelopeFilterF d φ^2) := by
    intro z
    have hst := sin_envelope_filter_stability d φ (sinEnvelopeDecode M z) hd hφ0 hφ'
      (decode_bounded M z hM).1 (decode_bounded M z hM).2
    rw [hG] at hst
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    rw [show (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 =
        (sinEnvelopeFilterF d φ - sinEnvelopeFilterF d (sinEnvelopeDecode M z))^2 from by ring]
    have hnn : (0:ℝ) ≤ (0 - sinEnvelopeFilterG d (sinEnvelopeDecode M z))^2 := sq_nonneg _
    linarith [hst, hnn]
  have hsum2 : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) ≤
      2*Real.pi^2*(1/(2*d))^2 * sinEnvelopeFilterF d φ^2 *
      ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) := by
    calc (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) ≤
        (2*Real.pi^2*(1/(2*d))^2*sinEnvelopeFilterF d φ^2) *
          (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2*(φ - sinEnvelopeDecode M z)^2) := by
          rw [Finset.mul_sum]
          refine Finset.sum_le_sum (fun z _ => (hper z).trans (le_of_eq (by ring)))
      _ ≤ (2*Real.pi^2*(1/(2*d))^2*sinEnvelopeFilterF d φ^2) *
          ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) :=
          mul_le_mul_of_nonneg_left hE2 (by positivity)
  have hpi : Real.pi^2 ≤ 10 := by nlinarith only [Real.pi_lt_d2, Real.pi_pos]
  have hA : (1:ℝ) + 10*Real.pi^2/3 ≤ 103/3 := by
    have h := mul_le_mul_of_nonneg_left hpi (show (0:ℝ) ≤ 10/3 by norm_num)
    nlinarith only [h]
  have h3div7 : 1440/(M:ℝ) ≤ 3/7 := by
    apply (div_le_iff₀ hMpos).mpr
    linarith [h3360]
  have hnum : ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) * (M:ℝ)^2 ≤ 730/21 := by
    have hrw : ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) * (M:ℝ)^2 =
        (1 + 10*Real.pi^2/3) + 1440/(M:ℝ) := by
      field_simp
    rw [hrw]
    nlinarith [hA, h3div7]
  calc (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) *
      (d*(M:ℝ))^2 ≤
      (2*Real.pi^2*(1/(2*d))^2*sinEnvelopeFilterF d φ^2 *
        ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3)) * (d*(M:ℝ))^2 :=
        mul_le_mul_of_nonneg_right hsum2 (sq_nonneg _)
    _ = sinEnvelopeFilterF d φ^2 * ((2*Real.pi^2*(1/(2*d))^2*(d*(M:ℝ))^2) *
        ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3)) := by ring
    _ ≤ sinEnvelopeFilterF d φ^2 * (5*(M:ℝ)^2 *
        ((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3)) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        have hXeq : 2*Real.pi^2*(1/(2*d))^2 * (d*(M:ℝ))^2 = (Real.pi^2/2) * (M:ℝ)^2 := by
          field_simp
        have hE2nn : (0:ℝ) ≤ (1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3 :=
          add_nonneg (div_nonneg (by positivity) (pow_nonneg hMpos.le 2))
            (div_nonneg (by norm_num) (pow_nonneg hMpos.le 3))
        rw [hXeq]
        exact mul_le_mul_of_nonneg_right (by nlinarith [hpi, sq_nonneg (M:ℝ)]) hE2nn
    _ = 5 * sinEnvelopeFilterF d φ^2 *
        (((1 + 10*Real.pi^2/3)/(M:ℝ)^2 + 1440/(M:ℝ)^3) * (M:ℝ)^2) := by ring
    _ ≤ 5 * sinEnvelopeFilterF d φ^2 * (730/21) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
    _ ≤ 174 * sinEnvelopeFilterF d φ^2 := by
        nlinarith [sq_nonneg (sinEnvelopeFilterF d φ)]

/-- The kernel-averaged squared success filter differs from its ideal value by at most
`29/(d*M)` times that value under the stated hypotheses. -/
private theorem se_kernel_wellF_stability (M : ℕ) (hM : 2 ≤ M) (φ d η : ℝ) (hd : 0 < d)
    (hφ : 2*d ≤ φ) (hφ' : φ ≤ 1/4) (hη : 0 < η) (hη1 : η ≤ 1)
    (hbudget : 420 / (d * η) ≤ (M : ℝ)) :
    |(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) - sinEnvelopeFilterF d φ^2| ≤
      29 * sinEnvelopeFilterF d φ^2 / (d * (M : ℝ)) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hDM : (420:ℝ) ≤ d * (M:ℝ) := by
    have h1 : 420 / (d * η) * (d * η) ≤ (M:ℝ) * (d * η) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    rw [div_mul_cancel₀ _ (mul_pos hd hη).ne'] at h1
    nlinarith [h1, hη1, mul_nonneg hMpos.le hd.le]
  have hdM : (0:ℝ) < d * (M:ℝ) := mul_pos hd hMpos
  have hφ0 : (0:ℝ) ≤ φ := by linarith
  have hFφ : (0:ℝ) ≤ sinEnvelopeFilterF d φ :=
    (sin_envelope_filter_nonnegative d φ hd).1
  have hwnn : ∀ z : Fin M, 0 ≤ ‖sinEnvelopeKernel M φ z‖^2 := fun z => sq_nonneg _
  have hw1 : ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 = 1 :=
    sin_envelope_kernel_normalized M φ hM
  have hQf := se_kernel_wellF_error M hM φ d η hd hφ hφ' hη hη1 hbudget
  have hQfnn : (0:ℝ) ≤ (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) :=
    Finset.sum_nonneg (fun z _ => mul_nonneg (hwnn z) (sq_nonneg _))
  have hmean : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) - sinEnvelopeFilterF d φ^2 =
      (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) +
      2*sinEnvelopeFilterF d φ *
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) := by
    have hmassum : sinEnvelopeFilterF d φ^2 = ∑ z : Fin M,
        ‖sinEnvelopeKernel M φ z‖^2 * sinEnvelopeFilterF d φ^2 := by
      calc sinEnvelopeFilterF d φ^2 =
          (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2) * sinEnvelopeFilterF d φ^2 := by
            rw [hw1, one_mul]
        _ = ∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 * sinEnvelopeFilterF d φ^2 :=
            Finset.sum_mul Finset.univ (fun z : Fin M => ‖sinEnvelopeKernel M φ z‖^2) _
    have hdist0 : ∀ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 - ‖sinEnvelopeKernel M φ z‖^2 *
        sinEnvelopeFilterF d φ^2 =
        ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 - sinEnvelopeFilterF d φ^2) := by
      intro z; ring
    have hper2 : ∀ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 - sinEnvelopeFilterF d φ^2) =
        ‖sinEnvelopeKernel M φ z‖^2 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
          2*sinEnvelopeFilterF d φ *
            (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) := by
      intro z; ring
    have hdist : ∀ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
        2*sinEnvelopeFilterF d φ *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) =
        ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2 +
        ‖sinEnvelopeKernel M φ z‖^2 *
          (2*sinEnvelopeFilterF d φ *
            (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) := by
      intro z; ring
    have hper3 : ∀ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (2*sinEnvelopeFilterF d φ *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) =
        2*sinEnvelopeFilterF d φ*(‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)) := by
      intro z; ring
    rw [hmassum, ← Finset.sum_sub_distrib,
      Finset.sum_congr rfl (fun z _ => hdist0 z),
      Finset.sum_congr rfl (fun z _ => hper2 z),
      Finset.sum_congr rfl (fun z _ => hdist z),
      Finset.sum_add_distrib,
      Finset.sum_congr rfl (fun z _ => hper3 z), ← Finset.mul_sum]
  have hvar : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ))^2 ≤
      (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) :=
    se_weighted_variance _ _ hwnn hw1
  have hsqrt : Real.sqrt (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) * (d*(M:ℝ)) ≤
      Real.sqrt 174 * sinEnvelopeFilterF d φ := by
    have h1 : (Real.sqrt (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) * (d*(M:ℝ)))^2 =
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) *
        (d*(M:ℝ))^2 := by
      rw [mul_pow, Real.sq_sqrt hQfnn]
    have h2 : (Real.sqrt 174 * sinEnvelopeFilterF d φ)^2 =
        174 * sinEnvelopeFilterF d φ^2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
    refine (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) hdM.le)
      (mul_nonneg (Real.sqrt_nonneg _) hFφ)).mp ?_
    rw [h1, h2]
    exact hQf
  have hs174 : Real.sqrt 174 ≤ 14 := by
    refine (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 14)).mp ?_
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 174)]
    norm_num
  have hS : |∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)| ≤
      Real.sqrt (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) := by
    refine (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp ?_
    rw [sq_abs, Real.sq_sqrt hQfnn]
    exact hvar
  have hlin : 2*sinEnvelopeFilterF d φ*Real.sqrt (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) ≤
      28 * sinEnvelopeFilterF d φ^2/(d*(M:ℝ)) := by
    apply (le_div_iff₀ hdM).mpr
    have hstep := mul_le_mul_of_nonneg_left hsqrt
      (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hFφ)
    have h2 : 2*(Real.sqrt 174 * sinEnvelopeFilterF d φ) ≤ 28*sinEnvelopeFilterF d φ := by
      have h3 := mul_le_mul_of_nonneg_left hs174 hFφ
      nlinarith [h3]
    calc 2*sinEnvelopeFilterF d φ*Real.sqrt (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) * (d*(M:ℝ)) =
        2*sinEnvelopeFilterF d φ*(Real.sqrt (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) * (d*(M:ℝ))) := by ring
      _ ≤ 2*sinEnvelopeFilterF d φ*(Real.sqrt 174 * sinEnvelopeFilterF d φ) := hstep
      _ = 2*(Real.sqrt 174 * sinEnvelopeFilterF d φ) * sinEnvelopeFilterF d φ := by ring
      _ ≤ 28*sinEnvelopeFilterF d φ * sinEnvelopeFilterF d φ :=
          mul_le_mul_of_nonneg_right h2 hFφ
      _ = 28 * sinEnvelopeFilterF d φ^2 := by ring
  have hQfdm : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) ≤
      sinEnvelopeFilterF d φ^2/(d*(M:ℝ)) := by
    have hq1 : (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) ≤
        174 * sinEnvelopeFilterF d φ^2/(d*(M:ℝ))^2 :=
      (le_div_iff₀ (by positivity : (0:ℝ) < (d*(M:ℝ))^2)).mpr hQf
    have hq2 : 174 * sinEnvelopeFilterF d φ^2/(d*(M:ℝ))^2 ≤
        sinEnvelopeFilterF d φ^2/(d*(M:ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : (0:ℝ) < (d*(M:ℝ))^2) hdM).mpr
      have hXF : (0:ℝ) ≤ (d*(M:ℝ)) * sinEnvelopeFilterF d φ^2 :=
        mul_nonneg hdM.le (sq_nonneg _)
      have h174X : (174:ℝ) ≤ d*(M:ℝ) := by linarith
      nlinarith [h174X, hXF, mul_nonneg hdM.le (sq_nonneg (sinEnvelopeFilterF d φ))]
    exact hq1.trans hq2
  have htri := abs_add_le (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
      (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2)
    (2*sinEnvelopeFilterF d φ *
      (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)))
  rw [abs_of_nonneg hQfnn, abs_mul,
    abs_of_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hFφ)] at htri
  rw [hmean]
  calc |(∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) +
      2*sinEnvelopeFilterF d φ *
        (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ))| ≤
      (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) +
      2*sinEnvelopeFilterF d φ *
        |∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)| := htri
    _ ≤ (∑ z : Fin M, ‖sinEnvelopeKernel M φ z‖^2 *
        (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d φ)^2) +
      28 * sinEnvelopeFilterF d φ^2/(d*(M:ℝ)) :=
        add_le_add (le_refl _)
          (le_trans (mul_le_mul_of_nonneg_left hS
            (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) hFφ)) hlin)
    _ ≤ sinEnvelopeFilterF d φ^2/(d*(M:ℝ)) + 28 * sinEnvelopeFilterF d φ^2/(d*(M:ℝ)) :=
        add_le_add hQfdm (le_refl _)
    _ = 29 * sinEnvelopeFilterF d φ^2/(d*(M:ℝ)) := by ring

/-- The ideal well-state amplitude is zero outside flag one and otherwise equals the spectral
kernel sum weighted by the exact success filter. -/
private theorem se_ideal_well_apply {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (p : Fin M × (Fin 3 × Fin D)) :
    sinEnvelopeIdealWellState M hM eig V B j d p =
      if p.2.1 = 1 then
        (V *ᵥ (fun i => (Vᴴ *ᵥ (B *ᵥ Ket j)) i * sinEnvelopeKernel M (eig i) p.1 *
          (sinEnvelopeFilterF d (eig i) : ℂ))) p.2.2 else 0 := by
  by_cases hp : p.2.1 = 1
  · simp [sinEnvelopeIdealWellState, TensorState, Ket, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, hp]
    apply Finset.sum_congr rfl
    intro i _
    rw [show (V *ᵥ Ket i) p.2.2 = V p.2.2 i from by
      simp [Matrix.mulVec, dotProduct, Ket]]
    ring
  · simp [sinEnvelopeIdealWellState, TensorState, Ket, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, hp]

/-- The difference of corrected actual and ideal well states is the spectral kernel sum weighted
by decoded-minus-exact success-filter values. -/
private theorem se_well_diff_apply {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (p : Fin M × (Fin 3 × Fin D)) :
    (sinEnvelopeActualWellStateCorrected M hM eig V B j d -
        sinEnvelopeIdealWellState M hM eig V B j d) p =
      if p.2.1 = 1 then
        (V *ᵥ (fun i => (Vᴴ *ᵥ (B *ᵥ Ket j)) i * sinEnvelopeKernel M (eig i) p.1 *
          ((sinEnvelopeFilterF d (sinEnvelopeDecode M p.1) - sinEnvelopeFilterF d (eig i) : ℝ) : ℂ))) p.2.2 else 0 := by
  by_cases hp : p.2.1 = 1
  · have h1 := sin_envelope_actual_well_apply M hM eig V B j d p
    have h2 := se_ideal_well_apply M hM eig V B j d p
    rw [Pi.sub_apply, h1, h2, if_pos hp, if_pos hp, if_pos hp, ← Pi.sub_apply]
    refine congrArg (fun v : Fin D → ℂ => v p.2.2) ?_
    rw [← Matrix.mulVec_sub]
    funext i
    simp only [Matrix.mulVec, dotProduct, Pi.sub_apply]
    apply Finset.sum_congr rfl
    intro k _
    push_cast
    ring
  · rw [Pi.sub_apply, sin_envelope_actual_well_apply M hM eig V B j d p,
      se_ideal_well_apply M hM eig V B j d p, if_neg hp, if_neg hp, if_neg hp]
    simp

/-- The ideal well state's squared norm equals the spectrally weighted sum of squared exact
success-filter values. -/
private theorem se_ideal_well_mass {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ p, ‖sinEnvelopeIdealWellState M hM eig V B j d p‖^2) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * sinEnvelopeFilterF d (eig i)^2 := by
  rw [Fintype.sum_prod_type]
  have hs (z : Fin M) :
      (∑ q : Fin 3 × Fin D,
        ‖sinEnvelopeIdealWellState M hM eig V B j d (z,q)‖^2) =
      ∑ k : Fin D, ‖(V *ᵥ (fun i => (Vᴴ *ᵥ (B *ᵥ Ket j)) i * sinEnvelopeKernel M (eig i) z *
        (sinEnvelopeFilterF d (eig i) : ℂ))) k‖^2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [se_ideal_well_apply]
    rw [Fin.sum_univ_succ (n := 2), Fin.sum_univ_succ (n := 1), Fin.sum_univ_succ (n := 0)]
    simp
  rw [Finset.sum_congr rfl (fun z _ => hs z)]
  simp only [← Complex.normSq_eq_norm_sq]
  simp_rw [sum_normSq_mulVec_of_mem_unitaryGroup hV]
  simp only [Complex.normSq_eq_norm_sq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc (∑ z : Fin M, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          ‖sinEnvelopeKernel M (eig i) z‖^2 * sinEnvelopeFilterF d (eig i)^2) =
      ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (∑ z : Fin M,
          ‖sinEnvelopeKernel M (eig i) z‖^2 * sinEnvelopeFilterF d (eig i)^2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun z _ => by ring)
    _ = ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ((∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2) * sinEnvelopeFilterF d (eig i)^2) := by
        rw [Finset.sum_mul]
    _ = ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * sinEnvelopeFilterF d (eig i)^2 := by
        rw [sin_envelope_kernel_normalized M (eig i) hM, one_mul]

/-- The squared norm of the difference of corrected actual and ideal well states equals the
spectrally weighted sum of kernel-weighted squared success-filter errors. -/
private theorem se_well_diff_normSq {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ p, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
        sinEnvelopeIdealWellState M hM eig V B j d) p‖^2) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ∑ z, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2 := by
  rw [Fintype.sum_prod_type]
  have hs (z : Fin M) :
      (∑ q : Fin 3 × Fin D, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
          sinEnvelopeIdealWellState M hM eig V B j d) (z,q)‖^2) =
      ∑ k : Fin D, ‖(V *ᵥ (fun i => (Vᴴ *ᵥ (B *ᵥ Ket j)) i * sinEnvelopeKernel M (eig i) z *
        ((sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i) : ℝ) : ℂ))) k‖^2 := by
    rw [Fintype.sum_prod_type]
    simp_rw [se_well_diff_apply]
    rw [Fin.sum_univ_succ (n := 2), Fin.sum_univ_succ (n := 1), Fin.sum_univ_succ (n := 0)]
    simp
  rw [Finset.sum_congr rfl (fun z _ => hs z)]
  simp only [← Complex.normSq_eq_norm_sq]
  simp_rw [sum_normSq_mulVec_of_mem_unitaryGroup hV]
  simp only [Complex.normSq_eq_norm_sq, norm_mul, mul_pow, Complex.norm_real, Real.norm_eq_abs,
      sq_abs]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc (∑ z : Fin M, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * ‖sinEnvelopeKernel M (eig i) z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2) =
      ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun z _ => by ring)
    _ = ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2) := by
        rfl

/-- For unitary `V` and `B`, the squared spectral coordinates of `B *ᵥ Ket j` sum to one. -/
private theorem se_beta_total {D : ℕ} (V B : Operator D) (j : Fin D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 = 1 := by
  have hVadj : Vᴴ ∈ Matrix.unitaryGroup (Fin D) ℂ := mem_unitaryGroup_adjoint hV
  have hv := sum_normSq_mulVec_of_mem_unitaryGroup hVadj (B *ᵥ Ket j)
  have hb := sum_normSq_mulVec_of_mem_unitaryGroup hB (Ket j)
  have hk : (∑ i : Fin D, Complex.normSq (Ket j i)) = 1 := by simp [Ket]
  simpa only [Complex.normSq_eq_norm_sq] using! hv.trans (hb.trans hk)

/-- The actual combined flag mass differs from the ideal mass by at most `47/(d*M)` times the
ideal mass under the stated spectral and resolution hypotheses. See
[HarrowHassidimLloyd2009]. -/
theorem sin_envelope_postselection_mass_stability {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hd : 0 < d) (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 0 ≤ eig i ∧ eig i ≤ 1/4)
    (hbudget : 21 / (d * η) ≤ (M : ℝ)) :
    |sinEnvelopeActualMass M hM eig V B j d - sinEnvelopeIdealMass M hM eig V B j d| ≤
      (47 / (d * (M : ℝ))) * sinEnvelopeIdealMass M hM eig V B j d := by
  have hdiff : sinEnvelopeActualMass M hM eig V B j d - sinEnvelopeIdealMass M hM eig V B j d =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ((∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
            sinEnvelopeFlagMass d (sinEnvelopeDecode M z)) - sinEnvelopeFlagMass d (eig i)) := by
    rw [sinEnvelopeActualMass, sinEnvelopeIdealMass, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [hdiff]
  calc |∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ((∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
            sinEnvelopeFlagMass d (sinEnvelopeDecode M z)) - sinEnvelopeFlagMass d (eig i))| ≤
      ∑ i, |‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ((∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
            sinEnvelopeFlagMass d (sinEnvelopeDecode M z)) - sinEnvelopeFlagMass d (eig i))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ((47 / (d * (M : ℝ))) * sinEnvelopeFlagMass d (eig i)) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_left
          (se_kernel_mass_stability M hM (eig i) d η hd (heig i).1 (heig i).2 hη hη1 hbudget)
          (sq_nonneg _)
    _ = (47 / (d * (M : ℝ))) * sinEnvelopeIdealMass M hM eig V B j d := by
        rw [sinEnvelopeIdealMass, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The corrected actual and ideal well-state masses differ by at most `47/(d*M)` times the
ideal well mass when eigenphases lie in `[2*d, 1/4]` and the resolution hypothesis holds.
See [HarrowHassidimLloyd2009]. -/
theorem sin_envelope_well_mass_stability {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hd : 0 < d) (h2d : 2 * d ≤ 1/4) (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1/4)
    (hbudget : 420 / (d * η) ≤ (M : ℝ)) :
    |(∑ p, ‖sinEnvelopeActualWellStateCorrected M hM eig V B j d p‖^2) -
      (∑ p, ‖sinEnvelopeIdealWellState M hM eig V B j d p‖^2)| ≤
      (47 / (d * (M : ℝ))) * (∑ p, ‖sinEnvelopeIdealWellState M hM eig V B j d p‖^2) := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hdM : (0:ℝ) < d * (M:ℝ) := mul_pos hd hMpos
  have h4729 : (29:ℝ) ≤ 47 := by norm_num
  rw [sin_envelope_actual_well_mass_formula M hM eig V B j d hV,
    se_ideal_well_mass M hM eig V B j d hV]
  have hdiff : (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2)) -
      (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * sinEnvelopeFilterF d (eig i)^2) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ((∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) - sinEnvelopeFilterF d (eig i)^2) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  have h4729 : (29:ℝ) ≤ 47 := by norm_num
  rw [hdiff]
  calc |∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ((∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) - sinEnvelopeFilterF d (eig i)^2)| ≤
      ∑ i, |‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ((∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) - sinEnvelopeFilterF d (eig i)^2)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ((47 / (d * (M : ℝ))) * sinEnvelopeFilterF d (eig i)^2) := by
        refine Finset.sum_le_sum (fun i _ => ?_)
        rw [abs_mul, abs_of_nonneg (sq_nonneg _)]
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        refine le_trans
          (se_kernel_wellF_stability M hM (eig i) d η hd (heig i).1 (heig i).2 hη hη1 hbudget) ?_
        have hF2 : (0:ℝ) ≤ sinEnvelopeFilterF d (eig i)^2 := sq_nonneg _
        calc (29:ℝ) * sinEnvelopeFilterF d (eig i)^2 / (d*(M:ℝ)) =
            (29:ℝ) * (sinEnvelopeFilterF d (eig i)^2 / (d*(M:ℝ))) := by ring
          _ ≤ 47 * (sinEnvelopeFilterF d (eig i)^2 / (d*(M:ℝ))) :=
              mul_le_mul_of_nonneg_right h4729 (div_nonneg hF2 hdM.le)
          _ = 47/(d*(M:ℝ)) * sinEnvelopeFilterF d (eig i)^2 := by ring
    _ = (47 / (d * (M : ℝ))) *
        (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * sinEnvelopeFilterF d (eig i)^2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun i _ => by ring)

/-- The normalized corrected actual well state is within `η` of the normalized ideal well state
under the stated spectral and resolution hypotheses. See [HarrowHassidimLloyd2009]. -/
theorem sin_envelope_conditional_well_output_error {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hd : 0 < d) (h2d : 2 * d ≤ 1/4) (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1/4)
    (hbudget : 420 / (d * η) ≤ (M : ℝ)) :
    ‖toEuclidean_fromVec (sinEnvelopeConditionalOutput
        (sinEnvelopeActualWellStateCorrected M hM eig V B j d) -
      sinEnvelopeConditionalOutput
        (sinEnvelopeIdealWellState M hM eig V B j d))‖ ≤ η := by
  have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hDM : (420:ℝ) ≤ d * (M:ℝ) := by
    have h1 : 420 / (d * η) * (d * η) ≤ (M:ℝ) * (d * η) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    rw [div_mul_cancel₀ _ (mul_pos hd hη).ne'] at h1
    nlinarith [h1, hη1, mul_nonneg hMpos.le hd.le]
  have hdM : (0:ℝ) < d * (M:ℝ) := mul_pos hd hMpos
  have hb1 := se_beta_total V B j hV hB

  have hsq : (∑ p, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
      sinEnvelopeIdealWellState M hM eig V B j d) p‖^2) ≤
      (174 / (d * (M:ℝ))^2) * (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        sinEnvelopeFilterF d (eig i)^2) := by
    rw [se_well_diff_normSq M hM eig V B j d hV]
    have hper : ∀ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2) ≤
        (174 / (d*(M:ℝ))^2) * (‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          sinEnvelopeFilterF d (eig i)^2) := by
      intro i
      have hQ := se_kernel_wellF_error M hM (eig i) d η hd (heig i).1 (heig i).2 hη hη1 hbudget
      have hdiv : (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2) ≤
          174 * sinEnvelopeFilterF d (eig i)^2 / (d*(M:ℝ))^2 :=
        (le_div_iff₀ (by positivity : (0:ℝ) < (d*(M:ℝ))^2)).mpr hQ
      calc ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
            (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2) ≤
          ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (174 * sinEnvelopeFilterF d (eig i)^2 / (d*(M:ℝ))^2) :=
            mul_le_mul_of_nonneg_left hdiv (sq_nonneg _)
        _ = (174 / (d*(M:ℝ))^2) * (‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
            sinEnvelopeFilterF d (eig i)^2) := by ring
    calc (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) - sinEnvelopeFilterF d (eig i))^2)) ≤
        ∑ i, (174 / (d*(M:ℝ))^2) * (‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          sinEnvelopeFilterF d (eig i)^2) := Finset.sum_le_sum (fun i _ => hper i)
      _ = (174 / (d*(M:ℝ))^2) * (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          sinEnvelopeFilterF d (eig i)^2) := by
          rw [Finset.mul_sum]

  have hpwpos : (0:ℝ) < (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      sinEnvelopeFilterF d (eig i)^2) := by
    have hF4 : ∀ i : Fin D, (4:ℝ) * d ≤ sinEnvelopeFilterF d (eig i) := by
      intro i
      have heigpos : (0:ℝ) < eig i := by nlinarith [(heig i).1, hd]
      have hw := (sin_envelope_filter_branch_values d hd).2.2.2.2.2.2.2.2 (eig i) (heig i).1
      rw [hw.1]
      exact (le_div_iff₀ heigpos).mpr (by nlinarith [(heig i).2, hd])
    have hcalc : (0:ℝ) < (∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (4*d)^2) := by
      rw [← Finset.sum_mul Finset.univ
        (fun i : Fin D => ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2) ((4*d)^2), hb1, one_mul]
      positivity
    calc (0:ℝ) < (∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (4*d)^2) := hcalc
      _ ≤ (∑ i : Fin D, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          sinEnvelopeFilterF d (eig i)^2) := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
          exact pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 4*d) (hF4 i) 2
  have hstrict : (∑ p, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
      sinEnvelopeIdealWellState M hM eig V B j d) p‖^2).sqrt <
      (∑ p, ‖sinEnvelopeIdealWellState M hM eig V B j d p‖^2).sqrt := by
    rw [se_ideal_well_mass M hM eig V B j d hV]
    have h174 : (174:ℝ) / (d*(M:ℝ))^2 < 1 := by
      apply (div_lt_one (by positivity : (0:ℝ) < (d*(M:ℝ))^2)).mpr
      nlinarith [hDM]
    have hlt : (∑ p, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
        sinEnvelopeIdealWellState M hM eig V B j d) p‖^2) <
        (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * sinEnvelopeFilterF d (eig i)^2) := by
      calc (∑ p, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
            sinEnvelopeIdealWellState M hM eig V B j d) p‖^2) ≤
          (174/(d*(M:ℝ))^2) * (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
            sinEnvelopeFilterF d (eig i)^2) := hsq
        _ < (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * sinEnvelopeFilterF d (eig i)^2) := by
            have hmul := mul_lt_mul_of_pos_right h174 hpwpos
            linarith
    exact Real.sqrt_lt_sqrt (Finset.sum_nonneg (fun p _ => sq_nonneg _)) hlt
  have hmain := se_conditional_output_error _ _ hstrict
  refine hmain.trans ?_
  have hs174 : Real.sqrt 174 ≤ 14 := by
    refine (sq_le_sq₀ (Real.sqrt_nonneg _) (by norm_num : (0:ℝ) ≤ 14)).mp ?_
    rw [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 174)]
    norm_num
  have h420η : (420:ℝ) ≤ (d*(M:ℝ))*η := by
    have h1 : 420 / (d * η) * (d * η) ≤ (M:ℝ) * (d * η) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    rw [div_mul_cancel₀ _ (mul_pos hd hη).ne'] at h1
    linarith
  have hcancel : (0:ℝ) < Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      sinEnvelopeFilterF d (eig i)^2) := Real.sqrt_pos.2 hpwpos
  have hA : (0:ℝ) ≤ 174 / (d*(M:ℝ))^2 := by positivity
  have hpw : (0:ℝ) ≤ (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      sinEnvelopeFilterF d (eig i)^2) := hpwpos.le
  have hbound : (Real.sqrt (∑ p, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
      sinEnvelopeIdealWellState M hM eig V B j d) p‖^2)) * (d*(M:ℝ)) ≤
      Real.sqrt 174 * Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        sinEnvelopeFilterF d (eig i)^2) := by
    have h2 : Real.sqrt ((174/(d*(M:ℝ))^2) * (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        sinEnvelopeFilterF d (eig i)^2)) =
        Real.sqrt 174/(d*(M:ℝ)) * Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          sinEnvelopeFilterF d (eig i)^2) := by
      rw [Real.sqrt_mul hA, Real.sqrt_div (by norm_num : (0:ℝ) ≤ 174),
        Real.sqrt_sq (by positivity : (0:ℝ) ≤ d*(M:ℝ))]
    calc (Real.sqrt (∑ p, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
          sinEnvelopeIdealWellState M hM eig V B j d) p‖^2)) * (d*(M:ℝ)) ≤
        Real.sqrt ((174/(d*(M:ℝ))^2) * (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          sinEnvelopeFilterF d (eig i)^2)) * (d*(M:ℝ)) :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hsq) (by positivity)
      _ = (Real.sqrt 174/(d*(M:ℝ))) * Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          sinEnvelopeFilterF d (eig i)^2) * (d*(M:ℝ)) := by rw [h2]
      _ = Real.sqrt 174 * Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          sinEnvelopeFilterF d (eig i)^2) := by field_simp
  rw [se_ideal_well_mass M hM eig V B j d hV]
  refine (div_le_iff₀ hcancel).mpr ?_
  have hs2 : (2:ℝ)*Real.sqrt 174 ≤ 28 := by nlinarith [hs174]
  have h28 : (28:ℝ) ≤ η*(d*(M:ℝ)) := by linarith [h420η]
  have h1 : (2:ℝ)*(Real.sqrt (∑ p, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
      sinEnvelopeIdealWellState M hM eig V B j d) p‖^2))*(d*(M:ℝ)) ≤
      2*(Real.sqrt 174*Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        sinEnvelopeFilterF d (eig i)^2)) := by
    nlinarith [hbound]
  have h2b : 2*(Real.sqrt 174*Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      sinEnvelopeFilterF d (eig i)^2)) ≤
      28*Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        sinEnvelopeFilterF d (eig i)^2) := by
    nlinarith [hs2, hcancel.le]
  have h3 : 28*Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      sinEnvelopeFilterF d (eig i)^2) ≤
      η*(d*(M:ℝ))*Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        sinEnvelopeFilterF d (eig i)^2) :=
    mul_le_mul_of_nonneg_right h28 hcancel.le
  have hchain : (2:ℝ)*(Real.sqrt (∑ p, ‖(sinEnvelopeActualWellStateCorrected M hM eig V B j d -
      sinEnvelopeIdealWellState M hM eig V B j d) p‖^2))*(d*(M:ℝ)) ≤
      η*(d*(M:ℝ))*Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        sinEnvelopeFilterF d (eig i)^2) :=
    (h1.trans h2b).trans h3
  nlinarith [hchain, hdM]

/-- For an angle between `2*d` and `π/2`, some `k ≤ ceil (1/(5*d)) + 1` gives amplified squared
sine at least `1/4`. -/
theorem sin_envelope_aa_angle_count (d θ : ℝ) (hd : 0 < d) (hl : 2*d ≤ θ)
    (hu : θ ≤ Real.pi/2) :
    ∃ k : ℕ, k ≤ Nat.ceil (1/(5*d))+1 ∧
      (1/4:ℝ) ≤ Real.sin ((2*(k:ℝ)+1)*θ)^2 := by
  have hθ : 0 < θ := lt_of_lt_of_le (by linarith) hl
  have hsin (x : ℝ) (hx : Real.pi/6 ≤ x) (hx' : x ≤ Real.pi/2) :
      (1/4:ℝ) ≤ Real.sin x^2 := by
    have hh := Real.sin_le_sin_of_le_of_le_pi_div_two
      (show -(Real.pi/2) ≤ Real.pi/6 by linarith only [Real.pi_pos]) hx' hx
    rw [Real.sin_pi_div_six] at hh
    nlinarith only [hh]
  by_cases hlarge : Real.pi/6 ≤ θ
  · refine ⟨0,by omega,?_⟩
    norm_num only [Nat.cast_zero, mul_zero,zero_add,one_mul]
    exact hsin θ hlarge hu
  · let x := Real.pi/(12*θ)-1/2
    let k := Nat.ceil x
    have hx : 0 ≤ x := by
      dsimp [x]
      have hh : (1/2:ℝ) ≤ Real.pi/(12*θ) :=
          (le_div_iff₀ (by positivity)).mpr (by linarith only [hlarge])
      linarith only [hh]
    have hk₀ : x ≤ (k:ℝ) := Nat.le_ceil x
    have hk₁ : (k:ℝ) < x+1 := Nat.ceil_lt_add_one hx
    have hxθ : (2*x+1)*θ = Real.pi/6 := by dsimp [x]; field_simp; ring
    have hlo : Real.pi/6 ≤ (2*(k:ℝ)+1)*θ := by
      have hh := mul_le_mul_of_nonneg_right hk₀ hθ.le
      nlinarith only [hh,hxθ]
    have hup : (2*(k:ℝ)+1)*θ ≤ Real.pi/2 := by
      have hh := mul_lt_mul_of_pos_right hk₁ hθ
      nlinarith only [hh,hxθ,hlarge]
    have hxc : x ≤ 1/(5*d) := by
      have hπ : Real.pi/(12*θ) ≤ 1/(5*d) := by
        apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
        have hm := mul_le_mul_of_nonneg_right hl (by norm_num : (0:ℝ) ≤ 12)
        have hp := mul_le_mul_of_nonneg_right Real.pi_lt_four.le hd.le
        nlinarith only [hm,hp,hd]
      dsimp [x]
      linarith only [hπ]
    refine ⟨k,(Nat.ceil_mono hxc).trans (Nat.le_succ _),hsin _ hlo hup⟩

/-- Matrix multiplication distributes over a finite sum of states. -/
private theorem se_mulVec_sum {H : Type} [Fintype H] [DecidableEq H] {ι : Type*} [Fintype ι]
    (A : Matrix H H ℂ) (f : ι → QState H) :
    A *ᵥ (∑ i, f i) = ∑ i, A *ᵥ f i := by
  funext x
  simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

/-- Scaling the right tensor factor scales the tensor state. -/
private theorem se_tensorState_smul_right {J : Type} (ψ : QState I) (c : ℂ) (w : QState J) :
    TensorState ψ (c • w) = c • TensorState ψ w := by
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

/-- Tensoring on the left distributes over a finite linear combination of right factors. -/
private theorem se_tensorState_sum_smul_right {J : Type} {ι : Type*} [Fintype ι]
    (ψ : QState I) (β : ι → ℂ) (f : ι → QState J) :
    TensorState ψ (∑ i, β i • f i) = ∑ i, β i • TensorState ψ (f i) := by
  funext p
  simp only [TensorState, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The phase-flag embedding commutes with complex scalar multiplication. -/
private theorem se_phaseFlagEmbed_smul (M : ℕ) (c : ℂ) (ψ : QState (Fin M × I)) :
    phaseFlagEmbed M (c • ψ) = c • phaseFlagEmbed M ψ := by
  funext p
  obtain ⟨x, b, i⟩ := p
  cases b <;> simp [phaseFlagEmbed]

/-- The phase-flag embedding commutes with finite sums. -/
private theorem se_phaseFlagEmbed_sum (M : ℕ) {ι : Type*} [Fintype ι]
    (f : ι → QState (Fin M × I)) :
    phaseFlagEmbed M (∑ i, f i) = ∑ i, phaseFlagEmbed M (f i) := by
  funext p
  obtain ⟨x, b, i⟩ := p
  cases b <;> simp [phaseFlagEmbed, Finset.sum_apply]

/-- A tensor state with the Boolean flag set to false equals its phase-flag embedding. -/
private theorem se_clean_embed {D : ℕ} (M : ℕ) (m₀ : Fin M) (ψ : QState (Fin 3 × Fin D)) :
    TensorState (Ket m₀) (TensorState (Ket false) ψ) =
      phaseFlagEmbed (I := Fin 3 × Fin D) M (TensorState (Ket m₀) ψ) := by
  funext p
  obtain ⟨x, b, s, i⟩ := p
  cases b <;> simp [TensorState, phaseFlagEmbed, Ket]

/-- The phase-flag embedding is the relabeling of a tensor state with Boolean flag false. -/
private theorem se_phaseFlagEmbed_eq_sector (D M : ℕ)
    (φ : QState (Fin M × (Fin 3 × Fin D))) :
    phaseFlagEmbed (I := Fin 3 × Fin D) M φ =
      relabelState (sinEnvelopeSectorEquiv D M) (TensorState (Ket false) φ) := by
  funext p
  obtain ⟨a, s, f, i⟩ := p
  cases s <;> simp [phaseFlagEmbed, relabelState, sinEnvelopeSectorEquiv, TensorState, Ket]

/-- Applying a lifted gate to an embedded state equals embedding the gate's action on that
state. -/
private theorem se_liftGate_apply {D M : ℕ}
    (G : Matrix (Fin M × (Fin 3 × Fin D)) (Fin M × (Fin 3 × Fin D)) ℂ)
    (φ : QState (Fin M × (Fin 3 × Fin D))) :
    sinEnvelopeLiftGate G *ᵥ phaseFlagEmbed (I := Fin 3 × Fin D) M φ =
      phaseFlagEmbed M (G *ᵥ φ) := by
  show ApplyGate _ _ = phaseFlagEmbed M (ApplyGate G φ)
  rw [sinEnvelopeLiftGate, se_phaseFlagEmbed_eq_sector, applyGate_relabelGate,
    applyGate_tensorGate, applyGate_one, ← se_phaseFlagEmbed_eq_sector]

/-- The preparation gate applies `B` to the data register while preserving the phase and
three-level flag basis states. -/
private theorem se_prepMain_apply {D M : ℕ} (m₀ : Fin M) (B : Operator D) (j : Fin D) :
    sinEnvelopePrepMain (M := M) B *ᵥ
        TensorState (Ket m₀) (TensorState (Ket (0 : Fin 3)) (Ket j)) =
      TensorState (Ket m₀) (TensorState (Ket (0 : Fin 3)) (B *ᵥ Ket j)) := by
  show ApplyGate _ _ = TensorState _ (TensorState _ (ApplyGate B (Ket j)))
  have hprod : TensorState (Ket m₀) (TensorState (Ket (0 : Fin 3)) (Ket j)) =
      relabelState (Equiv.prodAssoc (Fin M) (Fin 3) (Fin D))
        (TensorState (TensorState (Ket m₀) (Ket (0 : Fin 3))) (Ket j)) :=
    (relabelState_prodAssoc _ _ _).symm
  rw [sinEnvelopePrepMain, hprod, applyGate_relabelGate, applyGate_tensorGate_prodAssoc,
    applyGate_one, applyGate_one]

/-- A column of unitary `V` is an eigenvector of the continuous HHL oracle with eigenvalue `exp
(2*π*i*eig i)`. -/
private theorem se_oracle_column {D : ℕ} (eig : Fin D → ℝ)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D) :
    continuousHHLOracle eig V *ᵥ (V *ᵥ Ket i) =
      Complex.exp (2 * Real.pi * Complex.I * eig i) • (V *ᵥ Ket i) := by
  have hUV : Vᴴ * V = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! Matrix.mem_unitaryGroup_iff'.mp hV
  have hc : Vᴴ *ᵥ (V *ᵥ Ket i) = Ket i := by
    rw [Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec]
  unfold continuousHHLOracle
  rw [← Matrix.mulVec_mulVec, hc, ← Matrix.mulVec_mulVec]
  have hd : Matrix.diagonal (fun k => Complex.exp (2 * Real.pi * Complex.I * (eig k : ℂ)))
      *ᵥ Ket i = Complex.exp (2 * Real.pi * Complex.I * eig i) • Ket i := by
    funext k
    simp only [Matrix.mulVec, dotProduct, Matrix.diagonal_apply]
    by_cases hk : k = i
    · subst k; simp [Ket]
    · simp [Ket, hk]
  rw [hd, Matrix.mulVec_smul]

/-- Tensoring an oracle eigenvector with a three-level flag state preserves its oracle
eigenvalue. -/
private theorem se_oracleLift_eigen {D : ℕ} (eig : Fin D → ℝ) (V : Operator D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D) (g : QState (Fin 3)) :
    (TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) (continuousHHLOracle eig V)) *ᵥ
        TensorState g (V *ᵥ Ket i) =
      Complex.exp (2 * Real.pi * Complex.I * eig i) • TensorState g (V *ᵥ Ket i) := by
  show ApplyGate _ _ = _
  rw [applyGate_tensorGate, applyGate_one]
  rw [show ApplyGate (continuousHHLOracle eig V) (V *ᵥ Ket i) =
      Complex.exp (2 * Real.pi * Complex.I * eig i) • (V *ᵥ Ket i) from
    se_oracle_column eig V hV i]
  exact se_tensorState_smul_right g _ _

/-- Forward sine-envelope phase estimation maps a clean phase register and an oracle eigenvector
to the corresponding kernel state. -/
private theorem se_forward_image_eigen {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V : Operator D) (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (i : Fin D)
    (g : QState (Fin 3)) :
    (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (Ket (⟨0, by omega⟩ : Fin M)) (TensorState g (V *ᵥ Ket i))) =
      phaseFlagEmbed (I := Fin 3 × Fin D) M
        (TensorState (sinEnvelopeKernel M (eig i)) (TensorState g (V *ᵥ Ket i))) := by
  have hψ := se_oracleLift_eigen eig V hV i g
  have hmain := sin_envelope_forward_eigenstate (I := Fin 3 × Fin D) M hM _
    (TensorState g (V *ᵥ Ket i)) (eig i) hψ
  have hce : phaseFlagEmbed (I := Fin 3 × Fin D) M
        (TensorState (Ket (⟨0, by omega⟩ : Fin M)) (TensorState g (V *ᵥ Ket i))) =
      TensorState (Ket (⟨0, by omega⟩ : Fin M))
        (TensorState (Ket false) (TensorState g (V *ᵥ Ket i))) :=
    (se_clean_embed M _ _).symm
  calc (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (Ket (⟨0, by omega⟩ : Fin M)) (TensorState g (V *ᵥ Ket i)))
      = ApplyGate (evaluate (sinEnvelopeOracleLift (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))
          (TensorState (Ket (⟨0, by omega⟩ : Fin M))
            (TensorState (Ket false) (TensorState g (V *ᵥ Ket i)))) :=
        congrArg _ hce
    _ = phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (sinEnvelopeKernel M (eig i)) (TensorState g (V *ᵥ Ket i))) := by
        rw [show sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM =
            ((sinEnvelopePhaseCircuit (I := Fin 3 × Fin D) M hM).map stepToAdjoint).reverse
          from rfl, ← run_eq_evaluate]
        exact hmain

/-- The ideal filtered state expands in the columns of `V`, weighted by the prepared input's
spectral coordinates. -/
private theorem se_ideal_state_expansion {D : ℕ} (eig : Fin D → ℝ) (V B : Operator D)
    (j : Fin D) (d : ℝ) :
    (fun p : Fin 3 × Fin D =>
        ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) p.1) * Vᴴ) *ᵥ
          (B *ᵥ Ket j)) p.2) =
      ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i) := by
  funext p
  obtain ⟨s, k⟩ := p
  show ((V * Matrix.diagonal (fun i => sinEnvelopeHVector d (eig i) s) * Vᴴ) *ᵥ
      (B *ᵥ Ket j)) k = _
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, matrix_mulVec_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, TensorState, smul_eq_mul,
    Matrix.mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The HHL word evaluates to preparation, forward phase estimation, flag rotation, and the
adjoint forward operator in matrix composition order. -/
private theorem se_word_eval {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U : Operator D) (d : ℝ)
    (B : Operator D) :
    evaluate (sinEnvelopeOracleLift (D := D) (M := M) U) (sinEnvelopeHHLWord M hM d B) =
      (evaluate (sinEnvelopeOracleLift (D := D) (M := M) U)
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *
        (sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *
          (evaluate (sinEnvelopeOracleLift (D := D) (M := M) U)
              (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) *
            sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B))) := by
  rw [sinEnvelopeHHLWord, evaluate_append, evaluate_append, evaluate_append,
    evaluate_adjointCircuit]
  simp only [evaluate, instructionMatrix, mul_one]
  noncomm_ring

/-- Forward phase estimation of a prepared input expands as a sum of embedded kernel states in
the eigenbasis. -/
private theorem se_forward_spectral {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
        (sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B) *ᵥ
          TensorState (Ket (⟨0, by omega⟩ : Fin M))
            (TensorState (Ket false) (TensorState (Ket (0 : Fin 3)) (Ket j)))) =
      ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (sinEnvelopeKernel M (eig i))
            (TensorState (Ket (0 : Fin 3)) (V *ᵥ Ket i))) := by
  rw [se_clean_embed M _ _, se_liftGate_apply, se_prepMain_apply _ B j]
  conv_lhs => rw [gridHHL_eigen_expansion (M := M) V hV (B *ᵥ Ket j)]
  rw [se_tensorState_sum_smul_right, se_tensorState_sum_smul_right,
    se_phaseFlagEmbed_sum]
  simp_rw [se_phaseFlagEmbed_smul]
  rw [se_mulVec_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_smul]
  exact congrArg ((Vᴴ *ᵥ (B *ᵥ Ket j)) i • ·)
    (se_forward_image_eigen M hM eig V hV i (Ket (0 : Fin 3)))

/-- Forward phase estimation of the ideal filtered state expands into kernel states tensored
with the ideal spectral flag vectors. -/
private theorem se_forward_ideal {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
        sinEnvelopeHHLIdeal M hM eig V d B j =
      ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (sinEnvelopeKernel M (eig i))
            (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i))) := by
  unfold sinEnvelopeHHLIdeal
  rw [se_clean_embed M _ _, se_ideal_state_expansion eig V B j d]
  rw [se_tensorState_sum_smul_right, se_phaseFlagEmbed_sum]
  simp_rw [se_phaseFlagEmbed_smul]
  rw [se_mulVec_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_smul]
  exact congrArg ((Vᴴ *ᵥ (B *ᵥ Ket j)) i • ·)
    (se_forward_image_eigen M hM eig V hV i (sinEnvelopeHVector d (eig i)))

/-- A block-diagonal matrix acts independently on each block of a state. -/
private theorem se_blockDiag_mulVec {C : Type} [Fintype C] [DecidableEq C] {n : ℕ}
    (W : C → Matrix (Fin n) (Fin n) ℂ) (v : QState (C × Fin n)) (c : C) (i : Fin n) :
    (BlockDiag W *ᵥ v) (c, i) = (W c *ᵥ (fun i' => v (c, i'))) i := by
  show (∑ q : C × Fin n, BlockDiag W (c, i) q * v q) = _
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_eq_single c]
  · rw [show (∑ x : Fin n, BlockDiag W (c, i) (c, x) * v (c, x)) =
        ∑ x : Fin n, W c i x * v (c, x) from Finset.sum_congr rfl fun x _ => by
      rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.blockDiag_apply, if_pos rfl]]
    rfl
  · intro c' _ hc'
    apply Finset.sum_eq_zero
    intro x _
    rw [Qatlib.Concepts.QueryComplexity.DegreeMethod.blockDiag_apply, if_neg (fun h => hc' h.symm),
        zero_mul]
  · intro h
    exact absurd (Finset.mem_univ c) h

/-- The flag gate replaces the zero flag by the filter vector at each decoded label, weighted by
the phase kernel. -/
private theorem se_flagGate_kernel_apply {D : ℕ} (M : ℕ) (d : ℝ) (hd : 0 < d)
    (θ : ℝ) (w : QState (Fin D)) :
    sinEnvelopeFlagGate (D := D) (M := M) d *ᵥ
        TensorState (sinEnvelopeKernel M θ) (TensorState (Ket (0 : Fin 3)) w) =
      fun p : Fin M × (Fin 3 × Fin D) =>
        sinEnvelopeKernel M θ p.1 *
          TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M p.1)) w p.2 := by
  have hstate : TensorState (sinEnvelopeKernel M θ) (TensorState (Ket (0 : Fin 3)) w) =
      relabelState (Equiv.prodAssoc (Fin M) (Fin 3) (Fin D))
        (TensorState (TensorState (sinEnvelopeKernel M θ) (Ket (0 : Fin 3))) w) :=
    (relabelState_prodAssoc _ _ _).symm
  show ApplyGate _ _ = _
  rw [sinEnvelopeFlagGate, hstate, applyGate_relabelGate, applyGate_tensorGate,
    applyGate_one]
  funext p
  obtain ⟨z, s, k⟩ := p
  show ((BlockDiag (fun z : Fin M => sinEnvelopeFlagRotation d (sinEnvelopeDecode M z))) *ᵥ
      (TensorState (sinEnvelopeKernel M θ) (Ket (0 : Fin 3)))) (z, s) * w k = _
  rw [se_blockDiag_mulVec]
  have hvec : (fun s' => TensorState (sinEnvelopeKernel M θ) (Ket (0 : Fin 3)) (z, s')) =
      (sinEnvelopeKernel M θ z) • Ket (0 : Fin 3) := by
    funext s'
    simp [TensorState, Pi.smul_apply, smul_eq_mul]
  rw [hvec, Matrix.mulVec_smul,
    (sin_envelope_flag_rotation_unitary_and_column d (sinEnvelopeDecode M z) hd).2]
  simp [TensorState, Pi.smul_apply, smul_eq_mul, mul_assoc]

/-- The lifted flag gate applies the decoded filter vector inside the phase-flag embedding. -/
private theorem se_liftFlag_kernel_apply {D : ℕ} (M : ℕ) (d : ℝ) (hd : 0 < d)
    (θ : ℝ) (w : QState (Fin D)) :
    sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *ᵥ
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (TensorState (sinEnvelopeKernel M θ) (TensorState (Ket (0 : Fin 3)) w)) =
      phaseFlagEmbed (I := Fin 3 × Fin D) M
        (fun p : Fin M × (Fin 3 × Fin D) =>
          sinEnvelopeKernel M θ p.1 *
            TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M p.1)) w p.2) := by
  rw [se_liftGate_apply, se_flagGate_kernel_apply M d hd θ w]

/-- The flagged forward output is a spectral sum of kernel amplitudes and decoded filter
vectors. -/
private theorem se_flag_image {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ) (hd : 0 < d)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *ᵥ
        ((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
            (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
          (sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B) *ᵥ
            TensorState (Ket (⟨0, by omega⟩ : Fin M))
              (TensorState (Ket false) (TensorState (Ket (0 : Fin 3)) (Ket j))))) =
      ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2) := by
  rw [se_forward_spectral M hM eig V B j hV, se_mulVec_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.mulVec_smul]
  exact congrArg ((Vᴴ *ᵥ (B *ᵥ Ket j)) i • ·)
    (se_liftFlag_kernel_apply M d hd (eig i) (V *ᵥ Ket i))

/-- The spectral filter-error state vanishes on Boolean flag true and has the stated coordinate
sum on flag false. -/
private theorem se_diff_apply {D : ℕ} (M : ℕ) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ)
    (p : Fin M × (Bool × (Fin 3 × Fin D))) :
    (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        (phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2) -
         phaseFlagEmbed M
          (TensorState (sinEnvelopeKernel M (eig i))
            (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i))))) p =
      if p.2.1 then 0 else
        ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i *
          (sinEnvelopeKernel M (eig i) p.1 *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M p.1) p.2.2.1 -
              sinEnvelopeHVector d (eig i) p.2.2.1) * (V *ᵥ Ket i) p.2.2.2)) := by
  obtain ⟨z, b, s, k⟩ := p
  cases b <;> simp [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, phaseFlagEmbed,
    TensorState, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The squared norm of the embedded spectral error equals the sum of kernel-weighted
flag-vector errors weighted by squared spectral coefficients. -/
private theorem se_diff_parseval {D : ℕ} (M : ℕ) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i))))) p‖^2) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          ∑ s : Fin 3, ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2 := by
  rw [Fintype.sum_prod_type]
  have hinner (z : Fin M) (s : Fin 3) :
      (∑ k : Fin D, ‖∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i *
          (sinEnvelopeKernel M (eig i) z *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s) * (V *ᵥ Ket i) k))‖^2) =
        ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          (‖sinEnvelopeKernel M (eig i) z‖^2 *
            ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s‖^2) := by
    have hpt : ∀ k : Fin D, (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i *
          (sinEnvelopeKernel M (eig i) z *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s) * (V *ᵥ Ket i) k))) =
        (V *ᵥ (fun i => (Vᴴ *ᵥ (B *ᵥ Ket j)) i *
          (sinEnvelopeKernel M (eig i) z *
            (sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s)))) k := by
      intro k
      rw [matrix_mulVec_apply]
      apply Finset.sum_congr rfl
      intro i _
      ring
    simp_rw [hpt]
    simp only [← Complex.normSq_eq_norm_sq]
    rw [sum_normSq_mulVec_of_mem_unitaryGroup hV]
    simp only [Complex.normSq_eq_norm_sq, norm_mul, mul_pow]
  have hs (z : Fin M) :
      (∑ q : Bool × (Fin 3 × Fin D), ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i))))) (z, q)‖^2) =
        ∑ s : Fin 3, ∑ k : Fin D, ‖∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i *
          (sinEnvelopeKernel M (eig i) z *
            ((sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s) * (V *ᵥ Ket i) k))‖^2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    have htrue : (∑ q : Fin 3 × Fin D, ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q' : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q'.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q'.1)) (V *ᵥ Ket i) q'.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i))))) (z, (true, q))‖^2) =
        0 := by
      apply Finset.sum_eq_zero
      intro q _
      rw [se_diff_apply]
      simp
    rw [htrue, zero_add, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro s _
    apply Finset.sum_congr rfl
    intro k _
    rw [se_diff_apply]
    simp
  rw [Finset.sum_congr rfl (fun z _ => hs z)]
  simp_rw [hinner]
  have hswap : (∑ z : Fin M, ∑ s : Fin 3, ∑ i : Fin D,
      ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (‖sinEnvelopeKernel M (eig i) z‖^2 *
        ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
          sinEnvelopeHVector d (eig i) s‖^2)) =
      ∑ i : Fin D, ∑ z : Fin M, ∑ s : Fin 3,
        ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (‖sinEnvelopeKernel M (eig i) z‖^2 *
          ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2) := by
    rw [show (∑ z : Fin M, ∑ s : Fin 3, ∑ i : Fin D,
        ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (‖sinEnvelopeKernel M (eig i) z‖^2 *
          ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2)) =
        ∑ z : Fin M, ∑ i : Fin D, ∑ s : Fin 3,
          ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (‖sinEnvelopeKernel M (eig i) z‖^2 *
            ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
              sinEnvelopeHVector d (eig i) s‖^2) from
      Finset.sum_congr rfl fun z _ => Finset.sum_comm]
    rw [Finset.sum_comm]
  rw [hswap]
  apply Finset.sum_congr rfl
  intro i _
  have hper : ∀ z : Fin M, (∑ s : Fin 3, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        (‖sinEnvelopeKernel M (eig i) z‖^2 *
          ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2)) =
      ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (‖sinEnvelopeKernel M (eig i) z‖^2 *
        (∑ s : Fin 3, ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
          sinEnvelopeHVector d (eig i) s‖^2)) := by
    intro z
    have hpt : ∀ s : Fin 3, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        (‖sinEnvelopeKernel M (eig i) z‖^2 *
          ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2) =
        (‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * ‖sinEnvelopeKernel M (eig i) z‖^2) *
          ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
            sinEnvelopeHVector d (eig i) s‖^2 := fun s => by ring
    rw [Finset.sum_congr rfl (fun s _ => hpt s), ← Finset.mul_sum, mul_assoc]
  rw [Finset.sum_congr rfl (fun z _ => hper z), ← Finset.mul_sum]

/-- For spectrum in `[0, 1/4]` and `M ≥ 21/(d*η)`, the full actual HHL workspace state is within
Euclidean distance `η` of its ideal state. See [HarrowHassidimLloyd2009]. -/
theorem sin_envelope_hhl_full_workspace_error {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hd : 0 < d) (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 0 ≤ eig i ∧ eig i ≤ 1/4)
    (hbudget : 21 / (d * η) ≤ (M : ℝ)) :
    ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
        sinEnvelopeHHLIdeal M hM eig V d B j)‖ ≤ η := by
  classical
  have hU : continuousHHLOracle eig V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    continuous_hhl_oracle_unitary eig V hV
  have hf : WellFormedAdjointCircuit (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) :=
    wellFormedAdjointCircuit_stepToAdjoint_reverse _ (sin_envelope_phase_circuit_unitary M hM)
  have ho : sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V) ∈
      Matrix.unitaryGroup _ ℂ :=
    tensorGate_unitary (Submonoid.one_mem _)
      (controlOracle_unitary (tensorGate_unitary (Submonoid.one_mem _) hU))
  have hΦ : evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) ∈ Matrix.unitaryGroup _ ℂ :=
    hf.evaluate_unitary ho
  have hΦΦ : (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *
      evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp hΦ
    rwa [Matrix.star_eq_conjTranspose] at h
  have hE2 := se_forward_ideal M hM eig V B j d hV
  have hflag := se_flag_image M hM eig V B j d hd hV
  have hrun : sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j =
      (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *ᵥ
        (sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *ᵥ
          ((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
              (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
            (sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B) *ᵥ
              TensorState (Ket (⟨0, by omega⟩ : Fin M))
                (TensorState (Ket false) (TensorState (Ket (0 : Fin 3)) (Ket j)))))) := by
    show (evaluate _ (sinEnvelopeHHLWord M hM d B)) *ᵥ _ = _
    rw [se_word_eval, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
  have hideal_back : sinEnvelopeHHLIdeal M hM eig V d B j =
      (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *ᵥ
        ((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
            (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
          sinEnvelopeHHLIdeal M hM eig V d B j) := by
    rw [Matrix.mulVec_mulVec, hΦΦ, Matrix.one_mulVec]
  have hD : sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
      sinEnvelopeHHLIdeal M hM eig V d B j =
      (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *ᵥ
        (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i))))) := by
    rw [hrun, hideal_back, ← Matrix.mulVec_sub]
    congr 1
    have hX : sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *ᵥ
          ((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
              (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
            (sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B) *ᵥ
              TensorState (Ket (⟨0, by omega⟩ : Fin M))
                (TensorState (Ket false) (TensorState (Ket (0 : Fin 3)) (Ket j))))) =
        ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
          phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2) :=
      hflag
    rw [hX, hE2, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => (smul_sub _ _ _).symm
  have hnormD : (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
      ‖((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *ᵥ
        (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i)))))) p‖^2) =
      ∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
        ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
          (phaseFlagEmbed (I := Fin 3 × Fin D) M
            (fun q : Fin M × (Fin 3 × Fin D) =>
              sinEnvelopeKernel M (eig i) q.1 *
                TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2) -
           phaseFlagEmbed M
            (TensorState (sinEnvelopeKernel M (eig i))
              (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i))))) p‖^2 := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact sum_normSq_mulVec_of_mem_unitaryGroup (mem_unitaryGroup_adjoint hΦ) _
  calc ‖toEuclidean_fromVec (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
        sinEnvelopeHHLIdeal M hM eig V d B j)‖
      = Real.sqrt (∑ p, ‖(sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j -
          sinEnvelopeHHLIdeal M hM eig V d B j) p‖^2) := se_normVec_sqrt _
    _ = Real.sqrt (∑ p : Fin M × (Bool × (Fin 3 × Fin D)),
          ‖(∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
            (phaseFlagEmbed (I := Fin 3 × Fin D) M
              (fun q : Fin M × (Fin 3 × Fin D) =>
                sinEnvelopeKernel M (eig i) q.1 *
                  TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1))
                    (V *ᵥ Ket i) q.2) -
             phaseFlagEmbed M
              (TensorState (sinEnvelopeKernel M (eig i))
                (TensorState (sinEnvelopeHVector d (eig i)) (V *ᵥ Ket i))))) p‖^2) := by
        rw [hD]; exact congrArg Real.sqrt hnormD
    _ ≤ Real.sqrt (η^2) := Real.sqrt_le_sqrt (by
        rw [se_diff_parseval M eig V B j d hV]
        calc ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
              ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
                ∑ s : Fin 3, ‖sinEnvelopeHVector d (sinEnvelopeDecode M z) s -
                  sinEnvelopeHVector d (eig i) s‖^2
            ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * η^2 :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
                (sin_envelope_decoded_flag_error M hM (eig i) d η (heig i).1 (heig i).2 hd hη
                  hbudget) (sq_nonneg _)
          _ = η^2 := by
              rw [← Finset.sum_mul, se_beta_total V B j hV hB, one_mul])
    _ = η := Real.sqrt_sq hη.le

/-- A workspace matrix is block diagonal in the three-level flag coordinate. -/
private def se_flag_diag {D M : ℕ}
    (G : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ) :
    Prop :=
  ∀ p p' : Fin M × (Bool × (Fin 3 × Fin D)), p.2.2.1 ≠ p'.2.2.1 → G p p' = 0

/-- The identity matrix is block diagonal in the three-level flag coordinate. -/
private theorem se_flag_diag_one {D M : ℕ} :
    se_flag_diag (1 : Matrix (Fin M × (Bool × (Fin 3 × Fin D)))
      (Fin M × (Bool × (Fin 3 × Fin D))) ℂ) := by
  intro p p' h
  exact Matrix.one_apply_ne (fun he => h (by rw [he]))

/-- Products preserve block diagonality in the three-level flag coordinate. -/
private theorem se_flag_diag_mul {D M : ℕ}
    {G G' : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ}
    (hG : se_flag_diag G) (hG' : se_flag_diag G') : se_flag_diag (G * G') := by
  intro p p' h
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro p'' _
  by_cases h1 : p.2.2.1 = p''.2.2.1
  · rw [hG' p'' p' (fun hh => h (h1.trans hh)), mul_zero]
  · rw [hG p p'' h1, zero_mul]

/-- Taking the adjoint preserves block diagonality in the three-level flag coordinate. -/
private theorem se_flag_diag_adjoint {D M : ℕ}
    {G : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ}
    (hG : se_flag_diag G) : se_flag_diag Gᴴ := by
  intro p p' h
  simp [Matrix.conjTranspose_apply, hG p' p h.symm]

/-- A phase-register matrix tensored with the identity preserves the three-level flag
coordinate. -/
private theorem se_flag_diag_tensor_one {D M : ℕ} (T : Matrix (Fin M) (Fin M) ℂ) :
    se_flag_diag (TensorGate T
      (1 : Matrix (Bool × (Fin 3 × Fin D)) (Bool × (Fin 3 × Fin D)) ℂ)) := by
  intro p p' h
  obtain ⟨m, b, s, i⟩ := p
  obtain ⟨m', b', s', i'⟩ := p'
  rw [tensorGate_apply,
    Matrix.one_apply_ne (fun he => h (Prod.ext_iff.mp (Prod.ext_iff.mp he).2 |>.1)), mul_zero]

/-- The controlled phase-threshold permutation preserves the three-level flag coordinate. -/
private theorem se_flag_diag_perm {D M : ℕ} (k : ℕ) :
    se_flag_diag (D := D) (M := M)
      (permMatrix (phaseThresholdFlip (I := Fin 3 × Fin D) M k)) := by
  intro p p' h
  have hne : p ≠ phaseThresholdFlip (I := Fin 3 × Fin D) M k p' := by
    intro he
    apply h
    rw [he]
    rfl
  simp [permMatrix, hne]

/-- The lifted oracle preserves the three-level flag coordinate. -/
private theorem se_flag_diag_oracleLift {D M : ℕ} (U : Operator D) :
    se_flag_diag (D := D) (M := M) (sinEnvelopeOracleLift U) := by
  intro p p' h
  obtain ⟨m, b, s, i⟩ := p
  obtain ⟨m', b', s', i'⟩ := p'
  show (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ)
      (controlOracle (TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U))) (m, (b, s, i))
      (m', (b', s', i')) = 0
  rw [tensorGate_apply, mul_eq_zero]
  right
  simp only [controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.of_apply]
  by_cases hb : b = b'
  · subst hb
    rw [if_pos rfl]
    cases b
    · have hif : (if (false : Bool) = true then
          TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U else 1) = 1 := if_neg (by decide)
      rw [hif, Matrix.one_apply_ne (fun he => h (Prod.ext_iff.mp he).1)]
    · have hif : (if (true : Bool) = true then
          TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U else 1) =
          TensorGate (1 : Matrix (Fin 3) (Fin 3) ℂ) U := if_pos rfl
      rw [hif, tensorGate_apply, Matrix.one_apply_ne h, zero_mul]
  · rw [if_neg hb]

/-- Every instruction in the phase-threshold loop preserves the three-level flag coordinate. -/
private theorem se_flag_diag_loop_step {D : ℕ} (M n : ℕ) (U : Operator D) :
    ∀ s ∈ phaseThresholdLoop (I := Fin 3 × Fin D) M n,
      se_flag_diag (instructionMatrix (sinEnvelopeOracleLift (D := D) (M := M) U)
        (stepToAdjoint s)) := by
  induction n with
  | zero => intro s hs; simp [phaseThresholdLoop] at hs
  | succ n ih =>
    intro s hs
    simp only [phaseThresholdLoop, List.mem_append] at hs
    rcases hs with hs | hs
    · exact ih s hs
    · simp only [phaseThresholdBlock, List.mem_cons, List.mem_singleton, List.not_mem_nil,
        or_false] at hs
      rcases hs with rfl | rfl | rfl
      · exact se_flag_diag_perm n
      · exact se_flag_diag_oracleLift U
      · exact se_flag_diag_perm n

/-- Every instruction in the forward sine-envelope word preserves the three-level flag
coordinate. -/
private theorem se_flag_diag_forwardWord {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (U : Operator D) :
    ∀ c ∈ sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM,
      se_flag_diag (instructionMatrix (sinEnvelopeOracleLift (D := D) (M := M) U) c) := by
  intro c hc
  rw [sinEnvelopeForwardWord, List.mem_reverse] at hc
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hc
  simp only [sinEnvelopePhaseCircuit, List.mem_append, List.mem_singleton] at hs
  rcases hs with (rfl | hs) | rfl
  · exact se_flag_diag_tensor_one _
  · exact se_flag_diag_loop_step M _ U s hs
  · exact se_flag_diag_tensor_one _

/-- Evaluating a word whose instruction matrices preserve the three-level flag coordinate also
preserves that coordinate. -/
private theorem se_flag_diag_evaluate {D M : ℕ}
    (O : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ)
    (l : List (AdjointStep (Fin M × (Bool × (Fin 3 × Fin D))))) :
    (∀ c ∈ l, se_flag_diag (instructionMatrix O c)) →
      se_flag_diag (evaluate O l) := by
  induction l with
  | nil => intro _; exact se_flag_diag_one
  | cons c cs ih =>
    intro hl
    exact se_flag_diag_mul (hl c List.mem_cons_self)
      (ih (fun c' hc' => hl c' (List.mem_cons_of_mem _ hc')))

/-- A unitary that preserves the three-level flag coordinate preserves the probability of the
corrected well event. -/
private theorem se_measureProb_flag_diag {D M : ℕ}
    {G : Matrix (Fin M × (Bool × (Fin 3 × Fin D))) (Fin M × (Bool × (Fin 3 × Fin D))) ℂ}
    (hG : se_flag_diag G) (hGu : G ∈ Matrix.unitaryGroup _ ℂ)
    (v : QState (Fin M × (Bool × (Fin 3 × Fin D)))) :
    MeasureProb (G *ᵥ v) (sinEnvelopeWellSetCorrected D M) =
      MeasureProb v (sinEnvelopeWellSetCorrected D M) := by
  have hcol : Collapse (G *ᵥ v) (sinEnvelopeWellSetCorrected D M) =
      G *ᵥ Collapse v (sinEnvelopeWellSetCorrected D M) := by
    funext p
    rw [collapse_apply]
    by_cases hp : p ∈ sinEnvelopeWellSetCorrected D M
    · rw [if_pos hp]
      show (∑ p', G p p' * v p') =
          ∑ p', G p p' * Collapse v (sinEnvelopeWellSetCorrected D M) p'
      apply Finset.sum_congr rfl
      intro p' _
      by_cases hp' : p' ∈ sinEnvelopeWellSetCorrected D M
      · rw [collapse_apply, if_pos hp']
      · rw [collapse_apply, if_neg hp', mul_zero]
        have h1 : p.2.2.1 = 1 := (Finset.mem_filter.mp hp).2
        have h2 : p'.2.2.1 ≠ 1 :=
          fun hh => hp' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
        rw [hG p p' (by rw [h1]; exact h2.symm), zero_mul]
    · rw [if_neg hp]
      show (0 : ℂ) = ∑ p', G p p' * Collapse v (sinEnvelopeWellSetCorrected D M) p'
      symm
      apply Finset.sum_eq_zero
      intro p' _
      by_cases hp' : p' ∈ sinEnvelopeWellSetCorrected D M
      · rw [collapse_apply, if_pos hp']
        have h2 : p'.2.2.1 = 1 := (Finset.mem_filter.mp hp').2
        have h1 : p.2.2.1 ≠ 1 :=
          fun hh => hp (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hh⟩)
        rw [hG p p' (fun hh => h1 (hh.trans h2)), zero_mul]
      · rw [collapse_apply, if_neg hp', mul_zero]
  rw [← sum_normSq_collapse, ← sum_normSq_collapse, hcol]
  simp only [← Complex.normSq_eq_norm_sq]
  exact sum_normSq_mulVec_of_mem_unitaryGroup hGu _

/-- The ket at the clean input point equals the tensor product of the clean workspace kets and
the data ket. -/
private theorem se_ket_clean {D M : ℕ} (hM : 2 ≤ M) (j : Fin D) :
    Ket (sinEnvelopeCleanInputPoint hM j) =
      TensorState (Ket (⟨0, by omega⟩ : Fin M))
        (TensorState (Ket false) (TensorState (Ket (0 : Fin 3)) (Ket j))) := by
  have hpt : sinEnvelopeCleanInputPoint hM j =
      ((⟨0, by omega⟩ : Fin M), false, (0 : Fin 3), j) := rfl
  funext p
  obtain ⟨m, b, s, i⟩ := p
  rw [hpt]
  simp only [Ket, TensorState, Prod.mk.injEq]
  by_cases h1 : m = (⟨0, by omega⟩ : Fin M) <;>
    by_cases h2 : b = false <;>
    by_cases h3 : s = (0 : Fin 3) <;>
    by_cases h4 : i = j <;>
    simp [h1, h2, h3, h4]

/-- The spectral flag-image sum vanishes on Boolean flag true and equals the displayed
coordinate sum on Boolean flag false. -/
private theorem se_flag_image_apply {D : ℕ} (M : ℕ) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ)
    (p : Fin M × (Bool × (Fin 3 × Fin D))) :
    (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2)) p =
      if p.2.1 then 0 else
        ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i *
          (sinEnvelopeKernel M (eig i) p.1 *
            (sinEnvelopeHVector d (sinEnvelopeDecode M p.1) p.2.2.1 * (V *ᵥ Ket i) p.2.2.2)) := by
  obtain ⟨z, b, s, k⟩ := p
  cases b <;> simp [Finset.sum_apply, Pi.smul_apply, phaseFlagEmbed, TensorState,
    smul_eq_mul]

/-- Collapsing the forward flagged spectral state to the corrected well event gives the embedded
corrected actual well state. -/
private theorem se_run_well_collapse {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ) (hd : 0 < d)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    Collapse (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2))
        (sinEnvelopeWellSetCorrected D M) =
      fun p : Fin M × (Bool × (Fin 3 × Fin D)) =>
        if p.2.1 then 0 else
          sinEnvelopeActualWellStateCorrected M hM eig V B j d (p.1, p.2.2) := by
  funext p
  obtain ⟨z, b, s, k⟩ := p
  rw [collapse_apply]
  by_cases hs : s = 1
  · subst hs
    have hmem : (z, b, 1, k) ∈ sinEnvelopeWellSetCorrected D M := by
      simp [sinEnvelopeWellSetCorrected]
    rw [if_pos hmem]
    cases b
    · rw [se_flag_image_apply M eig V B j d]
      show (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i *
          (sinEnvelopeKernel M (eig i) z *
            (sinEnvelopeHVector d (sinEnvelopeDecode M z) 1 * (V *ᵥ Ket i) k))) =
        sinEnvelopeActualWellStateCorrected M hM eig V B j d (z, (1, k))
      rw [sin_envelope_actual_well_apply M hM eig V B j d (z, (1, k))]
      show (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i * (sinEnvelopeKernel M (eig i) z *
          (sinEnvelopeHVector d (sinEnvelopeDecode M z) 1 * (V *ᵥ Ket i) k))) =
        (V *ᵥ (fun i => (Vᴴ *ᵥ (B *ᵥ Ket j)) i * sinEnvelopeKernel M (eig i) z *
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) : ℂ))) k
      rw [matrix_mulVec_apply]
      have hF : sinEnvelopeHVector d (sinEnvelopeDecode M z) 1 =
          (sinEnvelopeFilterF d (sinEnvelopeDecode M z) : ℂ) := by
        simp [sinEnvelopeHVector]
      rw [hF]
      apply Finset.sum_congr rfl
      intro i _
      show (Vᴴ *ᵥ (B *ᵥ Ket j)) i * (sinEnvelopeKernel M (eig i) z *
          (↑(sinEnvelopeFilterF d (sinEnvelopeDecode M z)) * (V *ᵥ Ket i) k)) =
        (Vᴴ *ᵥ (B *ᵥ Ket j)) i * sinEnvelopeKernel M (eig i) z *
          ↑(sinEnvelopeFilterF d (sinEnvelopeDecode M z)) * (V *ᵥ Ket i) k
      ring
    · rw [se_flag_image_apply M eig V B j d]
      simp
  · have hnmem : (z, b, s, k) ∉ sinEnvelopeWellSetCorrected D M := by
      simp [sinEnvelopeWellSetCorrected, hs]
    rw [if_neg hnmem]
    cases b
    · show (0 : ℂ) = sinEnvelopeActualWellStateCorrected M hM eig V B j d (z, (s, k))
      rw [sin_envelope_actual_well_apply M hM eig V B j d (z, (s, k)), if_neg hs]
    · rfl

/-- The probability of the corrected well event in the flagged spectral state equals the
spectrally weighted sum of kernel-weighted squared success-filter values. -/
private theorem se_run_well_mass {D : ℕ} (M : ℕ) (hM : 2 ≤ M) (eig : Fin D → ℝ)
    (V B : Operator D) (j : Fin D) (d : ℝ) (hd : 0 < d)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) :
    MeasureProb (∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2))
        (sinEnvelopeWellSetCorrected D M) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 := by
  rw [← sum_normSq_collapse, se_run_well_collapse M hM eig V B j d hd hV,
    ← sin_envelope_actual_well_mass_formula M hM eig V B j d hV]
  have hpt : ∀ p : Fin M × (Bool × (Fin 3 × Fin D)),
      ‖(fun p' : Fin M × (Bool × (Fin 3 × Fin D)) =>
          if p'.2.1 then (0 : ℂ) else
            sinEnvelopeActualWellStateCorrected M hM eig V B j d (p'.1, p'.2.2)) p‖^2 =
        if p.2.1 then (0 : ℝ) else
          ‖sinEnvelopeActualWellStateCorrected M hM eig V B j d (p.1, p.2.2)‖^2 := by
    intro p
    by_cases hp : p.2.1 <;> simp [hp]
  rw [Finset.sum_congr rfl (fun p _ => hpt p)]
  rw [Fintype.sum_prod_type (fun p : Fin M × (Bool × (Fin 3 × Fin D)) =>
      if p.2.1 then (0 : ℝ) else
        ‖sinEnvelopeActualWellStateCorrected M hM eig V B j d (p.1, p.2.2)‖^2)]
  rw [Fintype.sum_prod_type (fun p : Fin M × (Fin 3 × Fin D) =>
      ‖sinEnvelopeActualWellStateCorrected M hM eig V B j d p‖^2)]
  apply Finset.sum_congr rfl
  intro z _
  rw [Fintype.sum_prod_type (fun q : Bool × (Fin 3 × Fin D) =>
      if (z, q).2.1 then (0 : ℝ) else
        ‖sinEnvelopeActualWellStateCorrected M hM eig V B j d ((z, q).1, (z, q).2.2)‖^2),
    Fintype.sum_bool]
  simp

/-- Under the stated positive-spectrum and resolution hypotheses, the base HHL operator is
unitary and some `k ≤ ceil (1/(5*d)) + 1` amplification iterations achieve success
probability at least `1/4` with the displayed query bound. See [HarrowHassidimLloyd2009]. -/
theorem sin_envelope_aa_success_and_cost {D : ℕ} (M : ℕ) (hM : 2 ≤ M)
    (eig : Fin D → ℝ) (V B : Operator D) (j : Fin D) (d η : ℝ)
    (hV : V ∈ Matrix.unitaryGroup (Fin D) ℂ) (hB : B ∈ Matrix.unitaryGroup (Fin D) ℂ)
    (hd : 0 < d) (h2d : 2 * d ≤ 1/4) (hη : 0 < η) (hη1 : η ≤ 1)
    (heig : ∀ i, 2 * d ≤ eig i ∧ eig i ≤ 1/4)
    (hbudget : 420 / (d * η) ≤ (M : ℝ)) :
    sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B ∈
      Matrix.unitaryGroup (Fin M × (Bool × (Fin 3 × Fin D))) ℂ ∧
    ∃ k : ℕ,
      k ≤ Nat.ceil (1 / (5 * d)) + 1 ∧
      MeasureProb (Run (preparedMark (sinEnvelopeWellSetCorrected D M))
          (preparedAACircuit (sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B)
            (sinEnvelopeCleanInputPoint hM j) k)
          (Ket (sinEnvelopeCleanInputPoint hM j)))
          (sinEnvelopeWellSetCorrected D M) ≥ 1/4 ∧
      ((2 * (k : ℝ) + 1) * (2 * ((M : ℝ) - 1)) + (k : ℝ) ≤
        (2 * ((Nat.ceil (1 / (5 * d)) : ℝ) + 1) + 1) * (2 * (M : ℝ)) +
          ((Nat.ceil (1 / (5 * d)) : ℝ) + 1)) := by
  classical
  have hU : continuousHHLOracle eig V ∈ Matrix.unitaryGroup (Fin D) ℂ :=
    continuous_hhl_oracle_unitary eig V hV
  have hA : sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B ∈
      Matrix.unitaryGroup (Fin M × (Bool × (Fin 3 × Fin D))) ℂ :=
    (sin_envelope_word_legality_and_counts D M hM d hd B (continuousHHLOracle eig V) hB hU).2.1
  refine ⟨hA, ?_⟩
  have hMpos : (0:ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hDM : (420:ℝ) ≤ d * (M:ℝ) := by
    have h1 : 420 / (d * η) * (d * η) ≤ (M:ℝ) * (d * η) :=
      mul_le_mul_of_nonneg_right hbudget (by positivity)
    rw [div_mul_cancel₀ _ (mul_pos hd hη).ne'] at h1
    nlinarith [h1, hη1, mul_nonneg hMpos.le hd.le]
  have hΦunitary : evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) ∈ Matrix.unitaryGroup _ ℂ := by
    have hf : WellFormedAdjointCircuit (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM) :=
      wellFormedAdjointCircuit_stepToAdjoint_reverse _
        (sin_envelope_phase_circuit_unitary M hM)
    have ho : sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V) ∈
        Matrix.unitaryGroup _ ℂ :=
      tensorGate_unitary (Submonoid.one_mem _)
        (controlOracle_unitary (tensorGate_unitary (Submonoid.one_mem _) hU))
    exact hf.evaluate_unitary ho
  have hflagdiag : se_flag_diag ((evaluate
        (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
        (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ) :=
    se_flag_diag_adjoint (se_flag_diag_evaluate _ _ (se_flag_diag_forwardWord M hM _))
  have hΦadj := mem_unitaryGroup_adjoint hΦunitary
  have hrun : sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j =
      (evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
          (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM))ᴴ *ᵥ
        (sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *ᵥ
          ((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
              (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
            (sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B) *ᵥ
              TensorState (Ket (⟨0, by omega⟩ : Fin M))
                (TensorState (Ket false) (TensorState (Ket (0 : Fin 3)) (Ket j)))))) := by
    show (evaluate _ (sinEnvelopeHHLWord M hM d B)) *ᵥ _ = _
    rw [se_word_eval, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
  have hflag' : sinEnvelopeLiftGate (sinEnvelopeFlagGate (D := D) (M := M) d) *ᵥ
        ((evaluate (sinEnvelopeOracleLift (D := D) (M := M) (continuousHHLOracle eig V))
            (sinEnvelopeForwardWord (I := Fin 3 × Fin D) M hM)) *ᵥ
          (sinEnvelopeLiftGate (sinEnvelopePrepMain (M := M) B) *ᵥ
            TensorState (Ket (⟨0, by omega⟩ : Fin M))
              (TensorState (Ket false) (TensorState (Ket (0 : Fin 3)) (Ket j))))) =
      ∑ i, (Vᴴ *ᵥ (B *ᵥ Ket j)) i •
        phaseFlagEmbed (I := Fin 3 × Fin D) M
          (fun q : Fin M × (Fin 3 × Fin D) =>
            sinEnvelopeKernel M (eig i) q.1 *
              TensorState (sinEnvelopeHVector d (sinEnvelopeDecode M q.1)) (V *ᵥ Ket i) q.2) :=
    se_flag_image M hM eig V B j d hd hV
  have hBornRun : MeasureProb (sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j)
        (sinEnvelopeWellSetCorrected D M) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 := by
    rw [hrun, se_measureProb_flag_diag hflagdiag hΦadj, hflag']
    exact se_run_well_mass M hM eig V B j d hd hV
  have hpa : preparedAAState (sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B)
        (sinEnvelopeCleanInputPoint hM j) =
      sinEnvelopeHHLRun M hM (continuousHHLOracle eig V) d B j := by
    show ApplyGate (sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B)
        (Ket (sinEnvelopeCleanInputPoint hM j)) = _
    rw [se_ket_clean hM j]
    rfl
  have hBornAA : MeasureProb (preparedAAState
        (sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B)
        (sinEnvelopeCleanInputPoint hM j)) (sinEnvelopeWellSetCorrected D M) =
      ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 := by
    rw [hpa, hBornRun]
  have hstab := sin_envelope_well_mass_stability M hM eig V B j d η hV hB hd h2d hη hη1
    heig hbudget
  rw [sin_envelope_actual_well_mass_formula M hM eig V B j d hV,
    se_ideal_well_mass M hM eig V B j d hV] at hstab
  have hb1 := se_beta_total V B j hV hB
  have hF4 : ∀ i : Fin D, (4:ℝ) * d ≤ sinEnvelopeFilterF d (eig i) := by
    intro i
    have heigpos : (0:ℝ) < eig i := by nlinarith [(heig i).1, hd]
    have hw := (sin_envelope_filter_branch_values d hd).2.2.2.2.2.2.2.2 (eig i) (heig i).1
    rw [hw.1]
    exact (le_div_iff₀ heigpos).mpr (by nlinarith [(heig i).2, hd])
  have hpw_ge : (16:ℝ) * d^2 ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      sinEnvelopeFilterF d (eig i)^2 := by
    calc (16:ℝ) * d^2 = (4*d)^2 := by ring
      _ = ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (4*d)^2 := by
          have h : (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (4*d)^2) = (4*d)^2 := by
            rw [← Finset.sum_mul, hb1, one_mul]
          rw [h]
      _ ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * sinEnvelopeFilterF d (eig i)^2 :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 4*d) (hF4 i) 2) (sq_nonneg _)
  have hpwnn : (0:ℝ) ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * sinEnvelopeFilterF d (eig i)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hpw'nn : (0:ℝ) ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 :=
    Finset.sum_nonneg fun i _ => mul_nonneg (sq_nonneg _)
      (Finset.sum_nonneg fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hpw'le : (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) ≤ 1/4 := by
    have hFσ : ∀ z : Fin M, sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 ≤ 1/4 := by
      intro z
      have h1 : sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 ≤
          sinEnvelopeFlagMass d (sinEnvelopeDecode M z) :=
        le_add_of_nonneg_right (sq_nonneg _)
      exact h1.trans (sin_envelope_filter_bounded d (sinEnvelopeDecode M z) hd)
    have hker : ∀ i : Fin D, (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) ≤ 1/4 := by
      intro i
      calc (∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
            sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2)
          ≤ ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 * (1/4) :=
            Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left (hFσ z) (sq_nonneg _)
        _ = 1/4 := by
            rw [← Finset.sum_mul, sin_envelope_kernel_normalized M (eig i) hM, one_mul]
    calc (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
            sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2)
        ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * (1/4) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hker i) (sq_nonneg _)
      _ = 1/4 := by rw [← Finset.sum_mul, hb1, one_mul]
  have h47 : (47:ℝ) / (d * (M:ℝ)) ≤ 47 / 420 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hDM
  have hpw'ge : (16:ℝ) * d^2 * (1 - 47/420) ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 := by
    have h1 := (abs_le.mp hstab).1
    have h2 : (47:ℝ)/(d*(M:ℝ)) * (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        sinEnvelopeFilterF d (eig i)^2) ≤
        47/420 * (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 * sinEnvelopeFilterF d (eig i)^2) :=
      mul_le_mul_of_nonneg_right h47 hpwnn
    have h3 : (1 - 47/420) * (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        sinEnvelopeFilterF d (eig i)^2) ≥ (1 - 47/420) * (16 * d^2) :=
      mul_le_mul_of_nonneg_left hpw_ge (by norm_num)
    nlinarith [h1, h2, h3]
  have hpos : (0:ℝ) < ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 := by
    have h0 : (0:ℝ) < 16 * d^2 * (1 - 47/420) := by
      have : (0:ℝ) < 1 - 47/420 := by norm_num
      positivity
    exact lt_of_lt_of_le h0 hpw'ge
  have hsqrt_nn : (0:ℝ) ≤ Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) := Real.sqrt_nonneg _
  have hsqrt_le : Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) ≤ 1/2 := by
    have h := Real.sqrt_le_sqrt hpw'le
    rwa [show (1/4:ℝ) = (1/2)^2 by norm_num, Real.sqrt_sq (by norm_num)] at h
  have hsqrt_pos : (0:ℝ) < Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) := Real.sqrt_pos.mpr hpos
  set θ := Real.arcsin (Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2)) with hθdef
  have hsinθ : Real.sin θ = Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
      ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
        sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) := by
    rw [hθdef]
    exact Real.sin_arcsin (by linarith [hsqrt_nn]) (by linarith [hsqrt_le])
  have hθ0 : 0 < θ := by
    rw [hθdef]
    rcases eq_or_lt_of_le (Real.arcsin_nonneg.mpr hsqrt_nn) with h0 | h0
    · exfalso
      have hs : Real.sin (Real.arcsin (Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
            sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2))) =
          Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
            ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
              sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) :=
        Real.sin_arcsin (by linarith [hsqrt_nn]) (by linarith [hsqrt_le])
      rw [← h0, Real.sin_zero] at hs
      exact absurd hs.symm (ne_of_gt hsqrt_pos)
    · exact h0
  have hθle : θ ≤ Real.pi/6 := by
    rw [hθdef]
    have h1 : Real.arcsin (Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2)) ≤ Real.arcsin (1/2) :=
      Real.arcsin_le_arcsin hsqrt_le
    have h2 : Real.arcsin (1/2) = Real.pi/6 := by
      rw [← Real.sin_pi_div_six, Real.arcsin_sin (by linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])]
    exact h1.trans_eq h2
  have hθπ2 : θ < Real.pi/2 := by linarith [hθle, Real.pi_pos]
  have hθ2d : 2*d ≤ θ := by
    rw [hθdef]
    have hmem : 2*d ∈ Set.Ioc (-(Real.pi/2)) (Real.pi/2) := by
      constructor
      · nlinarith [Real.pi_pos, hd]
      · nlinarith [Real.pi_gt_three, h2d]
    rw [Real.le_arcsin_iff_sin_le' hmem]
    have hsinle : Real.sin (2*d) ≤ 2*d := Real.sin_le (by positivity)
    have h2dle : 2*d ≤ Real.sqrt (∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
        ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
          sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2) := by
      have hsq : (2*d)^2 ≤ ∑ i, ‖(Vᴴ *ᵥ (B *ᵥ Ket j)) i‖^2 *
          ∑ z : Fin M, ‖sinEnvelopeKernel M (eig i) z‖^2 *
            sinEnvelopeFilterF d (sinEnvelopeDecode M z)^2 := by
        have h1 : (2*d)^2 = 4*d^2 := by ring
        rw [h1]
        nlinarith [hpw'ge, hd]
      refine (sq_le_sq₀ (by positivity) hsqrt_nn).mp ?_
      rwa [Real.sq_sqrt hpw'nn]
    exact hsinle.trans h2dle
  obtain ⟨k, hk, hsin⟩ := sin_envelope_aa_angle_count d θ hd hθ2d hθπ2.le
  have hprob : MeasureProb (preparedAAState
        (sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B)
        (sinEnvelopeCleanInputPoint hM j)) (sinEnvelopeWellSetCorrected D M) =
      (Real.sin θ)^2 := by
    rw [hBornAA, hθdef, Real.sin_arcsin (by linarith [hsqrt_nn]) (by linarith [hsqrt_le]),
      Real.sq_sqrt hpw'nn]
  have hborn := prepared_aa_born_success
    (sinEnvelopeAmplifiedWord M hM (continuousHHLOracle eig V) d B)
    (sinEnvelopeCleanInputPoint hM j) (sinEnvelopeWellSetCorrected D M) θ k hA hθ0 hθπ2 hprob
  refine ⟨k, hk, ?_, sin_envelope_aa_query_budget M hM d k hk⟩
  rw [hborn]
  exact hsin

end Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers
