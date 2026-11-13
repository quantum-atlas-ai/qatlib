/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralBounds
import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralExecutionContinuationDefs

/-!
# Sine envelope spectral filter circuits

This module constructs repeated sine envelope detection and reflection words on explicit phase
registers. It proves their well-formedness, exact query and gate counts, and action on
eigenstates and finite spectral superpositions.

`envelope_phase_actual_spectral_packet` identifies the zero branch with the diagonal kernel
filter. The bound `frontier1` compares the actual reflection with the ideal target reflection
while retaining the explicit target-amplitude error terms. The quantum walk spectral framework
is developed in [Szegedy2004].

## Main statements

* `envelopeDetectionWord_resources`: Well-formedness and exact detection resources.
* `envelope_phase_actual_spectral_packet`: Spectral packet and zero branch formulas.
* `frontier1`: Reflection error bound with explicit target terms and resource counts.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL
open Qatlib.Concepts.HhlAlgorithms.SinEnvProgram.SinEnvelopeHHLConsumers

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Matrix
open Qatlib
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

variable {I : Type} [Fintype I] [DecidableEq I]

/-- Relabelling a gate by an equivalence commutes with conjugate transpose. -/
private theorem envelope_relabel_adjoint {H K : Type} (e : H ≃ K)
    (U : Matrix H H ℂ) : (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
  ext i j
  rfl

omit [Fintype I] in

/-- The sine envelope forward word equals the compilation of the sine envelope phase circuit. -/
theorem envelopeForwardWord_eq_compile (M : ℕ) (hM : 2 ≤ M) :
    sinEnvelopeForwardWord (I := I) M hM =
      phaseCompileCircuit (sinEnvelopePhaseCircuit (I := I) M hM) := by
  have hmap : (sinEnvelopePhaseCircuit (I := I) M hM).map stepToAdjoint =
      (sinEnvelopePhaseCircuit (I := I) M hM).map phaseForwardStep :=
    List.map_congr_left fun s _ => by cases s <;> rfl
  simp only [sinEnvelopeForwardWord, phaseCompileCircuit, hmap]
  exact List.map_reverse.symm

/-- For `M ≥ 2`, the sine envelope forward word is a well-formed adjoint circuit. -/
theorem envelopeForwardWord_wellFormed (M : ℕ) (hM : 2 ≤ M) :
    WellFormedAdjointCircuit (sinEnvelopeForwardWord (I := I) M hM) := by
  rw [envelopeForwardWord_eq_compile M hM]
  exact phaseCompileCircuit_wellFormed (sin_envelope_phase_circuit_unitary (I := I) M hM)

/-- Lifting the identity through the phase tail gate gives the identity. -/
private theorem envelopeTailGate_one (M k : ℕ) :
    phaseTailGate (I := I) M k 1 = 1 := by
  rw [phaseTailGate, tensorGate_one, CircuitRelabel.relabelGate_one]

/-- The phase tail gate lift preserves matrix multiplication. -/
private theorem envelopeTailGate_mul (M k : ℕ)
    (U V : Matrix (PhaseReflectionSpace I M k) (PhaseReflectionSpace I M k) ℂ) :
    phaseTailGate (I := I) M k (U * V) =
      phaseTailGate (I := I) M k U * phaseTailGate (I := I) M k V := by
  unfold phaseTailGate
  rw [← CircuitRelabel.relabelGate_mul, tensorGate_mul, Matrix.one_mul]

/-- The phase tail gate lift commutes with conjugate transpose. -/
private theorem envelopeTailGate_adjoint (M k : ℕ)
    (U : Matrix (PhaseReflectionSpace I M k) (PhaseReflectionSpace I M k) ℂ) :
    phaseTailGate (I := I) M k Uᴴ = (phaseTailGate (I := I) M k U)ᴴ := by
  rw [phaseTailGate, phaseTailGate, envelope_relabel_adjoint,
    tensorGate_conjTranspose, Matrix.conjTranspose_one]

/-- Lifting the identity through the phase head gate gives the identity. -/
private theorem envelopeHeadGate_one (M k : ℕ) :
    phaseHeadGate (I := I) M k 1 = 1 := by
  rw [phaseHeadGate, tensorGate_one, CircuitRelabel.relabelGate_one]

/-- The phase head gate lift preserves matrix multiplication. -/
private theorem envelopeHeadGate_mul (M k : ℕ)
    (U V : Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ) :
    phaseHeadGate (I := I) M k (U * V) =
      phaseHeadGate (I := I) M k U * phaseHeadGate (I := I) M k V := by
  unfold phaseHeadGate
  rw [← CircuitRelabel.relabelGate_mul, tensorGate_mul, Matrix.one_mul]

/-- The phase head gate lift commutes with conjugate transpose. -/
private theorem envelopeHeadGate_adjoint (M k : ℕ)
    (U : Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ) :
    phaseHeadGate (I := I) M k Uᴴ = (phaseHeadGate (I := I) M k U)ᴴ := by
  rw [phaseHeadGate, phaseHeadGate, envelope_relabel_adjoint,
    tensorGate_conjTranspose, Matrix.conjTranspose_one]

/-- Two phase label functions on `Fin (k + 1)` are equal exactly when their zero coordinates and
successor-coordinate tails are equal. -/
private theorem envelope_function_eq_iff (M k : ℕ) (x y : Fin (k + 1) → Fin M) :
    x = y ↔ x 0 = y 0 ∧ (fun j : Fin k => x j.succ) = (fun j : Fin k => y j.succ) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    funext i
    exact Fin.cases h0 (fun j => congrFun ht j) i

omit [Fintype I] [DecidableEq I] in

/-- Lifting the parallel oracle through the phase tail gate gives the parallel oracle on the
enlarged phase register. -/
private theorem envelopeTailGate_oracle (M k : ℕ)
    (A : Matrix (Bool × I) (Bool × I) ℂ) :
    phaseTailGate (I := I) M k (parallelOracle (J := Fin k → Fin M) A) =
      parallelOracle (J := Fin (k + 1) → Fin M) A := by
  ext ⟨x, d⟩ ⟨y, e⟩
  simp only [phaseTailGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, phaseTailSplit, TensorGate, parallelOracle, select, Matrix.of_apply]
  by_cases hh : x 0 = y 0 <;>
    by_cases ht : (fun j : Fin k => x j.succ) = (fun j : Fin k => y j.succ)
  · have hxy := (envelope_function_eq_iff M k x y).mpr ⟨hh, ht⟩
    simp [hxy]
  · have hxy : x ≠ y := fun h => ht ((envelope_function_eq_iff M k x y).mp h).2
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((envelope_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((envelope_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]

omit [Fintype I] [DecidableEq I] in

/-- Lifting the parallel oracle through the phase head gate gives the parallel oracle on the
enlarged phase register. -/
private theorem envelopeHeadGate_oracle (M k : ℕ)
    (A : Matrix (Bool × I) (Bool × I) ℂ) :
    phaseHeadGate (I := I) M k (parallelOracle (J := Fin M) A) =
      parallelOracle (J := Fin (k + 1) → Fin M) A := by
  ext ⟨x, d⟩ ⟨y, e⟩
  simp only [phaseHeadGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, phaseHeadSplit, Equiv.trans_apply, phaseTailSplit, TensorGate,
    parallelOracle, select, Matrix.of_apply]
  by_cases hh : x 0 = y 0 <;>
    by_cases ht : (fun j : Fin k => x j.succ) = (fun j : Fin k => y j.succ)
  · have hxy := (envelope_function_eq_iff M k x y).mpr ⟨hh, ht⟩
    simp [hxy]
  · have hxy : x ≠ y := fun h => ht ((envelope_function_eq_iff M k x y).mp h).2
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((envelope_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((envelope_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]

/-- The repeated sine envelope detection word, recursively combining a lifted tail detection
word with a lifted forward word on the head register. -/
noncomputable def envelopeDetectionWord (M : ℕ) (hM : 2 ≤ M) : (k : ℕ) →
    List (AdjointStep (PhaseReflectionSpace I M k))
  | 0 => []
  | k + 1 =>
      phaseLiftWord (phaseTailGate M k) (envelopeDetectionWord M hM k) ++
        phaseLiftWord (phaseHeadGate M k) (sinEnvelopeForwardWord (I := I) M hM)

/-- The repeated sine envelope detection word is well formed and uses `k * (M - 1)` queries and
`k * (2 * (M - 1) + 2)` gates. -/
theorem envelopeDetectionWord_resources (M k : ℕ) (hM : 2 ≤ M) :
    WellFormedAdjointCircuit (envelopeDetectionWord (I := I) M hM k) ∧
      adjointQueryCount (envelopeDetectionWord (I := I) M hM k) = k * (M - 1) ∧
      adjointGateCount (envelopeDetectionWord (I := I) M hM k) = k * (2 * (M - 1) + 2) := by
  have hsingle := sin_envelope_forward_word_counts (I := I) M hM
  have hw : WellFormedAdjointCircuit (sinEnvelopeForwardWord (I := I) M hM) :=
    envelopeForwardWord_wellFormed (I := I) M hM
  induction k with
  | zero =>
    exact ⟨WellFormedAdjointCircuit.nil, by simp [envelopeDetectionWord, adjointQueryCount],
      by simp [envelopeDetectionWord, adjointGateCount]⟩
  | succ k ih =>
    have htail : WellFormedAdjointCircuit
        (phaseLiftWord (phaseTailGate (I := I) M k) (envelopeDetectionWord M hM k)) :=
      phaseLiftWord_wellFormed _ (fun U hU =>
        (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary (by simp) hU)) ih.1
    have hhead : WellFormedAdjointCircuit
        (phaseLiftWord (phaseHeadGate (I := I) M k) (sinEnvelopeForwardWord (I := I) M hM)) :=
      phaseLiftWord_wellFormed _ (fun U hU =>
        (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary (by simp) hU)) hw
    refine ⟨htail.append hhead, ?_, ?_⟩
    · rw [envelopeDetectionWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append,
        (phaseLiftWord_counts _ _).1,
        (phaseLiftWord_counts _ _).1, ih.2.1, hsingle.1]
      ring
    · rw [envelopeDetectionWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append,
        (phaseLiftWord_counts _ _).2,
        (phaseLiftWord_counts _ _).2, ih.2.2, hsingle.2]
      ring

/-- The evaluation matrix of the successor detection word factors into the lifted tail
evaluation and the lifted head forward evaluation. -/
theorem envelopeDetectionWord_evaluate_succ (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) :
    evaluate (parallelOracle (controlOracle W)) (envelopeDetectionWord M hM (k + 1)) =
      phaseTailGate (I := I) M k
        (evaluate (parallelOracle (controlOracle W)) (envelopeDetectionWord M hM k)) *
      phaseHeadGate (I := I) M k
        (evaluate (parallelOracle (controlOracle W)) (sinEnvelopeForwardWord (I := I) M hM)) := by
  have ht := phaseLiftWord_evaluate (phaseTailGate (I := I) M k)
    (envelopeTailGate_one M k) (envelopeTailGate_mul M k) (envelopeTailGate_adjoint M k)
    (parallelOracle (controlOracle W)) (envelopeDetectionWord M hM k)
  have hh := phaseLiftWord_evaluate (phaseHeadGate (I := I) M k)
    (envelopeHeadGate_one M k) (envelopeHeadGate_mul M k) (envelopeHeadGate_adjoint M k)
    (parallelOracle (controlOracle W)) (sinEnvelopeForwardWord (I := I) M hM)
  rw [envelopeTailGate_oracle M k (controlOracle W)] at ht
  rw [envelopeHeadGate_oracle M k (controlOracle W)] at hh
  rw [envelopeDetectionWord, evaluate_append, ht, hh]

/-- The eigenstate packet whose amplitudes are products of sine envelope kernels on the phase
labels, with the flag fixed to false. -/
noncomputable def envelopeKernelPacket (M k : ℕ) (φ : ℝ) (v : QState I) :
    QState (PhaseReflectionSpace I M k) :=
  fun p => (∏ j : Fin k, sinEnvelopeKernel M φ (p.1 j)) * (if p.2.1 then 0 else v p.2.2)

omit [Fintype I] [DecidableEq I] in

/-- Tensoring one sine envelope kernel with a tail packet and relabelling yields the successor
packet. -/
private theorem envelopeKernelPacket_succ (M k : ℕ) (φ : ℝ) (v : QState I) :
    relabelState (phaseTailSplit I M k).symm
      (TensorState (sinEnvelopeKernel M φ) (envelopeKernelPacket M k φ v)) =
        envelopeKernelPacket M (k + 1) φ v := by
  funext ⟨x, b, i⟩
  dsimp [relabelState, phaseTailSplit, TensorState, envelopeKernelPacket]
  rw [Fin.prod_univ_succ]
  ring

/-- A phase label function equals the all-zero phase index exactly when every label has value
zero. -/
private theorem envelope_zero_predicate (M k : ℕ) (hM : 0 < M) (x : Fin k → Fin M) :
    phaseZeroIndex M k hM = x ↔ ∀ j, (x j).val = 0 := by
  constructor
  · intro h j
    exact (congrArg Fin.val (congrFun h j)).symm
  · intro h
    funext j
    exact Fin.ext (by simp only [phaseZeroIndex]; exact (h j).symm)

omit [Fintype I] [DecidableEq I] in

/-- The successor phase embedding is the relabelled tensor product of zero tail labels, a zero
head label, a false flag, and the input state. -/
private theorem envelope_embed_head_split (M k : ℕ) (hM : 0 < M) (v : QState I) :
    phaseReflectionEmbed M (k + 1) v =
      relabelState (phaseHeadSplit I M k).symm
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (phaseZeroIndex M k hM))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) v))) := by
  rw [phaseReflectionEmbed_tensor M (k + 1) hM]
  funext ⟨x, b, i⟩
  have hx := envelope_function_eq_iff M k x (phaseZeroIndex M (k + 1) hM)
  simp only [phaseZeroIndex] at hx
  dsimp [relabelState, phaseHeadSplit, phaseTailSplit, TensorState,
    Qatlib.Foundations.PureStateMath.Ket, phaseZeroIndex]
  by_cases hh : x 0 = (⟨0, hM⟩ : Fin M) <;>
    by_cases ht : (fun j : Fin k => x j.succ) = (fun _ => (⟨0, hM⟩ : Fin M)) <;>
    simp [hx, hh, ht] <;> first
    | rw [if_pos (show (fun _ : Fin k => (⟨0, hM⟩ : Fin M)) = phaseZeroIndex M k hM from rfl)]
    | (intro _ he; exact (ht he).elim)

/-- On an eigenstate, the lifted head forward circuit creates one sine envelope kernel while
leaving the remaining phase registers in their embedded state. -/
private theorem envelope_head_eigen (M k : ℕ) (hM : 2 ≤ M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ)
    (hv : W *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    ApplyGate (phaseHeadGate M k
        (evaluate (parallelOracle (controlOracle W))
          (sinEnvelopeForwardWord (I := I) M hM)))
      (phaseReflectionEmbed M (k + 1) v) =
    relabelState (phaseTailSplit I M k).symm
      (TensorState (sinEnvelopeKernel M φ) (phaseReflectionEmbed M k v)) := by
  rw [phaseHeadGate, envelope_embed_head_split M k (by omega) v, applyGate_relabelGate,
    applyGate_tensorGate, applyGate_one, envelopeForwardWord_eq_compile M hM,
    phaseCompileCircuit_evaluate,
    show parallelOracle (J := Fin M) (controlOracle W) =
      TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle W) from
      parallelOracle_eq_kronecker _,
    sin_envelope_forward_eigenstate M hM W v φ hv,
    phaseReflectionEmbed_tensor M k (by omega)]
  funext ⟨x, b, i⟩
  cases b <;>
    simp [relabelState, phaseHeadSplit, phaseTailSplit, TensorState,
      Qatlib.Foundations.PureStateMath.Ket, phaseFlagEmbed]

/-- The repeated sine envelope detection circuit sends an embedded eigenstate to its product
kernel packet. -/
theorem envelopeDetectionWord_eigenstate (M k : ℕ) (hM : 2 ≤ M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ)
    (hv : W *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    ApplyGate (evaluate (parallelOracle (controlOracle W)) (envelopeDetectionWord M hM k))
      (phaseReflectionEmbed M k v) = envelopeKernelPacket M k φ v := by
  induction k with
  | zero =>
    simp only [envelopeDetectionWord, evaluate, applyGate_one]
    funext ⟨x, b, i⟩
    cases b <;> simp [phaseReflectionEmbed, envelopeKernelPacket]
  | succ k ih =>
    rw [envelopeDetectionWord_evaluate_succ W M k hM, applyGate_mul,
      envelope_head_eigen M k hM W v φ hv, phaseTailGate, applyGate_relabelGate,
      applyGate_tensorGate, applyGate_one, ih, envelopeKernelPacket_succ]

/-- Projecting a sine envelope packet onto the all-zero phase event gives the embedded
eigenstate scaled by the `k`th power of the zero-label kernel. -/
private theorem envelopeKernelPacket_project_zero (M k : ℕ) (hM : 0 < M) (φ : ℝ)
    (v : QState I) :
    ApplyGate (Projector (phaseZeroEvent M k)) (envelopeKernelPacket M k φ v) =
      (sinEnvelopeKernel M φ (⟨0, hM⟩ : Fin M)) ^ k • phaseReflectionEmbed M k v := by
  change Collapse (envelopeKernelPacket M k φ v) (phaseZeroEvent M k) = _
  funext ⟨x, b, i⟩
  by_cases hx : ∀ j, (x j).val = 0
  · have he := (envelope_zero_predicate M k hM x).mpr hx
    subst x
    cases b <;> simp [collapse_apply, phaseZeroEvent, envelopeKernelPacket,
      phaseReflectionEmbed, phaseZeroIndex]
  · cases b <;> simp [collapse_apply, phaseZeroEvent, phaseReflectionEmbed, hx]

/-- The adjoint detection word, followed in list order by the zero phase reflection and the
detection word, forming the compiled envelope reflection. -/
noncomputable def envelopeReflectionWord (M : ℕ) (hM : 2 ≤ M) (k : ℕ) :
    List (AdjointStep (PhaseReflectionSpace I M k)) :=
  adjointCircuit (envelopeDetectionWord M hM k) ++ [.gate (phaseZeroReflection M k)] ++
    envelopeDetectionWord M hM k

/-- The envelope reflection word is well formed and uses `2 * k * (M - 1)` queries and `4 * k *
(M - 1) + 4 * k + 1` gates. -/
theorem envelope_reflection_actual_queries_and_macros (M k : ℕ) (hM : 2 ≤ M) :
    WellFormedAdjointCircuit (envelopeReflectionWord (I := I) M hM k) ∧
      adjointQueryCount (envelopeReflectionWord (I := I) M hM k) = 2 * k * (M - 1) ∧
      adjointGateCount (envelopeReflectionWord (I := I) M hM k) =
        4 * k * (M - 1) + 4 * k + 1 := by
  obtain ⟨hw, hq, hg⟩ := envelopeDetectionWord_resources (I := I) M k hM
  have hz : WellFormedAdjointCircuit
      ([.gate (phaseZeroReflection (I := I) M k)] :
        List (AdjointStep (PhaseReflectionSpace I M k))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact reflectionAbout_unitary (projector_isOrthogonalProjector _)
  refine ⟨(hw.adjointCircuit.append hz).append hw, ?_, ?_⟩
  · simp only [envelopeReflectionWord,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append,
      adjointQueryCount_adjointCircuit, adjointQueryCount, hq]
    ring
  · simp only [envelopeReflectionWord,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append,
      adjointGateCount_adjointCircuit, adjointGateCount, hg]
    ring

/-- The output of the evaluated envelope reflection word on the phase embedding of the input
state. -/
noncomputable def envelopeReflectionState (W : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M)
    (k : ℕ) (ψ : QState I) : QState (PhaseReflectionSpace I M k) :=
  ApplyGate (evaluate (parallelOracle (controlOracle W)) (envelopeReflectionWord M hM k))
    (phaseReflectionEmbed M k ψ)

/-- For a unitary walk eigenstate, the sum of the envelope reflection output and the embedded
input equals the adjoint detection action on twice the zero-label kernel contribution. -/
theorem envelope_reflection_eigenstate_residual (M k : ℕ) (hM : 2 ≤ M)
    (W : Matrix I I ℂ) (v : QState I) (φ : ℝ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : W *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    envelopeReflectionState W M hM k v + phaseReflectionEmbed M k v =
      ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
        ((2 : ℂ) • ((sinEnvelopeKernel M φ (⟨0, by omega⟩ : Fin M)) ^ k •
          phaseReflectionEmbed M k v)) := by
  have hD : (evaluate (parallelOracle (controlOracle W))
      (envelopeDetectionWord (I := I) M hM k)) ∈
      Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (envelopeDetectionWord_resources M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  have hcancel : ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
      (ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k)) (phaseReflectionEmbed M k v)) =
      phaseReflectionEmbed M k v := by
    rw [← applyGate_mul,
      show (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ *
        (evaluate (parallelOracle (controlOracle W))
          (envelopeDetectionWord M hM k)) = 1 by
        simpa only [Matrix.star_eq_conjTranspose] using! hD.1, applyGate_one]
  have hstate : envelopeReflectionState W M hM k v =
      ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
      (ApplyGate (phaseZeroReflection M k)
        (ApplyGate (evaluate (parallelOracle (controlOracle W))
          (envelopeDetectionWord M hM k)) (phaseReflectionEmbed M k v))) := by
    simp only [envelopeReflectionState, envelopeReflectionWord, evaluate_append,
      evaluate_adjointCircuit, evaluate, instructionMatrix, Matrix.mul_one,
      applyGate_mul]
  have hlin : ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
      ((2 : ℂ) • ApplyGate (Projector (phaseZeroEvent M k))
          (ApplyGate (evaluate (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k)) (phaseReflectionEmbed M k v)) -
        ApplyGate (evaluate (parallelOracle (controlOracle W))
          (envelopeDetectionWord M hM k)) (phaseReflectionEmbed M k v)) =
      (2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
        (ApplyGate (Projector (phaseZeroEvent M k))
          (ApplyGate (evaluate (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k)) (phaseReflectionEmbed M k v))) -
        phaseReflectionEmbed M k v := by
    simp only [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_smul] at hcancel ⊢
    rw [hcancel]
  rw [hstate, phaseZeroReflection, applyGate_reflectionAbout, hlin]
  have hforward := envelopeDetectionWord_eigenstate M k hM W v φ hv
  change ApplyGate (evaluate (parallelOracle (controlOracle W))
      (envelopeDetectionWord M hM k)) (phaseReflectionEmbed M k v) =
    envelopeKernelPacket M k φ v at hforward
  rw [hforward, envelopeKernelPacket_project_zero M k (by omega)]
  simp only [ApplyGate, Matrix.mulVec_smul]
  module

/-- For a unitary walk eigenstate, the deviation of envelope reflection from negation is at most
twice the `k`th power of the zero-label kernel norm times the input norm. -/
theorem envelope_reflection_eigenstate_error (M k : ℕ) (hM : 2 ≤ M)
    (W : Matrix I I ℂ) (v : QState I) (φ : ℝ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : W *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    ‖toEuclidean_fromVec (envelopeReflectionState W M hM k v +
      phaseReflectionEmbed M k v)‖ ≤
      2 * ‖sinEnvelopeKernel M φ (⟨0, by omega⟩ : Fin M)‖ ^ k *
        ‖toEuclidean_fromVec v‖ := by
  have hD : (evaluate (parallelOracle (controlOracle W))
      (envelopeDetectionWord (I := I) M hM k)) ∈
      Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (envelopeDetectionWord_resources M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  rw [envelope_reflection_eigenstate_residual M k hM W v φ hW hv,
    norm_applyGate_of_mem_unitaryGroup (adjoint_unitary hD)]
  change ‖(2 : ℂ) • ((sinEnvelopeKernel M φ (⟨0, by omega⟩ : Fin M)) ^ k •
    toEuclidean_fromVec (phaseReflectionEmbed M k v))‖ ≤ _
  rw [norm_smul, norm_smul, norm_pow, phaseReflectionEmbed_norm M k (by omega)]
  norm_num [mul_assoc]

/-- The state produced by applying the repeated sine envelope detection circuit to an embedded
input. -/
noncomputable def envelopeDetectionState (W : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M)
    (k : ℕ) (ψ : QState I) : QState (PhaseReflectionSpace I M k) :=
  ApplyGate (evaluate (parallelOracle (controlOracle W)) (envelopeDetectionWord M hM k))
    (phaseReflectionEmbed M k ψ)

/-- The unnormalized output branch obtained from envelope detection by taking all phase labels
zero and the flag false. -/
noncomputable def envelopeZeroBranch (W : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M)
    (k : ℕ) (ψ : QState I) : QState I :=
  fun i => envelopeDetectionState W M hM k ψ (phaseZeroIndex M k (by omega), (false, i))

/-- For a finite eigenstate superposition, envelope detection is the sum of its kernel packets,
and the zero branch multiplies each coefficient by the corresponding zero-label kernel
power. -/
theorem envelope_phase_actual_spectral_packet
    (J : Type) [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j) :
    envelopeDetectionState W M hM k (∑ j, c j • v j) =
        ∑ j, c j • envelopeKernelPacket M k (φ j) (v j) ∧
      envelopeZeroBranch W M hM k (∑ j, c j • v j) =
        ∑ j, (c j * (sinEnvelopeKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) • v j := by
  have hd : envelopeDetectionState W M hM k (∑ j, c j • v j) =
      ∑ j, c j • envelopeKernelPacket M k (φ j) (v j) := by
    let L := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
      (envelopeDetectionWord (I := I) M hM k))).comp (degenerateEmbedLinear M k)
    change L (∑ j, c j • v j) = _
    rw [map_sum]
    simp only [map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (c j • ·) (envelopeDetectionWord_eigenstate M k hM W (v j) (φ j) (he j))
  refine ⟨hd, ?_⟩
  funext i
  simp [envelopeZeroBranch, hd, envelopeKernelPacket, phaseZeroIndex,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

omit [DecidableEq I] in

/-- For an orthonormal family, bounds diagonal filtering error by the target amplitude
discrepancy and the off-target multiplier bound weighted by their respective coefficient
masses. -/
theorem envelope_packet_filter_error
    (J : Type) [Fintype J] [DecidableEq J]
    (v : J → QState I) (c α : J → ℂ) (T : Finset J) (s : ℂ) (C : ℝ)
    (hv : ∀ j l, Qatlib.Foundations.PureStateMath.Inner (v j) (v l) = if j = l then 1 else 0)
    (hC : 0 ≤ C) (hs : ∀ j ∈ T, α j = s) (hb : ∀ j, j ∉ T → ‖α j‖ ≤ C) :
    ‖toEuclidean_fromVec (∑ j, (c j * α j) • v j - spectralTargetState v c T)‖
      ≤ ‖1 - s‖ * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2)
        + C * Real.sqrt (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) := by
  have hd : (∑ j, (c j * α j) • v j - spectralTargetState v c T)
      = ∑ j, ((c j * α j) - (if j ∈ T then c j else 0)) • v j := by
    have ht : spectralTargetState v c T = ∑ j, (if j ∈ T then c j else 0) • v j := by
      simp [spectralTargetState, ite_smul, Finset.sum_ite_mem]
    rw [ht, ← Finset.sum_sub_distrib]
    refine congrArg (fun f : J → QState I => ∑ j, f j) ?_
    funext j
    by_cases hj : j ∈ T <;> simp [hj, sub_smul]
  rw [hd]
  have hnorm : ‖toEuclidean_fromVec
      (∑ j, ((c j * α j) - (if j ∈ T then c j else 0)) • v j)‖ ^ 2
      = ∑ j, ‖(c j * α j) - (if j ∈ T then c j else 0)‖ ^ 2 :=
    degenerate_packet_norm_sq v _ hv
  have hper : ∀ j, ‖(c j * α j) - (if j ∈ T then c j else 0)‖ ^ 2
      ≤ ‖c j‖ ^ 2 * (if j ∈ T then ‖1 - s‖ ^ 2 else C ^ 2) := by
    intro j
    by_cases hj : j ∈ T
    · have hR : (if j ∈ T then ‖1 - s‖ ^ 2 else C ^ 2) = ‖1 - s‖ ^ 2 := if_pos hj
      rw [hR, if_pos hj, hs j hj,
        show c j * s - c j = -(c j * (1 - s)) by ring, norm_neg, norm_mul, mul_pow]
    · have hR : (if j ∈ T then ‖1 - s‖ ^ 2 else C ^ 2) = C ^ 2 := if_neg hj
      rw [hR, if_neg hj, show c j * α j - 0 = c j * α j by ring, norm_mul, mul_pow]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb j hj) 2)
        (sq_nonneg _)
  have hsplit : (∑ j, ‖c j‖ ^ 2 * (if j ∈ T then ‖1 - s‖ ^ 2 else C ^ 2))
      = ‖1 - s‖ ^ 2 * (∑ j ∈ T, ‖c j‖ ^ 2)
        + C ^ 2 * (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) := by
    have h1 : (∑ j, ‖c j‖ ^ 2 * (if j ∈ T then ‖1 - s‖ ^ 2 else C ^ 2))
        = ∑ j, (if j ∈ T then ‖c j‖ ^ 2 * ‖1 - s‖ ^ 2 else ‖c j‖ ^ 2 * C ^ 2) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ T <;> simp [hj]
    have hA : (∑ j, if j ∈ T then ‖c j‖ ^ 2 * ‖1 - s‖ ^ 2 else 0)
        = ‖1 - s‖ ^ 2 * (∑ j ∈ T, ‖c j‖ ^ 2) := by
      rw [Finset.sum_ite_mem Finset.univ T (fun j => ‖c j‖ ^ 2 * ‖1 - s‖ ^ 2),
        Finset.univ_inter, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hB : (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2 * C ^ 2)
        = C ^ 2 * (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ T
      · simp [hj]
      · simp only [if_neg hj]
        ring
    have hkey : (∑ j, (if j ∈ T then ‖c j‖ ^ 2 * ‖1 - s‖ ^ 2 else ‖c j‖ ^ 2 * C ^ 2))
        = (∑ j, if j ∈ T then ‖c j‖ ^ 2 * ‖1 - s‖ ^ 2 else (0:ℝ))
          + ∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2 * C ^ 2 := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : j ∈ T <;> simp [hj]
    rw [h1, hkey, hA, hB]
  have har : 0 ≤ ∑ j ∈ T, ‖c j‖ ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hrr : 0 ≤ ∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2 := by
    refine Finset.sum_nonneg fun j _ => ?_
    by_cases hj : j ∈ T <;> simp [hj]
  have hle : (∑ j, ‖(c j * α j) - (if j ∈ T then c j else 0)‖ ^ 2)
      ≤ (‖1 - s‖ * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2)
          + C * Real.sqrt (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2)) ^ 2 := by
    have hexp : (‖1 - s‖ * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2)
          + C * Real.sqrt (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2)) ^ 2
        = ‖1 - s‖ ^ 2 * (∑ j ∈ T, ‖c j‖ ^ 2)
          + C ^ 2 * (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2)
          + 2 * (‖1 - s‖ * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2))
            * (C * Real.sqrt (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2)) := by
      rw [add_sq, mul_pow, mul_pow, Real.sq_sqrt har, Real.sq_sqrt hrr]
      ring
    rw [hexp]
    have hsum' := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hper j)
    rw [hsplit] at hsum'
    have hcross : 0 ≤ 2 * (‖1 - s‖ * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2))
        * (C * Real.sqrt (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2)) :=
      mul_nonneg (mul_nonneg (by norm_num)
        (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)))
        (mul_nonneg hC (Real.sqrt_nonneg _))
    linarith
  have h1 : ‖toEuclidean_fromVec
      (∑ j, ((c j * α j) - (if j ∈ T then c j else 0)) • v j)‖ ^ 2
      ≤ (‖1 - s‖ * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2)
        + C * Real.sqrt (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2)) ^ 2 := by
    rw [hnorm]
    exact hle
  have h2 := Real.sqrt_le_sqrt h1
  rwa [Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (add_nonneg (mul_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))
      (mul_nonneg hC (Real.sqrt_nonneg _)))] at h2

/-- Phases at distance zero from zero have the same sine envelope zero-label kernel as phase
zero. -/
theorem envelope_zero_phase_kernel (M : ℕ) (hM : 0 < M) (φ : ℝ)
    (hφ : phaseDistance φ 0 = 0) :
    sinEnvelopeKernel M φ (⟨0, hM⟩ : Fin M)
      = sinEnvelopeKernel M 0 (⟨0, hM⟩ : Fin M) := by
  have hz : φ - 0 - (⌊φ + 1 / 2⌋ : ℤ) = 0 := by
    have hz' := hφ
    simp only [phaseDistance, sub_zero, abs_eq_zero] at hz'
    linarith
  have hφ' : φ = ((⌊φ + 1 / 2⌋ : ℤ) : ℝ) := by linarith
  have hk := sin_envelope_kernel_int_add M 0 (⟨0, hM⟩ : Fin M) (⌊φ + 1 / 2⌋ : ℤ)
  rw [hφ', show ((⌊φ + 1 / 2⌋ : ℤ) : ℝ) = 0 + ((⌊φ + 1 / 2⌋ : ℤ) : ℝ) from by simp, hk]

/-- Bounds the actual envelope reflection error by off-target contraction and explicit
target-amplitude terms under the stated spectral gap hypotheses, and gives its exact query
and gate counts. -/
theorem frontier1
    (J : Type) [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ)
    (φ : J → ℝ) (T : Finset J) (η : ℝ)
    (hW : W ∈ Matrix.unitaryGroup I ℂ) (hη : 0 < η) (hfar : 1 ≤ (M : ℝ) * η)
    (hv : ∀ j l, Qatlib.Foundations.PureStateMath.Inner (v j) (v l) = if j = l then 1 else 0)
    (hc : (∑ j, ‖c j‖ ^ 2) = 1)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j)
    (ht : ∀ j ∈ T, phaseDistance (φ j) 0 = 0)
    (hg : ∀ j, j ∉ T → η ≤ phaseDistance (φ j) 0) :
    ‖toEuclidean_fromVec (envelopeReflectionState W M hM k (∑ j, c j • v j) -
        phaseReflectionEmbed M k
          ((2 : ℂ) • spectralTargetState v c T - ∑ j, c j • v j))‖
      ≤ 2 * (clause33Contraction M η) ^ k * Real.sqrt (1 - ∑ j ∈ T, ‖c j‖ ^ 2)
        + 2 * ‖1 - (sinEnvelopeKernel M 0 (⟨0, by omega⟩ : Fin M)) ^ k‖
            * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2)
        + 4 * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2)
    ∧ adjointQueryCount (envelopeReflectionWord (I := I) M hM k) = 2 * k * (M - 1)
    ∧ adjointGateCount (envelopeReflectionWord (I := I) M hM k)
        = 4 * k * (M - 1) + 4 * k + 1 := by
  have hM0 : 0 < M := by omega
  have hD : (evaluate (parallelOracle (controlOracle W))
      (envelopeDetectionWord (I := I) M hM k)) ∈
      Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (envelopeDetectionWord_resources M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))

  have hzbranch : envelopeZeroBranch W M hM k (∑ j, c j • v j)
      = ∑ j, (c j * (sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M)) ^ k) • v j :=
    (envelope_phase_actual_spectral_packet J W M k hM v c φ he).2

  have hρ2 : (clause33Contraction M η) ^ 2 = 10 / ((M : ℝ)^2 * η^2)^2 := by
    rw [clause33Contraction, div_pow, Real.sq_sqrt (by norm_num)]
  have hpass : ∀ j, j ∉ T →
      ‖sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M)‖ ≤ clause33Contraction M η := by
    intro j hj
    have hgap := sin_envelope_zero_label_gap_bound M hM (φ j) η hη hfar (hg j hj)
    have hsq : ‖sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M)‖ ^ 2
        ≤ (clause33Contraction M η) ^ 2 := by
      rw [hρ2]; exact hgap
    have hroot := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (by
      unfold clause33Contraction; positivity)] at hroot
    exact hroot

  have hz : ‖toEuclidean_fromVec (envelopeZeroBranch W M hM k (∑ j, c j • v j)
      - spectralTargetState v c T)‖
      ≤ ‖1 - (sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M)) ^ k‖ *
          Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2)
        + (clause33Contraction M η) ^ k * Real.sqrt (1 - ∑ j ∈ T, ‖c j‖ ^ 2) := by
    have hrc : (∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2)
        = 1 - ∑ j ∈ T, ‖c j‖ ^ 2 := by
      have hta : (∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0) = ∑ j ∈ T, ‖c j‖ ^ 2 := by
        rw [Finset.sum_ite_mem Finset.univ T (fun j => ‖c j‖ ^ 2), Finset.univ_inter]
      have hsplit : (∑ j, ‖c j‖ ^ 2)
          = (∑ j, if j ∈ T then ‖c j‖ ^ 2 else 0) +
            ∑ j, if j ∈ T then (0:ℝ) else ‖c j‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : j ∈ T <;> simp [hj]
      rw [hc, hta] at hsplit
      linarith
    rw [hzbranch]
    have h := envelope_packet_filter_error (I := I) (J := J) v c
      (fun j => (sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M)) ^ k) T
      ((sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M)) ^ k) ((clause33Contraction M η) ^ k) hv
      (pow_nonneg (by unfold clause33Contraction; positivity) k)
      (fun j hj => by
        show sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M) ^ k =
          sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M) ^ k
        rw [envelope_zero_phase_kernel M hM0 (φ j) (ht j hj)])
      (fun j hj => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _) (hpass j hj) k)
    rw [hrc] at h
    exact h

  have hsum : envelopeReflectionState W M hM k (∑ j, c j • v j) +
      phaseReflectionEmbed M k (∑ j, c j • v j) =
      ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
        ((2 : ℂ) • phaseReflectionEmbed M k (envelopeZeroBranch W M hM k
          (∑ j, c j • v j))) := by
    let E := degenerateEmbedLinear (I := I) M k
    let R := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
      (envelopeReflectionWord (I := I) M hM k))).comp E
    let L := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
      (envelopeDetectionWord (I := I) M hM k))ᴴ).comp ((2 : ℂ) • E)
    have hres (j : J) : R (v j) + E (v j) =
        L ((sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M)) ^ k • v j) := by
      change envelopeReflectionState W M hM k (v j) + phaseReflectionEmbed M k (v j) =
        ApplyGate (evaluate (parallelOracle (controlOracle W))
          (envelopeDetectionWord M hM k))ᴴ
          ((2 : ℂ) • E ((sinEnvelopeKernel M (φ j) (⟨0, hM0⟩ : Fin M)) ^ k • v j))
      rw [E.map_smul]
      exact envelope_reflection_eigenstate_residual M k hM W (v j) (φ j) hW (he j)
    change R (∑ j, c j • v j) + E (∑ j, c j • v j) =
      L (envelopeZeroBranch W M hM k (∑ j, c j • v j))
    rw [hzbranch, map_sum, map_sum, map_sum]
    simp only [map_smul, ← Finset.sum_add_distrib, ← smul_add, mul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hres j, map_smul]

  have herror : envelopeReflectionState W M hM k (∑ j, c j • v j) -
      phaseReflectionEmbed M k ((2 : ℂ) • spectralTargetState v c T - ∑ j, c j • v j) =
      ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
        ((2 : ℂ) • phaseReflectionEmbed M k
          (envelopeZeroBranch W M hM k (∑ j, c j • v j) - spectralTargetState v c T))
      + ((2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
          (envelopeDetectionWord M hM k))ᴴ
          (phaseReflectionEmbed M k (spectralTargetState v c T)) -
        (2 : ℂ) • phaseReflectionEmbed M k (spectralTargetState v c T)) := by
    have hP2 : phaseReflectionEmbed M k
        ((2 : ℂ) • spectralTargetState v c T - ∑ j, c j • v j)
        = (2 : ℂ) • phaseReflectionEmbed M k (spectralTargetState v c T)
          - phaseReflectionEmbed M k (∑ j, c j • v j) := by
      change degenerateEmbedLinear (I := I) M k
        ((2 : ℂ) • spectralTargetState v c T - ∑ j, c j • v j)
        = (2 : ℂ) • degenerateEmbedLinear (I := I) M k (spectralTargetState v c T)
          - degenerateEmbedLinear (I := I) M k (∑ j, c j • v j)
      rw [map_sub, map_smul]
    have hP1 : phaseReflectionEmbed M k
        (envelopeZeroBranch W M hM k (∑ j, c j • v j) - spectralTargetState v c T)
        = phaseReflectionEmbed M k (envelopeZeroBranch W M hM k (∑ j, c j • v j))
          - phaseReflectionEmbed M k (spectralTargetState v c T) :=
      (degenerateEmbedLinear (I := I) M k).map_sub _ _
    have hA1 : ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
        ((2 : ℂ) • (phaseReflectionEmbed M k (envelopeZeroBranch W M hM k (∑ j, c j • v j))
          - phaseReflectionEmbed M k (spectralTargetState v c T)))
        = (2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (envelopeZeroBranch W M hM k (∑ j, c j • v j)))
          - (2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (spectralTargetState v c T)) := by
      simp only [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
    have hA2 : ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
        ((2 : ℂ) • phaseReflectionEmbed M k
          (envelopeZeroBranch W M hM k (∑ j, c j • v j)))
        = (2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (envelopeZeroBranch W M hM k (∑ j, c j • v j))) := by
      simp only [ApplyGate, Matrix.mulVec_smul]
    rw [hP2, hP1, hA1, ← hA2, ← hsum]
    module

  have htnorm : ‖toEuclidean_fromVec
      (phaseReflectionEmbed M k (spectralTargetState v c T))‖
      = Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2) := by
    rw [phaseReflectionEmbed_norm M k hM0]
    have hsq := spectralTargetState_norm_sq v c T hv
    have h1 := Real.sqrt_le_sqrt (le_of_eq hsq)
    rw [Real.sqrt_sq (norm_nonneg _)] at h1
    have h2 := Real.sqrt_le_sqrt (le_of_eq hsq.symm)
    rw [Real.sqrt_sq (norm_nonneg _)] at h2
    exact le_antisymm h1 h2

  have hsecond : ‖toEuclidean_fromVec ((2 : ℂ) • ApplyGate (evaluate
        (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
        (phaseReflectionEmbed M k (spectralTargetState v c T)) -
      (2 : ℂ) • phaseReflectionEmbed M k (spectralTargetState v c T))‖
      ≤ 4 * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2) := by
    have hsplit : ((2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
        (phaseReflectionEmbed M k (spectralTargetState v c T)) -
      (2 : ℂ) • phaseReflectionEmbed M k (spectralTargetState v c T))
        = (2 : ℂ) • (ApplyGate (evaluate (parallelOracle (controlOracle W))
          (envelopeDetectionWord M hM k))ᴴ
          (phaseReflectionEmbed M k (spectralTargetState v c T)) -
        phaseReflectionEmbed M k (spectralTargetState v c T)) := by
      module
    rw [hsplit]
    change ‖(2 : ℂ) • toEuclidean_fromVec (ApplyGate (evaluate (parallelOracle
          (controlOracle W))
          (envelopeDetectionWord M hM k))ᴴ
          (phaseReflectionEmbed M k (spectralTargetState v c T)) -
        phaseReflectionEmbed M k (spectralTargetState v c T))‖
      ≤ 4 * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2)
    rw [norm_smul]
    have htri : ‖toEuclidean_fromVec (ApplyGate (evaluate (parallelOracle
          (controlOracle W))
          (envelopeDetectionWord M hM k))ᴴ
          (phaseReflectionEmbed M k (spectralTargetState v c T)) -
          phaseReflectionEmbed M k (spectralTargetState v c T))‖
        ≤ 2 * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2) := by
      calc ‖toEuclidean_fromVec (ApplyGate (evaluate (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (spectralTargetState v c T)) -
            phaseReflectionEmbed M k (spectralTargetState v c T))‖
          ≤ ‖toEuclidean_fromVec (ApplyGate (evaluate (parallelOracle (controlOracle W))
              (envelopeDetectionWord M hM k))ᴴ
              (phaseReflectionEmbed M k (spectralTargetState v c T)))‖ +
            ‖toEuclidean_fromVec
              (phaseReflectionEmbed M k (spectralTargetState v c T))‖ :=
            norm_sub_le
              (toEuclidean_fromVec (ApplyGate (evaluate (parallelOracle
                (controlOracle W))
                (envelopeDetectionWord M hM k))ᴴ
                (phaseReflectionEmbed M k (spectralTargetState v c T))))
              (toEuclidean_fromVec
                (phaseReflectionEmbed M k (spectralTargetState v c T)))
        _ = 2 * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2) := by
            rw [norm_applyGate_of_mem_unitaryGroup (adjoint_unitary hD), htnorm]
            ring
    have h2norm : ‖(2 : ℂ)‖ = 2 := by norm_num
    rw [h2norm]
    nlinarith [htri]

  have hfirst : ‖toEuclidean_fromVec (ApplyGate (evaluate (parallelOracle
        (controlOracle W))
        (envelopeDetectionWord M hM k))ᴴ
        ((2 : ℂ) • phaseReflectionEmbed M k
          (envelopeZeroBranch W M hM k (∑ j, c j • v j)
            - spectralTargetState v c T)))‖
      = 2 * ‖toEuclidean_fromVec (envelopeZeroBranch W M hM k (∑ j, c j • v j)
          - spectralTargetState v c T)‖ := by
    rw [norm_applyGate_of_mem_unitaryGroup (adjoint_unitary hD)]
    change ‖(2 : ℂ) • toEuclidean_fromVec (phaseReflectionEmbed M k
        (envelopeZeroBranch W M hM k (∑ j, c j • v j)
            - spectralTargetState v c T))‖ = _
    rw [norm_smul, phaseReflectionEmbed_norm M k hM0]
    norm_num [Complex.norm_ofNat]

  refine ⟨?_,
    (envelope_reflection_actual_queries_and_macros (I := I) M k hM).2.1,
    (envelope_reflection_actual_queries_and_macros (I := I) M k hM).2.2⟩
  calc ‖toEuclidean_fromVec (envelopeReflectionState W M hM k (∑ j, c j • v j) -
        phaseReflectionEmbed M k
          ((2 : ℂ) • spectralTargetState v c T - ∑ j, c j • v j))‖
      = ‖toEuclidean_fromVec
          (ApplyGate (evaluate (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k))ᴴ
            ((2 : ℂ) • phaseReflectionEmbed M k
              (envelopeZeroBranch W M hM k (∑ j, c j • v j)
                - spectralTargetState v c T))
            + ((2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
                (envelopeDetectionWord M hM k))ᴴ
                (phaseReflectionEmbed M k (spectralTargetState v c T)) -
              (2 : ℂ) • phaseReflectionEmbed M k (spectralTargetState v c T)))‖ :=
        by rw [herror]
    _ ≤ ‖toEuclidean_fromVec (ApplyGate (evaluate (parallelOracle (controlOracle W))
          (envelopeDetectionWord M hM k))ᴴ
          ((2 : ℂ) • phaseReflectionEmbed M k
            (envelopeZeroBranch W M hM k (∑ j, c j • v j)
              - spectralTargetState v c T)))‖
        + ‖toEuclidean_fromVec ((2 : ℂ) • ApplyGate (evaluate
            (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (spectralTargetState v c T)) -
          (2 : ℂ) • phaseReflectionEmbed M k (spectralTargetState v c T))‖ :=
        norm_add_le
          (toEuclidean_fromVec (ApplyGate (evaluate (parallelOracle
            (controlOracle W))
            (envelopeDetectionWord M hM k))ᴴ
            ((2 : ℂ) • phaseReflectionEmbed M k
              (envelopeZeroBranch W M hM k (∑ j, c j • v j)
                - spectralTargetState v c T))))
          (toEuclidean_fromVec ((2 : ℂ) • ApplyGate (evaluate
            (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (spectralTargetState v c T)) -
            (2 : ℂ) • phaseReflectionEmbed M k (spectralTargetState v c T)))
    _ = 2 * ‖toEuclidean_fromVec (envelopeZeroBranch W M hM k (∑ j, c j • v j)
          - spectralTargetState v c T)‖
        + ‖toEuclidean_fromVec ((2 : ℂ) • ApplyGate (evaluate
            (parallelOracle (controlOracle W))
            (envelopeDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (spectralTargetState v c T)) -
          (2 : ℂ) • phaseReflectionEmbed M k (spectralTargetState v c T))‖ :=
        by rw [hfirst]
    _ ≤ 2 * (clause33Contraction M η) ^ k * Real.sqrt (1 - ∑ j ∈ T, ‖c j‖ ^ 2)
        + 2 * ‖1 - (sinEnvelopeKernel M 0 (⟨0, hM0⟩ : Fin M)) ^ k‖
            * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2)
        + 4 * Real.sqrt (∑ j ∈ T, ‖c j‖ ^ 2) := by
          nlinarith [hz, hsecond]

end Qatlib.Concepts.WalkSearch.FrameSpectral
