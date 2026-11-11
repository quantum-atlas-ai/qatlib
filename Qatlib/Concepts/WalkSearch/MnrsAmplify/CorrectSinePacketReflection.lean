/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralFilterWord
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Aligned sine packet phase reflections

`alignedPhaseCircuit` prepares a sine envelope, applies controlled phase queries, and unprepares
the envelope so that zero phase gives the zero label. Repeated detection packets define
`alignedReflectionWord`; its eigenstate action and exact query and gate counts are proved
alongside the corresponding spectral superposition formulas.

The finite difference estimates for `overlapSum` give quadratic decay away from zero phase.
`frontier1` combines this decay with an orthonormal spectral decomposition to bound the
reflection error by the unmarked coefficient norm, with exact preservation of the zero phase
component. For background on search via quantum walks, see [MagniezNayakRolandSantha2011].

## Main statements

* `alignedDetectionWord_resources`: The repeated detection word is well formed and uses `k * (M
  - 1)` queries and `k * (2 * (M - 1) + 2)` explicit gates.
* `frontier1`: For an orthonormal eigenvector family with normalized coefficients, zero phase on
  `T`, and phase distance at least `η > 0` outside `T`, the aligned reflection error is at most
  `2 * (π^2 / (M^2 * η^2))^k` times the square root of the coefficient mass outside `T`. The
  reflection word has `2 * k * (M - 1)` queries and `4 * k * (M - 1) + 4 * k + 1` gates.

## References

* [Magniez et al., 2011][MagniezNayakRolandSantha2011]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxHeartbeats 800000
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.NativeNumerics.LayeredMean
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralFilter.ZeroPhaseFilter
open Qatlib.Concepts.WalkSearch.FrameSpectral
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.HhlAlgorithms.SinEnvFilter.SinEnvelopeHHL

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator
variable {I : Type} [Fintype I] [DecidableEq I]

/-- The sine envelope phase state after applying the adjoint preparation map, or the zero state
when `M < 2`. -/
noncomputable def alignedKernel (M : ℕ) (φ : ℝ) : QState (Fin M) :=
  if hM : 2 ≤ M then
    ApplyGate (sinEnvelopePrep M hM)ᴴ
      (fun τ => Complex.exp (2*Real.pi*Complex.I*((τ.val:ℝ)*φ)) * sinEnvelopeState M τ)
  else 0

/-- Prepare the sine envelope, run the phase threshold loop for `M - 1` steps, and apply the
adjoint preparation gate. -/
noncomputable def alignedPhaseCircuit (M : ℕ) (hM : 2 ≤ M) :
    Circuit (Fin M × (Bool × I)) :=
  [Step.gate (TensorGate (sinEnvelopePrep M hM)
      (1 : Matrix (Bool × I) (Bool × I) ℂ))] ++
    phaseThresholdLoop M (M-1) ++
    [Step.gate (TensorGate (sinEnvelopePrep M hM)ᴴ
      (1 : Matrix (Bool × I) (Bool × I) ℂ))]

/-- The adjoint step word obtained by converting and reversing the steps of
`alignedPhaseCircuit`. -/
noncomputable def alignedForwardWord (M : ℕ) (hM : 2 ≤ M) :
    List (AdjointStep (Fin M × (Bool × I))) :=
  ((alignedPhaseCircuit (I := I) M hM).map stepToAdjoint).reverse

/-- Every explicit gate in `alignedPhaseCircuit M hM` is unitary. -/
theorem aligned_phase_circuit_unitary (M : ℕ) (hM : 2 ≤ M) :
    IsUnitaryCircuit (alignedPhaseCircuit (I := I) M hM) := by
  intro G hG
  simp only [alignedPhaseCircuit, List.mem_append, List.mem_singleton,
    Step.gate.injEq] at hG
  rcases hG with (rfl | hG) | rfl
  · exact tensorGate_unitary (sin_envelope_state_normalized_and_prep M hM).2.1
      (Submonoid.one_mem _)
  · exact (phaseThresholdLoop_resources (I := I) M (M-1)).2.2 _ hG
  · exact tensorGate_unitary
      (adjoint_unitary (sin_envelope_state_normalized_and_prep M hM).2.1)
      (Submonoid.one_mem _)

/-- The aligned forward word has `M - 1` oracle queries and `2 * (M - 1) + 2` explicit gates. -/
theorem aligned_forward_word_counts (M : ℕ) (hM : 2 ≤ M) :
    adjointQueryCount (alignedForwardWord (I := I) M hM) = M-1 ∧
      adjointGateCount (alignedForwardWord (I := I) M hM) = 2*(M-1)+2 := by
  have ht := phaseThresholdLoop_resources (I := I) M (M-1)
  constructor
  · rw [alignedForwardWord, adjointQueryCount_reverse, adjointQueryCount_map_stepToAdjoint]
    simp [alignedPhaseCircuit, queryCount_append, QueryCount, ht.1]
  · rw [alignedForwardWord, adjointGateCount_reverse, adjointGateCount_map_stepToAdjoint]
    simp [alignedPhaseCircuit, gateCount_append, GateCount, ht.2.1]

/-- On a zero ancilla embedding of an eigenvector of `U` with phase `φ`, the aligned phase
circuit produces the corresponding `alignedKernel M φ` tensor packet with the phase flag
embedding. -/
theorem aligned_forward_eigenstate (M : ℕ) (hM : 2 ≤ M) (U : Matrix I I ℂ)
    (ψ : QState I) (φ : ℝ)
    (hψ : U *ᵥ ψ = Complex.exp (2*Real.pi*Complex.I*φ) • ψ) :
    Run (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle U))
        (alignedPhaseCircuit M hM)
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ)) =
      phaseFlagEmbed M (TensorState (alignedKernel M φ) ψ) := by
  have hi : TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) ψ) =
      phaseFlagEmbed M (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) ψ) := by
    ext p
    rcases p with ⟨x,b,i⟩
    cases b <;> simp [TensorState, phaseFlagEmbed, Qatlib.Foundations.PureStateMath.Ket]
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
  have hprep : ApplyGate (sinEnvelopePrep M hM) (Qatlib.Foundations.PureStateMath.Ket (⟨0, by omega⟩ : Fin M)) =
      sinEnvelopeState M := (sin_envelope_state_normalized_and_prep M hM).2.2
  rw [alignedPhaseCircuit, run_append, run_append, hi]
  simp only [Run]
  rw [phaseFlagEmbed_phaseGate, applyGate_tensorGate, applyGate_one,
    hprep,
    phaseThresholdLoop_action, hp, phaseFlagEmbed_phaseGate,
    applyGate_tensorGate, applyGate_one]
  simp only [alignedKernel, dif_pos hM]

/-- Relabeling a matrix commutes with taking its conjugate transpose. -/
private theorem aligned_relabel_adjoint {H K : Type} (e : H ≃ K)
    (U : Matrix H H ℂ) : (relabelGate e U)ᴴ = relabelGate e Uᴴ := by
  ext i j
  rfl

omit [Fintype I] in

/-- The aligned forward word equals the phase compiler output for `alignedPhaseCircuit`. -/
theorem alignedForwardWord_eq_compile (M : ℕ) (hM : 2 ≤ M) :
    alignedForwardWord (I := I) M hM =
      phaseCompileCircuit (alignedPhaseCircuit (I := I) M hM) := by
  have hmap : (alignedPhaseCircuit (I := I) M hM).map stepToAdjoint =
      (alignedPhaseCircuit (I := I) M hM).map phaseForwardStep :=
    List.map_congr_left fun s _ => by cases s <;> rfl
  simp only [alignedForwardWord, phaseCompileCircuit, hmap]
  exact List.map_reverse.symm

/-- The compiled aligned forward word satisfies `WellFormedAdjointCircuit`. -/
theorem alignedForwardWord_wellFormed (M : ℕ) (hM : 2 ≤ M) :
    WellFormedAdjointCircuit (alignedForwardWord (I := I) M hM) := by
  rw [alignedForwardWord_eq_compile M hM]
  exact phaseCompileCircuit_wellFormed (aligned_phase_circuit_unitary (I := I) M hM)

/-- Lifting the identity matrix to the tail registers gives the identity matrix. -/
private theorem alignedTailGate_one (M k : ℕ) :
    phaseTailGate (I := I) M k 1 = 1 := by
  rw [phaseTailGate, tensorGate_one, CircuitRelabel.relabelGate_one]

/-- The tail register gate lift preserves matrix multiplication. -/
private theorem alignedTailGate_mul (M k : ℕ)
    (U V : Matrix (PhaseReflectionSpace I M k) (PhaseReflectionSpace I M k) ℂ) :
    phaseTailGate (I := I) M k (U * V) =
      phaseTailGate (I := I) M k U * phaseTailGate (I := I) M k V := by
  unfold phaseTailGate
  rw [← CircuitRelabel.relabelGate_mul, tensorGate_mul, Matrix.one_mul]

/-- The tail register gate lift commutes with conjugate transpose. -/
private theorem alignedTailGate_adjoint (M k : ℕ)
    (U : Matrix (PhaseReflectionSpace I M k) (PhaseReflectionSpace I M k) ℂ) :
    phaseTailGate (I := I) M k Uᴴ = (phaseTailGate (I := I) M k U)ᴴ := by
  rw [phaseTailGate, phaseTailGate, aligned_relabel_adjoint,
    tensorGate_conjTranspose, Matrix.conjTranspose_one]

/-- Lifting the identity matrix to the head register gives the identity matrix. -/
private theorem alignedHeadGate_one (M k : ℕ) :
    phaseHeadGate (I := I) M k 1 = 1 := by
  rw [phaseHeadGate, tensorGate_one, CircuitRelabel.relabelGate_one]

/-- The head register gate lift preserves matrix multiplication. -/
private theorem alignedHeadGate_mul (M k : ℕ)
    (U V : Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ) :
    phaseHeadGate (I := I) M k (U * V) =
      phaseHeadGate (I := I) M k U * phaseHeadGate (I := I) M k V := by
  unfold phaseHeadGate
  rw [← CircuitRelabel.relabelGate_mul, tensorGate_mul, Matrix.one_mul]

/-- The head register gate lift commutes with conjugate transpose. -/
private theorem alignedHeadGate_adjoint (M k : ℕ)
    (U : Matrix (Fin M × (Bool × I)) (Fin M × (Bool × I)) ℂ) :
    phaseHeadGate (I := I) M k Uᴴ = (phaseHeadGate (I := I) M k U)ᴴ := by
  rw [phaseHeadGate, phaseHeadGate, aligned_relabel_adjoint,
    tensorGate_conjTranspose, Matrix.conjTranspose_one]

/-- Two functions on `Fin (k + 1)` are equal exactly when their values at zero and their
restrictions to successor indices agree. -/
private theorem aligned_function_eq_iff (M k : ℕ) (x y : Fin (k + 1) → Fin M) :
    x = y ↔ x 0 = y 0 ∧ (fun j : Fin k => x j.succ) = (fun j : Fin k => y j.succ) := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h0, ht⟩
    funext i
    exact Fin.cases h0 (fun j => congrFun ht j) i

omit [Fintype I] [DecidableEq I] in

/-- Lifting the parallel oracle on the tail registers yields the parallel oracle on all `k + 1`
registers. -/
private theorem alignedTailGate_oracle (M k : ℕ)
    (A : Matrix (Bool × I) (Bool × I) ℂ) :
    phaseTailGate (I := I) M k (parallelOracle (J := Fin k → Fin M) A) =
      parallelOracle (J := Fin (k + 1) → Fin M) A := by
  ext ⟨x, d⟩ ⟨y, e⟩
  simp only [phaseTailGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, phaseTailSplit, TensorGate, parallelOracle, select, Matrix.of_apply]
  by_cases hh : x 0 = y 0 <;>
    by_cases ht : (fun j : Fin k => x j.succ) = (fun j : Fin k => y j.succ)
  · have hxy := (aligned_function_eq_iff M k x y).mpr ⟨hh, ht⟩
    simp [hxy]
  · have hxy : x ≠ y := fun h => ht ((aligned_function_eq_iff M k x y).mp h).2
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((aligned_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((aligned_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]

omit [Fintype I] [DecidableEq I] in

/-- Lifting the parallel oracle on the head register yields the parallel oracle on all `k + 1`
registers. -/
private theorem alignedHeadGate_oracle (M k : ℕ)
    (A : Matrix (Bool × I) (Bool × I) ℂ) :
    phaseHeadGate (I := I) M k (parallelOracle (J := Fin M) A) =
      parallelOracle (J := Fin (k + 1) → Fin M) A := by
  ext ⟨x, d⟩ ⟨y, e⟩
  simp only [phaseHeadGate, relabelGate, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, phaseHeadSplit, Equiv.trans_apply, phaseTailSplit, TensorGate,
    parallelOracle, select, Matrix.of_apply]
  by_cases hh : x 0 = y 0 <;>
    by_cases ht : (fun j : Fin k => x j.succ) = (fun j : Fin k => y j.succ)
  · have hxy := (aligned_function_eq_iff M k x y).mpr ⟨hh, ht⟩
    simp [hxy]
  · have hxy : x ≠ y := fun h => ht ((aligned_function_eq_iff M k x y).mp h).2
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((aligned_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]
  · have hxy : x ≠ y := fun h => hh ((aligned_function_eq_iff M k x y).mp h).1
    simp [hh, ht, hxy]

/-- Recursively combine lifted aligned forward words to perform detection on `k` phase
registers. -/
noncomputable def alignedDetectionWord (M : ℕ) (hM : 2 ≤ M) : (k : ℕ) →
    List (AdjointStep (PhaseReflectionSpace I M k))
  | 0 => []
  | k + 1 =>
      phaseLiftWord (phaseTailGate M k) (alignedDetectionWord M hM k) ++
        phaseLiftWord (phaseHeadGate M k) (alignedForwardWord (I := I) M hM)

/-- The repeated detection word is well formed and uses `k * (M - 1)` queries and `k * (2 * (M -
1) + 2)` explicit gates. -/
theorem alignedDetectionWord_resources (M k : ℕ) (hM : 2 ≤ M) :
    WellFormedAdjointCircuit (alignedDetectionWord (I := I) M hM k) ∧
      adjointQueryCount (alignedDetectionWord (I := I) M hM k) = k * (M - 1) ∧
      adjointGateCount (alignedDetectionWord (I := I) M hM k) = k * (2 * (M - 1) + 2) := by
  have hsingle := aligned_forward_word_counts (I := I) M hM
  have hw : WellFormedAdjointCircuit (alignedForwardWord (I := I) M hM) :=
    alignedForwardWord_wellFormed (I := I) M hM
  induction k with
  | zero =>
    exact ⟨WellFormedAdjointCircuit.nil, by simp [alignedDetectionWord, adjointQueryCount],
      by simp [alignedDetectionWord, adjointGateCount]⟩
  | succ k ih =>
    have htail : WellFormedAdjointCircuit
        (phaseLiftWord (phaseTailGate (I := I) M k) (alignedDetectionWord M hM k)) :=
      phaseLiftWord_wellFormed _ (fun U hU =>
        (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary (by simp) hU)) ih.1
    have hhead : WellFormedAdjointCircuit
        (phaseLiftWord (phaseHeadGate (I := I) M k) (alignedForwardWord (I := I) M hM)) :=
      phaseLiftWord_wellFormed _ (fun U hU =>
        (relabelGate_mem_unitaryGroup _ _).mpr (tensorGate_unitary (by simp) hU)) hw
    refine ⟨htail.append hhead, ?_, ?_⟩
    · rw [alignedDetectionWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append,
        (phaseLiftWord_counts _ _).1,
        (phaseLiftWord_counts _ _).1, ih.2.1, hsingle.1]
      ring
    · rw [alignedDetectionWord, Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append,
        (phaseLiftWord_counts _ _).2,
        (phaseLiftWord_counts _ _).2, ih.2.2, hsingle.2]
      ring

/-- The evaluated detection word on `k + 1` registers is the product of the lifted tail
detection matrix and the lifted head forward matrix. -/
theorem alignedDetectionWord_evaluate_succ (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) :
    evaluate (parallelOracle (controlOracle W)) (alignedDetectionWord M hM (k + 1)) =
      phaseTailGate (I := I) M k
        (evaluate (parallelOracle (controlOracle W)) (alignedDetectionWord M hM k)) *
      phaseHeadGate (I := I) M k
        (evaluate (parallelOracle (controlOracle W)) (alignedForwardWord (I := I) M hM)) := by
  have ht := phaseLiftWord_evaluate (phaseTailGate (I := I) M k)
    (alignedTailGate_one M k) (alignedTailGate_mul M k) (alignedTailGate_adjoint M k)
    (parallelOracle (controlOracle W)) (alignedDetectionWord M hM k)
  have hh := phaseLiftWord_evaluate (phaseHeadGate (I := I) M k)
    (alignedHeadGate_one M k) (alignedHeadGate_mul M k) (alignedHeadGate_adjoint M k)
    (parallelOracle (controlOracle W)) (alignedForwardWord (I := I) M hM)
  rw [alignedTailGate_oracle M k (controlOracle W)] at ht
  rw [alignedHeadGate_oracle M k (controlOracle W)] at hh
  rw [alignedDetectionWord, evaluate_append, ht, hh]

/-- The product of `k` aligned phase kernels with the system state `v`, supported on the false
flag. -/
noncomputable def alignedKernelPacket (M k : ℕ) (φ : ℝ) (v : QState I) :
    QState (PhaseReflectionSpace I M k) :=
  fun p => (∏ j : Fin k, alignedKernel M φ (p.1 j)) * (if p.2.1 then 0 else v p.2.2)

omit [Fintype I] [DecidableEq I] in

/-- Relabeling the tensor product of one aligned kernel and a `k` register packet gives the
packet on `k + 1` registers. -/
private theorem alignedKernelPacket_succ (M k : ℕ) (φ : ℝ) (v : QState I) :
    relabelState (phaseTailSplit I M k).symm
      (TensorState (alignedKernel M φ) (alignedKernelPacket M k φ v)) =
        alignedKernelPacket M (k + 1) φ v := by
  funext ⟨x, b, i⟩
  dsimp [relabelState, phaseTailSplit, TensorState, alignedKernelPacket]
  rw [Fin.prod_univ_succ]
  ring

/-- The distinguished zero phase register index equals `x` exactly when every coordinate of `x`
has value zero. -/
private theorem aligned_zero_predicate (M k : ℕ) (hM : 0 < M) (x : Fin k → Fin M) :
    phaseZeroIndex M k hM = x ↔ ∀ j, (x j).val = 0 := by
  constructor
  · intro h j
    exact (congrArg Fin.val (congrFun h j)).symm
  · intro h
    funext j
    exact Fin.ext (by simp only [phaseZeroIndex]; exact (h j).symm)

omit [Fintype I] [DecidableEq I] in

/-- The zero phase register embedding on `k + 1` registers is the relabeled tensor product of
the zero tail index, zero head label, false flag, and system state. -/
private theorem aligned_embed_head_split (M k : ℕ) (hM : 0 < M) (v : QState I) :
    phaseReflectionEmbed M (k + 1) v =
      relabelState (phaseHeadSplit I M k).symm
        (TensorState (Qatlib.Foundations.PureStateMath.Ket (phaseZeroIndex M k hM))
          (TensorState (Qatlib.Foundations.PureStateMath.Ket (⟨0, hM⟩ : Fin M)) (TensorState (Qatlib.Foundations.PureStateMath.Ket false) v))) := by
  rw [phaseReflectionEmbed_tensor M (k + 1) hM]
  funext ⟨x, b, i⟩
  have hx := aligned_function_eq_iff M k x (phaseZeroIndex M (k + 1) hM)
  simp only [phaseZeroIndex] at hx
  dsimp [relabelState, phaseHeadSplit, phaseTailSplit, TensorState,
    Qatlib.Foundations.PureStateMath.Ket, phaseZeroIndex]
  by_cases hh : x 0 = (⟨0, hM⟩ : Fin M) <;>
    by_cases ht : (fun j : Fin k => x j.succ) = (fun _ => (⟨0, hM⟩ : Fin M)) <;>
    simp [hx, hh, ht] <;> first
    | rw [if_pos (show (fun _ : Fin k => (⟨0, hM⟩ : Fin M)) = phaseZeroIndex M k hM from rfl)]
    | (intro _ he; exact (ht he).elim)

/-- On an embedded eigenvector of `W`, the lifted head forward word replaces the zero head label
by its aligned phase kernel while the tail labels remain zero. -/
private theorem aligned_head_eigen (M k : ℕ) (hM : 2 ≤ M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ)
    (hv : W *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    ApplyGate (phaseHeadGate M k
        (evaluate (parallelOracle (controlOracle W))
          (alignedForwardWord (I := I) M hM)))
      (phaseReflectionEmbed M (k + 1) v) =
    relabelState (phaseTailSplit I M k).symm
      (TensorState (alignedKernel M φ) (phaseReflectionEmbed M k v)) := by
  rw [phaseHeadGate, aligned_embed_head_split M k (by omega) v, applyGate_relabelGate,
    applyGate_tensorGate, applyGate_one, alignedForwardWord_eq_compile M hM,
    phaseCompileCircuit_evaluate,
    show parallelOracle (J := Fin M) (controlOracle W) =
      TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) (controlOracle W) from
      parallelOracle_eq_kronecker _,
    aligned_forward_eigenstate M hM W v φ hv,
    phaseReflectionEmbed_tensor M k (by omega)]
  funext ⟨x, b, i⟩
  cases b <;>
    simp [relabelState, phaseHeadSplit, phaseTailSplit, TensorState,
      Qatlib.Foundations.PureStateMath.Ket, phaseFlagEmbed]

/-- On the zero register embedding of an eigenvector with phase `φ`, the evaluated repeated
detection word produces `alignedKernelPacket M k φ v`. -/
theorem alignedDetectionWord_eigenstate (M k : ℕ) (hM : 2 ≤ M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ)
    (hv : W *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    ApplyGate (evaluate (parallelOracle (controlOracle W)) (alignedDetectionWord M hM k))
      (phaseReflectionEmbed M k v) = alignedKernelPacket M k φ v := by
  induction k with
  | zero =>
    simp only [alignedDetectionWord, evaluate, applyGate_one]
    funext ⟨x, b, i⟩
    cases b <;> simp [phaseReflectionEmbed, alignedKernelPacket]
  | succ k ih =>
    rw [alignedDetectionWord_evaluate_succ W M k hM, applyGate_mul,
      aligned_head_eigen M k hM W v φ hv, phaseTailGate, applyGate_relabelGate,
      applyGate_tensorGate, applyGate_one, ih, alignedKernelPacket_succ]

/-- Projecting the kernel packet onto the zero phase event gives the zero register embedding
scaled by the `k`th power of the aligned kernel's zero amplitude. -/
private theorem alignedKernelPacket_project_zero (M k : ℕ) (hM : 0 < M) (φ : ℝ)
    (v : QState I) :
    ApplyGate (Projector (phaseZeroEvent M k)) (alignedKernelPacket M k φ v) =
      (alignedKernel M φ (⟨0, hM⟩ : Fin M)) ^ k • phaseReflectionEmbed M k v := by
  change Collapse (alignedKernelPacket M k φ v) (phaseZeroEvent M k) = _
  funext ⟨x, b, i⟩
  by_cases hx : ∀ j, (x j).val = 0
  · have he := (aligned_zero_predicate M k hM x).mpr hx
    subst x
    cases b <;> simp [collapse_apply, phaseZeroEvent, alignedKernelPacket,
      phaseReflectionEmbed, phaseZeroIndex]
  · cases b <;> simp [collapse_apply, phaseZeroEvent, phaseReflectionEmbed, hx]

/-- The adjoint detection word, zero event reflection gate, and forward detection word
concatenated in the order used by the evaluation convention. -/
noncomputable def alignedReflectionWord (M : ℕ) (hM : 2 ≤ M) (k : ℕ) :
    List (AdjointStep (PhaseReflectionSpace I M k)) :=
  adjointCircuit (alignedDetectionWord M hM k) ++ [.gate (phaseZeroReflection M k)] ++
    alignedDetectionWord M hM k

/-- The aligned reflection word is well formed and has exactly `2 * k * (M - 1)` queries and `4
* k * (M - 1) + 4 * k + 1` explicit gates. -/
theorem aligned_reflection_actual_queries_and_macros (M k : ℕ) (hM : 2 ≤ M) :
    WellFormedAdjointCircuit (alignedReflectionWord (I := I) M hM k) ∧
      adjointQueryCount (alignedReflectionWord (I := I) M hM k) = 2 * k * (M - 1) ∧
      adjointGateCount (alignedReflectionWord (I := I) M hM k) =
        4 * k * (M - 1) + 4 * k + 1 := by
  obtain ⟨hw, hq, hg⟩ := alignedDetectionWord_resources (I := I) M k hM
  have hz : WellFormedAdjointCircuit
      ([.gate (phaseZeroReflection (I := I) M k)] :
        List (AdjointStep (PhaseReflectionSpace I M k))) := by
    simp only [WellFormedAdjointCircuit.gate_cons_iff, WellFormedAdjointCircuit.nil, and_true]
    exact reflectionAbout_unitary (projector_isOrthogonalProjector _)
  refine ⟨(hw.adjointCircuit.append hz).append hw, ?_, ?_⟩
  · simp only [alignedReflectionWord,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointQueryCount_append,
      adjointQueryCount_adjointCircuit, adjointQueryCount, hq]
    ring
  · simp only [alignedReflectionWord,
      Qatlib.Concepts.CoherentSim.CoherentOAA.adjointGateCount_append,
      adjointGateCount_adjointCircuit, adjointGateCount, hg]
    ring

/-- Apply the evaluated aligned reflection word to the zero phase register embedding of the
input system state. -/
noncomputable def alignedReflectionState (W : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M)
    (k : ℕ) (ψ : QState I) : QState (PhaseReflectionSpace I M k) :=
  ApplyGate (evaluate (parallelOracle (controlOracle W)) (alignedReflectionWord M hM k))
    (phaseReflectionEmbed M k ψ)

/-- For a unitary `W` and an eigenvector of phase `φ`, the reflection output plus the input
embedding equals inverse detection applied to twice the zero embedding scaled by the zero
kernel amplitude to power `k`. -/
theorem aligned_reflection_eigenstate_residual (M k : ℕ) (hM : 2 ≤ M)
    (W : Matrix I I ℂ) (v : QState I) (φ : ℝ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : W *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    alignedReflectionState W M hM k v + phaseReflectionEmbed M k v =
      ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
        ((2 : ℂ) • ((alignedKernel M φ (⟨0, by omega⟩ : Fin M)) ^ k •
          phaseReflectionEmbed M k v)) := by
  have hD : (evaluate (parallelOracle (controlOracle W))
      (alignedDetectionWord (I := I) M hM k)) ∈
      Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (alignedDetectionWord_resources M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  have hcancel : ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
      (ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k)) (phaseReflectionEmbed M k v)) =
      phaseReflectionEmbed M k v := by
    rw [← applyGate_mul,
      show (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ *
        (evaluate (parallelOracle (controlOracle W))
          (alignedDetectionWord M hM k)) = 1 by
        simpa only [Matrix.star_eq_conjTranspose] using! hD.1, applyGate_one]
  have hstate : alignedReflectionState W M hM k v =
      ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
      (ApplyGate (phaseZeroReflection M k)
        (ApplyGate (evaluate (parallelOracle (controlOracle W))
          (alignedDetectionWord M hM k)) (phaseReflectionEmbed M k v))) := by
    simp only [alignedReflectionState, alignedReflectionWord, evaluate_append,
      evaluate_adjointCircuit, evaluate, instructionMatrix, Matrix.mul_one,
      applyGate_mul]
  have hlin : ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
      ((2 : ℂ) • ApplyGate (Projector (phaseZeroEvent M k))
          (ApplyGate (evaluate (parallelOracle (controlOracle W))
            (alignedDetectionWord M hM k)) (phaseReflectionEmbed M k v)) -
        ApplyGate (evaluate (parallelOracle (controlOracle W))
          (alignedDetectionWord M hM k)) (phaseReflectionEmbed M k v)) =
      (2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
        (ApplyGate (Projector (phaseZeroEvent M k))
          (ApplyGate (evaluate (parallelOracle (controlOracle W))
            (alignedDetectionWord M hM k)) (phaseReflectionEmbed M k v))) -
        phaseReflectionEmbed M k v := by
    simp only [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_smul] at hcancel ⊢
    rw [hcancel]
  rw [hstate, phaseZeroReflection, applyGate_reflectionAbout, hlin]
  have hforward := alignedDetectionWord_eigenstate M k hM W v φ hv
  change ApplyGate (evaluate (parallelOracle (controlOracle W))
      (alignedDetectionWord M hM k)) (phaseReflectionEmbed M k v) =
    alignedKernelPacket M k φ v at hforward
  rw [hforward, alignedKernelPacket_project_zero M k (by omega)]
  simp only [ApplyGate, Matrix.mulVec_smul]
  module

/-- For an eigenvector of unitary `W`, the Euclidean norm of the reflection output plus its
embedding is at most twice the `k`th power of the zero kernel amplitude norm times the
vector norm. -/
theorem aligned_reflection_eigenstate_error (M k : ℕ) (hM : 2 ≤ M)
    (W : Matrix I I ℂ) (v : QState I) (φ : ℝ) (hW : W ∈ Matrix.unitaryGroup I ℂ)
    (hv : W *ᵥ v = Complex.exp (2 * Real.pi * Complex.I * φ) • v) :
    ‖toEuclidean_fromVec (alignedReflectionState W M hM k v +
      phaseReflectionEmbed M k v)‖ ≤
      2 * ‖alignedKernel M φ (⟨0, by omega⟩ : Fin M)‖ ^ k *
        ‖toEuclidean_fromVec v‖ := by
  have hD : (evaluate (parallelOracle (controlOracle W))
      (alignedDetectionWord (I := I) M hM k)) ∈
      Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (alignedDetectionWord_resources M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  rw [aligned_reflection_eigenstate_residual M k hM W v φ hW hv,
    norm_applyGate_of_mem_unitaryGroup (adjoint_unitary hD)]
  change ‖(2 : ℂ) • ((alignedKernel M φ (⟨0, by omega⟩ : Fin M)) ^ k •
    toEuclidean_fromVec (phaseReflectionEmbed M k v))‖ ≤ _
  rw [norm_smul, norm_smul, norm_pow, phaseReflectionEmbed_norm M k (by omega)]
  norm_num [mul_assoc]

/-- Apply the evaluated repeated detection word to the zero phase register embedding of the
input system state. -/
noncomputable def alignedDetectionState (W : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M)
    (k : ℕ) (ψ : QState I) : QState (PhaseReflectionSpace I M k) :=
  ApplyGate (evaluate (parallelOracle (controlOracle W)) (alignedDetectionWord M hM k))
    (phaseReflectionEmbed M k ψ)

/-- Read the amplitudes of `alignedDetectionState` with all phase labels zero and the flag false
as a system state. -/
noncomputable def alignedZeroBranch (W : Matrix I I ℂ) (M : ℕ) (hM : 2 ≤ M)
    (k : ℕ) (ψ : QState I) : QState I :=
  fun i => alignedDetectionState W M hM k ψ (phaseZeroIndex M k (by omega), (false, i))

/-- Detection of a finite eigenvector superposition is the corresponding superposition of
aligned packets, and its zero branch multiplies each coefficient by the `k`th power of that
eigenphase's zero kernel amplitude. -/
theorem aligned_phase_actual_spectral_packet
    (J : Type) [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j) :
    alignedDetectionState W M hM k (∑ j, c j • v j) =
        ∑ j, c j • alignedKernelPacket M k (φ j) (v j) ∧
      alignedZeroBranch W M hM k (∑ j, c j • v j) =
        ∑ j, (c j * (alignedKernel M (φ j) (⟨0, by omega⟩ : Fin M)) ^ k) • v j := by
  have hd : alignedDetectionState W M hM k (∑ j, c j • v j) =
      ∑ j, c j • alignedKernelPacket M k (φ j) (v j) := by
    let L := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
      (alignedDetectionWord (I := I) M hM k))).comp (degenerateEmbedLinear M k)
    change L (∑ j, c j • v j) = _
    rw [map_sum]
    simp only [map_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    exact congrArg (c j • ·) (alignedDetectionWord_eigenstate M k hM W (v j) (φ j) (he j))
  refine ⟨hd, ?_⟩
  funext i
  simp [alignedZeroBranch, hd, alignedKernelPacket, phaseZeroIndex,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_assoc]

end Qatlib.Concepts.WalkSearch.MnrsAmplify

namespace Qatlib.Concepts.WalkSearch.MnrsAmplify.CorrectSinePacketReflection
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- A finite weighted geometric sum multiplied by `1 - z` equals its two endpoint terms plus a
geometric sum of first differences. -/
theorem weighted_first_diff (w : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, w i * z ^ i) * (1-z) =
      w 0 - w (n-1) * z^n +
        z * ∑ i ∈ Finset.range (n-1), (w (i+1)-w i) * z^i := by
  have h := Finset.sum_range_by_parts w (fun i => z ^ i) n
  simp only [smul_eq_mul] at h
  rw [h, sub_mul, mul_assoc, geom_sum_mul_neg, Finset.sum_mul]
  simp_rw [mul_assoc, geom_sum_mul_neg, mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, Finset.sum_range_sub]
  simp_rw [pow_succ]
  rw [show (∑ i ∈ Finset.range (n-1), (w (i+1)-w i) * (z^i*z)) =
      z * (∑ i ∈ Finset.range (n-1), (w (i+1)-w i) * z^i) by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring]
  ring

/-- The forward difference `w (i + 1) - w i` of a complex sequence. -/
def nextDiff (w : ℕ → ℂ) (i : ℕ) : ℂ := w (i+1)-w i

/-- Multiplying a finite weighted geometric sum by `(1 - z)^2` expresses it through endpoint
values, endpoint first differences, and a sum of second differences. -/
theorem weighted_second_diff (w : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range n, w i * z ^ i) * (1-z)^2 =
      (w 0-w (n-1)*z^n)*(1-z) +
        z * (nextDiff w 0 - nextDiff w ((n-1)-1)*z^(n-1) +
          z * ∑ i ∈ Finset.range ((n-1)-1), nextDiff (nextDiff w) i * z^i) := by
  calc
    _ = ((∑ i ∈ Finset.range n, w i * z ^ i) * (1-z))*(1-z) := by ring
    _ = (w 0-w (n-1)*z^n)*(1-z) +
        z * ((∑ i ∈ Finset.range (n-1), nextDiff w i * z^i)*(1-z)) := by
          rw [weighted_first_diff]
          simp only [nextDiff]
          ring
    _ = _ := by rw [weighted_first_diff]; rfl

/-- For `‖z‖ = 1`, bound the weighted geometric sum times `‖1 - z‖^2` by endpoint norms,
endpoint first difference norms, and the sum of second difference norms. -/
theorem weighted_second_diff_bound (w : ℕ → ℂ) (z : ℂ) (n : ℕ) (hz : ‖z‖ = 1) :
    ‖(∑ i ∈ Finset.range n, w i * z ^ i)‖ * ‖1-z‖^2 ≤
      (‖w 0‖ + ‖w (n-1)‖)*‖1-z‖ +
        ‖nextDiff w 0‖ + ‖nextDiff w ((n-1)-1)‖ +
          ∑ i ∈ Finset.range ((n-1)-1), ‖nextDiff (nextDiff w) i‖ := by
  have hsum : ‖∑ i ∈ Finset.range ((n-1)-1), nextDiff (nextDiff w) i * z^i‖ ≤
      ∑ i ∈ Finset.range ((n-1)-1), ‖nextDiff (nextDiff w) i‖ := by
    calc
      _ ≤ ∑ i ∈ Finset.range ((n-1)-1), ‖nextDiff (nextDiff w) i * z^i‖ :=
        norm_sum_le _ _
      _ = _ := by simp [norm_pow, hz]
  have hA : ‖(w 0-w (n-1)*z^n)*(1-z)‖ ≤
      (‖w 0‖ + ‖w (n-1)‖)*‖1-z‖ := by
    rw [norm_mul]
    gcongr
    simpa [norm_pow, hz] using! norm_sub_le (w 0) (w (n-1)*z^n)
  have hB : ‖z * (nextDiff w 0 - nextDiff w ((n-1)-1)*z^(n-1) +
      z * ∑ i ∈ Finset.range ((n-1)-1), nextDiff (nextDiff w) i * z^i)‖ ≤
      ‖nextDiff w 0‖ + ‖nextDiff w ((n-1)-1)‖ +
        ∑ i ∈ Finset.range ((n-1)-1), ‖nextDiff (nextDiff w) i‖ := by
    simp only [norm_mul, hz, one_mul]
    calc
      _ ≤ ‖nextDiff w 0 - nextDiff w ((n-1)-1)*z^(n-1)‖ +
          ‖z * ∑ i ∈ Finset.range ((n-1)-1), nextDiff (nextDiff w) i * z^i‖ :=
        norm_add_le _ _
      _ ≤ (‖nextDiff w 0‖ + ‖nextDiff w ((n-1)-1)‖) +
          ∑ i ∈ Finset.range ((n-1)-1), ‖nextDiff (nextDiff w) i‖ := by
        apply add_le_add
        · simpa [norm_mul, norm_pow, hz] using!
            norm_sub_le (nextDiff w 0) (nextDiff w ((n-1)-1)*z^(n-1))
        · simpa [norm_mul, hz] using! hsum
  calc
    _ = ‖(∑ i ∈ Finset.range n, w i*z^i)*(1-z)^2‖ := by rw [norm_mul,norm_pow]
    _ = _ := congrArg norm (weighted_second_diff w z n)
    _ ≤ ‖(w 0-w (n-1)*z^n)*(1-z)‖ +
        ‖z * (nextDiff w 0 - nextDiff w ((n-1)-1)*z^(n-1) +
          z * ∑ i ∈ Finset.range ((n-1)-1), nextDiff (nextDiff w) i*z^i)‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- The second difference of squared sine with step `h` equals `2 * sin(h)^2 * cos(2 * (x +
h))`. -/
theorem sin_sq_second_diff_identity (x h : ℝ) :
    Real.sin (x+2*h)^2-2*Real.sin (x+h)^2+Real.sin x^2 =
      2*Real.sin h^2*Real.cos (2*(x+h)) := by
  rw [Real.sin_sq_eq_half_sub (x+2*h), Real.sin_sq_eq_half_sub (x+h),
    Real.sin_sq_eq_half_sub x, Real.sin_sq_eq_half_sub h]
  rw [show 2*(x+2*h)=2*(x+h)+2*h by ring,
    show 2*x=2*(x+h)-2*h by ring, Real.cos_add, Real.cos_sub]
  ring

/-- The absolute second difference of squared sine with step `h` is at most `2 * h^2`. -/
theorem sin_sq_second_diff_bound (x h : ℝ) :
    |Real.sin (x+2*h)^2-2*Real.sin (x+h)^2+Real.sin x^2| ≤ 2*h^2 := by
  rw [sin_sq_second_diff_identity, abs_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0:ℝ)≤2), abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ 2*Real.sin h^2*1 :=
      mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (by positivity)
    _ ≤ 2*h^2 := by nlinarith only [Real.sin_sq_le_sq (x := h)]

/-- For `2 ≤ M`, `|sin (π / (2 * M))| ≤ π / (2 * M)`. -/
theorem sin_half_endpoint_bound (M : ℕ) (hM : 2 ≤ M) :
    |Real.sin (Real.pi/(2*(M:ℝ)))| ≤ Real.pi/(2*(M:ℝ)) := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  simpa only [abs_of_pos (by positivity : (0:ℝ)<Real.pi/(2*(M:ℝ)))] using!
    (Real.abs_sin_le_abs (x := Real.pi/(2*(M:ℝ))))

/-- The real weight `(2 / M) * sin (π * (n + 1 / 2) / M)^2` of the sine envelope at index `n`. -/
noncomputable def sineWeight (M n : ℕ) : ℝ :=
  (2/(M:ℝ))*Real.sin (Real.pi*((n:ℝ)+1/2)/(M:ℝ))^2

/-- The unit complex phase `exp (2 * π * I * φ)`. -/
noncomputable def phaseUnit (φ : ℝ) : ℂ := Complex.exp (2*Real.pi*Complex.I*φ)

/-- The finite geometric sum of the sine weights against powers of `phaseUnit φ` over indices
below `M`. -/
noncomputable def overlapSum (M : ℕ) (φ : ℝ) : ℂ :=
  ∑ n ∈ Finset.range M, (sineWeight M n : ℂ) * (phaseUnit φ)^n

/-- The complex phase `phaseUnit φ` has norm one. -/
theorem phaseUnit_norm (φ : ℝ) : ‖phaseUnit φ‖ = 1 := by
  simp [phaseUnit, Complex.norm_exp, Complex.mul_re]

/-- Every sine envelope weight is nonnegative. -/
theorem sineWeight_nonneg (M n : ℕ) : 0 ≤ sineWeight M n := by
  unfold sineWeight
  positivity

/-- For `2 ≤ M`, the first sine weight is at most `π^2 / (2 * M^3)`. -/
theorem sineWeight_zero_bound (M : ℕ) (hM : 2 ≤ M) :
    sineWeight M 0 ≤ Real.pi^2/(2*(M:ℝ)^3) := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  unfold sineWeight
  simp only [Nat.cast_zero]
  calc
    _ ≤ (2/(M:ℝ))*(Real.pi*((0:ℝ)+1/2)/(M:ℝ))^2 :=
      mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x := Real.pi*((0:ℝ)+1/2)/(M:ℝ)))
        (by positivity)
    _ = Real.pi^2/(2*(M:ℝ)^3) := by field_simp; ring

/-- For `2 ≤ M`, the sine weight at index one is at most `9 * π^2 / (2 * M^3)`. -/
theorem sineWeight_one_bound (M : ℕ) (hM : 2 ≤ M) :
    sineWeight M 1 ≤ 9*Real.pi^2/(2*(M:ℝ)^3) := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  unfold sineWeight
  simp only [Nat.cast_one]
  calc
    _ ≤ (2/(M:ℝ))*(Real.pi*((1:ℝ)+1/2)/(M:ℝ))^2 :=
      mul_le_mul_of_nonneg_left (Real.sin_sq_le_sq (x := Real.pi*((1:ℝ)+1/2)/(M:ℝ)))
        (by positivity)
    _ = 9*Real.pi^2/(2*(M:ℝ)^3) := by field_simp; ring

/-- For `n < M`, the sine weight at the reversed index `M - 1 - n` equals the weight at `n`. -/
theorem sineWeight_reverse (M n : ℕ) (hn : n<M) :
    sineWeight M (M-1-n) = sineWeight M n := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hc : ((M-1-n:ℕ):ℝ) = (M:ℝ)-1-(n:ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    norm_num
  unfold sineWeight
  rw [hc, show Real.pi*((M:ℝ)-1-(n:ℝ)+1/2)/(M:ℝ) =
      Real.pi-Real.pi*((n:ℝ)+1/2)/(M:ℝ) by field_simp; ring,
    Real.sin_pi_sub]

/-- For `2 ≤ M`, the absolute second difference of the sine weights is at most `4 * π^2 / M^3`. -/
theorem sineWeight_second_bound (M n : ℕ) (hM : 2 ≤ M) :
    |sineWeight M (n+2)-2*sineWeight M (n+1)+sineWeight M n| ≤
      4*Real.pi^2/(M:ℝ)^3 := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  let x := Real.pi*((n:ℝ)+1/2)/(M:ℝ)
  let h := Real.pi/(M:ℝ)
  have ha : Real.pi*((n+2:ℕ)+1/2)/(M:ℝ) = x+2*h := by
    dsimp [x,h]; push_cast; ring
  have hb : Real.pi*((n+1:ℕ)+1/2)/(M:ℝ) = x+h := by
    dsimp [x,h]; push_cast; ring
  have he : sineWeight M (n+2)-2*sineWeight M (n+1)+sineWeight M n =
      (2/(M:ℝ))*(Real.sin (x+2*h)^2-2*Real.sin (x+h)^2+Real.sin x^2) := by
    simp only [sineWeight,ha,hb]; dsimp [x]; ring
  rw [he,abs_mul,abs_of_nonneg (by positivity : (0:ℝ)≤2/(M:ℝ))]
  calc
    _ ≤ (2/(M:ℝ))*(2*h^2) :=
      mul_le_mul_of_nonneg_left (sin_sq_second_diff_bound x h) (by positivity)
    _ = _ := by dsimp [h]; field_simp; ring

/-- The complex norm of a sine weight equals its real value. -/
theorem sineWeight_norm (M n : ℕ) : ‖(sineWeight M n : ℂ)‖ = sineWeight M n := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sineWeight_nonneg M n)]

/-- For `2 ≤ M`, the last sine weight equals the first weight. -/
theorem sineWeight_last (M : ℕ) (hM : 2 ≤ M) : sineWeight M (M-1) = sineWeight M 0 := by
  simpa only [Nat.sub_zero] using! sineWeight_reverse M 0 (by omega)

/-- For `2 ≤ M`, the penultimate sine weight equals the weight at index one. -/
theorem sineWeight_penultimate (M : ℕ) (hM : 2 ≤ M) :
    sineWeight M (M-2) = sineWeight M 1 := by
  simpa only [Nat.sub_sub] using! sineWeight_reverse M 1 (by omega)

/-- For `2 ≤ M`, the norm of the first forward difference of the complex sine weights is at most
`5 * π^2 / M^3`. -/
theorem sineWeight_diff_zero (M : ℕ) (hM : 2 ≤ M) :
    ‖nextDiff (fun n => (sineWeight M n : ℂ)) 0‖ ≤ 5*Real.pi^2/(M:ℝ)^3 := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  calc
    _ ≤ sineWeight M 1 + sineWeight M 0 := by
      simpa only [nextDiff,Nat.zero_add,sineWeight_norm] using!
        norm_sub_le (sineWeight M 1 : ℂ) (sineWeight M 0 : ℂ)
    _ ≤ 9*Real.pi^2/(2*(M:ℝ)^3)+Real.pi^2/(2*(M:ℝ)^3) :=
      add_le_add (sineWeight_one_bound M hM) (sineWeight_zero_bound M hM)
    _ = _ := by field_simp; ring

/-- For `2 ≤ M`, the forward difference of the complex sine weights at `(M - 1) - 1` has norm at
most `5 * π^2 / M^3`. -/
theorem sineWeight_diff_last (M : ℕ) (hM : 2 ≤ M) :
    ‖nextDiff (fun n => (sineWeight M n : ℂ)) ((M-1)-1)‖ ≤
      5*Real.pi^2/(M:ℝ)^3 := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hi : (M-1)-1 = M-2 := by omega
  rw [hi,nextDiff,show M-2+1=M-1 by omega,sineWeight_last M hM,
    sineWeight_penultimate M hM]
  calc
    _ ≤ sineWeight M 0 + sineWeight M 1 := by
      simpa only [sineWeight_norm] using!
        norm_sub_le (sineWeight M 0 : ℂ) (sineWeight M 1 : ℂ)
    _ ≤ Real.pi^2/(2*(M:ℝ)^3)+9*Real.pi^2/(2*(M:ℝ)^3) :=
      add_le_add (sineWeight_zero_bound M hM) (sineWeight_one_bound M hM)
    _ = _ := by field_simp; ring

/-- For `2 ≤ M`, every complex second forward difference of the sine weights has norm at most `4
* π^2 / M^3`. -/
theorem sineWeight_complex_second (M n : ℕ) (hM : 2 ≤ M) :
    ‖nextDiff (nextDiff (fun j => (sineWeight M j : ℂ))) n‖ ≤
      4*Real.pi^2/(M:ℝ)^3 := by
  have he : nextDiff (nextDiff (fun j => (sineWeight M j : ℂ))) n =
      ((sineWeight M (n+2)-2*sineWeight M (n+1)+sineWeight M n : ℝ):ℂ) := by
    simp only [nextDiff,Nat.add_assoc]
    push_cast
    ring
  rw [he,Complex.norm_real,Real.norm_eq_abs]
  exact sineWeight_second_bound M n hM

/-- For `2 ≤ M`, the product `‖overlapSum M φ‖ * ‖1 - phaseUnit φ‖^2` is at most `16 * π^2 /
M^2`. -/
theorem overlapSum_difference_bound (M : ℕ) (hM : 2 ≤ M) (φ : ℝ) :
    ‖overlapSum M φ‖ * ‖1-phaseUnit φ‖^2 ≤ 16*Real.pi^2/(M:ℝ)^2 := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hm2 : (2:ℝ)≤M := by exact_mod_cast hM
  have hz : ‖1-phaseUnit φ‖ ≤ 2 := by
    have h := norm_sub_le (1:ℂ) (phaseUnit φ)
    rw [norm_one,phaseUnit_norm] at h
    linarith
  have hedge : ‖(sineWeight M 0:ℂ)‖+‖(sineWeight M (M-1):ℂ)‖ ≤
      Real.pi^2/(M:ℝ)^3 := by
    rw [sineWeight_norm,sineWeight_norm,sineWeight_last M hM]
    calc
      _ ≤ Real.pi^2/(2*(M:ℝ)^3)+Real.pi^2/(2*(M:ℝ)^3) :=
        add_le_add (sineWeight_zero_bound M hM) (sineWeight_zero_bound M hM)
      _ = _ := by field_simp; ring
  have hsum : (∑ i ∈ Finset.range ((M-1)-1),
      ‖nextDiff (nextDiff (fun j => (sineWeight M j:ℂ))) i‖) ≤
        4*Real.pi^2/(M:ℝ)^2 := by
    calc
      _ ≤ ∑ _i ∈ Finset.range ((M-1)-1), 4*Real.pi^2/(M:ℝ)^3 :=
        Finset.sum_le_sum (fun i _ => sineWeight_complex_second M i hM)
      _ = (((M-1)-1:ℕ):ℝ)*(4*Real.pi^2/(M:ℝ)^3) := by simp
      _ ≤ (M:ℝ)*(4*Real.pi^2/(M:ℝ)^3) := by
        gcongr
        exact_mod_cast (show (M-1)-1≤M by omega)
      _ = _ := by field_simp
  have hsmall : 12*Real.pi^2/(M:ℝ)^3 ≤ 6*Real.pi^2/(M:ℝ)^2 := by
    calc
      _ = (12/(M:ℝ))*(Real.pi^2/(M:ℝ)^2) := by field_simp
      _ ≤ 6*(Real.pi^2/(M:ℝ)^2) := by
        gcongr
        exact (div_le_iff₀ hm).2 (by linarith)
      _ = _ := by ring
  have h := weighted_second_diff_bound (fun j => (sineWeight M j:ℂ))
    (phaseUnit φ) M (phaseUnit_norm φ)
  change ‖overlapSum M φ‖ * ‖1-phaseUnit φ‖^2 ≤ _ at h
  have hb : (‖(sineWeight M 0:ℂ)‖+‖(sineWeight M (M-1):ℂ)‖)*‖1-phaseUnit φ‖ ≤
      2*Real.pi^2/(M:ℝ)^3 := by
    calc
      _ ≤ (Real.pi^2/(M:ℝ)^3)*2 :=
        mul_le_mul hedge hz (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have hd0 := sineWeight_diff_zero M hM
  have hd1 := sineWeight_diff_last M hM
  have hnon : 0 ≤ Real.pi^2/(M:ℝ)^2 := by positivity
  (try dsimp only at h)
  simp only [mul_div_assoc] at hb hd0 hd1 hsum hsmall ⊢
  linarith

/-- If the phase distance of `φ` from zero is at least a positive `η` and `2 ≤ M`, then
`‖overlapSum M φ‖ ≤ π^2 / (M^2 * η^2)`. -/
theorem overlapSum_far_bound (M : ℕ) (hM : 2 ≤ M) (φ η : ℝ)
    (hη : 0<η) (hg : η≤phaseDistance φ 0) :
    ‖overlapSum M φ‖ ≤ Real.pi^2/((M:ℝ)^2*η^2) := by
  have hm : (0:ℝ)<M := by exact_mod_cast (show 0<M by omega)
  have hc : 4*η≤‖1-phaseUnit φ‖ := by
    have h := phase_chord_lower_bound φ
    rw [← norm_sub_rev] at h
    exact le_trans (by nlinarith) h
  have hsq : 16*η^2 ≤ ‖1-phaseUnit φ‖^2 := by nlinarith [norm_nonneg (1-phaseUnit φ)]
  have hb := overlapSum_difference_bound M hM φ
  have hm2 : 0<(M:ℝ)^2 := sq_pos_of_pos hm
  have hmul : ‖overlapSum M φ‖*(16*η^2)*(M:ℝ)^2 ≤16*Real.pi^2 := by
    calc
      _ ≤ (‖overlapSum M φ‖*‖1-phaseUnit φ‖^2)*(M:ℝ)^2 := by
        gcongr
      _ ≤ (16*Real.pi^2/(M:ℝ)^2)*(M:ℝ)^2 := by gcongr
      _ = _ := by field_simp
  apply (le_div_iff₀ (by positivity : (0:ℝ)<(M:ℝ)^2*η^2)).2
  nlinarith

/-- The squared norm of the sine envelope amplitude at `τ` equals `sineWeight M τ.val`. -/
theorem sineWeight_eq_norm (M : ℕ) (τ : Fin M) :
    ‖sinEnvelopeState M τ‖^2 = sineWeight M τ.val := by
  simp only [sinEnvelopeState,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs,
    Real.sq_sqrt (by positivity : (0:ℝ)≤2/(M:ℝ))]
  rfl

/-- The `n`th power of `phaseUnit φ` equals `exp (2 * π * I * (n * φ))`. -/
theorem phaseUnit_pow (φ : ℝ) (n : ℕ) :
    (phaseUnit φ)^n = Complex.exp (2*Real.pi*Complex.I*((n:ℝ)*φ)) := by
  rw [phaseUnit,← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The inner product of the basis ket at `i` with `ψ` is the amplitude `ψ i`. -/
theorem inner_ket_read {M : ℕ} (i : Fin M) (ψ : QState (Fin M)) :
    Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket i) ψ = ψ i := by
  simp [inner_apply,Qatlib.Foundations.PureStateMath.Ket]

/-- For `2 ≤ M`, the zero label amplitude of `alignedKernel M φ` equals `overlapSum M φ`. -/
theorem aligned_zero_label_overlap (M : ℕ) (hM : 2≤M) (φ : ℝ) :
    alignedKernel M φ (⟨0,by omega⟩:Fin M) = overlapSum M φ := by
  let f : QState (Fin M) := fun τ =>
    Complex.exp (2*Real.pi*Complex.I*((τ.val:ℝ)*φ))*sinEnvelopeState M τ
  have hprep := (sin_envelope_state_normalized_and_prep M hM).2.2
  calc
    _ = Qatlib.Foundations.PureStateMath.Inner (Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩:Fin M))
        ((sinEnvelopePrep M hM)ᴴ *ᵥ f) := by
      rw [inner_ket_read]
      simp only [alignedKernel,dif_pos hM]
      rfl
    _ = Qatlib.Foundations.PureStateMath.Inner ((sinEnvelopePrep M hM)*ᵥ Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩:Fin M)) f :=
      (inner_mulVec_left_rect _ _ _).symm
    _ = Qatlib.Foundations.PureStateMath.Inner (sinEnvelopeState M) f := by rw [hprep]
    _ = ∑ τ : Fin M, ((‖sinEnvelopeState M τ‖^2:ℝ):ℂ)*
        Complex.exp (2*Real.pi*Complex.I*((τ.val:ℝ)*φ)) := by
      rw [inner_apply]
      apply Finset.sum_congr rfl
      intro τ _
      dsimp [f]
      calc
        _ = ((starRingEnd ℂ) (sinEnvelopeState M τ)*sinEnvelopeState M τ)*
            Complex.exp (2*Real.pi*Complex.I*((τ.val:ℝ)*φ)) := by push_cast; ring
        _ = _ := by rw [← Complex.normSq_eq_conj_mul_self,Complex.normSq_eq_norm_sq]; push_cast; rfl
    _ = ∑ τ : Fin M, (sineWeight M τ.val:ℂ)*(phaseUnit φ)^τ.val := by
      apply Finset.sum_congr rfl
      intro τ _
      rw [sineWeight_eq_norm,phaseUnit_pow]
    _ = overlapSum M φ := by
      unfold overlapSum
      exact Fin.sum_univ_eq_sum_range (fun n => (sineWeight M n:ℂ)*(phaseUnit φ)^n) M

/-- For `2 ≤ M`, the aligned kernel at phase zero is the zero basis ket. -/
theorem alignedKernel_zero (M : ℕ) (hM : 2≤M) :
    alignedKernel M 0 = Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩:Fin M) := by
  simp only [alignedKernel,dif_pos hM,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul]
  rw [← (sin_envelope_state_normalized_and_prep M hM).2.2]
  change (sinEnvelopePrep M hM)ᴴ *ᵥ
    ((sinEnvelopePrep M hM)*ᵥ Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩:Fin M)) = _
  rw [Matrix.mulVec_mulVec]
  rw [show (sinEnvelopePrep M hM)ᴴ*sinEnvelopePrep M hM=1 by
    simpa only [Matrix.star_eq_conjTranspose] using!
      (sin_envelope_state_normalized_and_prep M hM).2.1.1,Matrix.one_mulVec]

/-- For `2 ≤ M`, any phase at distance zero from zero has aligned kernel equal to the zero basis
ket. -/
theorem alignedKernel_zero_distance (M : ℕ) (hM : 2≤M) (φ : ℝ)
    (hφ : phaseDistance φ 0=0) :
    alignedKernel M φ = Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩:Fin M) := by
  have hd : φ-(⌊φ+1/2⌋:ℤ)=0 := by
    simpa only [phaseDistance,sub_zero,abs_eq_zero] using! hφ
  have he : φ=((⌊φ+1/2⌋:ℤ):ℝ) := by linarith
  have hp : phaseUnit φ=1 := by rw [phaseUnit,he,exp_two_pi_I_int]
  have hk : alignedKernel M φ=alignedKernel M 0 := by
    simp only [alignedKernel,dif_pos hM]
    congr 1
    funext τ
    rw [← phaseUnit_pow,hp]
    simp
  exact hk.trans (alignedKernel_zero M hM)

/-- For `2 ≤ M` and phase distance at least a positive `η`, the zero label amplitude norm is at
most `π^2 / (M^2 * η^2)`. -/
theorem aligned_zero_label_far_bound (M : ℕ) (hM : 2≤M) (φ η : ℝ)
    (hη : 0<η) (hg : η≤phaseDistance φ 0) :
    ‖alignedKernel M φ (⟨0,by omega⟩:Fin M)‖≤Real.pi^2/((M:ℝ)^2*η^2) := by
  rw [aligned_zero_label_overlap M hM φ]
  exact overlapSum_far_bound M hM φ η hη hg

variable {I : Type}

/-- At phase distance zero, the repeated aligned kernel packet is exactly the zero phase
register embedding of the system state. -/
theorem alignedKernelPacket_zero_distance (M k : ℕ) (hM : 2≤M) (φ : ℝ)
    (hφ : phaseDistance φ 0=0) (v : QState I) :
    alignedKernelPacket M k φ v = phaseReflectionEmbed M k v := by
  have hz := alignedKernel_zero_distance M hM φ hφ
  funext ⟨x,b,i⟩
  cases b with
  | true => simp [alignedKernelPacket,phaseReflectionEmbed]
  | false =>
    by_cases hx : ∀ j, (x j).val=0
    · have he : x=phaseZeroIndex M k (by omega) := by
        funext j
        apply Fin.ext
        exact hx j
      subst x
      simp [alignedKernelPacket,phaseReflectionEmbed,hz,phaseZeroIndex,Qatlib.Foundations.PureStateMath.Ket]
    · obtain ⟨j,hj⟩ := not_forall.mp hx
      have hne : x j ≠ (⟨0,by omega⟩:Fin M) := fun he => hj (congrArg Fin.val he)
      have hp : (∏ j : Fin k, alignedKernel M φ (x j))=0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hz]; simp [Qatlib.Foundations.PureStateMath.Ket,hne])
      simp [alignedKernelPacket,phaseReflectionEmbed,hx,hp]

variable {I : Type} [Fintype I] [DecidableEq I]

/-- The evaluated aligned detection word fixes the zero register embedding of an eigenvector
whose phase has distance zero from zero. -/
theorem aligned_detection_zero_fixed (M k : ℕ) (hM : 2≤M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ)
    (he : W*ᵥv=Complex.exp (2*Real.pi*Complex.I*φ)•v)
    (ht : phaseDistance φ 0=0) :
    ApplyGate (evaluate (parallelOracle (controlOracle W)) (alignedDetectionWord M hM k))
      (phaseReflectionEmbed M k v) = phaseReflectionEmbed M k v := by
  rw [alignedDetectionWord_eigenstate M k hM W v φ he,
    alignedKernelPacket_zero_distance M k hM φ ht v]

/-- For unitary `W`, the adjoint of the evaluated aligned detection word fixes the embedded
eigenvector when its phase has distance zero from zero. -/
theorem aligned_inverse_zero_fixed (M k : ℕ) (hM : 2≤M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ) (hW : W∈Matrix.unitaryGroup I ℂ)
    (he : W*ᵥv=Complex.exp (2*Real.pi*Complex.I*φ)•v)
    (ht : phaseDistance φ 0=0) :
    ApplyGate (evaluate (parallelOracle (controlOracle W)) (alignedDetectionWord M hM k))ᴴ
      (phaseReflectionEmbed M k v) = phaseReflectionEmbed M k v := by
  let D := evaluate (parallelOracle (controlOracle W)) (alignedDetectionWord (I:=I) M hM k)
  have hD : D∈Matrix.unitaryGroup (PhaseReflectionSpace I M k) ℂ :=
    (alignedDetectionWord_resources M k hM).1.evaluate_unitary
      (parallelOracle_unitary (controlOracle_unitary hW))
  have hf : ApplyGate D (phaseReflectionEmbed M k v)=phaseReflectionEmbed M k v :=
    aligned_detection_zero_fixed M k hM W v φ he ht
  change ApplyGate Dᴴ (phaseReflectionEmbed M k v)=_
  calc
    _ = ApplyGate Dᴴ (ApplyGate D (phaseReflectionEmbed M k v)) := by rw [hf]
    _ = _ := by
      rw [← applyGate_mul,show Dᴴ*D=1 by
        simpa only [Matrix.star_eq_conjTranspose] using! hD.1,applyGate_one]

/-- For unitary `W`, the aligned reflection exactly fixes the embedded eigenvector at phase
distance zero. -/
theorem aligned_reflection_zero_exact (M k : ℕ) (hM : 2≤M) (W : Matrix I I ℂ)
    (v : QState I) (φ : ℝ) (hW : W∈Matrix.unitaryGroup I ℂ)
    (he : W*ᵥv=Complex.exp (2*Real.pi*Complex.I*φ)•v)
    (ht : phaseDistance φ 0=0) :
    alignedReflectionState W M hM k v=phaseReflectionEmbed M k v := by
  have hr := aligned_reflection_eigenstate_residual M k hM W v φ hW he
  have hk : alignedKernel M φ (⟨0,by omega⟩:Fin M)=1 := by
    rw [alignedKernel_zero_distance M hM φ ht]
    simp [Qatlib.Foundations.PureStateMath.Ket]
  rw [hk,one_pow,one_smul] at hr
  have hi := aligned_inverse_zero_fixed M k hM W v φ hW he ht
  have hl : ApplyGate (evaluate (parallelOracle (controlOracle W))
      (alignedDetectionWord (I:=I) M hM k))ᴴ
        ((2:ℂ)•phaseReflectionEmbed M k v) = (2:ℂ)•phaseReflectionEmbed M k v := by
    simp only [ApplyGate,Matrix.mulVec_smul]
    exact congrArg ((2:ℂ) • ·) hi
  rw [hl] at hr
  calc
    _ = (2:ℂ)•phaseReflectionEmbed M k v-phaseReflectionEmbed M k v :=
      (eq_sub_iff_add_eq).2 hr
    _ = _ := by module

open Qatlib
open scoped Classical Matrix.Norms.L2Operator

/-- For an orthonormal eigenvector family with normalized coefficients, zero phase on `T`, and
phase distance at least `η > 0` outside `T`, the aligned reflection error is at most `2 *
(π^2 / (M^2 * η^2))^k` times the square root of the coefficient mass outside `T`. The
reflection word has `2 * k * (M - 1)` queries and `4 * k * (M - 1) + 4 * k + 1` gates. -/
theorem frontier1
    (J : Type) [Fintype J] [DecidableEq J]
    (W : Matrix I I ℂ) (M k : ℕ) (hM : 2 ≤ M) (v : J → QState I) (c : J → ℂ)
    (φ : J → ℝ) (T : Finset J) (η : ℝ)
    (hW : W ∈ Matrix.unitaryGroup I ℂ) (hη : 0 < η)
    (hv : ∀ j l, Qatlib.Foundations.PureStateMath.Inner (v j) (v l) = if j = l then 1 else 0)
    (hc : (∑ j, ‖c j‖ ^ 2) = 1)
    (he : ∀ j, W *ᵥ v j = Complex.exp (2 * Real.pi * Complex.I * (φ j : ℂ)) • v j)
    (ht : ∀ j ∈ T, phaseDistance (φ j) 0 = 0)
    (hg : ∀ j, j ∉ T → η ≤ phaseDistance (φ j) 0) :
    ‖toEuclidean_fromVec (alignedReflectionState W M hM k (∑ j, c j • v j) -
        phaseReflectionEmbed M k ((2:ℂ) • spectralTargetState v c T - ∑ j, c j • v j))‖
      ≤ 2 * (Real.pi^2/((M:ℝ)^2*η^2))^k * Real.sqrt (1-∑ j∈T, ‖c j‖^2)
    ∧ adjointQueryCount (alignedReflectionWord (I:=I) M hM k)=2*k*(M-1)
    ∧ adjointGateCount (alignedReflectionWord (I:=I) M hM k)=4*k*(M-1)+4*k+1 := by
  have hM0 : 0<M := by omega
  have hD := (alignedDetectionWord_resources (I:=I) M k hM).1.evaluate_unitary
    (parallelOracle_unitary (controlOracle_unitary hW))
  have hzbranch := (aligned_phase_actual_spectral_packet J W M k hM v c φ he).2
  have hz : ‖toEuclidean_fromVec (alignedZeroBranch W M hM k (∑ j,c j • v j)
      -spectralTargetState v c T)‖
      ≤ (Real.pi^2/((M:ℝ)^2*η^2))^k * Real.sqrt (1-∑ j∈T, ‖c j‖^2) := by
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
    have h := envelope_packet_filter_error (I:=I) (J:=J) v c
      (fun j => (alignedKernel M (φ j) (⟨0,hM0⟩:Fin M))^k) T 1
      ((Real.pi^2/((M:ℝ)^2*η^2))^k) hv (by positivity)
      (fun j hj => by
        (try dsimp only)
        rw [alignedKernel_zero_distance M hM (φ j) (ht j hj)]
        simp [Qatlib.Foundations.PureStateMath.Ket])
      (fun j hj => by
        rw [norm_pow]
        exact pow_le_pow_left₀ (norm_nonneg _)
          (aligned_zero_label_far_bound M hM (φ j) η hη (hg j hj)) k)
    simpa only [hrc,sub_self,norm_zero,zero_mul,zero_add] using! h

  have hsum : alignedReflectionState W M hM k (∑ j, c j • v j) +
      phaseReflectionEmbed M k (∑ j, c j • v j) =
      ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
        ((2 : ℂ) • phaseReflectionEmbed M k (alignedZeroBranch W M hM k
          (∑ j, c j • v j))) := by
    let E := degenerateEmbedLinear (I := I) M k
    let R := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
      (alignedReflectionWord (I := I) M hM k))).comp E
    let L := (degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
      (alignedDetectionWord (I := I) M hM k))ᴴ).comp ((2 : ℂ) • E)
    have hres (j : J) : R (v j) + E (v j) =
        L ((alignedKernel M (φ j) (⟨0, hM0⟩ : Fin M)) ^ k • v j) := by
      change alignedReflectionState W M hM k (v j) + phaseReflectionEmbed M k (v j) =
        ApplyGate (evaluate (parallelOracle (controlOracle W))
          (alignedDetectionWord M hM k))ᴴ
          ((2 : ℂ) • E ((alignedKernel M (φ j) (⟨0, hM0⟩ : Fin M)) ^ k • v j))
      rw [E.map_smul]
      exact aligned_reflection_eigenstate_residual M k hM W (v j) (φ j) hW (he j)
    change R (∑ j, c j • v j) + E (∑ j, c j • v j) =
      L (alignedZeroBranch W M hM k (∑ j, c j • v j))
    rw [hzbranch, map_sum, map_sum, map_sum]
    simp only [map_smul, ← Finset.sum_add_distrib, ← smul_add, mul_smul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hres j, map_smul]

  have herror : alignedReflectionState W M hM k (∑ j, c j • v j) -
      phaseReflectionEmbed M k ((2 : ℂ) • spectralTargetState v c T - ∑ j, c j • v j) =
      ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
        ((2 : ℂ) • phaseReflectionEmbed M k
          (alignedZeroBranch W M hM k (∑ j, c j • v j) - spectralTargetState v c T))
      + ((2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
          (alignedDetectionWord M hM k))ᴴ
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
        (alignedZeroBranch W M hM k (∑ j, c j • v j) - spectralTargetState v c T)
        = phaseReflectionEmbed M k (alignedZeroBranch W M hM k (∑ j, c j • v j))
          - phaseReflectionEmbed M k (spectralTargetState v c T) :=
      (degenerateEmbedLinear (I := I) M k).map_sub _ _
    have hA1 : ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
        ((2 : ℂ) • (phaseReflectionEmbed M k (alignedZeroBranch W M hM k (∑ j, c j • v j))
          - phaseReflectionEmbed M k (spectralTargetState v c T)))
        = (2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
            (alignedDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (alignedZeroBranch W M hM k (∑ j, c j • v j)))
          - (2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
            (alignedDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (spectralTargetState v c T)) := by
      simp only [ApplyGate, Matrix.mulVec_sub, Matrix.mulVec_smul, smul_sub]
    have hA2 : ApplyGate (evaluate (parallelOracle (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
        ((2 : ℂ) • phaseReflectionEmbed M k
          (alignedZeroBranch W M hM k (∑ j, c j • v j)))
        = (2 : ℂ) • ApplyGate (evaluate (parallelOracle (controlOracle W))
            (alignedDetectionWord M hM k))ᴴ
            (phaseReflectionEmbed M k (alignedZeroBranch W M hM k (∑ j, c j • v j))) := by
      simp only [ApplyGate, Matrix.mulVec_smul]
    rw [hP2, hP1, hA1, ← hA2, ← hsum]
    module
  have hfixed : ApplyGate (evaluate (parallelOracle (controlOracle W))
      (alignedDetectionWord M hM k))ᴴ (phaseReflectionEmbed M k (spectralTargetState v c T))
        = phaseReflectionEmbed M k (spectralTargetState v c T) := by
    let E := degenerateEmbedLinear (I:=I) M k
    let A := degenerateApplyLinear (evaluate (parallelOracle (controlOracle W))
      (alignedDetectionWord (I:=I) M hM k))ᴴ
    change A (E (∑ j∈T,c j • v j))=E (∑ j∈T,c j • v j)
    simp only [map_sum,map_smul]
    apply Finset.sum_congr rfl
    intro j hj
    rw [show A (E (v j))=E (v j) from
      aligned_inverse_zero_fixed M k hM W (v j) (φ j) hW (he j) (ht j hj)]
  rw [hfixed,sub_self,add_zero] at herror

  have hfirst : ‖toEuclidean_fromVec (ApplyGate (evaluate (parallelOracle
        (controlOracle W))
        (alignedDetectionWord M hM k))ᴴ
        ((2 : ℂ) • phaseReflectionEmbed M k
          (alignedZeroBranch W M hM k (∑ j, c j • v j)
            - spectralTargetState v c T)))‖
      = 2 * ‖toEuclidean_fromVec (alignedZeroBranch W M hM k (∑ j, c j • v j)
          - spectralTargetState v c T)‖ := by
    rw [norm_applyGate_of_mem_unitaryGroup (adjoint_unitary hD)]
    change ‖(2 : ℂ) • toEuclidean_fromVec (phaseReflectionEmbed M k
        (alignedZeroBranch W M hM k (∑ j, c j • v j)
            - spectralTargetState v c T))‖ = _
    rw [norm_smul, phaseReflectionEmbed_norm M k hM0]
    norm_num [Complex.norm_ofNat]
  refine ⟨?_,(aligned_reflection_actual_queries_and_macros (I:=I) M k hM).2.1,
    (aligned_reflection_actual_queries_and_macros (I:=I) M k hM).2.2⟩
  rw [herror,hfirst]
  nlinarith [hz]

/-- The product of the adjoint Fourier matrix and the sine envelope preparation matrix. -/
noncomputable def zeroPacketPrep (M : ℕ) (hM : 2≤M) : Matrix (Fin M) (Fin M) ℂ :=
  (QFTMatrix M)ᴴ * sinEnvelopePrep M hM

/-- The matrix `zeroPacketPrep M hM` is unitary. -/
theorem zeroPacketPrep_unitary (M : ℕ) (hM : 2≤M) :
    zeroPacketPrep M hM∈Matrix.unitaryGroup (Fin M) ℂ :=
  (Matrix.unitaryGroup (Fin M) ℂ).mul_mem
    (adjoint_unitary (qftMatrix_unitary (by omega)))
    (sin_envelope_state_normalized_and_prep M hM).2.1

/-- Applying `zeroPacketPrep` to the zero basis ket gives `sinEnvelopeKernel M 0`. -/
theorem zeroPacketPrep_column (M : ℕ) (hM : 2≤M) :
    zeroPacketPrep M hM *ᵥ Qatlib.Foundations.PureStateMath.Ket (⟨0,by omega⟩:Fin M)=sinEnvelopeKernel M 0 := by
  rw [zeroPacketPrep,← Matrix.mulVec_mulVec,
    (sin_envelope_state_normalized_and_prep M hM).2.2]
  unfold sinEnvelopeKernel
  congr 1
  funext τ
  simp

/-- Applying the adjoint of `zeroPacketPrep` to `sinEnvelopeKernel M φ` gives `alignedKernel M
φ`. -/
theorem aligned_as_packet_alignment (M : ℕ) (hM : 2≤M) (φ : ℝ) :
    (zeroPacketPrep M hM)ᴴ *ᵥ sinEnvelopeKernel M φ=alignedKernel M φ := by
  rw [zeroPacketPrep,Matrix.conjTranspose_mul,Matrix.conjTranspose_conjTranspose]
  unfold sinEnvelopeKernel
  change ((sinEnvelopePrep M hM)ᴴ * QFTMatrix M) *ᵥ
    ((QFTMatrix M)ᴴ *ᵥ _) = _
  rw [Matrix.mulVec_mulVec]
  have hu : QFTMatrix M*(QFTMatrix M)ᴴ=1 := by
    simpa only [Matrix.star_eq_conjTranspose] using! (qftMatrix_unitary (by omega : 0<M)).2
  rw [Matrix.mul_assoc,hu,Matrix.mul_one]
  simp [alignedKernel,hM,ApplyGate]

end Qatlib.Concepts.WalkSearch.MnrsAmplify.CorrectSinePacketReflection
