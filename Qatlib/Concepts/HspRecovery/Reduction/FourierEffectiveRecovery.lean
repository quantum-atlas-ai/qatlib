/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.HspRecovery.Reduction.FourierEffectiveRecoveryDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false

namespace Qatlib.Concepts.HspRecovery.ReductionCore

open Matrix
open scoped Classical

variable {I : Type} [Fintype I] [DecidableEq I]

omit [Fintype I] in

theorem recordOracle_swap (M N : ℕ) (U : Matrix I I ℂ) :
    relabelGate (recordSwap M N) (recordOracle N M U) = recordOracle M N U := by
  ext ⟨x,b,y,i⟩ ⟨x',b',y',i'⟩
  cases b <;> cases b' <;>
    simp [recordOracle, relabelGate, Matrix.reindex_apply, recordSwap,
      TensorGate, Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle, Qatlib.Concepts.BlockEncoding.LCU.select, Matrix.one_apply]
    <;> split_ifs <;> simp_all

theorem recordOracle_unitary (M N : ℕ) (U : Matrix I I ℂ)
    (hU : U ∈ Matrix.unitaryGroup I ℂ) :
    recordOracle M N U ∈ Matrix.unitaryGroup (RecordSpace M N I) ℂ :=
  tensorGate_unitary (by simp)
    (Qatlib.Concepts.LocalMachine.LocalTransport.controlOracle_unitary (tensorGate_unitary (by simp) hU))

theorem spectator_eigen {J : Type} [Fintype J] [DecidableEq J]
    (U : Matrix I I ℂ) (ψ : QState I) (χ : QState J) (φ : ℝ)
    (hψ : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) :
    ApplyGate (TensorGate (1 : Matrix J J ℂ) U) (TensorState χ ψ) =
      Complex.exp (2 * Real.pi * Complex.I * φ) • TensorState χ ψ := by
  rw [applyGate_tensorGate, applyGate_one, hψ]
  funext p
  simp only [TensorState, Pi.smul_apply, smul_eq_mul]
  ring

theorem recordRun_eigen (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hψ : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ) :
    recordRun M N hM hN U ψ =
      TensorState (qpeKernel M φ)
        (TensorState (Ket false) (TensorState (qpeKernel N φ) ψ)) := by
  have hfirst := (counted_offgrid_qpe_clean_flag M hM
    (TensorGate (1 : Matrix (Fin N) (Fin N) ℂ) U)
    (TensorState (Ket (⟨0,hN⟩ : Fin N)) ψ)).1
  rw [qpeOutput_eigen M _ _ φ (spectator_eigen U ψ _ φ hψ)] at hfirst
  change Run (recordOracle M N U) (countedPhaseCircuit M) _ = _ at hfirst
  have hmid : (fun p : RecordSpace M N I =>
      if p.2.1 then 0 else
        TensorState (qpeKernel M φ) (TensorState (Ket (⟨0,hN⟩ : Fin N)) ψ)
          (p.1,p.2.2)) =
      relabelState (recordSwap M N)
        (TensorState (Ket (⟨0,hN⟩ : Fin N))
          (TensorState (Ket false) (TensorState (qpeKernel M φ) ψ))) := by
    funext ⟨x,b,y,i⟩
    cases b <;> simp [relabelState, recordSwap, TensorState, Ket]
  have hsecond := (counted_offgrid_qpe_clean_flag N hN
    (TensorGate (1 : Matrix (Fin M) (Fin M) ℂ) U)
    (TensorState (qpeKernel M φ) ψ)).1
  rw [qpeOutput_eigen N _ _ φ (spectator_eigen U ψ _ φ hψ)] at hsecond
  change Run (recordOracle N M U) (countedPhaseCircuit N) _ = _ at hsecond
  unfold recordRun recordCircuit recordInput
  rw [run_append, hfirst, hmid, ← recordOracle_swap M N U,
    (run_relabelCircuit_readout (recordSwap M N) (recordOracle N M U)
      (countedPhaseCircuit N) _ ∅).1, hsecond]
  funext ⟨x,b,y,i⟩
  cases b <;> simp [relabelState, recordSwap, TensorState, Ket]
  ring

theorem recordCircuit_resources (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    QueryCount (recordCircuit (I := I) M N) = (M-1) + (N-1) ∧
    GateCount (recordCircuit (I := I) M N) = 2*(M-1) + 2*(N-1) + 4 ∧
    IsUnitaryCircuit (recordCircuit (I := I) M N) := by
  have hM' := (counted_offgrid_qpe_clean_flag M hM
    (1 : Matrix (Fin N × I) (Fin N × I) ℂ) (0 : QState (Fin N × I))).2
  have hN' := (counted_offgrid_qpe_clean_flag N hN
    (1 : Matrix (Fin M × I) (Fin M × I) ℂ) (0 : QState (Fin M × I))).2
  have hr := relabelCircuit_legality_resources (recordSwap (I := I) M N)
    (countedPhaseCircuit N)
  refine ⟨?_, ?_, ?_⟩
  · simp only [recordCircuit, queryCount_append, hr.2.1, hM'.1, hN'.1]
  · simp only [recordCircuit, gateCount_append, hr.2.2.1, hM'.2.1, hN'.2.1]
    omega
  · exact (isUnitaryCircuit_append _ _).mpr ⟨hM'.2.2, hr.1.mpr hN'.2.2⟩

theorem recordRun_normalized (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (U : Matrix I I ℂ) (hU : U ∈ Matrix.unitaryGroup I ℂ)
    (ψ : QState I) (hψ : Normalized ψ) :
    Normalized (recordRun M N hM hN U ψ) := by
  apply normalized_run _ (recordOracle_unitary M N U hU) _
    (recordCircuit_resources (I := I) M N hM hN).2.2
  exact normalized_tensorState (normalized_ket _)
    (normalized_tensorState (normalized_ket _)
      (normalized_tensorState (normalized_ket _) hψ))

theorem recordRun_joint_law (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hψ : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ)
    (hnorm : Normalized ψ) (S : Finset (Fin M)) (T : Finset (Fin N)) :
    MeasureProb (recordRun M N hM hN U ψ) (recordEvent M N S T) =
      MeasureProb (qpeKernel M φ) S * MeasureProb (qpeKernel N φ) T := by
  rw [recordRun_eigen M N hM hN U ψ φ hψ]
  simp only [recordEvent, measureProb_tensorState_prod, measureProb_univ (normalized_ket false),
    measureProb_univ hnorm, one_mul, mul_one]

theorem recordRun_joint_window (M N : ℕ) (hM : 2 ≤ M) (hN : 2 ≤ N)
    (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hψ : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ)
    (hnorm : Normalized ψ) :
    (8 / Real.pi^2)^2 ≤
      MeasureProb (recordRun M N (by omega) (by omega) U ψ)
        (recordEvent M N (phaseWindow M φ) (phaseWindow N φ)) := by
  rw [recordRun_joint_law M N (by omega) (by omega) U ψ φ hψ hnorm]
  have hm : 8 / Real.pi^2 ≤ MeasureProb (qpeKernel M φ) (phaseWindow M φ) :=
    offgrid_phase_window_probability M φ hM
  have hn : 8 / Real.pi^2 ≤ MeasureProb (qpeKernel N φ) (phaseWindow N φ) :=
    offgrid_phase_window_probability N φ hN
  nlinarith [mul_le_mul hm hn (by positivity : (0 : ℝ) ≤ 8 / Real.pi^2)
    (measureProb_nonneg (qpeKernel M φ) (phaseWindow M φ))]

theorem classifiedCircuit_resources (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (label : Fin M × Fin N → Bool) :
    QueryCount (classifiedCircuit (I := I) M N label) = (M-1) + (N-1) ∧
    GateCount (classifiedCircuit (I := I) M N label) = 2*(M-1) + 2*(N-1) + 5 ∧
    IsUnitaryCircuit (classifiedCircuit (I := I) M N label) := by
  obtain ⟨hq,hg,hu⟩ := recordCircuit_resources (I := I) M N hM hN
  refine ⟨?_, ?_, ?_⟩
  · simp [classifiedCircuit, queryCount_append, hq]
  · simp [classifiedCircuit, gateCount_append, hg]
  · apply (isUnitaryCircuit_append _ _).mpr
    exact ⟨hu, by simp [permMatrix_unitary (classifierFlip_involutive (I := I) M N label)]⟩

theorem classifiedRun_eigen (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hψ : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ)
    (label : Fin M × Fin N → Bool) :
    Run (recordOracle M N U) (classifiedCircuit M N label) (recordInput M N hM hN ψ) =
      fun p => if p.2.1 = label (p.1,p.2.2.1) then
        qpeKernel M φ p.1 * (qpeKernel N φ p.2.2.1 * ψ p.2.2.2) else 0 := by
  rw [classifiedCircuit, run_append]
  change ApplyGate (permMatrix (classifierFlip M N label)) (recordRun M N hM hN U ψ) = _
  rw [recordRun_eigen M N hM hN U ψ φ hψ]
  funext ⟨x,b,y,i⟩
  rw [applyGate_permMatrix (classifierFlip_involutive M N label)]
  cases b <;> cases h : label (x,y) <;> simp [classifierFlip, TensorState, Ket, h]

theorem resolutionForTolerance_radius (ε : ℚ) (hε : 0 < ε) :
    2 ≤ resolutionForTolerance ε ∧ 1 / (resolutionForTolerance ε : ℝ) ≤ (ε : ℝ) := by
  refine ⟨le_max_left _ _, ?_⟩
  have hεR : 0 < (ε : ℝ) := by exact_mod_cast hε
  have hQ : ε⁻¹ ≤ (resolutionForTolerance ε : ℚ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right 2 ⌈ε⁻¹⌉₊)
  have hR : (ε : ℝ)⁻¹ ≤ (resolutionForTolerance ε : ℝ) := by exact_mod_cast hQ
  have hp : 0 < (resolutionForTolerance ε : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) (le_max_left 2 ⌈ε⁻¹⌉₊))
  apply (div_le_iff₀ hp).mpr
  have hd : (1 : ℝ) / (ε : ℝ) ≤ (resolutionForTolerance ε : ℝ) := by
    simpa only [one_div] using hR
  have hm : (1 : ℝ) ≤ (resolutionForTolerance ε : ℝ) * (ε : ℝ) :=
    (div_le_iff₀ hεR).mp hd
  nlinarith

theorem rationalTolerance_record (ε δ : ℚ) (hε : 0 < ε) (hδ : 0 < δ)
    (U : Matrix I I ℂ) (ψ : QState I) (φ : ℝ)
    (hψ : ApplyGate U ψ = Complex.exp (2 * Real.pi * Complex.I * φ) • ψ)
    (hnorm : Normalized ψ) :
    let M := resolutionForTolerance ε
    let N := resolutionForTolerance δ
    (8 / Real.pi^2)^2 ≤ MeasureProb
      (recordRun M N (by have := (resolutionForTolerance_radius ε hε).1; omega)
        (by have := (resolutionForTolerance_radius δ hδ).1; omega) U ψ)
      (recordEvent M N (radiusWindow M φ ε) (radiusWindow N φ δ)) ∧
    QueryCount (recordCircuit (I := I) M N) = (M-1) + (N-1) := by
  (try dsimp only)
  obtain ⟨hM,hrM⟩ := resolutionForTolerance_radius ε hε
  obtain ⟨hN,hrN⟩ := resolutionForTolerance_radius δ hδ
  refine ⟨?_, (recordCircuit_resources _ _ (by omega) (by omega)).1⟩
  apply (recordRun_joint_window _ _ hM hN U ψ φ hψ hnorm).trans
  apply measureProb_mono
  intro p hp
  simp only [recordEvent, Finset.mem_product, phaseWindow, radiusWindow,
    Finset.mem_filter, Finset.mem_univ, true_and, and_true] at hp ⊢
  exact ⟨hp.1.trans hrM, hp.2.trans hrN⟩

private theorem run_weighted_sum {K J : Type} [Fintype K] [DecidableEq K] [Fintype J]
    (O : Matrix K K ℂ) (C : Circuit K) (v : J → QState K) (c : J → ℂ) :
    Run O C (∑ j, c j • v j) = ∑ j, c j • Run O C (v j) := by
  have ha (A : Matrix K K ℂ) (w : J → QState K) :
      ApplyGate A (∑ j, c j • w j) = ∑ j, c j • ApplyGate A (w j) := by
    simp only [ApplyGate, Matrix.mulVec_sum, Matrix.mulVec_smul]
  induction C generalizing v with
  | nil => rfl
  | cons s C ih =>
    cases s <;> simp only [Run] <;> rw [ha, ih]

theorem recordRun_sum {J : Type} [Fintype J]
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (U : Matrix I I ℂ)
    (v : J → QState I) (c : J → ℂ) :
    recordRun M N hM hN U (∑ j, c j • v j) =
      ∑ j, c j • recordRun M N hM hN U (v j) := by
  have hi : recordInput M N hM hN (∑ j, c j • v j) =
      ∑ j, c j • recordInput M N hM hN (v j) := by
    funext p
    simp only [recordInput, TensorState, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  unfold recordRun
  rw [hi, run_weighted_sum]

theorem recordRun_spectral_law {J : Type} [Fintype J]
    (M N : ℕ) (hM : 0 < M) (hN : 0 < N) (U : Matrix I I ℂ)
    (v : J → QState I) (c : J → ℂ) (φ : J → ℝ)
    (hv : ∀ j k, Inner (v j) (v k) = if j = k then 1 else 0)
    (he : ∀ j, ApplyGate U (v j) = Complex.exp (2 * Real.pi * Complex.I * φ j) • v j)
    (x : Fin M) (y : Fin N) :
    MeasureProb (recordRun M N hM hN U (∑ j, c j • v j)) (recordEvent M N {x} {y}) =
      ∑ j, ‖c j‖^2 * ‖qpeKernel M (φ j) x‖^2 * ‖qpeKernel N (φ j) y‖^2 := by
  rw [recordRun_sum]
  simp_rw [recordRun_eigen M N hM hN U (v _) (φ _) (he _)]
  simp only [recordEvent, MeasureProb, Finset.sum_product, Finset.sum_singleton,
    BornProb, Fintype.sum_bool]
  simp [Finset.sum_apply, TensorState, Ket, smul_eq_mul]
  have hnorm := sum_norm_sq_orthonormal v
    (fun j => c j * (qpeKernel M (φ j) x * qpeKernel N (φ j) y)) hv
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, norm_mul, mul_pow,
    mul_assoc] using hnorm

end Qatlib.Concepts.HspRecovery.ReductionCore
