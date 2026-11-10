/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
import Qatlib.Concepts.LocalMachine.LocalTransport.NumericalDyadicPhase
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
set_option warningAsError false

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.AmplitudeCore.PreparedReadout
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

namespace Qatlib.Concepts.NativeNumerics.NumericalQFT

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

set_option autoImplicit false
set_option linter.unusedVariables false

private theorem nat_le_two_pow : ∀ n : ℕ, n ≤ 2 ^ n := by
  intro n
  induction n with
  | zero => omega
  | succ m ih =>
      have h1 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_pow' m 1
      have h2 : 2 ^ (m + 1) = 2 ^ m + 2 ^ m := by
        rw [pow_succ]
        omega
      omega

theorem localQFT_length (n : ℕ) :
    (localQFT n).length = n + n * (n - 1) / 2 + n / 2 := by
  obtain ⟨-, -, -, gc, -, -⟩ := localQFT_exact_gate_counts_and_wires n
  obtain ⟨-, -, -, -, -, -, gclen, -⟩ :=
    localDyadicProgram_run_adjoint_cost n (localQFT n) (Ket (ZeroStr n))
  rw [← gclen]
  exact gc

private theorem two_mul_localQFT_length_le (n : ℕ) :
    2 * (localQFT n).length ≤ 2 ^ (2 * n + 6) := by
  rw [localQFT_length n]
  have hle2 : n ≤ 2 ^ n := nat_le_two_pow n
  have h1 : n * (n - 1) / 2 * 2 ≤ n * (n - 1) := Nat.div_mul_le_self (n * (n - 1)) 2
  have h2 : n / 2 * 2 ≤ n := Nat.div_mul_le_self n 2
  have hmid : n + n * (n - 1) ≤ n * n := by
    rcases n with _ | n
    · simp
    · rw [Nat.add_sub_cancel]
      exact Nat.le_of_eq (by ring)
  have h4 : n * n ≤ 2 ^ (2 * n) := by
    have hmul := Nat.mul_le_mul hle2 hle2
    rwa [← pow_add, show n + n = 2 * n from by omega] at hmul
  have h5 : 2 * n ≤ 2 ^ (2 * n) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · omega
    · have hstep : 2 ^ (n + 1) ≤ 2 ^ (2 * n) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      have hsplit : 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
      omega
  have h7 : 2 ^ (2 * n) + 2 ^ (2 * n) = 2 ^ (2 * n + 1) := by
    rw [pow_succ]
    omega
  have h8 : 2 ^ (2 * n + 1) ≤ 2 ^ (2 * n + 6) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

def numericalPhaseBudget (n : ℕ) (t : ℕ) : ℕ := t + 2 * (n + 1) + 4

theorem numericalPhaseBudget_two_len (n t : ℕ) :
    2 * ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ (numericalPhaseBudget n t)
      ≤ ((2 : ℝ) ⁻¹) ^ t := by
  have hk : numericalPhaseBudget n t = t + 2 * n + 6 := by
    unfold numericalPhaseBudget
    omega
  have hnat2 : (2 * (localQFT n).length : ℕ) ≤ 2 ^ (2 * n + 6) :=
    two_mul_localQFT_length_le n
  have hle : 2 * ((localQFT n).length : ℝ) / ((2 : ℝ) ^ (2 * n + 6)) ≤ 1 := by
    rw [_root_.div_le_one (by positivity : (0 : ℝ) < ((2 : ℝ) ^ (2 * n + 6)))]
    exact_mod_cast hnat2
  have hinv : ((2 : ℝ) ⁻¹) ^ (2 * n + 6) = 1 / ((2 : ℝ) ^ (2 * n + 6)) := by
    rw [inv_eq_one_div, _root_.div_pow, one_pow]
  have hwpos : (0 : ℝ) < ((2 : ℝ) ⁻¹) ^ t := by positivity
  rw [show ((2 : ℝ) ⁻¹) ^ (numericalPhaseBudget n t)
      = ((2 : ℝ) ⁻¹) ^ t * (1 / ((2 : ℝ) ^ (2 * n + 6))) from by
      rw [hk, ← hinv, ← pow_add]
      congr 1]
  calc 2 * ((localQFT n).length : ℝ) * (((2 : ℝ) ⁻¹) ^ t * (1 / ((2 : ℝ) ^ (2 * n + 6))))
      = ((2 : ℝ) ⁻¹) ^ t * (2 * ((localQFT n).length : ℝ) / ((2 : ℝ) ^ (2 * n + 6))) := by
        ring
    _ ≤ ((2 : ℝ) ⁻¹) ^ t * 1 :=
        mul_le_mul_of_nonneg_left hle (le_of_lt hwpos)
    _ = ((2 : ℝ) ⁻¹) ^ t := by ring

theorem numerical_qft_forward_inverse_born_budget (n t : ℕ) (ψ : QState (Reg n))
    (S : Finset (Reg n)) (hψ : Normalized ψ) :
    let k := numericalPhaseBudget n t
    |MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) (numericalDyadicCircuit k (localQFT n)) ψ) S
      - MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))) ψ) S|
      ≤ ((2 : ℝ) ⁻¹) ^ t ∧
    |MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (numericalDyadicCircuit k (localProgramAdjoint (localQFT n))) ψ) S
      - MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ ψ) S|
      ≤ ((2 : ℝ) ⁻¹) ^ t := by
  intro k
  have hlen : (localProgramAdjoint (localQFT n)).length = (localQFT n).length := by
    simp [localProgramAdjoint]
  have hqftU : relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))
      ∈ Matrix.unitaryGroup (Reg n) ℂ :=
    (relabelGate_mem_unitaryGroup (bitVecEquiv n).symm (QFTMatrix (2 ^ n))).mpr
      (qftMatrix_unitary (by positivity : 0 < 2 ^ n))
  have hbound : ∀ (A B : Matrix (Reg n) (Reg n) ℂ),
      A ∈ Matrix.unitaryGroup (Reg n) ℂ → B ∈ Matrix.unitaryGroup (Reg n) ℂ →
      ‖A - B‖ ≤ ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k →
      |MeasureProb (ApplyGate A ψ) S - MeasureProb (ApplyGate B ψ) S|
        ≤ ((2 : ℝ) ⁻¹) ^ t := by
    intro A B hA hB hAB
    have hAn := normalized_applyGate hA hψ
    have hBn := normalized_applyGate hB hψ
    have h1 := measureProb_sub_le_two_mul_l2 (ApplyGate A ψ) (ApplyGate B ψ) S hAn hBn
    have h2 : ‖toEuclidean_fromVec (ApplyGate A ψ - ApplyGate B ψ)‖
        ≤ ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := by
      have hsub : ApplyGate A ψ - ApplyGate B ψ = ApplyGate (A - B) ψ := by
        funext i
        simp only [ApplyGate, Pi.sub_apply, Matrix.sub_mulVec]
      rw [hsub]
      calc ‖toEuclidean_fromVec (ApplyGate (A - B) ψ)‖
          ≤ ‖A - B‖ * ‖toEuclidean_fromVec ψ‖ := norm_applyGate_le _ _
        _ = ‖A - B‖ := by rw [(normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ, mul_one]
        _ ≤ ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := hAB
    have hnum : 2 * (((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k) ≤ ((2 : ℝ) ⁻¹) ^ t := by
      have hsplit : 2 * (((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k)
          = 2 * ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := by ring
      rw [hsplit]
      exact numericalPhaseBudget_two_len n t
    calc |MeasureProb (ApplyGate A ψ) S - MeasureProb (ApplyGate B ψ) S|
        ≤ 2 * ‖toEuclidean_fromVec (ApplyGate A ψ - ApplyGate B ψ)‖ := h1
      _ ≤ 2 * (((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k) := by linarith [h2]
      _ ≤ ((2 : ℝ) ⁻¹) ^ t := hnum

  have herrF : ‖numericalProgramMatrix k (localQFT n)
      - relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))‖
      ≤ ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := by
    have h := numericalProgramMatrix_error k (localQFT n)
    rw [localProgramMatrix_localQFT n] at h
    exact h
  obtain ⟨runF, -, matUn, -, -⟩ :=
    numericalDyadicProgram_run n k (localQFT n) (Ket (ZeroStr n))
  have runFψ := (numericalDyadicProgram_run n k (localQFT n) ψ).1
  rw [runFψ]
  refine ⟨hbound _ _ matUn hqftU herrF, ?_⟩

  obtain ⟨runA, -, matAn, -, -⟩ :=
    numericalDyadicProgram_run n k (localProgramAdjoint (localQFT n)) (Ket (ZeroStr n))
  have runAψ := (numericalDyadicProgram_run n k (localProgramAdjoint (localQFT n)) ψ).1
  have herrA : ‖numericalProgramMatrix k (localProgramAdjoint (localQFT n))
      - (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ‖
      ≤ ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := by
    have h := numericalProgramMatrix_error k (localProgramAdjoint (localQFT n))
    rw [hlen] at h
    rw [(localQFT_exact_positive_matrix n).2] at h
    exact h
  rw [runAψ]
  exact hbound _ _ matAn
    (unitaryGroup_conjTranspose_mem hqftU) herrA

theorem numerical_qft_actual_grid_readout_and_arithmetic_ledger :
    ∀ (n t : ℕ) (y : Fin (2 ^ n)),
    let k := numericalPhaseBudget n t
    MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (numericalDyadicCircuit k (localProgramAdjoint (localQFT n)))
        (relabelState (bitVecEquiv n).symm (PhaseState (2 ^ n) y))) {((bitVecEquiv n).symm y)}
      ≥ 1 - ((2 : ℝ) ⁻¹) ^ t ∧
    numericalDyadicTermCount k (localQFT n) = 2 * (k + 7) * (n * (n - 1) / 2) ∧
    numericalDyadicSquaringCount k (localQFT n) = (k + 7) * (n * (n - 1) / 2) := by
  intro n t y k
  set input := relabelState (bitVecEquiv n).symm (PhaseState (2 ^ n) y) with hindef
  have hinputnorm : Normalized input :=
    relabelState_normalized _ _ (phaseState_normalized (by positivity : 0 < 2 ^ n) y.val)
  have hexact : ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ input
      = Ket ((bitVecEquiv n).symm y) := by
    rw [relabelGate_conjTranspose, applyGate_relabelGate,
      qftMatrix_conjTranspose_mulVec_phaseState (by positivity : 0 < 2 ^ n) y,
      relabelState_ket]
  obtain ⟨runA, -, matAn, -, -⟩ :=
    numericalDyadicProgram_run n k (localProgramAdjoint (localQFT n)) input
  have hnumnorm : Normalized (Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (numericalDyadicCircuit k (localProgramAdjoint (localQFT n))) input) := by
    rw [runA]
    exact normalized_applyGate matAn hinputnorm

  have hmp := measureProb_sub_le_two_mul_l2
    (Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (numericalDyadicCircuit k (localProgramAdjoint (localQFT n))) input)
    (Ket ((bitVecEquiv n).symm y)) {((bitVecEquiv n).symm y)}
    hnumnorm (normalized_ket _)
  have hdist : ‖toEuclidean_fromVec (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (numericalDyadicCircuit k (localProgramAdjoint (localQFT n))) input
      - Ket ((bitVecEquiv n).symm y))‖
      ≤ ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := by
    have hsub : ApplyGate (numericalProgramMatrix k (localProgramAdjoint (localQFT n))) input
        - Ket ((bitVecEquiv n).symm y)
        = ApplyGate (numericalProgramMatrix k (localProgramAdjoint (localQFT n))
          - (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ) input := by
      rw [← hexact]
      funext i
      simp only [ApplyGate, Pi.sub_apply, Matrix.sub_mulVec]
    rw [runA, hsub]
    have herrA : ‖numericalProgramMatrix k (localProgramAdjoint (localQFT n))
        - (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ‖
        ≤ ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := by
      have hlen : (localProgramAdjoint (localQFT n)).length = (localQFT n).length := by
        simp [localProgramAdjoint]
      have h := numericalProgramMatrix_error k (localProgramAdjoint (localQFT n))
      rw [hlen] at h
      rw [(localQFT_exact_positive_matrix n).2] at h
      exact h
    calc ‖toEuclidean_fromVec (ApplyGate
          (numericalProgramMatrix k (localProgramAdjoint (localQFT n))
            - (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ) input)‖
        ≤ ‖numericalProgramMatrix k (localProgramAdjoint (localQFT n))
            - (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ‖
          * ‖toEuclidean_fromVec input‖ := norm_applyGate_le _ _
      _ = ‖numericalProgramMatrix k (localProgramAdjoint (localQFT n))
            - (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ‖ := by
          rw [(normalized_iff_norm_toEuclidean_fromVec input).mp hinputnorm, mul_one]
      _ ≤ ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := herrA
  have hnum : 2 * (((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k) ≤ ((2 : ℝ) ⁻¹) ^ t := by
    have hsplit : 2 * (((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k)
        = 2 * ((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k := by ring
    rw [hsplit]
    exact numericalPhaseBudget_two_len n t
  have hprob1 : MeasureProb (Ket ((bitVecEquiv n).symm y)) {((bitVecEquiv n).symm y)} = 1 :=
    measureProb_ket_self _
  rw [hprob1] at hmp
  have hle : MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (numericalDyadicCircuit k (localProgramAdjoint (localQFT n))) input)
      {((bitVecEquiv n).symm y)} ≥ 1 - ((2 : ℝ) ⁻¹) ^ t := by
    have hstep : 2 * ‖toEuclidean_fromVec (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (numericalDyadicCircuit k (localProgramAdjoint (localQFT n))) input
        - Ket ((bitVecEquiv n).symm y))‖
        ≤ 2 * (((localQFT n).length : ℝ) * ((2 : ℝ) ⁻¹) ^ k) :=
      mul_le_mul_of_nonneg_left hdist (by norm_num : (0 : ℝ) ≤ 2)
    have hmp' := hmp.trans hstep
    have h1 := (abs_le.mp hmp').1
    linarith [h1, hnum]
  refine ⟨hle, ?_, ?_⟩
  · rw [numericalDyadicTermCount_eq k (localQFT n)]
    congr 1
    exact (localQFT_class_counts n).2.1
  · rw [numericalDyadicSquaringCount_eq k (localQFT n)]
    congr 1
    exact (localQFT_class_counts n).2.1

theorem numerical_qft_concrete_consumer :
    numericalPhaseBudget 2 3 = 13 ∧
    numericalPhaseBudget 0 0 = 6 ∧
    piRatApprox 0 = 38279241713339684 / 12184551018734375 ∧
    16 * Real.arctan ((1 / 5 : ℝ)) - 4 * Real.arctan ((1 / 239 : ℝ)) = Real.pi ∧
    (let k := numericalPhaseBudget 2 3;
      MeasureProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ)
        (numericalDyadicCircuit k (localProgramAdjoint (localQFT 2)))
        (relabelState (bitVecEquiv 2).symm (PhaseState (2 ^ 2) 2)))
        {((bitVecEquiv 2).symm ⟨2, by norm_num⟩)}
        ≥ 1 - ((2 : ℝ) ⁻¹) ^ 3 ∧
      numericalDyadicTermCount k (localQFT 2) = 2 * (k + 7) * (2 * (2 - 1) / 2) ∧
      numericalDyadicSquaringCount k (localQFT 2) = (k + 7) * (2 * (2 - 1) / 2)) := by
  refine ⟨rfl, rfl, ?_, rational_machin_pi_identity, ?_⟩
  · norm_num [piRatApprox, atanRatSeries]
  · intro k
    have hinst := numerical_qft_actual_grid_readout_and_arithmetic_ledger 2 3 ⟨2, by norm_num⟩
    obtain ⟨h1, h2, h3⟩ := hinst
    exact ⟨h1, h2, h3⟩

end Qatlib.Concepts.NativeNumerics.NumericalQFT
