/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.QuditTeleport.TeleportCore.Transform
import Qatlib.Concepts.LchsSimulation.StaticLchs.HybridError
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.SpectralReadout.PhaseReadout.BornPerturbation
set_option warningAsError false

open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder Classical

set_option autoImplicit false

variable {n : ℕ}

theorem unitaryGroup_conjTranspose_mem {U : Matrix (Reg n) (Reg n) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Reg n) ℂ) : Uᴴ ∈ Matrix.unitaryGroup (Reg n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_conjTranspose]
  have h0 := Matrix.mem_unitaryGroup_iff.mp hU
  rwa [Matrix.star_eq_conjTranspose] at h0

theorem relabelState_ket {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (e : I ≃ J) (i : I) : relabelState e (Ket i) = Ket (e i) := by
  funext x
  show (Ket i) (e.symm x) = Ket (e i) x
  simp only [Ket]
  by_cases h : e.symm x = i
  · rw [if_pos h, if_pos ((Equiv.symm_apply_eq e).mp h)]
  · rw [if_neg h, if_neg (fun h' => h ((Equiv.symm_apply_eq e).mpr h'))]

theorem relabelState_normalized {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    [DecidableEq J] (e : I ≃ J) (v : QState I) (hv : Normalized v) :
    Normalized (relabelState e v) := by
  unfold Normalized at hv ⊢
  show ∑ i, ‖v (e.symm i)‖ ^ 2 = 1
  rw [Equiv.sum_comp e.symm (fun i => ‖v i‖ ^ 2)]
  exact hv

theorem measureProb_ket_self {I : Type*} [Fintype I] [DecidableEq I] (t : I) :
    MeasureProb (Ket t) {t} = 1 := by
  show ∑ i ∈ {t}, BornProb (Ket t) i = 1
  rw [Finset.sum_singleton]
  show ‖Ket t t‖ ^ 2 = 1
  simp [Ket]

theorem approxLocalQFT_forward_inverse_born_error (n b : ℕ) (ψ : QState (Reg n))
    (S : Finset (Reg n)) (hψ : Normalized ψ) :
    |MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) (localProgramCircuit (approxLocalQFT n b)) ψ) S -
      MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))) ψ) S|
      ≤ Real.pi * (n : ℝ) / (2 ^ b : ℝ) ∧
    |MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (localProgramCircuit (localProgramAdjoint (approxLocalQFT n b))) ψ) S -
      MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ ψ) S|
      ≤ Real.pi * (n : ℝ) / (2 ^ b : ℝ) := by
  obtain ⟨run, adj, -, -, matU, -⟩ :=
    localDyadicProgram_run_adjoint_cost n (approxLocalQFT n b) ψ
  obtain ⟨g9fwd, g9adj⟩ := approxLocalQFT_operator_error n b
  have hqftU : relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))
      ∈ Matrix.unitaryGroup (Reg n) ℂ :=
    (relabelGate_mem_unitaryGroup (bitVecEquiv n).symm (QFTMatrix (2 ^ n))).mpr
      (qftMatrix_unitary (by positivity : 0 < 2 ^ n))
  have hψnorm : ‖toEuclidean_fromVec ψ‖ = 1 :=
    (normalized_iff_norm_toEuclidean_fromVec ψ).mp hψ
  have hbound : ∀ (A B : Matrix (Reg n) (Reg n) ℂ),
      A ∈ Matrix.unitaryGroup (Reg n) ℂ → B ∈ Matrix.unitaryGroup (Reg n) ℂ →
      ‖A - B‖ ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1) →
      |MeasureProb (ApplyGate A ψ) S - MeasureProb (ApplyGate B ψ) S|
        ≤ Real.pi * (n : ℝ) / (2 ^ b : ℝ) := by
    intro A B hA hB hAB
    have hAn := normalized_applyGate hA hψ
    have hBn := normalized_applyGate hB hψ
    have h1 := measureProb_sub_le_two_mul_l2 (ApplyGate A ψ) (ApplyGate B ψ) S hAn hBn
    have h2 : ‖toEuclidean_fromVec (ApplyGate A ψ - ApplyGate B ψ)‖
        ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1) := by
      have hsub : ApplyGate A ψ - ApplyGate B ψ = ApplyGate (A - B) ψ := by
        funext i
        simp only [ApplyGate, Pi.sub_apply, Matrix.sub_mulVec]
      rw [hsub]
      calc ‖toEuclidean_fromVec (ApplyGate (A - B) ψ)‖
          ≤ ‖A - B‖ * ‖toEuclidean_fromVec ψ‖ := norm_applyGate_le _ _
        _ = ‖A - B‖ := by rw [hψnorm, mul_one]
        _ ≤ Real.pi * (n : ℝ) / 2 ^ (b + 1) := hAB
    have h3 : 2 * (Real.pi * (n : ℝ) / (2 ^ (b + 1) : ℝ))
        = Real.pi * (n : ℝ) / (2 ^ b : ℝ) := by
      rw [show (2:ℝ) ^ (b + 1) = 2 ^ b * 2 from pow_succ _ _]
      field_simp
    calc |MeasureProb (ApplyGate A ψ) S - MeasureProb (ApplyGate B ψ) S|
        ≤ 2 * ‖toEuclidean_fromVec (ApplyGate A ψ - ApplyGate B ψ)‖ := h1
      _ ≤ 2 * (Real.pi * (n : ℝ) / 2 ^ (b + 1)) := by linarith [h2]
      _ = Real.pi * (n : ℝ) / (2 ^ b : ℝ) := h3
  rw [run]
  refine ⟨hbound _ _ matU hqftU g9fwd, ?_⟩
  obtain ⟨runA, -, -, -, -, -, -, -, -⟩ :=
    localDyadicProgram_run_adjoint_cost n (localProgramAdjoint (approxLocalQFT n b)) ψ
  rw [adj] at g9adj
  rw [runA, adj]
  exact hbound _ _ (unitaryGroup_conjTranspose_mem matU)
    (unitaryGroup_conjTranspose_mem hqftU) g9adj

theorem localQFT_grid_actual_readout_consumer (n b : ℕ) (j : Fin (2 ^ n)) :
    let input := relabelState (bitVecEquiv n).symm (PhaseState (2 ^ n) j.val)
    localGridReadoutCircuit n b = localProgramCircuit (localProgramAdjoint (approxLocalQFT n b)) ∧
    Normalized (Run (1 : Matrix (Reg n) (Reg n) ℂ) (localGridReadoutCircuit n b) input) ∧
    MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) (localGridReadoutCircuit n b) input)
      {(bitVecEquiv n).symm j} ≥ 1 - Real.pi * (n : ℝ) / (2 ^ b : ℝ) ∧
    (n ≤ b + 2 → Run (1 : Matrix (Reg n) (Reg n) ℂ) (localGridReadoutCircuit n b) input =
      Ket ((bitVecEquiv n).symm j)) ∧
    QueryCount (localGridReadoutCircuit n b) = 0 ∧
    GateCount (localGridReadoutCircuit n b) =
      n + (∑ i ∈ Finset.range n, min (n - 1 - i) (b + 1)) + n / 2 := by
  show _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _
  obtain ⟨run, adj, -, -, matU, qc, gc, gcadj, -⟩ :=
    localDyadicProgram_run_adjoint_cost n (approxLocalQFT n b)
      (relabelState (bitVecEquiv n).symm (PhaseState (2 ^ n) j.val))
  obtain ⟨runA, -, -, -, -, qcA, -, -, -⟩ := localDyadicProgram_run_adjoint_cost n
    (localProgramAdjoint (approxLocalQFT n b))
    (relabelState (bitVecEquiv n).symm (PhaseState (2 ^ n) j.val))
  have hinputnorm : Normalized (relabelState (bitVecEquiv n).symm (PhaseState (2 ^ n) j.val)) :=
    relabelState_normalized _ _ (phaseState_normalized (by positivity : 0 < 2 ^ n) j.val)
  have hexact : ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n)))ᴴ
        (relabelState (bitVecEquiv n).symm (PhaseState (2 ^ n) j.val))
      = Ket ((bitVecEquiv n).symm j) := by
    rw [relabelGate_conjTranspose, applyGate_relabelGate,
      qftMatrix_conjTranspose_mulVec_phaseState (by positivity : 0 < 2 ^ n) j,
      relabelState_ket]
  refine ⟨rfl, ?_, ?_, ?_, qcA, ?_⟩
  · show Normalized (Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (localProgramCircuit (localProgramAdjoint (approxLocalQFT n b))) _)
    rw [runA, adj]
    exact normalized_applyGate (unitaryGroup_conjTranspose_mem matU) hinputnorm
  · obtain ⟨-, g10adj⟩ := approxLocalQFT_forward_inverse_born_error n b
      (relabelState (bitVecEquiv n).symm (PhaseState (2 ^ n) j.val))
      {(bitVecEquiv n).symm j} hinputnorm
    rw [hexact, measureProb_ket_self] at g10adj
    have h1 := (abs_le.mp g10adj).1
    show MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (localProgramCircuit (localProgramAdjoint (approxLocalQFT n b)))
        (relabelState (bitVecEquiv n).symm (PhaseState (2 ^ n) j.val)))
        {(bitVecEquiv n).symm j} ≥ 1 - Real.pi * (n : ℝ) / (2 ^ b : ℝ)
    linarith [h1]
  · intro hn
    have hcomplete := (approxLocalQFT_actual_filter_and_cost n b).2.2.2.2 hn
    show Run (1 : Matrix (Reg n) (Reg n) ℂ)
        (localProgramCircuit (localProgramAdjoint (approxLocalQFT n b))) _ = _
    rw [runA, adj, hcomplete, localProgramMatrix_localQFT n, hexact]
  · show GateCount (localProgramCircuit (localProgramAdjoint (approxLocalQFT n b))) = _
    rw [gcadj]
    exact gc.symm.trans (approxLocalQFT_actual_filter_and_cost n b).2.2.1

theorem localQFT_three_bit_readout_and_inverse_consumer :
    let input := relabelState (bitVecEquiv 3).symm (PhaseState 8 5)
    let gs := localQFT 3
    Run (1 : Matrix (Reg 3) (Reg 3) ℂ) (localProgramCircuit (localProgramAdjoint gs)) input =
      Ket (![true,false,true] : Reg 3) ∧
    GateCount (localProgramCircuit gs) = 7 ∧
    Run (1 : Matrix (Reg 3) (Reg 3) ℂ)
      (localProgramCircuit (gs ++ localProgramAdjoint gs)) (Ket (![true,false,true] : Reg 3)) =
        Ket (![true,false,true] : Reg 3) ∧
    GateCount (localProgramCircuit (gs ++ localProgramAdjoint gs)) = 14 := by
  show _ ∧ _ ∧ _ ∧ _
  have h53 : (bitVecEquiv 3).symm ⟨5, by norm_num⟩ = (![true, false, true] : Reg 3) :=
    (Equiv.symm_apply_eq (bitVecEquiv 3)).mpr (by decide)
  obtain ⟨runF, adjF, -, -, matUF, -, gcF, -, -⟩ :=
    localDyadicProgram_run_adjoint_cost 3 (localQFT 3) (Ket (![true,false,true] : Reg 3))
  obtain ⟨runA, -, -, -, -, -, -, -, -⟩ := localDyadicProgram_run_adjoint_cost 3
    (localProgramAdjoint (localQFT 3)) (relabelState (bitVecEquiv 3).symm (PhaseState 8 5))
  obtain ⟨runRT, -, -, -, -, -, gcRT, -, -⟩ := localDyadicProgram_run_adjoint_cost 3
    (localQFT 3 ++ localProgramAdjoint (localQFT 3)) (Ket (![true,false,true] : Reg 3))
  have hexact : ApplyGate (relabelGate (bitVecEquiv 3).symm (QFTMatrix (2 ^ 3)))ᴴ
        (relabelState (bitVecEquiv 3).symm (PhaseState 8 5))
      = Ket (![true,false,true] : Reg 3) := by
    rw [relabelGate_conjTranspose, applyGate_relabelGate]
    show relabelState (bitVecEquiv 3).symm (ApplyGate (QFTMatrix 8)ᴴ (PhaseState 8 5)) = _
    rw [show (5 : ℕ) = ((⟨5, by norm_num⟩ : Fin 8).val) from rfl,
      qftMatrix_conjTranspose_mulVec_phaseState (by norm_num : 0 < 8) ⟨5, by norm_num⟩,
      relabelState_ket, h53]
  have hUstar : (localProgramMatrix (localQFT 3))ᴴ * localProgramMatrix (localQFT 3) = 1 := by
    have h0 := Matrix.mem_unitaryGroup_iff'.mp matUF
    rwa [Matrix.star_eq_conjTranspose] at h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · show Run (1 : Matrix (Reg 3) (Reg 3) ℂ)
        (localProgramCircuit (localProgramAdjoint (localQFT 3)))
        (relabelState (bitVecEquiv 3).symm (PhaseState 8 5)) = _
    rw [runA, adjF, localProgramMatrix_localQFT 3, hexact]
  · rw [gcF]
    decide
  · show Run (1 : Matrix (Reg 3) (Reg 3) ℂ)
        (localProgramCircuit (localQFT 3 ++ localProgramAdjoint (localQFT 3))) _ = _
    rw [runRT, localProgramMatrix_append, adjF, hUstar, applyGate_one]
  · rw [gcRT, List.length_append,
      show (localProgramAdjoint (localQFT 3)).length = (localQFT 3).length from by
        simp [localProgramAdjoint],
      show (localQFT 3).length = 7 from by decide]

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
