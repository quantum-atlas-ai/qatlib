/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.LocalQFTReadout
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

namespace Qatlib.Concepts.AEMeanReadout.LocalAEBackend

open Matrix

open scoped Classical Matrix.Norms.L2Operator

set_option autoImplicit false

theorem offgrid_window_filter_map (n : ℕ) (φ : ℝ) :
    (Finset.univ.filter (fun z : Reg n =>
        phaseDistance φ (((bitVecEquiv n z).val : ℝ)/(2^n : ℝ)) ≤ 1/(2^n : ℝ)))
      = (Finset.univ.filter (fun z : Fin (2^n) =>
          phaseDistance φ ((z.val : ℝ)/(2^n : ℝ)) ≤ 1/(2^n : ℝ))).map
        (bitVecEquiv n).symm := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map_equiv,
    Equiv.symm_symm]

theorem local_offgrid_readout_probability (n b : ℕ) (hn : 1 ≤ n) (φ : ℝ) :
    let ψ := relabelState (bitVecEquiv n).symm (offGridPhase (2^n) φ)
    let C := localProgramCircuit (localProgramAdjoint (approxLocalQFT n b))
    let E := Finset.univ.filter (fun z : Reg n =>
      phaseDistance φ (((bitVecEquiv n z).val : ℝ)/(2^n : ℝ)) ≤ 1/(2^n : ℝ))
    MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ) C ψ) E
      ≥ 8/Real.pi^2 - Real.pi*(n:ℝ)/(2^b:ℝ) := by
  have hM : 0 < 2^n := by positivity
  have hM2 : 2 ≤ 2^n := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.pow_add, Nat.pow_one]
    calc (2 : ℕ) = 2*1 := by ring
      _ ≤ 2*2^k := Nat.mul_le_mul le_rfl Nat.one_le_two_pow
  have hcastwin : (Finset.univ.filter (fun z : Fin (2^n) =>
        phaseDistance φ ((z.val : ℝ)/((2^n : ℕ) : ℝ)) ≤ 1/((2^n : ℕ) : ℝ)))
      = Finset.univ.filter (fun z : Fin (2^n) =>
          phaseDistance φ ((z.val : ℝ)/(2^n : ℝ)) ≤ 1/(2^n : ℝ)) := by
    apply Finset.filter_congr
    intro z _
    rw [Nat.cast_pow, Nat.cast_ofNat]
  have hψnorm : Normalized (relabelState (bitVecEquiv n).symm (offGridPhase (2^n) φ)) :=
    relabelState_normalized _ _
      ((offgrid_phase_kernel_formula (2^n) φ ⟨0, hM⟩ hM).2.2)
  have hideal : ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2^n)))ᴴ
        (relabelState (bitVecEquiv n).symm (offGridPhase (2^n) φ))
      = relabelState (bitVecEquiv n).symm (qpeKernel (2^n) φ) := by
    rw [relabelGate_conjTranspose, applyGate_relabelGate]
    rfl
  have hmass : MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm
          (QFTMatrix (2^n)))ᴴ
          (relabelState (bitVecEquiv n).symm (offGridPhase (2^n) φ)))
        (Finset.univ.filter (fun z : Reg n =>
          phaseDistance φ (((bitVecEquiv n z).val : ℝ)/(2^n : ℝ)) ≤ 1/(2^n : ℝ)))
      = ∑ z ∈ Finset.univ.filter (fun z : Fin (2^n) =>
          phaseDistance φ ((z.val : ℝ)/(2^n : ℝ)) ≤ 1/(2^n : ℝ)),
          ‖qpeKernel (2^n) φ z‖^2 := by
    rw [hideal, offgrid_window_filter_map n φ, measureProb_relabelState]
    rfl
  have hwindow := offgrid_phase_window_probability (2^n) φ hM2
  rw [hcastwin] at hwindow
  obtain ⟨-, hborn⟩ := approxLocalQFT_forward_inverse_born_error n b
    (relabelState (bitVecEquiv n).symm (offGridPhase (2^n) φ))
    (Finset.univ.filter (fun z : Reg n =>
      phaseDistance φ (((bitVecEquiv n z).val : ℝ)/(2^n : ℝ)) ≤ 1/(2^n : ℝ))) hψnorm
  have hlower := (abs_le.mp hborn).1
  show MeasureProb (Run (1 : Matrix (Reg n) (Reg n) ℂ)
      (localProgramCircuit (localProgramAdjoint (approxLocalQFT n b)))
      (relabelState (bitVecEquiv n).symm (offGridPhase (2^n) φ)))
      (Finset.univ.filter (fun z : Reg n =>
        phaseDistance φ (((bitVecEquiv n z).val : ℝ)/(2^n : ℝ)) ≤ 1/(2^n : ℝ)))
    ≥ 8/Real.pi^2 - Real.pi*(n:ℝ)/(2^b:ℝ)
  linarith

end Qatlib.Concepts.AEMeanReadout.LocalAEBackend
