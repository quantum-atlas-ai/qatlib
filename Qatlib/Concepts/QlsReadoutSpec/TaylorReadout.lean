/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.EndToEnd
import Qatlib.Concepts.QuditTeleport.TeleportCore.BellReferenceProtocol

/-!
# Concrete Taylor simulation and phase readout

This module instantiates logarithmic-cutoff Taylor simulation with Pauli Hamiltonians. It gives
explicit query and gate counts for the noncommuting X + Z example and error-controlled
four-point phase readout for Z with a Hadamard-prepared input. Related mathematical background
is given in [BerryEtAl2015Taylor].

## Main statements

* `log_taylor_noncommuting_xz_actual_consumer`: Concrete simulation cost and workspace error.
* `log_taylor_z_hadamard_actual_readout`: Concrete phase-event masses and circuit costs.

## References

* [Berry et al., 2015][BerryEtAl2015Taylor]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 800000
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.CoherentSim.CleanQPEBands
open Qatlib.Concepts.QuditTeleport.TeleportCore
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.CoherentSim.EndToEnd
open Qatlib.Concepts.CoherentSim.TaylorBounds
open Qatlib.Concepts.CoherentSim.TaylorEncoding

namespace Qatlib.Concepts.QlsReadoutSpec.TaylorReadout
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open scoped BigOperators Matrix.Norms.L2Operator

/-- Either Pauli X or Pauli Z is both unitary and Hermitian. -/
private theorem logTaylor_pauli (a : Bool) :
    (if a then pauliZ else pauliX) ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧
    (if a then pauliZ else pauliX).IsHermitian := by
  have hh : (if a then pauliZ else pauliX)ᴴ = (if a then pauliZ else pauliX) := by
    cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
      norm_num [pauliX, pauliZ, Matrix.conjTranspose_apply]
  refine ⟨?_, hh⟩
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, hh]
  cases a <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [pauliX, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]

/-- The four-point QPE kernel for the two Pauli Z eigenphases is exactly the basis state at
index three or one, respectively. -/
private theorem logTaylor_Z_kernel (j : Fin 2) (z : Fin 4) :
    qpeKernel 4 (-(Real.pi / 2) * (if j = 0 then 1 else -1) / (2 * Real.pi)) z =
      Ket (if j = 0 then (3 : Fin 4) else 1) z := by
  have hp : Real.pi ≠ 0 := Real.pi_ne_zero
  fin_cases j
  · have he : -(Real.pi / 2) * (1 : ℝ) / (2 * Real.pi) = -(1 / 4 : ℝ) := by
      field_simp
      norm_num
    simp only [Fin.zero_eta, Fin.isValue, ↓reduceIte]
    rw [he, ← qpeKernel_int_add 4 (-(1 / 4 : ℝ)) z 1]
    convert! (offgrid_phase_geometric_and_periodic 4 0 z (by norm_num)).2.2 (3 : Fin 4) using 1
    norm_num
  · have he : -(Real.pi / 2) * (-1 : ℝ) / (2 * Real.pi) = (1 / 4 : ℝ) := by
      field_simp
      norm_num
    simp only [Fin.ext_iff, Fin.val_zero, Nat.one_ne_zero, if_false]
    rw [he]
    convert! (offgrid_phase_geometric_and_periodic 4 0 z (by norm_num)).2.2 (1 : Fin 4) using 1
    norm_num

/-- The specified Taylor circuit for X + Z has cutoff 14, 168 queries, and 388 gates, and
approximates unit-time evolution with full-workspace error at most half the input norm. -/
theorem log_taylor_noncommuting_xz_actual_consumer :   let h := fun _ : Fin 2 => (1:ℝ)
  let U := fun j : Fin 2 => if j=0 then pauliX else pauliZ
  let j0 : Fin 2 := 0
  let cs := logTaylorSimulationWord (D := 2) h j0 1 2 1 1
  logTaylorCutoff (taylorSegments 2 1) 1 = 14 ∧
  adjointQueryCount cs = 168 ∧ adjointGateCount cs = 388 ∧
  (∀ psi : QState (Fin 2), ‖toEuclidean_fromVec
    (evaluate (taylorQuery U 14) cs *ᵥ (taylorFrame j0 14 *ᵥ psi) -
      taylorFrame j0 14 *ᵥ (hamiltonianEvolution (pauliX+pauliZ) 1 *ᵥ psi))‖ ≤
    (1/2:ℝ)*‖toEuclidean_fromVec psi‖) := by
  let h := fun _ : Fin 2 => (1:ℝ)
  let U := fun j : Fin 2 => if j=0 then pauliX else pauliZ
  have hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ (U j).IsHermitian := by
    intro j
    fin_cases j
    · exact logTaylor_pauli false
    · exact logTaylor_pauli true
  have hH : (∑ j, (h j:ℂ) • U j) = pauliX+pauliZ := by
    simp [h, U, Fin.sum_univ_two]
  have hL : (∑ j, |h j|) ≤ (2:ℕ) := by norm_num [h, Fin.sum_univ_two]
  have hc := log_taylor_actual_program_and_inverse_cost 2 h U 0 1 2 1 1 hU hL (by norm_num)
  have he := log_taylor_coherent_full_workspace_error 2 h U 0 1 2 1 1 hU hL (by norm_num)
  rw [hH] at he
  have hs : taylorSegments 2 1 = 4 := rfl
  have hK : logTaylorCutoff 4 1 = 14 := by decide
  refine ⟨hK, ?_, ?_, ?_⟩
  · simpa only [hs, hK, Nat.reduceMul] using! hc.2.1
  · simpa only [hs, hK, Nat.reduceMul, Nat.reduceAdd] using! hc.2.2.1
  · simpa only [hs, hK, pow_one] using! he

/-- For `K = 2 * (k + 9)`, the specified Pauli Z readout circuit uses `36 * K` queries and `72 *
K + 165` gates. Its mass on phase indices one and three is at least `1 - (1/2)^k`, and each
individual mass differs from one half by at most `(1/2)^k`. -/
theorem log_taylor_z_hadamard_actual_readout : ∀ k : ℕ,
  let h := fun _ : Unit => (1:ℝ)
  let U := fun _ : Unit => pauliZ
  let B := relabelGate boolEquivFin2 Hadamard
  let cs := logTaylorQPEPreparedWord h () (Real.pi/2) 1 2 4 k B
  let out := logTaylorQPEOutput h U () (Real.pi/2) 1 2 4 k (by omega) B 0
  let K := 2*(k+9)
  adjointQueryCount cs = 36*K ∧ adjointGateCount cs = 72*K+165 ∧
  cleanQPEEventMass 4 out ({1,3} : Finset (Fin 4)) ≥ 1-(1/2:ℝ)^k ∧
  (∀ z ∈ ({1,3} : Finset (Fin 4)),
    |cleanQPEEventMass 4 out {z} - 1/2| ≤ (1/2:ℝ)^k) := by
  intro k
  let h := fun _ : Unit => (1:ℝ)
  let U := fun _ : Unit => pauliZ
  let B := relabelGate boolEquivFin2 Hadamard
  let eig := fun j : Fin 2 => if j=0 then (1:ℝ) else -1
  have hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin 2) ℂ ∧ (U j).IsHermitian :=
    fun _ => logTaylor_pauli true
  have hL : (∑ j, |h j|) ≤ (1:ℕ) := by norm_num [h]
  have hT : |Real.pi/2| ≤ (2:ℕ) := by
    rw [abs_of_pos (by positivity)]
    have := Real.pi_lt_four
    norm_num at *
    linarith
  have hB : B ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    teleportRelabelGate_mem_unitaryGroup hadamard_unitary boolEquivFin2
  have hs : (∑ a, (h a:ℂ) • U a) =
      (1 : Operator 2) * Matrix.diagonal (fun j => (eig j:ℂ)) * (1 : Operator 2)ᴴ := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [h, U, eig, pauliZ]
  have hbeta (j : Fin 2) : ((1 : Operator 2)ᴴ *ᵥ (B *ᵥ Ket (0:Fin 2))) j =
      (Real.sqrt 2 : ℂ)⁻¹ := by
    fin_cases j <;> norm_num [B, relabelGate, boolEquivFin2, Hadamard,
      Matrix.mulVec, dotProduct, Fin.sum_univ_two, Ket]
  have hc (j : Fin 2) : ‖((1 : Operator 2)ᴴ *ᵥ (B *ᵥ Ket (0:Fin 2))) j‖ ^ 2 = (1/2:ℝ) := by
    rw [hbeta, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), inv_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have ht (E : Finset (Fin 4)) := log_taylor_actual_spectral_qpe_and_cost 2 h U ()
    (Real.pi/2) 1 2 4 k (by norm_num) B 1 eig 0 E hU hL hT hB (Submonoid.one_mem _) hs
  have hm (E : Finset (Fin 4)) :
      |cleanQPEEventMass 4 (logTaylorQPEOutput h U () (Real.pi/2) 1 2 4 k (by norm_num) B 0) E -
        (∑ j : Fin 2, (1/2:ℝ) * (∑ z ∈ E, ‖Ket (if j=0 then (3:Fin 4) else 1) z‖^2))| ≤
      (1/2:ℝ)^k := by
    have hh := (ht E).2.2.2
    try dsimp only at hh
    simpa only [hc, eig, logTaylor_Z_kernel] using! hh
  have hK : logTaylorCutoff (taylorSegments 1 2) (logTaylorQPEPrecision 4 k) = 2*(k+9) := by
    have hc1 : Nat.clog 2 (max 1 (2*(4-1))) = 3 := by decide
    have hc2 : Nat.clog 2 (max 1 (taylorSegments 1 2)) = 2 := by decide
    simp only [logTaylorCutoff, logTaylorQPEPrecision, hc1, hc2]
    try omega
  have hn (a z : Fin 4) : ‖Ket a z‖^2 = if z=a then (1:ℝ) else 0 := by
    by_cases hz : z=a <;> simp [Ket, hz]
  have hz13 : (1 : Fin 4) ≠ 3 := by decide
  have hz31 : (3 : Fin 4) ≠ 1 := Ne.symm hz13
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hq := (ht {1,3}).2.1
    try dsimp only at hq
    conv at hq => rhs; rw [hK]
    norm_num only [taylorSegments] at hq
    change adjointQueryCount (logTaylorQPEPreparedWord h () (Real.pi/2) 1 2 4 k B) =
      36*(2*(k+9))
    calc
      _ = (4-1)*3*4*(2*(k+9)) := hq
      _ = _ := by ring
  · have hg := (ht {1,3}).2.2.1
    try dsimp only at hg
    conv at hg => rhs; rw [hK]
    norm_num only [taylorSegments] at hg
    change adjointGateCount (logTaylorQPEPreparedWord h () (Real.pi/2) 1 2 4 k B) =
      72*(2*(k+9))+165
    calc
      _ = 2*(4-1)+3+(4-1)*4*(6*(2*(k+9))+13) := hg
      _ = _ := by ring
  · have hh := hm {1,3}
    simp_rw [hn] at hh
    norm_num [Fin.sum_univ_two, hz13, hz31] at hh
    have hb := (abs_le.mp hh).1
    change 1-(1/2:ℝ)^k ≤ _
    linarith
  · intro z hz
    have hh := hm {z}
    simp_rw [hn] at hh
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> norm_num [Fin.sum_univ_two, hz13, hz31] at hh ⊢ <;> exact hh

end Qatlib.Concepts.QlsReadoutSpec.TaylorReadout
