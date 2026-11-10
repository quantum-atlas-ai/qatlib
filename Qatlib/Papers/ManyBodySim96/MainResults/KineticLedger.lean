/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ManyBodySim96.MainResults.Basic
import Qatlib.Papers.ManyBodySim96.MainResults.LocalEvolution
import Qatlib.Concepts.QftPreparation.LocalQft
import Qatlib.Concepts.QftPreparation.LocalQFTImplementation
import Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum.LocalDyadicGate
import Qatlib.Concepts.GateVocabulary.GateVocab.CircuitRelabel
import Qatlib.Concepts.TensorRegisters.RegisterModel.TensorRegistersDefs
import Qatlib.Concepts.SpectralFilter.PhaseReadout.PhaseEstimation
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.GateVocabulary.GateVocab
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Concepts.TensorRegisters.RegisterModel
open Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open scoped BigOperators Matrix.Norms.L2Operator Kronecker

namespace Qatlib.Papers.ManyBodySim96.MainResults

theorem localQFT_program_ledger (k : ℕ) :
    GateCount (localProgramCircuit (localQFT k)) = k + k * (k - 1) / 2 + k / 2 ∧
      GateCount (localProgramCircuit (localProgramAdjoint (localQFT k))) =
        k + k * (k - 1) / 2 + k / 2 ∧
      QueryCount (localProgramCircuit (localQFT k)) = 0 ∧
      localProgramMatrix (localQFT k) =
        relabelGate (bitVecEquiv k).symm (QFTMatrix (2 ^ k)) ∧
      localProgramMatrix (localProgramAdjoint (localQFT k)) =
        (localProgramMatrix (localQFT k))ᴴ ∧
      localProgramMatrix (localQFT k) ∈ Matrix.unitaryGroup (Reg k) ℂ := by
  obtain ⟨hmat, hadj⟩ := localQFT_exact_positive_matrix k
  obtain ⟨-, -, -, hgc, hqc, -⟩ := localQFT_exact_gate_counts_and_wires k
  have hunit : localProgramMatrix (localQFT k) ∈ Matrix.unitaryGroup (Reg k) ℂ := by
    rw [hmat]
    exact (relabelGate_mem_unitaryGroup (bitVecEquiv k).symm (QFTMatrix (2 ^ k))).mpr
      (qftMatrix_unitary (Nat.two_pow_pos k))
  have hadj' : localProgramMatrix (localProgramAdjoint (localQFT k)) =
      (localProgramMatrix (localQFT k))ᴴ := by
    rw [hmat]
    exact hadj
  have hadjgc : GateCount (localProgramCircuit (localProgramAdjoint (localQFT k))) =
      k + k * (k - 1) / 2 + k / 2 := by
    obtain ⟨-, -, -, -, -, -, hgcLen, hgcAdj, -⟩ :=
      localDyadicProgram_run_adjoint_cost k (localQFT k) (Ket (ZeroStr k))
    have hlen : (localQFT k).length = k + k * (k - 1) / 2 + k / 2 := by
      rw [← hgcLen]
      exact hgc
    rw [hgcAdj, hlen]
  exact ⟨hgc, hadjgc, hqc, hmat, hadj', hunit⟩

theorem qftProgram_unitary (k : ℕ) :
    localProgramMatrix (localQFT k) ∈ Matrix.unitaryGroup (Reg k) ℂ :=
  (localQFT_program_ledger k).2.2.2.2.2

theorem kinetic_actual_qft (k : ℕ) (lam : Fin (2 ^ k) → ℝ) (dt : ℝ) :
    HamiltonianEvolution (kineticHamiltonian (QFTMatrix (2 ^ k)) lam) dt =
        kineticLayer (QFTMatrix (2 ^ k)) lam dt ∧
      kineticLayer (QFTMatrix (2 ^ k)) lam dt ∈ Matrix.unitaryGroup (Fin (2 ^ k)) ℂ := by
  refine ⟨kineticLayer_eq_evolution _ (qftMatrix_unitary (Nat.two_pow_pos k)) lam dt,
    kineticLayer_mem_unitaryGroup _ (qftMatrix_unitary (Nat.two_pow_pos k)) lam dt⟩

theorem kinetic_particle_lift {N k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (e : Fin (2 ^ (N * k)) ≃ Fin (2 ^ k) × B)
    (lam : Fin (2 ^ k) → ℝ) (dt : ℝ) :
    HamiltonianEvolution (partitionLift e (kineticHamiltonian (QFTMatrix (2 ^ k)) lam)) dt =
      partitionLift e (kineticLayer (QFTMatrix (2 ^ k)) lam dt) := by
  rw [evolution_partitionLift, kineticLayer_eq_evolution _ (qftMatrix_unitary (Nat.two_pow_pos k))]

def kineticQFTGates (k : ℕ) : ℕ := 2 * (k + k * (k - 1) / 2 + k / 2)

theorem kineticQFTGates_le (k : ℕ) (hk : 1 ≤ k) : kineticQFTGates k ≤ 4 * k ^ 2 := by
  unfold kineticQFTGates
  have hA : 2 * (k * (k - 1) / 2) ≤ k * k :=
    (Nat.mul_div_le _ _).trans (Nat.mul_le_mul_left k (Nat.sub_le k 1))
  have hB : 2 * (k / 2) ≤ k := Nat.mul_div_le _ _
  have hexp : 2 * (k + k * (k - 1) / 2 + k / 2)
      = 2 * k + 2 * (k * (k - 1) / 2) + 2 * (k / 2) := by ring
  rw [hexp]
  nlinarith [hA, hB, hk]

theorem particle_qft_gate_bound (N k r : ℕ) (hk : 1 ≤ k) :
    N * r * kineticQFTGates k ≤ 4 * N * r * k ^ 2 := by
  calc N * r * kineticQFTGates k ≤ N * r * (4 * k ^ 2) :=
        Nat.mul_le_mul_left _ (kineticQFTGates_le k hk)
    _ = 4 * N * r * k ^ 2 := by ring

def pairPotentialVec (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ) :
    Fin (2 ^ k * 2 ^ k) → ℝ :=
  fun i => V (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

theorem pairPotential_hermitian (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ) :
    (potentialHamiltonian (pairPotentialVec k V)).IsHermitian :=
  potentialHamiltonian_isHermitian _

theorem pairPotential_action (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ)
    (dt : ℝ) (ψ : QState (Fin (2 ^ k * 2 ^ k))) (i : Fin (2 ^ k * 2 ^ k)) :
    (potentialLayer (pairPotentialVec k V) dt *ᵥ ψ) i =
      phaseVal (dt * V (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) * ψ i := by
  simp only [potentialLayer, potentialPhaseVec, pairPotentialVec, phaseDiag_mulVec_apply]

theorem pairPotential_layer_unitary (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ)
    (dt : ℝ) :
    potentialLayer (pairPotentialVec k V) dt ∈
      Matrix.unitaryGroup (Fin (2 ^ k * 2 ^ k)) ℂ :=
  potentialLayer_mem_unitaryGroup _ dt

theorem pairPotential_layer_evolution (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ)
    (dt : ℝ) :
    HamiltonianEvolution (potentialHamiltonian (pairPotentialVec k V)) dt =
      potentialLayer (pairPotentialVec k V) dt :=
  potentialLayer_eq_evolution _ dt

theorem pairPotential_particle_lift {N k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (e : Fin (2 ^ (N * k)) ≃ Fin (2 ^ k * 2 ^ k) × B)
    (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ) (dt : ℝ) :
    HamiltonianEvolution
        (partitionLift e (potentialHamiltonian (pairPotentialVec k V))) dt =
      partitionLift e (potentialLayer (pairPotentialVec k V) dt) := by
  rw [evolution_partitionLift, pairPotential_layer_evolution]

theorem pairPotential_zero_identity (k : ℕ) (dt : ℝ) :
    potentialLayer (pairPotentialVec k (fun _ _ => (0 : ℝ))) dt = 1 := by
  ext i j
  simp only [potentialLayer, potentialPhaseVec, pairPotentialVec, phaseDiag, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp [phaseVal, NormedSpace.exp_zero]
  · simp [h]

def gridStep (k : ℕ) (L : ℝ) : ℝ := L / (2 : ℝ) ^ k

def posValue (k : ℕ) (L : ℝ) (x : Fin (2 ^ k)) : ℝ := (x.val : ℝ) * gridStep k L

theorem gridStep_pos {k : ℕ} {L : ℝ} (hL : 0 < L) : 0 < gridStep k L := by
  unfold gridStep
  positivity

theorem posValue_succ {k : ℕ} (L : ℝ) (x : Fin (2 ^ k))
    (h : x.val + 1 < 2 ^ k) :
    posValue k L ⟨x.val + 1, h⟩ - posValue k L x = gridStep k L := by
  unfold posValue
  push_cast
  ring

theorem posValue_nonneg (k : ℕ) (L : ℝ) (x : Fin (2 ^ k)) (hL : 0 < L) :
    0 ≤ posValue k L x := by
  unfold posValue
  exact mul_nonneg (Nat.cast_nonneg _) (gridStep_pos hL).le

theorem posValue_lt (k : ℕ) (L : ℝ) (x : Fin (2 ^ k)) (hL : 0 < L) :
    posValue k L x < L := by
  unfold posValue gridStep
  have hpow : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
  have hx : (x.val : ℝ) < (2 : ℝ) ^ k := by
    have := x.isLt
    exact_mod_cast this
  have hs : 0 < L / (2 : ℝ) ^ k := div_pos hL hpow
  calc (x.val : ℝ) * (L / (2 : ℝ) ^ k)
      < (2 : ℝ) ^ k * (L / (2 : ℝ) ^ k) :=
        mul_lt_mul_of_pos_right hx hs
    _ = L := by field_simp

theorem posValue_injective (k : ℕ) (L : ℝ) (hL : 0 < L) :
    Function.Injective (posValue k L) := by
  intro x y hxy
  unfold posValue at hxy
  have hs : 0 < gridStep k L := gridStep_pos hL
  have hcast : (x.val : ℝ) = (y.val : ℝ) := by
    by_contra hne
    have hlt : (x.val : ℝ) < (y.val : ℝ) ∨ (y.val : ℝ) < (x.val : ℝ) := by
      rcases lt_trichotomy (x.val : ℝ) (y.val : ℝ) with h | h | h
      · exact Or.inl h
      · exact absurd h hne
      · exact Or.inr h
    rcases hlt with hlt | hlt
    · have := mul_lt_mul_of_pos_right hlt hs
      linarith [hxy]
    · have := mul_lt_mul_of_pos_right hlt hs
      linarith [hxy]
  exact Fin.ext (by exact_mod_cast hcast)

end Qatlib.Papers.ManyBodySim96.MainResults
