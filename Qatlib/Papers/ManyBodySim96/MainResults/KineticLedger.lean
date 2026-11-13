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

/-!
# Kinetic Fourier-transform costs and position grids

This module records the exact local Fourier-transform implementation and the quadratic gate
bound for a forward and inverse transform pair. It identifies kinetic and pair-potential
evolutions before and after lifting to a particle register, and verifies the spacing, range, and
injectivity of the discretized position grid.

The mathematical setting is that of [Wiesner1996].

## Main statements

* `localQFT_program_ledger`: Records the exact forward and adjoint Fourier-program gate counts,
  zero forward query count, Fourier matrix identity, adjoint identity, and unitarity on `k`
  qubits.
* `particle_qft_gate_bound`: For `k ≥ 1`, the Fourier-transform pairs for `N` particles and `r`
  segments cost at most `4 * N * r * k ^ 2` gates.
* `pairPotential_particle_lift`: Lifting a pair-potential Hamiltonian to a partitioned particle
  register commutes with its exact evolution.
* `posValue_injective`: Distinct grid labels represent distinct positions when `L > 0`.

## References

* [Wiesner, 1996][Wiesner1996]
-/

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

/-- Records the exact forward and adjoint Fourier-program gate counts, zero forward query count,
Fourier matrix identity, adjoint identity, and unitarity on `k` qubits. [Wiesner1996] -/
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

/-- The local `k`-qubit Fourier program has a unitary matrix. -/
theorem qftProgram_unitary (k : ℕ) :
    localProgramMatrix (localQFT k) ∈ Matrix.unitaryGroup (Reg k) ℂ :=
  (localQFT_program_ledger k).2.2.2.2.2

/-- In the Fourier basis, the kinetic layer equals exact kinetic Hamiltonian evolution and is
unitary. [Wiesner1996] -/
theorem kinetic_actual_qft (k : ℕ) (lam : Fin (2 ^ k) → ℝ) (dt : ℝ) :
    HamiltonianEvolution (kineticHamiltonian (QFTMatrix (2 ^ k)) lam) dt =
        kineticLayer (QFTMatrix (2 ^ k)) lam dt ∧
      kineticLayer (QFTMatrix (2 ^ k)) lam dt ∈ Matrix.unitaryGroup (Fin (2 ^ k)) ℂ := by
  refine ⟨kineticLayer_eq_evolution _ (qftMatrix_unitary (Nat.two_pow_pos k)) lam dt,
    kineticLayer_mem_unitaryGroup _ (qftMatrix_unitary (Nat.two_pow_pos k)) lam dt⟩

/-- Lifting a Fourier-diagonalized kinetic Hamiltonian to a partitioned particle register
commutes with its exact evolution. [Wiesner1996] -/
theorem kinetic_particle_lift {N k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (e : Fin (2 ^ (N * k)) ≃ Fin (2 ^ k) × B)
    (lam : Fin (2 ^ k) → ℝ) (dt : ℝ) :
    HamiltonianEvolution (partitionLift e (kineticHamiltonian (QFTMatrix (2 ^ k)) lam)) dt =
      partitionLift e (kineticLayer (QFTMatrix (2 ^ k)) lam dt) := by
  rw [evolution_partitionLift, kineticLayer_eq_evolution _ (qftMatrix_unitary (Nat.two_pow_pos k))]

/-- The combined gate count of the forward and inverse local Fourier transforms on `k` qubits. -/
def kineticQFTGates (k : ℕ) : ℕ := 2 * (k + k * (k - 1) / 2 + k / 2)

/-- For `k ≥ 1`, a forward and inverse Fourier-transform pair uses at most `4 * k ^ 2` gates. -/
theorem kineticQFTGates_le (k : ℕ) (hk : 1 ≤ k) : kineticQFTGates k ≤ 4 * k ^ 2 := by
  unfold kineticQFTGates
  have hA : 2 * (k * (k - 1) / 2) ≤ k * k :=
    (Nat.mul_div_le _ _).trans (Nat.mul_le_mul_left k (Nat.sub_le k 1))
  have hB : 2 * (k / 2) ≤ k := Nat.mul_div_le _ _
  have hexp : 2 * (k + k * (k - 1) / 2 + k / 2)
      = 2 * k + 2 * (k * (k - 1) / 2) + 2 * (k / 2) := by ring
  rw [hexp]
  nlinarith [hA, hB, hk]

/-- For `k ≥ 1`, the Fourier-transform pairs for `N` particles and `r` segments cost at most `4
* N * r * k ^ 2` gates. -/
theorem particle_qft_gate_bound (N k r : ℕ) (hk : 1 ≤ k) :
    N * r * kineticQFTGates k ≤ 4 * N * r * k ^ 2 := by
  calc N * r * kineticQFTGates k ≤ N * r * (4 * k ^ 2) :=
        Nat.mul_le_mul_left _ (kineticQFTGates_le k hk)
    _ = 4 * N * r * k ^ 2 := by ring

/-- Flattens a two-particle potential table into a vector using the product-index equivalence. -/
def pairPotentialVec (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ) :
    Fin (2 ^ k * 2 ^ k) → ℝ :=
  fun i => V (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2

/-- The diagonal Hamiltonian of a real two-particle potential is Hermitian. -/
theorem pairPotential_hermitian (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ) :
    (potentialHamiltonian (pairPotentialVec k V)).IsHermitian :=
  potentialHamiltonian_isHermitian _

/-- A pair-potential layer multiplies each amplitude by the phase of the potential at its two
decoded position labels. [Wiesner1996] -/
theorem pairPotential_action (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ)
    (dt : ℝ) (ψ : QState (Fin (2 ^ k * 2 ^ k))) (i : Fin (2 ^ k * 2 ^ k)) :
    (potentialLayer (pairPotentialVec k V) dt *ᵥ ψ) i =
      phaseVal (dt * V (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2) * ψ i := by
  simp only [potentialLayer, potentialPhaseVec, pairPotentialVec, phaseDiag_mulVec_apply]

/-- Every real pair-potential phase layer is unitary. -/
theorem pairPotential_layer_unitary (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ)
    (dt : ℝ) :
    potentialLayer (pairPotentialVec k V) dt ∈
      Matrix.unitaryGroup (Fin (2 ^ k * 2 ^ k)) ℂ :=
  potentialLayer_mem_unitaryGroup _ dt

/-- A pair-potential layer equals the exact evolution of its diagonal Hamiltonian. -/
theorem pairPotential_layer_evolution (k : ℕ) (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ)
    (dt : ℝ) :
    HamiltonianEvolution (potentialHamiltonian (pairPotentialVec k V)) dt =
      potentialLayer (pairPotentialVec k V) dt :=
  potentialLayer_eq_evolution _ dt

/-- Lifting a pair-potential Hamiltonian to a partitioned particle register commutes with its
exact evolution. [Wiesner1996] -/
theorem pairPotential_particle_lift {N k : ℕ} {B : Type*} [Fintype B] [DecidableEq B]
    (e : Fin (2 ^ (N * k)) ≃ Fin (2 ^ k * 2 ^ k) × B)
    (V : Fin (2 ^ k) → Fin (2 ^ k) → ℝ) (dt : ℝ) :
    HamiltonianEvolution
        (partitionLift e (potentialHamiltonian (pairPotentialVec k V))) dt =
      partitionLift e (potentialLayer (pairPotentialVec k V) dt) := by
  rw [evolution_partitionLift, pairPotential_layer_evolution]

/-- The phase layer for the zero pair potential is the identity matrix. -/
theorem pairPotential_zero_identity (k : ℕ) (dt : ℝ) :
    potentialLayer (pairPotentialVec k (fun _ _ => (0 : ℝ))) dt = 1 := by
  ext i j
  simp only [potentialLayer, potentialPhaseVec, pairPotentialVec, phaseDiag, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h
    simp [phaseVal, NormedSpace.exp_zero]
  · simp [h]

/-- The spacing `L / 2 ^ k` of a grid with `2 ^ k` position labels. -/
def gridStep (k : ℕ) (L : ℝ) : ℝ := L / (2 : ℝ) ^ k

/-- The real position represented by a grid label, equal to its index times the grid spacing. -/
def posValue (k : ℕ) (L : ℝ) (x : Fin (2 ^ k)) : ℝ := (x.val : ℝ) * gridStep k L

/-- A positive interval length gives a positive grid spacing. -/
theorem gridStep_pos {k : ℕ} {L : ℝ} (hL : 0 < L) : 0 < gridStep k L := by
  unfold gridStep
  positivity

/-- Consecutive valid position labels differ by exactly one grid spacing. -/
theorem posValue_succ {k : ℕ} (L : ℝ) (x : Fin (2 ^ k))
    (h : x.val + 1 < 2 ^ k) :
    posValue k L ⟨x.val + 1, h⟩ - posValue k L x = gridStep k L := by
  unfold posValue
  push_cast
  ring

/-- Every represented position is nonnegative when `L > 0`. -/
theorem posValue_nonneg (k : ℕ) (L : ℝ) (x : Fin (2 ^ k)) (hL : 0 < L) :
    0 ≤ posValue k L x := by
  unfold posValue
  exact mul_nonneg (Nat.cast_nonneg _) (gridStep_pos hL).le

/-- Every represented position is strictly less than `L` when `L > 0`. -/
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

/-- Distinct grid labels represent distinct positions when `L > 0`. [Wiesner1996] -/
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
