/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.LocalMachine.LocalTransport.ControlledQueryCircuit
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.QspSimulation.Achievability.HamiltonianSimulation
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Concepts.CopyEvolution.Discriminate

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.PhaseGeometry.Phase

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open scoped Matrix.Norms.L2Operator

variable {H I : Type*} [Fintype H] [Fintype I] [DecidableEq H] [DecidableEq I]

noncomputable def compileHamiltonian (F : Matrix H I ℂ)
    (bc : ℂ) (zc : List ℂ) (bs : ℂ) (zs : List ℂ) :
    List (AdjointStep (Bool × (Bool × H))) :=
  compileSelected (compileRealPartQSVT (rangeProjector F) (rangeProjector F) bc zc)
    (.gate ((-Complex.I) • (1 : Matrix (Bool × H) (Bool × H) ℂ)) ::
      compileRealPartQSVT (rangeProjector F) (rangeProjector F) bs zs)

omit [DecidableEq I] in

theorem evaluate_compileHamiltonian (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (bc : ℂ) (zc : List ℂ) (bs : ℂ) (zs : List ℂ) :
    evaluate (controlOracle (parallelOracle (J := Bool) U))
      (compileHamiltonian F bc zc bs zs) = hamiltonianCircuit U F bc zc bs zs := by
  simp only [compileHamiltonian, evaluate_compileSelected, evaluate, instructionMatrix,
    evaluate_compileRealPartQSVT, Matrix.smul_mul, Matrix.one_mul]
  rfl

omit [Fintype H] [DecidableEq I] in

theorem counts_compileHamiltonian (F : Matrix H I ℂ)
    (bc : ℂ) (zc : List ℂ) (bs : ℂ) (zs : List ℂ) :
    adjointQueryCount (compileHamiltonian F bc zc bs zs) = zc.length + zs.length ∧
    adjointGateCount (compileHamiltonian F bc zc bs zs) = zc.length + zs.length + 5 := by
  constructor
  · simp only [compileHamiltonian, queryCount_compileSelected, adjointQueryCount]
    rw [(counts_compileRealPartQSVT _ _ bc zc).1, (counts_compileRealPartQSVT _ _ bs zs).1]
  · simp only [compileHamiltonian, gateCount_compileSelected, adjointGateCount]
    rw [(counts_compileRealPartQSVT _ _ bc zc).2, (counts_compileRealPartQSVT _ _ bs zs).2]
    omega

theorem compileHamiltonian_wellFormed {F : Matrix H I ℂ} (hF : IsIsometry F)
    {bc bs : ℂ} (hbc : IsPhase bc) (zc : List ℂ) (hzc : ∀ z ∈ zc, IsPhase z)
    (hbs : IsPhase bs) (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) :
    WellFormedAdjointCircuit (compileHamiltonian F bc zc bs zs) := by
  have hP := rangeProjector_isOrthogonalProjector hF
  have hc := compileRealPartQSVT_wellFormed hP hP hbc zc hzc
  have hs := compileRealPartQSVT_wellFormed hP hP hbs zs hzs
  apply compileSelected_wellFormed hc
  intro V hv
  rcases List.mem_cons.mp hv with hv | hv
  · cases hv
    have hphase : (-Complex.I : ℂ) ∈ unitary ℂ := by constructor <;> simp
    exact Unitary.smul_mem_of_mem hphase (Matrix.unitaryGroup (Bool × H) ℂ).one_mem
  · exact hs V hv

theorem hamiltonianSimulation_counted_exists
    {A : Matrix I I ℂ} {U : Matrix H H ℂ} {F : Matrix H I ℂ}
    (hA : A.IsHermitian) (h : ProjectedUnitaryEncoding A U F F)
    (t : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (n : ℕ) (cs : List (AdjointStep (Bool × (Bool × H)))),
      WellFormedAdjointCircuit cs ∧
      BlockEncoding (hamiltonianEvolution A t)
        (evaluate (controlOracle (parallelOracle (J := Bool) U)) cs)
        (hamiltonianFrame F) (hamiltonianFrame F) 8 ε ∧
      adjointQueryCount cs = 4 * n + 1 ∧ adjointGateCount cs = 4 * n + 6 := by
  obtain ⟨n, bc, zc, bs, zs, hbc, hzc, hlc, hbs, hzs, hls, he⟩ :=
    hamiltonianSimulation_exists hA h t hε
  refine ⟨n, compileHamiltonian F bc zc bs zs,
    compileHamiltonian_wellFormed h.left_isometry hbc zc hzc hbs zs hzs, ?_, ?_, ?_⟩
  · rw [evaluate_compileHamiltonian]
    exact he
  · rw [(counts_compileHamiltonian F bc zc bs zs).1, hlc, hls]
    omega
  · rw [(counts_compileHamiltonian F bc zc bs zs).2, hlc, hls]
    omega

end Qatlib.Concepts.QspSimulation.Achievability
