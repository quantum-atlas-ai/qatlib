/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSingValue19.Implementation.QlsQsvtDefs

/-!
# QSVT linear systems implementation guarantees

The theorem `clause17_endpoint` assembles phase existence, polynomial approximation,
pseudoinverse, robustness, and Hamiltonian simulation results in the framework of
[GilyenSuLowWiebe2019]. Supporting results prove the access ledger counts, corrected window
estimates, phase recovery certificate, controlled walk identities, and consistency of the
declared program budget.

## Main statements

* `clause17_near_optimal_window_count`: Gives explicit lower and upper bounds on the corrected
  window count.
* `clause17_efficient_phase_recovery`: Certifies inversion for legal phase recovery input.
* `clause17_endpoint`: Collects the implementation guarantees and supporting QSVT results.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.QsvtCore.HamiltonianSim
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.SignalPrimitive.SparseSim
open Qatlib.Papers.QSingValue19.AlgorithmApps

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.Implementation

open Qatlib
open Matrix

/-- The access ledger has d data queries, d adjoint queries, 2⌊d/2⌋ projector negations, and d
phase gates. -/
theorem clause17_access_ledger_counts (d bitTime peakWorkspace : ℕ) :
    (qlsQsvtAccessLedger d bitTime peakWorkspace).dataQueries = d ∧
      (qlsQsvtAccessLedger d bitTime peakWorkspace).adjointQueries = d ∧
      (qlsQsvtAccessLedger d bitTime peakWorkspace).projectorNots = 2 * (d / 2) ∧
      (qlsQsvtAccessLedger d bitTime peakWorkspace).phaseGates = d := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The scalar expression κ² log(1/ε) is monotone under the stated nonnegative condition number
and logarithmic accuracy inequalities. -/
theorem clause17_near_optimal_degree_mono (κ κ' : ℝ) (ε ε' : ℝ)
    (hκ : 0 ≤ κ) (hκ' : 0 ≤ κ') (hε : 0 < ε) (hε1 : ε < 1) (hε' : 0 < ε') (hε'1 : ε' < 1)
    (hle : κ ≤ κ') (hlog : Real.log (1 / ε) ≤ Real.log (1 / ε')) :
    κ ^ 2 * Real.log (1 / ε) ≤ κ' ^ 2 * Real.log (1 / ε') := by
  have hsq : κ ^ 2 ≤ κ' ^ 2 := by nlinarith
  have hlog0 : 0 ≤ Real.log (1 / ε) := by
    have hinv : (1:ℝ) ≤ 1 / ε := by
      rw [le_div_iff₀ hε]
      linarith [hε1]
    exact Real.log_nonneg hinv
  calc κ ^ 2 * Real.log (1 / ε) ≤ κ' ^ 2 * Real.log (1 / ε) :=
      mul_le_mul_of_nonneg_right hsq hlog0
    _ ≤ κ' ^ 2 * Real.log (1 / ε') := mul_le_mul_of_nonneg_left hlog (sq_nonneg _)

/-- An inequality between the real degree expressions implies the same inequality between their
natural ceiling budgets. -/
theorem clause17_near_optimal_degree_ceil (κ κ' : ℝ) (ε ε' : ℝ)
    (h : κ ^ 2 * Real.log (1 / ε) ≤ κ' ^ 2 * Real.log (1 / ε')) :
    nearOptimalDegreeBudget κ ε ≤ nearOptimalDegreeBudget κ' ε' := by
  unfold nearOptimalDegreeBudget
  have hceil : κ' ^ 2 * Real.log (1 / ε')
      ≤ (↑(Nat.ceil (κ' ^ 2 * Real.log (1 / ε'))) : ℝ) := by
    exact_mod_cast (Nat.le_ceil _)
  exact (Nat.ceil_le).2 (h.trans hceil)

/-- For nonnegative τ and ε ∈ (0, 1], the corrected window count is at least τ + 1 and at most
the stated logarithmic expression with constant eleven. -/
theorem clause17_near_optimal_window_count (τ ε : ℝ) (hτ : 0 ≤ τ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    τ + 1 ≤ (nearOptimalWindowCount τ ε : ℝ) ∧
      (nearOptimalWindowCount τ ε : ℝ) ≤
        11 * (τ + 1 + Real.log (32 / ε) / Real.log (1 + Real.log (32 / ε) / max τ 1)) := by
  unfold nearOptimalWindowCount
  exact ⟨lcCorrectedQ_length_budget τ ε, lcCorrectedQ_upper τ ε hτ hε hε1⟩

/-- Legal rational polynomial and precision input yields a `PhaseInversionCertified` result for
`efficientInversion`. -/
theorem clause17_efficient_phase_recovery (p : List ℚ) (d : ℕ) (eps : ℚ)
    (hleg : PhaseInversionLegal p d eps) :
    PhaseInversionCertified efficientInversion p d eps :=
  efficientInversion_certified p d eps hleg

/-- Hadamard conjugation of the controlled scalar phase equals the signal step multiplied by the
global phase exp(iθ/2). -/
theorem clause17_single_ancilla_realization (θ : ℝ) :
    lcHad * Matrix.diagonal ![1, Complex.exp (Complex.I * (θ : ℂ))] * lcHad =
      Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) • lcSignalStep θ :=
  lcHad_controlled_scalar θ

/-- The plus frame embeds a state as the equal amplitude two branch vector of its image under L. -/
theorem clause17_effective_frame_prepare {I W : Type} [Fintype I] [DecidableEq I]
    [Fintype W] [DecidableEq W] (L : Matrix W I ℂ) (ψ : I → ℂ) :
    lcPlusFrame L *ᵥ ψ = lcBranchVector (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) (L *ᵥ ψ) :=
  lcPlusFrame_branch L ψ

/-- On a walk eigenvector with eigenvalue z, the controlled walk acts on the branch amplitudes
by the diagonal matrix with entries one and z. -/
theorem clause17_controlled_walk_branch {W : Type} [Fintype W] [DecidableEq W]
    (V : Matrix W W ℂ) (w : W → ℂ) (z : ℂ) (hw : V *ᵥ w = z • w) (a : Fin 2 → ℂ) :
    lcControlledWalk V *ᵥ lcBranchVector a w =
      lcBranchVector ((Matrix.diagonal ![1, z]) *ᵥ a) w :=
  lcControlledWalk_branch V w z hw a

/-- A legal gate level simulation has base gate cost at most its bit time and a success wire
within its qubit range. -/
theorem clause17_gate_level_budget (P : GateLevelSimulation) (h : SimulationLegal P) :
    baseGateCost P ≤ P.bitTime ∧ P.successWire < P.qubitCount := by
  exact ⟨h.2.2, h.2.1⟩

/-- For a legal simulation, the program budget has gate count equal to the base gate cost,
bounded by its bit time, and qubit count equal to the simulation qubit count. -/
theorem clause17_program_budget_consistent (P : GateLevelSimulation) (classicalBits : ℕ)
    (h : SimulationLegal P) :
    (qlsQsvtProgramBudget P classicalBits).gateCount = baseGateCost P ∧
      (qlsQsvtProgramBudget P classicalBits).gateCount ≤
        (qlsQsvtProgramBudget P classicalBits).bitTime ∧
      (qlsQsvtProgramBudget P classicalBits).qubits = P.qubitCount := by
  obtain ⟨hcost, hwire⟩ := clause17_gate_level_budget P h
  exact ⟨rfl, hcost, rfl⟩

/-- Collects QSVT phase and approximation results, pseudoinverse and simulation bounds,
conditional singular transform robustness, window estimates, phase recovery, branch
identities, and legal gate budget bounds. See [GilyenSuLowWiebe2019]. -/
theorem clause17_endpoint :
    Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistence ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem3Characterization ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSP ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma23PolynomialLevel ∧
      Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalPseudoinverse ∧
      Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41OriginalPseudoinverse ∧
      Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41WindowedPolynomial ∧
      Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostBounds ∧
      Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostEquation ∧
      Qatlib.Concepts.QsvtCore.PolyApprox.Lemma25SignApproximation ∧
      Qatlib.Concepts.QsvtCore.PolyApprox.Lemma29RectangleApproximation ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma9ChebyshevWord ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.SignalWordTransport ∧
      Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransport ∧
      Qatlib.Concepts.QsvtCore.QsVtMain.SourceConventionQSVTGeneral ∧
      SvtRobustnessBound ∧ SvtEqualityAtZero ∧
      (∀ τ ε : ℝ, 0 ≤ τ → 0 < ε → ε ≤ 1 →
        τ + 1 ≤ (nearOptimalWindowCount τ ε : ℝ) ∧
          (nearOptimalWindowCount τ ε : ℝ) ≤
            11 * (τ + 1 + Real.log (32 / ε) /
              Real.log (1 + Real.log (32 / ε) / max τ 1))) ∧
      (∀ (p : List ℚ) (d : ℕ) (eps : ℚ), PhaseInversionLegal p d eps →
        PhaseInversionCertified efficientInversion p d eps) ∧
      (∀ θ : ℝ,
        lcHad * Matrix.diagonal ![1, Complex.exp (Complex.I * (θ : ℂ))] * lcHad =
          Complex.exp (Complex.I * ((θ / 2 : ℝ) : ℂ)) • lcSignalStep θ) ∧
      (∀ {I W : Type} [Fintype I] [DecidableEq I] [Fintype W] [DecidableEq W]
        (L : Matrix W I ℂ) (ψ : I → ℂ),
        lcPlusFrame L *ᵥ ψ = lcBranchVector (fun _ => (((Real.sqrt 2)⁻¹ : ℝ) : ℂ)) (L *ᵥ ψ)) ∧
      (∀ {W : Type} [Fintype W] [DecidableEq W]
        (V : Matrix W W ℂ) (w : W → ℂ) (z : ℂ) (_hw : V *ᵥ w = z • w) (a : Fin 2 → ℂ),
        lcControlledWalk V *ᵥ lcBranchVector a w =
          lcBranchVector ((Matrix.diagonal ![1, z]) *ᵥ a) w) ∧
      (∀ (P : GateLevelSimulation), SimulationLegal P →
        baseGateCost P ≤ P.bitTime ∧ P.successWire < P.qubitCount) := by
  refine ⟨Qatlib.Concepts.QsvtCore.PhaseExistence.corollary8ComplexPhaseExistence, Qatlib.Concepts.QsvtCore.PhaseExistence.theorem3Characterization, Qatlib.Concepts.QsvtCore.PhaseExistence.corollary10RealQSP,
    Qatlib.Concepts.QsvtCore.QsVtStability.lemma23PolynomialLevel, Qatlib.Concepts.QsvtCore.LinearSystems.nearOptimalPseudoinverse, Qatlib.Concepts.QsvtCore.LinearSystems.theorem41OriginalPseudoinverse,
    Qatlib.Concepts.QsvtCore.LinearSystems.theorem41WindowedPolynomial, Qatlib.Concepts.QsvtCore.HamiltonianSim.simulationCostBounds_answer, Qatlib.Concepts.QsvtCore.HamiltonianSim.simulationCostEquation_answer,
    Qatlib.Concepts.QsvtCore.PolyApprox.lemma25SignApproximation_answer, Qatlib.Concepts.QsvtCore.PolyApprox.lemma29RectangleApproximation_answer, Qatlib.Concepts.QsvtCore.PhaseExistence.lemma9ChebyshevWord,
    Qatlib.Concepts.QsvtCore.PhaseExistence.signalWordTransport, Qatlib.Concepts.QsvtCore.PhaseExistence.singleQubitWordTransport, Qatlib.Concepts.QsvtCore.QsVtMain.sourceConventionQSVTGeneral,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (Qatlib.Papers.QSingValue19.AlgorithmApps.clause1_endpoint).1
  · exact (Qatlib.Papers.QSingValue19.AlgorithmApps.clause1_endpoint).2.1
  · intro τ ε hτ hε hε1
    exact clause17_near_optimal_window_count τ ε hτ hε hε1
  · intro p d eps hleg
    exact clause17_efficient_phase_recovery p d eps hleg
  · intro θ
    exact clause17_single_ancilla_realization θ
  · intro I W _ _ _ _ L ψ
    exact clause17_effective_frame_prepare L ψ
  · intro W _ _ V w z hw a
    exact clause17_controlled_walk_branch V w z hw a
  · intro P h
    exact clause17_gate_level_budget P h

end Qatlib.Papers.QSingValue19.Implementation
