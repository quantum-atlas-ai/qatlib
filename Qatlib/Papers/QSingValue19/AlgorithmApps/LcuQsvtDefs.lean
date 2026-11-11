/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCoreAuxiliary
import Qatlib.Papers.HamLCUSim12.Multiproduct.Lemma12IntegerNodesCorrectedHami
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncationLowc
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
import Qatlib.Concepts.QsvtCore.QsVtMain.ConventionQSVTGeneralGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitSignal
import Qatlib.Concepts.QsvtCore.PhaseExistence.SingleQubitWordTransportGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Lemma9ChebyshevWordGily
import Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostBoundsGily
import Qatlib.Concepts.QsvtCore.HamiltonianSim.SimulationCostEquationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary8ComplexPhaseExistenceGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Corollary10RealQSPGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem3CharacterizationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem4PCharacterizationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem4QCharacterizationGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.Theorem5RealCharacterizationGily
import Qatlib.Concepts.QsvtCore.QsVtStability.Lemma23PolynomialLevel
import Qatlib.Concepts.QsvtCore.QsVtStability.Lemma23InteriorRobustnessGily
import Qatlib.Concepts.QsvtCore.PolyApprox.Lemma25SignApproximationGily
import Qatlib.Concepts.QsvtCore.PolyApprox.Lemma29RectangleApproximationGily
import Qatlib.Concepts.QsvtCore.LinearSystems.NearOptimalPseudoinverseGily
import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41OriginalPseudoinverseGily
import Qatlib.Concepts.QsvtCore.LinearSystems.Theorem41WindowedPolynomialGily
import Qatlib.Concepts.QsvtCore.HamiltonianSim.HermitianEvolutionLipschitzGily
import Qatlib.Concepts.QsvtCore.PhaseExistence.SVTransformSubgoalGily
import Qatlib.Papers.HamLCUSim12.LCUDeferred.SubtractionRetryTailHami
import Qatlib.Concepts.CoherentSim.ResetDiscard.Theorem13CorrectedHami
import Qatlib.Concepts.QspSimulation.Achievability.LcuQsvt
import Qatlib.Concepts.QspSimulation.WordModel.Lc17AuxWord
import Qatlib.Concepts.SignalPrimitive.SparseSim.Lc17AuxWalkBranch
import Qatlib.Concepts.QspSimulation.Achievability.SimQsp
import Qatlib.Concepts.QspSimulation.Achievability.SimQspDefs
import Qatlib.Concepts.BlockEncoding.EncodingCore.SparseOverlapEncoding

/-!
# Definitions for LCU and QSVT applications

This module defines the robustness conditions, word plans, query ledgers, corrected integer
nodes, and retry costs used in the application statements associated with
[GilyenSuLowWiebe2019]. The predicates `SparseSimulationWord`, `SparseEigenphaseTransport`, and
`Lc17EndpointContract` specify the spectral simulation and synthesis guarantees assembled by the
companion results.

## Main statements

* `printedRobustnessAdequacy`: Compares the rank dependent constant with the printed robustness
  factor.
* `SparseSimulationWord`: Specifies simulation error and success mass on normalized
  eigenvectors.
* `Lc17EndpointContract`: Collects phase synthesis, word transport, and sparse simulation
  requirements.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LcuQsvtApprox.PhaseRecovery
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Papers.HamLCUSim12.LCUDeferred
open Qatlib.Papers.HamLCUSim12.Multiproduct
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Qatlib.Concepts.SketchSpectral.MatrixFunctions
open Qatlib.Concepts.QsvtCore.HamiltonianSim
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.QsvtCore.PhaseExistence
open Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis
open Qatlib.Concepts.QsvtCore.PolyApprox
open Qatlib.Concepts.QsvtCore.QsVtMain
open Qatlib.Concepts.BlockEncoding.Postselection Qatlib.Concepts.QsvtCore.QsVtStability
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.CoherentSim.ResetDiscard

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QSingValue19.AlgorithmApps

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- The explicit constant 144 used in the quasicommutator estimates. -/
noncomputable def quasicommutatorConstant : ℝ := 144

/-- The condition that the printed robustness factor at δ dominates 2 plus the quasicommutator
constant times the rank logarithmic weight. -/
noncomputable def printedRobustnessAdequacy (δ : ℝ) (r : ℕ) : Prop :=
  2 + quasicommutatorConstant * hermitianRankLogWeight r ≤ modulusRobustnessFactor δ

/-- The rank dependent perturbation threshold 2/(exp(7 + 2r) − 1). -/
noncomputable def printedRobustnessThreshold (r : ℕ) : ℝ :=
  2 / (Real.exp (7 + 2 * r) - 1)

/-- The conditional printed perturbation bounds for odd and even singular transforms of
contractions, subject to a modulus of continuity and dilation rank adequacy. -/
noncomputable def SvtRobustnessBound : Prop :=
  ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A B : Matrix O I ℂ) (f : ℝ → ℂ) (ω : ℝ → ℝ),
    ‖A‖ ≤ 1 → ‖B‖ ≤ 1 → ModulusOfContinuity f ω → 0 < ‖A - B‖ →
      (IsOddFunction f →
        printedRobustnessAdequacy ‖A - B‖
          (min (hermitianDilation A).rank (hermitianDilation B).rank) →
        ‖oddSingularTransform A f - oddSingularTransform B f‖ ≤
          modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖) ∧
      (IsEvenFunction f →
        printedRobustnessAdequacy ‖A - B‖
          (min (hermitianDilation A).rank (hermitianDilation B).rank) →
        ‖rightSingularTransform A f - rightSingularTransform B f‖ ≤
          modulusRobustnessFactor ‖A - B‖ * ω ‖A - B‖)

/-- The assertion that zero matrix distance implies equality of both odd and right singular
transforms. -/
noncomputable def SvtEqualityAtZero : Prop :=
  ∀ (I O : Type) [Fintype I] [DecidableEq I] [Fintype O] [DecidableEq O]
    (A B : Matrix O I ℂ) (f : ℝ → ℂ),
    ‖A - B‖ = 0 →
      oddSingularTransform A f = oddSingularTransform B f ∧
        rightSingularTransform A f = rightSingularTransform B f

/-- The polynomial bridge robustness bound specialized to degree zero. -/
noncomputable def zeroDegreeBridgeRate (δ : ℝ) : ℝ := polynomialRobustnessBound 0 δ

/-- The interior robustness rate specialized to degree zero. -/
noncomputable def zeroDegreeInteriorRate (m δ : ℝ) : ℝ := interiorRobustnessRate 0 m δ

/-- A record of a polynomial degree, a real angle list, and a QSVT cost ledger. -/
structure LcuWordPlan where

  degree : ℕ

  angles : List ℝ

  ledger : QsvtCostLedger

/-- The QSVT ledger obtained from the source compilation counts at degree d, together with
supplied integer time and peak workspace values. -/
def lcuWordLedger (d : ℕ) (bitTime peakWorkspace : ℕ) : QsvtCostLedger where
  dataQueries := (sourceCppQuadruple d).1
  adjointQueries := (sourceCppQuadruple d).1
  projectorNots := (sourceCppQuadruple d).2.1
  phaseGates := (sourceCppQuadruple d).2.2.2
  elementaryGates := 0
  integerBitTime := bitTime
  peakWorkspace := peakWorkspace

/-- The natural ceiling of exp((k + 1) `gammaReq` η k), used as the corrected integer node. -/
noncomputable def integerNodeNat (η : ℝ) (k : ℕ) : ℕ :=
  Nat.ceil (Real.exp (((k + 1 : ℕ) : ℝ) * gammaReq η k))

/-- The repetition count equal to q for q ≤ k and to the corrected integer node otherwise. -/
noncomputable def repetitionCount (η : ℝ) (k q : ℕ) : ℕ :=
  if q ≤ k then q else integerNodeNat η k

/-- The natural count 5rk times the corrected integer node times 2m5^(k − 1). -/
noncomputable def exponentialCount (η : ℝ) (k m r : ℕ) : ℕ :=
  5 * r * k * integerNodeNat η k * (2 * m * 5 ^ (k - 1))

/-- The real exponential budget 1000m5^(k − 1)k^(9/4)exp((1 + log(η)/2)k)r. -/
noncomputable def eq67Budget (η : ℝ) (k m r : ℕ) : ℝ :=
  1000 * (m : ℝ) * (5 : ℝ) ^ (k - 1) * (k : ℝ) ^ (9 / 4 : ℝ) *
    Real.exp ((1 + Real.log η / 2) * (k : ℝ)) * (r : ℝ)

/-- The number 3r of recovery attempts. -/
def retryAttemptCount (r : ℕ) : ℕ := 3 * r

/-- The number 2r of tolerated recovery failures. -/
def retryToleratedFailures (r : ℕ) : ℕ := 2 * r

/-- The recovery step budget 5r. -/
def retryStepBudget (r : ℕ) : ℕ := 5 * r

/-- The exponential recovery failure bound exp(−r/14). -/
noncomputable def retryFailureBound (r : ℕ) : ℝ := Real.exp (-(r : ℝ) / 14)

/-- The natural conversion of the integer retry count for the supplied simulation parameters. -/
noncomputable def retryCountNat (m h t ε β : ℝ) (k : ℕ) : ℕ :=
  (retryCount m h t ε β k).toNat

/-- A record of an integer node, gamma parameter, retry rounds, exponential count, and real
budget. -/
structure LcuNodeLedger where

  node : ℕ

  gamma : ℝ

  retryRounds : ℕ

  exponentials : ℕ

  budget : ℝ

/-- Two boundary angles and a list of internal phase angles specifying a source word plan. -/
structure SourceWordPlan where

  gamma0 : ℝ

  gamma1 : ℝ

  psis : List ℝ

/-- The number of internal phase angles in a source word plan. -/
def SourceWordPlan.phaseGates (w : SourceWordPlan) : ℕ := w.psis.length

/-- Twice the natural half of the internal phase list length. -/
def SourceWordPlan.projectorNots (w : SourceWordPlan) : ℕ := 2 * (w.psis.length / 2)

/-- The fixed count of two boundary rotations in a source word plan. -/
def SourceWordPlan.boundaryRotations (w : SourceWordPlan) : ℕ := 2

/-- The existence of a phase list of the specified corrected length whose compressed simulation
has squared error at most ε² and success mass at least 1 − 2ε on every normalized
eigenvector. -/
noncomputable def SparseSimulationWord (n d : ℕ) (b : ℝ)
    (O : LqSparseOracle n d b)
    (L : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (_R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ)
    (t ε : ℝ) : Prop :=
  ∃ phis : List ℝ,
    phis.length = 2 * (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) - 1) ∧
    ∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
      ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
        (∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
              (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i -
            Complex.exp (Complex.I * (-(ev : ℂ) * t)) * ψ i‖ ^ 2) ≤ ε ^ 2 ∧
        1 - 2 * ε ≤ ∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
              (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i‖ ^ 2

/-- The decomposition of each normalized sparse matrix eigenvector after frame embedding into
two normalized walk eigenvectors with the stated eigenphases and conditional orthogonality. -/
noncomputable def SparseEigenphaseTransport (n d : ℕ) (b : ℝ)
    (O : LqSparseOracle n d b)
    (L : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (_R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ) : Prop :=
  ∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
    ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
      ∃ (wp wm : Fin 2 × Fin (2 ^ n) → ℂ) (ap am : ℝ),
        (∑ j, ‖wp j‖ ^ 2 = 1) ∧ (∑ j, ‖wm j‖ ^ 2 = 1) ∧
        (|((d : ℝ) * b)⁻¹ * ev| < 1 → (∑ j, star (wp j) * wm j = 0)) ∧
        (∃ V : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ,
          V ∈ Matrix.unitaryGroup _ ℂ ∧
          V = Complex.I • S * (2 • (L * L.conjTranspose) - 1) ∧
          V *ᵥ wp =
            Complex.exp (Complex.I * ((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))) • wp ∧
          V *ᵥ wm =
            -(Complex.exp (Complex.I * (-((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))))) • wm) ∧
        ((L *ᵥ ψ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
          (Complex.exp (Complex.I * (ap : ℂ)) • wp +
            Complex.exp (Complex.I * (am : ℂ)) • wm))

/-- The corrected Jacobi–Anger window count `lcCorrectedQ` τ ε. -/
noncomputable def lcuWindowCount (τ ε : ℝ) : ℕ := lcCorrectedQ τ ε

/-- The conjunction of polynomial pair characterization, bounded phase synthesis, source word
realization and approximation, sparse eigenphase transport and simulation, and corrected
window count estimates. -/
noncomputable def Lc17EndpointContract : Prop :=
    (∀ (n : ℕ) (P Q : Polynomial ℂ),
      (∃ (base : ℂ) (zs : List ℂ), IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧
        zs.length = n ∧ responseP base zs = P ∧ responseQ base zs = Q) ↔
      Th3Pair n P Q)
  ∧ (∀ (n : ℕ) (P Q : Polynomial ℂ), Th3Pair n P Q →
      (lqSynthWithCount n P Q).1 = synthesizePair n P Q ∧
        (lqSynthWithCount n P Q).2 ≤ lqSynthOpCount n ∧
        (synthesizePair n P Q).2.length = n ∧
        IsPhase (synthesizePair n P Q).1 ∧
        (∀ z ∈ (synthesizePair n P Q).2, IsPhase z) ∧
        responseP (synthesizePair n P Q).1 (synthesizePair n P Q).2 = P ∧
        responseQ (synthesizePair n P Q).1 (synthesizePair n P Q).2 = Q)
  ∧ (∀ (d : ℕ) (A Qt : Polynomial ℝ), Even d → 0 < d →
      A.comp (-Polynomial.X) = A → Qt.comp (-Polynomial.X) = -Qt →
      A.degree ≤ (d : WithBot ℕ) → Qt.degree < (d : WithBot ℕ) →
      (∀ x ∈ Set.Icc (-1 : ℝ) 1,
        A.eval x * A.eval x + (1 - x * x) * (Qt.eval x * Qt.eval x) ≤ 1) →
      A.eval 1 = 1 →
      ∃ (γ₀ γ₁ : ℝ) (psis : List ℝ), psis.length + 1 = d ∧
        ∀ x ∈ Set.Icc (-1 : ℝ) 1,
          lqRepoAmpWord γ₀ γ₁ psis x =
            realEval A (Complex.ofReal x) +
              Complex.I * ((Real.sqrt (1 - x * x) : ℝ) : ℂ) *
                realEval Qt (Complex.ofReal x))
  ∧ (∀ (N : ℕ) (h : ℝ → ℝ) (A Qt : Polynomial ℝ) (ε : ℝ),
      Even N → 0 < N →
      (∀ θ : ℝ, h (-θ) = -h θ) → (∀ θ : ℝ, h (θ + 2 * Real.pi) = h θ) →
      A.comp (-Polynomial.X) = A → Qt.comp (-Polynomial.X) = -Qt →
      A.degree ≤ (N : WithBot ℕ) → Qt.degree < (N : WithBot ℕ) →
      (0 < ε → ε ≤ 1 / 16 →
        (∀ θ ∈ Set.Icc 0 (2 * Real.pi),
          ‖realEval A (Real.cos (θ / 2) : ℂ) +
              Complex.I * ((Real.sin (θ / 2) : ℝ) : ℂ) *
                realEval Qt (Real.cos (θ / 2) : ℂ) -
              Complex.exp (Complex.I * (h θ : ℂ))‖ ≤ ε) →
        ∃ (γ₀ γ₁ : ℝ) (psis : List ℝ), psis.length + 1 = N ∧
          ∀ x ∈ Set.Icc (-1 : ℝ) 1,
            ‖lqRepoAmpWord γ₀ γ₁ psis x -
                Complex.exp (Complex.I * (h (2 * Real.arccos x) : ℂ))‖ ≤ 8 * ε ∧
            (lqRepoAmpWord γ₀ γ₁ psis x).re * (lqRepoAmpWord γ₀ γ₁ psis x).re
              + (lqRepoAmpWord γ₀ γ₁ psis x).im * (lqRepoAmpWord γ₀ γ₁ psis x).im
              ≥ (1 - 8 * ε) ^ 2 ∧
            (lqRepoAmpWord γ₀ γ₁ psis x).re * (lqRepoAmpWord γ₀ γ₁ psis x).re
              + (lqRepoAmpWord γ₀ γ₁ psis x).im * (lqRepoAmpWord γ₀ γ₁ psis x).im
              ≥ 1 - 16 * ε ∧
            Complex.normSq (lqRepoWord γ₀ γ₁ psis x 0 0 -
                lqIdealOp h (2 * Real.arccos x) 0 0) +
              Complex.normSq (lqRepoWord γ₀ γ₁ psis x 1 0)
              ≤ (8 * ε + 4 * Real.sqrt ε) ^ 2))
  ∧ (∀ (n d : ℕ) (b : ℝ), 0 < d → 0 < b → ∀ O : LqSparseOracle n d b,
      ∃ (L R : Matrix (Fin 2 × Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
        (S : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ),
        LqWalkFrame ((d : ℝ) * b)⁻¹ O.H L R S ∧
        (∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
          ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
            ∃ (wp wm : Fin 2 × Fin (2 ^ n) → ℂ) (ap am : ℝ),
              (∑ j, ‖wp j‖ ^ 2 = 1) ∧ (∑ j, ‖wm j‖ ^ 2 = 1) ∧
              (|((d : ℝ) * b)⁻¹ * ev| < 1 → (∑ j, star (wp j) * wm j = 0)) ∧
              (∃ V : Matrix (Fin 2 × Fin (2 ^ n)) (Fin 2 × Fin (2 ^ n)) ℂ,
                V ∈ Matrix.unitaryGroup _ ℂ ∧
                V = Complex.I • S * (2 • (L * L.conjTranspose) - 1) ∧
                V *ᵥ wp =
                  Complex.exp (Complex.I * ((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))) • wp ∧
                V *ᵥ wm =
                  -(Complex.exp (Complex.I * (-((Real.arcsin (((d : ℝ) * b)⁻¹ * ev) : ℂ))))) • wm) ∧
              ((L *ᵥ ψ) = ((1 / Real.sqrt 2 : ℝ) : ℂ) •
                (Complex.exp (Complex.I * (ap : ℂ)) • wp +
                  Complex.exp (Complex.I * (am : ℂ)) • wm))) ∧
        (∀ (t ε : ℝ), 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
          ∃ phis : List ℝ,
            phis.length = 2 * (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) - 1) ∧
            ∀ (ψ : Fin (2 ^ n) → ℂ), (∑ i, ‖ψ i‖ ^ 2 = 1) →
              ∀ ev : ℝ, O.H *ᵥ ψ = (ev : ℂ) • ψ →
                (∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
                      (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i -
                    Complex.exp (Complex.I * (-(ev : ℂ) * t)) * ψ i‖ ^ 2) ≤ ε ^ 2 ∧
                1 - 2 * ε ≤ ∑ i, ‖(Qatlib.Concepts.Execution.WorkspaceCP.compress (lcPlusFrame L)
                      (lcSimWord (lcWalk S L) phis) (lcPlusFrame L) *ᵥ ψ) i‖ ^ 2))
  ∧ (∀ (d : ℕ) (b t ε : ℝ), 0 < d → 0 < b → 0 ≤ t → 0 < ε → ε ≤ 1 / 2 →
      3 * (t * (d : ℝ) * b) ≤ (lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) ∧
        2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
          8 * (Real.log (32 / (ε / 8)) /
            Real.log (1 + Real.log (32 / (ε / 8)) / max (t * (d : ℝ) * b) 1) + 2) ∧
        2 * ((lcCorrectedQ (t * (d : ℝ) * b) (ε / 8) : ℝ) - 1) ≤
          2 * (3 * (t * (d : ℝ) * b) + 3 * Real.log (32 / (ε / 8)) + 8))

end Qatlib.Papers.QSingValue19.AlgorithmApps
