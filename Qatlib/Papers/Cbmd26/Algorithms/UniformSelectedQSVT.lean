/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.UniformQSVTPhases
import Qatlib.Papers.Cbmd26.Algorithms.FourBranchWordBridge
import Qatlib.Papers.Cbmd26.Algorithms.TwoOracleWordBridge
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.QsvtCore.LinearSystems
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace CBMD
open Matrix Polynomial

open scoped Classical BigOperators Matrix.Norms.L2Operator
variable {J H I : Type} [Fintype J] [DecidableEq J] [Fintype H] [DecidableEq H]
  [Fintype I] [DecidableEq I]

def flatBranchCoefficients (c : J → ℂ) (kj : Fin 4 × J) : ℂ :=
  fourBranchCoefficients kj.1 * c kj.2

omit [DecidableEq J] [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I] in

theorem flatBranchCoefficients_mass (c : J → ℂ) :
    coefficientMass (flatBranchCoefficients c) = 4 * coefficientMass c := by
  simp only [coefficientMass, flatBranchCoefficients, Fintype.sum_prod_type, norm_mul]
  have hn (k : Fin 4) : ‖fourBranchCoefficients k‖ = 1 := by
    fin_cases k <;> norm_num [fourBranchCoefficients]
  simp only [hn, one_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

def flatResponseWord (c : J → ℂ) (j₀ : J) (F : Matrix H I ℂ) (D : ℕ)
    (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ)) :
    List (AdjointStep ((Fin 4 × J) × (Bool × H))) :=
  outerCoefficientWord (flatBranchCoefficients c) (0, j₀)
    (reindexAdjointWord (Equiv.prodAssoc (Fin 4) J (Bool × H))
      (compileFourSelected (fun k => indexedHermitianResponseWord F
        (uniformBranchDegree D k) (base k) (zs k))))

def flatResponseOracle (U : J → Matrix H H ℂ) :
    Matrix ((Fin 4 × J) × (Bool × H)) ((Fin 4 × J) × (Bool × H)) ℂ :=
  (maskedOracle fourActive (select (fun j => parallelOracle (J := Bool) (U j)))).submatrix
    (Equiv.prodAssoc (Fin 4) J (Bool × H)) (Equiv.prodAssoc (Fin 4) J (Bool × H))

omit [DecidableEq I] in

theorem flatResponseWord_evaluate (c : J → ℂ) (j₀ : J) (U : J → Matrix H H ℂ)
    (F : Matrix H I ℂ) (D : ℕ) (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ)) :
    evaluate (flatResponseOracle U) (flatResponseWord c j₀ F D base zs) =
      coefficientLCUUnitary (flatBranchCoefficients c)
        (fun kj : Fin 4 × J => evaluate (parallelOracle (U kj.2))
          (hermitianResponseWord F (uniformBranchDegree D kj.1) (base kj.1 kj.2)
            ((zs kj.1).map (fun z => z kj.2)))) (0, j₀) := by
  apply outerCoefficientWord_evaluate
  rw [flatResponseOracle, reindexAdjointWord_evaluate, compileFourSelected_evaluate]
  simp only [indexedHermitianResponseWord_evaluate]
  ext ⟨⟨k,j⟩,b,h⟩ ⟨⟨l,m⟩,d,n⟩
  by_cases hk : k = l <;> by_cases hj : j = m <;>
    simp [select, hk, hj]

omit [Fintype H] [DecidableEq I] in

theorem flatResponseWord_cost (c : J → ℂ) (j₀ : J) (F : Matrix H I ℂ) (D : ℕ)
    (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ))
    (hlen : ∀ k, (zs k).length = uniformBranchDegree D k) :
    adjointQueryCount (flatResponseWord c j₀ F D base zs) = 8 * D + 2 ∧
    adjointGateCount (flatResponseWord c j₀ F D base zs) = 8 * D + 15 := by
  simp only [flatResponseWord, (outerCoefficientWord_cost _ _ _).1,
    (outerCoefficientWord_cost _ _ _).2, (reindexAdjointWord_cost _ _).1,
    (reindexAdjointWord_cost _ _).2, (compileFourSelected_cost _).1,
    (compileFourSelected_cost _).2, (indexedHermitianResponseWord_cost _ _ _ _).1,
    (indexedHermitianResponseWord_cost _ _ _ _).2, hlen, Finset.sum_add_distrib,
    uniformBranchDegree_sum]
  norm_num

theorem flatResponseWord_wellFormed (c : J → ℂ) (j₀ : J) (hc : 0 < coefficientMass c)
    (F : Matrix H I ℂ) (hF : IsIsometry F) (D : ℕ)
    (base : Fin 4 → J → ℂ) (hb : ∀ k j, IsPhase (base k j))
    (zs : Fin 4 → List (J → ℂ)) (hz : ∀ k, ∀ z ∈ zs k, ∀ j, IsPhase (z j)) :
    WellFormedAdjointCircuit (flatResponseWord c j₀ F D base zs) := by
  apply outerCoefficientWord_wellFormed
  · rw [flatBranchCoefficients_mass]
    positivity
  apply reindexAdjointWord_wellFormed
  apply compileFourSelected_wellFormed
  intro k
  exact indexedHermitianResponseWord_wellFormed F hF _ _ (hb k) _ (hz k)

omit [DecidableEq J] [Fintype H] [DecidableEq H] in

theorem flatBranch_polynomial_sum (c : J → ℂ) (A : J → Matrix I I ℂ)
    (P : J → Polynomial ℂ) :
    (∑ kj : Fin 4 × J, flatBranchCoefficients c kj •
      aeval (A kj.2) ((ComplexPolynomialSplit.branches (P kj.2) kj.1).map Complex.ofRealHom)) =
      ∑ j, c j • aeval (A j) (P j) := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  have hid := congrArg (aeval (A j)) (ComplexPolynomialSplit.branches_identity (P j))
  have hc : ComplexPolynomialSplit.coefficients = fourBranchCoefficients := by
    funext k
    fin_cases k <;> norm_num [ComplexPolynomialSplit.coefficients, fourBranchCoefficients]
  simp only [map_sum, map_smul, hc] at hid
  rw [← hid, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  simp only [flatBranchCoefficients, smul_smul, mul_comm]

omit [Fintype J] [DecidableEq J] in

theorem bounded_polynomial_family_phases (P : J → Polynomial ℂ) (D : ℕ)
    (hD : ∀ j, (P j).natDegree ≤ D)
    (hP : ∀ j, ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖(P j).eval (x : ℂ)‖ ≤ 1) :
    ∃ (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ)),
      (∀ k j, IsPhase (base k j)) ∧
      (∀ k, ∀ z ∈ zs k, ∀ j, IsPhase (z j)) ∧
      (∀ k, (zs k).length = uniformBranchDegree D k) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : J → Matrix I I ℂ) (U : J → Matrix H H ℂ) (F : Matrix H I ℂ),
      (∀ j, (A j).IsHermitian) → (∀ j, ProjectedUnitaryEncoding (A j) (U j) F F) →
      ∀ kj : Fin 4 × J,
      ProjectedUnitaryEncoding
        (aeval (A kj.2) ((ComplexPolynomialSplit.branches (P kj.2) kj.1).map Complex.ofRealHom))
        (evaluate (parallelOracle (U kj.2))
          (hermitianResponseWord F (uniformBranchDegree D kj.1) (base kj.1 kj.2)
            ((zs kj.1).map (fun z => z kj.2)))) (averageFrame F) (averageFrame F) := by
  have hex := fun k j => hermitian_actual_qsvt_uniform_phases
    (ComplexPolynomialSplit.branches (P j) k) (uniformBranchDegree D k)
    (branches_uniform_degree (P j) D (hD j) k) (branches_uniform_parity (P j) D k)
    (ComplexPolynomialSplit.branches_bounded (P j) (hP j) k)
  choose base raw hb hz hlen hr ha using hex
  refine ⟨base, (fun k => phaseColumns _ (raw k) (hlen k)), hb, ?_, ?_, ?_⟩
  · intro k
    exact phaseColumns_phase _ _ (hlen k) (hz k)
  · intro k
    exact phaseColumns_length _ _ (hlen k)
  intro H I _ _ _ _ A U F hA hAU kj
  rw [phaseColumns_map]
  exact (ha kj.1 kj.2 H I (A kj.2) (U kj.2) F (hA kj.2) (hAU kj.2)).1

theorem flat_polynomial_family_encoding (c : J → ℂ) (j₀ : J) (hc : 0 < coefficientMass c)
    (P : J → Polynomial ℂ) (D : ℕ) (A : J → Matrix I I ℂ) (U : J → Matrix H H ℂ)
    (F : Matrix H I ℂ) (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ))
    (hbranch : ∀ kj : Fin 4 × J, ProjectedUnitaryEncoding
      (aeval (A kj.2) ((ComplexPolynomialSplit.branches (P kj.2) kj.1).map Complex.ofRealHom))
      (evaluate (parallelOracle (U kj.2))
        (hermitianResponseWord F (uniformBranchDegree D kj.1) (base kj.1 kj.2)
          ((zs kj.1).map (fun z => z kj.2)))) (averageFrame F) (averageFrame F)) :
    BlockEncoding (∑ j, c j • aeval (A j) (P j))
      (evaluate (flatResponseOracle U) (flatResponseWord c j₀ F D base zs))
      (tagFrame (0, j₀) (averageFrame F)) (tagFrame (0, j₀) (averageFrame F))
      (4 * coefficientMass c) 0 := by
  rw [flatResponseWord_evaluate]
  have hscale : scaledLCUCoefficients (flatBranchCoefficients c) (fun _ => (1 : ℝ)) =
      flatBranchCoefficients c := by ext kj; simp [scaledLCUCoefficients]
  have hm : 0 < coefficientMass (scaledLCUCoefficients (flatBranchCoefficients c)
      (fun _ => (1 : ℝ))) := by rw [hscale, flatBranchCoefficients_mass]; positivity
  have h := scaled_approximate_lcu_encoding (0, j₀) _ _ (averageFrame F) (averageFrame F)
    (flatBranchCoefficients c) (fun _ => 1) (fun _ => 0) (fun kj => (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (hbranch kj))) hm
  simp only [hscale, flatBranch_polynomial_sum, mul_one, mul_zero, Finset.sum_const_zero] at h
  rw [show (∑ kj, ‖flatBranchCoefficients c kj‖) = 4 * coefficientMass c from
    flatBranchCoefficients_mass c] at h
  exact h

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
