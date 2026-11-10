/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ApproximateQSVTBridge
import Qatlib.Papers.Cbmd26.Algorithms.IndexedQSVTBridge
import Mathlib.Data.List.OfFn
set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
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
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace CBMD
open Matrix Polynomial

open scoped Classical BigOperators Matrix.Norms.L2Operator

def uniformBranchDegree (D : ℕ) : Fin 4 → ℕ := ![2 * D, 2 * D + 1, 2 * D, 2 * D + 1]

theorem uniformBranchDegree_sum (D : ℕ) : (∑ k, uniformBranchDegree D k) = 8 * D + 2 := by
  simp [uniformBranchDegree, Fin.sum_univ_succ]
  omega

theorem branches_uniform_parity (P : Polynomial ℂ) (D : ℕ) (k : Fin 4) :
    HasRealParity (uniformBranchDegree D k) (ComplexPolynomialSplit.branches P k) := by
  fin_cases k
  · exact ComplexPolynomialSplit.evenPart_parity (ComplexPolynomialSplit.reP P) D
  · exact ComplexPolynomialSplit.oddPart_parity (ComplexPolynomialSplit.reP P) D
  · exact ComplexPolynomialSplit.evenPart_parity (ComplexPolynomialSplit.imP P) D
  · exact ComplexPolynomialSplit.oddPart_parity (ComplexPolynomialSplit.imP P) D

theorem branches_uniform_degree (P : Polynomial ℂ) (D : ℕ) (hD : P.natDegree ≤ D) (k : Fin 4) :
    (ComplexPolynomialSplit.branches P k).degree ≤ (uniformBranchDegree D k : WithBot ℕ) := by
  apply (ComplexPolynomialSplit.branches_degree P k).trans
  apply WithBot.coe_le_coe.mpr
  fin_cases k <;> simp [ComplexPolynomialSplit.branchDegrees, uniformBranchDegree] <;> omega

theorem normalized_approximation_qsvt_common_degree
    (P : Polynomial ℂ) (D : ℕ) (hD : P.natDegree ≤ D)
    (g : ℝ → ℂ) (s : Set ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1 + η)
    (hg : ∀ x ∈ s, ‖g x‖ ≤ 1)
    (happrox : ∀ x ∈ s, ‖P.eval (x : ℂ) - g x‖ ≤ η) :
    ∃ (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      (∀ k, IsPhase (base k) ∧ (∀ z ∈ zs k, IsPhase z) ∧
        (zs k).length = uniformBranchDegree D k) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
        (hA : A.IsHermitian),
      ProjectedUnitaryEncoding A U F F →
      (∀ i, orderedHermitianValues hA i ∈ s) →
      BlockEncoding (hermitianFunction A hA g)
        (coefficientLCUUnitary fourBranchCoefficients
          (fun k => evaluate (parallelOracle U)
            (hermitianResponseWord F (uniformBranchDegree D k) (base k) (zs k))) 0)
        (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) 4 (2 * η) := by
  let Q := normalizedApproximation P η
  have hQd : Q.natDegree ≤ D :=
    (Polynomial.natDegree_smul_le ((1 + η)⁻¹ : ℝ) P).trans hD
  obtain ⟨base, zs, hp, hactual⟩ := four_parity_qsvt_uniform_phases
    (ComplexPolynomialSplit.branches Q) (uniformBranchDegree D)
    (branches_uniform_degree Q D hQd) (branches_uniform_parity Q D)
    (ComplexPolynomialSplit.branches_bounded Q (normalizedApproximation_bounded P η hη hP))
  refine ⟨base, zs, hp, ?_⟩
  intro H I _ _ _ _ A U F hA hAU hs
  obtain ⟨_, hblock⟩ := hactual H I A U F hA hAU
  have hid : (∑ k, fourBranchCoefficients k •
      (ComplexPolynomialSplit.branches Q k).map Complex.ofRealHom) = Q := by
    have hc : fourBranchCoefficients = ComplexPolynomialSplit.coefficients := by
      funext k
      fin_cases k <;> norm_num [fourBranchCoefficients, ComplexPolynomialSplit.coefficients]
    rw [hc]
    exact ComplexPolynomialSplit.branches_identity Q
  rw [hid] at hblock
  have hε : 0 ≤ 2 * η / (1 + η) := by positivity
  have herr : ‖hermitianFunction A hA g - aeval A Q‖ ≤ 2 * η / (1 + η) := by
    apply hermitian_complex_polynomial_error I A hA Q g _ hε
    intro i
    have hi := hs i
    have hh := normalized_scalar_error (P.eval (orderedHermitianValues hA i : ℂ))
      (g (orderedHermitianValues hA i)) η hη (hg _ hi) (happrox _ hi)
    rw [norm_sub_rev]
    simpa only [Q, normalizedApproximation, Polynomial.eval_smul] using hh
  have h := hblock.perturb hε herr
  simp only [zero_add] at h
  exact h.mono (div_le_self (by positivity) (by linarith))

def phaseColumns {J : Type*} (d : ℕ) (zs : J → List ℂ) (hlen : ∀ j, (zs j).length = d) :
    List (J → ℂ) :=
  List.ofFn (fun k : Fin d => fun j => (zs j)[k.val]'(by rw [hlen j]; exact k.isLt))

theorem phaseColumns_length {J : Type*} (d : ℕ) (zs : J → List ℂ)
    (hlen : ∀ j, (zs j).length = d) : (phaseColumns d zs hlen).length = d := by
  simp [phaseColumns]

theorem phaseColumns_map {J : Type*} (d : ℕ) (zs : J → List ℂ)
    (hlen : ∀ j, (zs j).length = d) (j : J) :
    (phaseColumns d zs hlen).map (fun z => z j) = zs j := by
  apply List.ext_getElem
  · simp [phaseColumns_length, hlen]
  · intro i hi hj
    simp [phaseColumns, List.getElem_ofFn]

theorem phaseColumns_phase {J : Type*} (d : ℕ) (zs : J → List ℂ)
    (hlen : ∀ j, (zs j).length = d) (hp : ∀ j, ∀ z ∈ zs j, IsPhase z) :
    ∀ z ∈ phaseColumns d zs hlen, ∀ j, IsPhase (z j) := by
  intro z hz j
  apply hp j
  rw [← phaseColumns_map d zs hlen j]
  exact List.mem_map.mpr ⟨z, hz, rfl⟩

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
