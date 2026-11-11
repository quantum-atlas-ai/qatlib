/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SignalPrimitive.HermitianQSVT
import Qatlib.Concepts.LcuPostselect.ScaledLCU.ApproximateCoefficientLCU
import Qatlib.Papers.Cbmd26.Algorithms.ComplexPolynomialSplit

/-!
# Uniform QSVT Phases for Complex Polynomials

`hermitian_actual_qsvt_uniform_phases` synthesizes phases for any bounded real polynomial with a
degree bound and matching parity. The phases work for every Hermitian matrix with a projected
unitary encoding, and `hermitianResponseWord` uses exactly the chosen degree in oracle queries.

`fourBranchCoefficients` combines the four real parity branches with coefficients `1`, `1`,
`Complex.I`, and `Complex.I`. The resulting LCU gives an exact block encoding of a bounded
complex polynomial with normalization four, as used in the CBMD constructions of [WangEtAl2026].

## Main statements

* `hermitian_actual_qsvt_uniform_phases` gives matrix-independent phases with `d` queries and `d
  + 1` fixed gates.
* `four_parity_qsvt_uniform_phases` combines four parity-polynomial encodings with normalization
  `4` and error `0`.
* `complex_polynomial_qsvt_uniform_phases` applies the real-parity split to a complex
  polynomial, with at most `2 * P.natDegree + 1` queries per branch.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
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
set_option maxHeartbeats 200000

namespace CBMD

open Matrix Polynomial

open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- A real polynomial bounded by one on `[-1, 1]`, with degree at most `d` and parity `d`, has
phases valid for every Hermitian projected unitary encoding. The response word exactly
encodes the polynomial with `d` queries and `d + 1` fixed gates. -/
theorem hermitian_actual_qsvt_uniform_phases
    (p : Polynomial ℝ) (d : ℕ)
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hpar : HasRealParity d p)
    (hbounded : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ (base : ℂ) (zs : List ℂ),
      IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = d ∧
      (∀ x : ℝ, ((responseP base zs).eval (x : ℂ)).re = p.eval x) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ),
      A.IsHermitian → ProjectedUnitaryEncoding A U F F →
      ProjectedUnitaryEncoding (aeval A (p.map Complex.ofRealHom))
        (evaluate (parallelOracle U) (hermitianResponseWord F d base zs))
        (averageFrame F) (averageFrame F) ∧
      adjointQueryCount (hermitianResponseWord F d base zs) = d ∧
      adjointGateCount (hermitianResponseWord F d base zs) = d + 1 := by
  obtain ⟨base, zs, hbase, hzs, hn, hpoly, hresponse⟩ :=
    exists_phases_of_bounded hpdeg hpar hbounded
  have hreal : realPartPolynomial (responseP base zs) = p.map Complex.ofRealHom := by
    unfold realPartPolynomial
    change (2 : ℂ)⁻¹ • (responseP base zs +
      Qatlib.Concepts.QsvtCore.PhaseExistence.PhaseSynthesis.conjugatePolynomial (responseP base zs)) = _
    rw [hpoly, Polynomial.C_mul', smul_smul]
    norm_num
  refine ⟨base, zs, hbase, hzs, hn, hresponse, ?_⟩
  intro H I _ _ _ _ A U F hA hAU
  have hactual : ProjectedUnitaryEncoding (aeval A (p.map Complex.ofRealHom))
      (evaluate (parallelOracle U) (hermitianResponseWord F d base zs))
      (averageFrame F) (averageFrame F) := by
    unfold hermitianResponseWord
    split_ifs with hodd
    · rw [evaluate_compileRealPartQSVT]
      have h := realPartQSVT_odd_projectedEncoding hAU hbase zs hzs
        (by simpa only [hn] using hodd)
      rw [hreal, hermitian_dilation_polynomial_odd A hA p d hpar hodd] at h
      exact h
    · have heven : d % 2 = 0 := by omega
      rw [evaluate_swapQueries, parallelOracle_adjoint, evaluate_compileRealPartQSVT]
      have h := realPartQSVT_even_right_projectedEncoding hAU hbase zs hzs
        (by simpa only [hn] using heven)
      rw [hreal, hermitian_dilation_polynomial_even A hA p d hpar heven] at h
      exact h
  exact ⟨hactual, hermitianResponseWord_counts F d base zs hn⟩

/-- For a Hermitian projected unitary encoding, a bounded real parity polynomial has a phase
response word exactly encoding its matrix evaluation, using `d` queries and `d + 1` fixed
gates. -/
theorem hermitian_actual_qsvt_without_lipschitz
    (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (p : Polynomial ℝ) (d : ℕ)
    (hA : A.IsHermitian) (hAU : ProjectedUnitaryEncoding A U F F)
    (hpdeg : p.degree ≤ (d : WithBot ℕ)) (hpar : HasRealParity d p)
    (hbounded : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |p.eval x| ≤ 1) :
    ∃ (base : ℂ) (zs : List ℂ),
      IsPhase base ∧ (∀ z ∈ zs, IsPhase z) ∧ zs.length = d ∧
      (∀ x : ℝ, ((responseP base zs).eval (x : ℂ)).re = p.eval x) ∧
      ProjectedUnitaryEncoding (aeval A (p.map Complex.ofRealHom))
        (evaluate (parallelOracle U) (hermitianResponseWord F d base zs))
        (averageFrame F) (averageFrame F) ∧
      adjointQueryCount (hermitianResponseWord F d base zs) = d ∧
      adjointGateCount (hermitianResponseWord F d base zs) = d + 1 := by
  obtain ⟨base, zs, hbase, hzs, hn, hresponse, hactual⟩ :=
    hermitian_actual_qsvt_uniform_phases p d hpdeg hpar hbounded
  exact ⟨base, zs, hbase, hzs, hn, hresponse, hactual H I A U F hA hAU⟩

/-- The four LCU coefficients, equal to `1` on branches `0` and `1` and to `Complex.I` on
branches `2` and `3`. -/
def fourBranchCoefficients (j : Fin 4) : ℂ := if j.val < 2 then 1 else Complex.I

/-- Four bounded real parity polynomials have matrix-independent QSVT phases whose coefficient
LCU exactly block-encodes their weighted sum with normalization `4`. Each branch uses its
specified degree in queries and one additional fixed gate. -/
theorem four_parity_qsvt_uniform_phases
    (p : Fin 4 → Polynomial ℝ) (d : Fin 4 → ℕ)
    (hpdeg : ∀ j, (p j).degree ≤ (d j : WithBot ℕ))
    (hpar : ∀ j, HasRealParity (d j) (p j))
    (hbounded : ∀ j, ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(p j).eval x| ≤ 1) :
    ∃ (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧ (zs j).length = d j) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ),
      A.IsHermitian → ProjectedUnitaryEncoding A U F F →
      (∀ j, adjointQueryCount (hermitianResponseWord F (d j) (base j) (zs j)) = d j ∧
        adjointGateCount (hermitianResponseWord F (d j) (base j) (zs j)) = d j + 1) ∧
      BlockEncoding (aeval A (∑ j, fourBranchCoefficients j • (p j).map Complex.ofRealHom))
        (coefficientLCUUnitary fourBranchCoefficients
          (fun j => evaluate (parallelOracle U) (hermitianResponseWord F (d j) (base j) (zs j))) 0)
        (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) 4 0 := by
  have hex := fun j => hermitian_actual_qsvt_uniform_phases
    (p j) (d j) (hpdeg j) (hpar j) (hbounded j)
  choose base zs hbase hzs hlen hresponse hactual using hex
  refine ⟨base, zs, (fun j => ⟨hbase j, hzs j, hlen j⟩), ?_⟩
  intro H I _ _ _ _ A U F hA hAU
  have hencoding := fun j => (hactual j H I A U F hA hAU).1
  have hqueries := fun j => (hactual j H I A U F hA hAU).2.1
  have hgates := fun j => (hactual j H I A U F hA hAU).2.2
  refine ⟨(fun j => ⟨hqueries j, hgates j⟩), ?_⟩
  simp only [map_sum, map_smul]
  have hmass : coefficientMass
      (scaledLCUCoefficients fourBranchCoefficients (fun _ : Fin 4 => (1 : ℝ))) = 4 := by
    norm_num [coefficientMass, scaledLCUCoefficients, fourBranchCoefficients,
      Fin.sum_univ_succ]
  have h := scaled_approximate_lcu_encoding (0 : Fin 4)
    (fun j => aeval A ((p j).map Complex.ofRealHom))
    (fun j => evaluate (parallelOracle U) (hermitianResponseWord F (d j) (base j) (zs j)))
    (averageFrame F) (averageFrame F) fourBranchCoefficients
    (fun _ => (1 : ℝ)) (fun _ => (0 : ℝ))
    (fun j => (Qatlib.Concepts.BlockEncoding.ProjectedUnitaryEncoding.toBlockEncoding (hencoding j))) (by rw [hmass]; norm_num)
  have hcoeff : scaledLCUCoefficients fourBranchCoefficients
      (fun _ : Fin 4 => (1 : ℝ)) = fourBranchCoefficients := by
    funext j
    simp only [scaledLCUCoefficients, Complex.ofReal_one, mul_one]
  have hscale : (∑ j : Fin 4, ‖fourBranchCoefficients j‖ * (1 : ℝ)) = 4 := by
    norm_num [fourBranchCoefficients, Fin.sum_univ_succ]
  have herr : (∑ j : Fin 4, ‖fourBranchCoefficients j‖ * (0 : ℝ)) = 0 := by simp
  rw [hcoeff, hscale, herr] at h
  exact h

/-- For a fixed Hermitian projected unitary encoding, combines four bounded real
parity-polynomial QSVT words into an exact block encoding with normalization `4` and the
stated branch costs. -/
theorem four_parity_qsvt_blockEncoding
    (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
    (p : Fin 4 → Polynomial ℝ) (d : Fin 4 → ℕ)
    (hA : A.IsHermitian) (hAU : ProjectedUnitaryEncoding A U F F)
    (hpdeg : ∀ j, (p j).degree ≤ (d j : WithBot ℕ))
    (hpar : ∀ j, HasRealParity (d j) (p j))
    (hbounded : ∀ j, ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(p j).eval x| ≤ 1) :
    ∃ (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧ (zs j).length = d j) ∧
      (∀ j, adjointQueryCount (hermitianResponseWord F (d j) (base j) (zs j)) = d j ∧
        adjointGateCount (hermitianResponseWord F (d j) (base j) (zs j)) = d j + 1) ∧
      BlockEncoding (aeval A (∑ j, fourBranchCoefficients j • (p j).map Complex.ofRealHom))
        (coefficientLCUUnitary fourBranchCoefficients
          (fun j => evaluate (parallelOracle U) (hermitianResponseWord F (d j) (base j) (zs j))) 0)
        (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) 4 0 := by
  obtain ⟨base, zs, hphases, hactual⟩ :=
    four_parity_qsvt_uniform_phases p d hpdeg hpar hbounded
  exact ⟨base, zs, hphases, hactual H I A U F hA hAU⟩

/-- A complex polynomial bounded by one on `[-1, 1]` has matrix-independent phases for its four
real parity branches, whose LCU exactly block-encodes `aeval A P` with normalization `4`.
Each branch has at most `2 * P.natDegree + 1` queries. -/
theorem complex_polynomial_qsvt_uniform_phases
    (P : Polynomial ℂ)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1) :
    ∃ (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧
        (zs j).length = ComplexPolynomialSplit.branchDegrees P j) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ),
      A.IsHermitian → ProjectedUnitaryEncoding A U F F →
      (∀ j, adjointQueryCount (hermitianResponseWord F
          (ComplexPolynomialSplit.branchDegrees P j) (base j) (zs j)) =
          ComplexPolynomialSplit.branchDegrees P j ∧
        adjointGateCount (hermitianResponseWord F
          (ComplexPolynomialSplit.branchDegrees P j) (base j) (zs j)) =
          ComplexPolynomialSplit.branchDegrees P j + 1 ∧
        adjointQueryCount (hermitianResponseWord F
          (ComplexPolynomialSplit.branchDegrees P j) (base j) (zs j)) ≤
          2 * P.natDegree + 1) ∧
      BlockEncoding (aeval A P)
        (coefficientLCUUnitary fourBranchCoefficients
          (fun j => evaluate (parallelOracle U) (hermitianResponseWord F
            (ComplexPolynomialSplit.branchDegrees P j) (base j) (zs j))) 0)
        (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) 4 0 := by
  obtain ⟨base, zs, hphases, hactual⟩ := four_parity_qsvt_uniform_phases
    (ComplexPolynomialSplit.branches P) (ComplexPolynomialSplit.branchDegrees P)
    (ComplexPolynomialSplit.branches_degree P)
    (ComplexPolynomialSplit.branches_parity P)
    (ComplexPolynomialSplit.branches_bounded P hP)
  refine ⟨base, zs, hphases, ?_⟩
  intro H I _ _ _ _ A U F hA hAU
  obtain ⟨hcounts, hblock⟩ := hactual H I A U F hA hAU
  refine ⟨?_, ?_⟩
  · intro j
    refine ⟨(hcounts j).1, (hcounts j).2, ?_⟩
    rw [(hcounts j).1]
    exact ComplexPolynomialSplit.branchDegrees_le P j
  · have hcoeff : fourBranchCoefficients = ComplexPolynomialSplit.coefficients := by
      funext j
      fin_cases j <;> norm_num [fourBranchCoefficients, ComplexPolynomialSplit.coefficients]
    have hid : (∑ j, fourBranchCoefficients j •
        (ComplexPolynomialSplit.branches P j).map Complex.ofRealHom) = P := by
      rw [hcoeff]
      exact ComplexPolynomialSplit.branches_identity P
    rw [hid] at hblock
    exact hblock

end CBMD

end Qatlib.Papers.Cbmd26.Algorithms
