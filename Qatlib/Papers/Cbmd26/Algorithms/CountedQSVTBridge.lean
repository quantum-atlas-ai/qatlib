/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.FourBranchWordBridge
import Qatlib.Papers.Cbmd26.Algorithms.StaticExponentialBridge

/-!
# Counted four-branch polynomial transformation

Combines four real parity branches in `fourQSVTWord`, a clean controlled QSVT word with exact
query and gate counts. Uniform phase choices encode a bounded complex polynomial of a Hermitian
input, and `static_exponential_counted_qsvt_uniform` gives the corresponding exponential
encoding. These results support the contour-based algorithms of [WangEtAl2026].

## Main statements

* `complex_polynomial_counted_qsvt_uniform`: encodes bounded complex polynomials with scale
  four.
* `static_exponential_counted_qsvt_uniform`: supplies an exponential encoding and a degree-based
  query bound.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

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
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
noncomputable section
namespace CBMD
open Matrix Polynomial
open scoped BigOperators Matrix.Norms.L2Operator

variable {H I : Type} [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]

/-- An isometric frame and unit-modulus phase data make the Hermitian response word well formed. -/
theorem hermitianResponseWord_wellFormed (F : Matrix H I ℂ) (hF : IsIsometry F)
    (d : ℕ) (base : ℂ) (hb : IsPhase base) (zs : List ℂ)
    (hzs : ∀ z ∈ zs, IsPhase z) :
    WellFormedAdjointCircuit (hermitianResponseWord F d base zs) := by
  have hw := compileRealPartQSVT_wellFormed (rangeProjector_isOrthogonalProjector hF)
    (rangeProjector_isOrthogonalProjector hF) hb zs hzs
  unfold hermitianResponseWord
  split_ifs
  · exact hw
  · exact hw.swapQueries

/-- Combines four Hermitian response words using the clean four-coefficient LCU construction. -/
def fourQSVTWord (F : Matrix H I ℂ) (d : Fin 4 → ℕ)
    (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) :
    List (AdjointStep (Bool × (Fin 4 × (Bool × H)))) :=
  cleanFourCoefficientWord fourBranchCoefficients
    (fun j => hermitianResponseWord F (d j) (base j) (zs j))

/-- The four branch coefficients have total absolute mass four. -/
theorem fourBranchCoefficients_mass : coefficientMass fourBranchCoefficients = 4 := by
  norm_num [coefficientMass, fourBranchCoefficients, Fin.sum_univ_succ]

omit [DecidableEq I] in

/-- With phase-list lengths matching the branch degrees, the four-branch word uses the sum of
the degrees in queries and three times that sum plus thirteen gates. -/
theorem fourQSVTWord_cost (F : Matrix H I ℂ) (d : Fin 4 → ℕ)
    (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ) (hlen : ∀ j, (zs j).length = d j) :
    adjointQueryCount (fourQSVTWord F d base zs) = ∑ j, d j ∧
    adjointGateCount (fourQSVTWord F d base zs) = 3 * (∑ j, d j) + 13 := by
  obtain ⟨hq, hg⟩ := cleanFourCoefficientWord_cost fourBranchCoefficients
    (fun j => hermitianResponseWord F (d j) (base j) (zs j))
  simp_rw [(hermitianResponseWord_counts F _ _ _ (hlen _)).1] at hq hg
  simp_rw [(hermitianResponseWord_counts F _ _ _ (hlen _)).2] at hg
  refine ⟨hq, ?_⟩
  change adjointGateCount (fourQSVTWord F d base zs) = _ at hg
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      smul_eq_mul, mul_one] at hg
  omega

/-- The four-branch clean controlled word preserves the specified LCU block encoding and is well
formed, with the stated exact query and gate counts. -/
theorem fourQSVTWord_blockEncoding (A : Matrix I I ℂ) (U : Matrix H H ℂ)
    (hU : U ∈ Matrix.unitaryGroup H ℂ) (F : Matrix H I ℂ) (hF : IsIsometry F)
    (d : Fin 4 → ℕ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ)
    (hp : ∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧ (zs j).length = d j)
    (α ε : ℝ)
    (henc : BlockEncoding A
      (coefficientLCUUnitary fourBranchCoefficients
        (fun j => evaluate (parallelOracle U) (hermitianResponseWord F (d j) (base j) (zs j))) 0)
      (tagFrame 0 (averageFrame F)) (tagFrame 0 (averageFrame F)) α ε) :
    WellFormedAdjointCircuit (fourQSVTWord F d base zs) ∧
    BlockEncoding A
      (evaluate (controlOracle (parallelOracle (J := Fin 4) (parallelOracle (J := Bool) U)))
        (fourQSVTWord F d base zs))
      (tagFrame false (tagFrame 0 (averageFrame F)))
      (tagFrame false (tagFrame 0 (averageFrame F))) α ε ∧
    adjointQueryCount (fourQSVTWord F d base zs) = ∑ j, d j ∧
    adjointGateCount (fourQSVTWord F d base zs) = 3 * (∑ j, d j) + 13 := by
  obtain ⟨hw, he, _, _⟩ := cleanFourCoefficientWord_blockEncoding (parallelOracle U)
    (parallelOracle_unitary hU) fourBranchCoefficients
    (by rw [fourBranchCoefficients_mass]; norm_num)
    (fun j => hermitianResponseWord F (d j) (base j) (zs j))
    (fun j => hermitianResponseWord_wellFormed F hF _ _ (hp j).1 _ (hp j).2.1)
    A (tagFrame 0 (averageFrame F)) α ε henc
  exact ⟨hw, he, fourQSVTWord_cost F d base zs (fun j => (hp j).2.2)⟩

/-- A complex polynomial bounded by one on `[-1, 1]` has uniform phase data giving an exact
scale-four encoding of its evaluation on any Hermitian projected input, with at most `4 * (2
* P.natDegree + 1)` queries [WangEtAl2026]. -/
theorem complex_polynomial_counted_qsvt_uniform (P : Polynomial ℂ)
    (hP : ∀ x ∈ Set.Icc (-1 : ℝ) 1, ‖P.eval (x : ℂ)‖ ≤ 1) :
    ∃ (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧
        (zs j).length = ComplexPolynomialSplit.branchDegrees P j) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
        (_hA : A.IsHermitian), ProjectedUnitaryEncoding A U F F →
      WellFormedAdjointCircuit (fourQSVTWord F (ComplexPolynomialSplit.branchDegrees P) base zs) ∧
      BlockEncoding (aeval A P)
        (evaluate (controlOracle (parallelOracle (J := Fin 4) (parallelOracle (J := Bool) U)))
          (fourQSVTWord F (ComplexPolynomialSplit.branchDegrees P) base zs))
        (tagFrame false (tagFrame 0 (averageFrame F)))
        (tagFrame false (tagFrame 0 (averageFrame F))) 4 0 ∧
      adjointQueryCount (fourQSVTWord F (ComplexPolynomialSplit.branchDegrees P) base zs)
        ≤ 4 * (2 * P.natDegree + 1) := by
  obtain ⟨base, zs, hp, ha⟩ := complex_polynomial_qsvt_uniform_phases P hP
  refine ⟨base, zs, hp, ?_⟩
  intro H I _ _ _ _ A U F hA hAU
  obtain ⟨_, he⟩ := ha H I A U F hA hAU
  obtain ⟨hw, hblock, hq, _⟩ := fourQSVTWord_blockEncoding (aeval A P) U hAU.unitary
    F hAU.left_isometry (ComplexPolynomialSplit.branchDegrees P) base zs hp 4 0 he
  refine ⟨hw, hblock, ?_⟩
  rw [hq]
  calc
    _ ≤ ∑ _j : Fin 4, (2 * P.natDegree + 1) :=
      Finset.sum_le_sum (fun j _ => ComplexPolynomialSplit.branchDegrees_le P j)
    _ = _ := by simp

/-- Constructs uniform polynomial and phase data encoding `exp (-iτA)` with scale four and error
`ε`, with degree and query bounds given by the stated dyadic order [WangEtAl2026]. -/
theorem static_exponential_counted_qsvt_uniform (τ ε : ℝ) (hε : 0 < ε) :
    ∃ (P : Polynomial ℂ) (base : Fin 4 → ℂ) (zs : Fin 4 → List ℂ),
      P.natDegree ≤ dyadicOrder ((ε/2) / (2 * Real.exp (2 * |τ|))) ∧
      (∀ j, IsPhase (base j) ∧ (∀ z ∈ zs j, IsPhase z) ∧
        (zs j).length = ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2)) j) ∧
      ∀ (H I : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
        (A : Matrix I I ℂ) (U : Matrix H H ℂ) (F : Matrix H I ℂ)
        (_hA : A.IsHermitian), ProjectedUnitaryEncoding A U F F →
      WellFormedAdjointCircuit (fourQSVTWord F
        (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2))) base zs) ∧
      BlockEncoding (NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A))
        (evaluate (controlOracle (parallelOracle (J := Fin 4) (parallelOracle (J := Bool) U)))
          (fourQSVTWord F (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2))) base zs))
        (tagFrame false (tagFrame 0 (averageFrame F)))
        (tagFrame false (tagFrame 0 (averageFrame F))) 4 ε ∧
      adjointQueryCount (fourQSVTWord F
          (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2))) base zs) ≤
        4 * (2 * dyadicOrder ((ε/2) / (2 * Real.exp (2 * |τ|))) + 1) := by
  obtain ⟨P, base, zs, hd, hp, ha⟩ := static_exponential_qsvt_exists τ ε hε
  refine ⟨P, base, zs, hd, hp, ?_⟩
  intro H I _ _ _ _ A U F hA hAU
  obtain ⟨hc, he⟩ := ha H I A U F hA hAU
  obtain ⟨hw, hblock, hq, _⟩ := fourQSVTWord_blockEncoding
    (NormedSpace.exp ((-Complex.I * (τ : ℂ)) • A)) U hAU.unitary F hAU.left_isometry
    (ComplexPolynomialSplit.branchDegrees (normalizedApproximation P (ε/2))) base zs hp 4 ε he
  refine ⟨hw, hblock, ?_⟩
  rw [hq]
  calc
    _ ≤ ∑ _j : Fin 4, (2 * dyadicOrder ((ε/2) / (2 * Real.exp (2 * |τ|))) + 1) := by
      apply Finset.sum_le_sum
      intro j _
      rw [← (hermitianResponseWord_counts F _ _ _ (hp j).2.2).1]
      exact hc j
    _ = _ := by simp

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
