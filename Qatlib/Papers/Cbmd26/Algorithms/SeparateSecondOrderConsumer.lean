/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.SeparateSecondOrderWord
import Qatlib.Papers.Cbmd26.Algorithms.UniformPropagatorApproximation

/-!
# Uniform second-order encodings from separate oracles

This module combines polynomial approximation with separate matrix access to encode finite
linear combinations of second-order propagators. The phase choices depend on scalar parameters
and sample data, uniformly over matrix instances satisfying the spectral and encoding hypotheses
of [WangEtAl2026].

## Main statements

* `secondOrder_normalized_sample_error`: lifts a scalar approximation to a matrix error bound of
  `2 * η`.
* `secondOrder_separate_uniform`: constructs valid phases and a counted block encoding with
  normalization `4 * coefficientMass c`.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option backward.isDefEq.respectTransparency false

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
set_option maxHeartbeats 800000
noncomputable section
namespace CBMD
open Matrix Polynomial

open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- On a Hermitian normalized sample with spectrum in `[g, 1]`, scalar polynomial error at most
`η` gives matrix error at most `2 * η` after applying `normalizedApproximation`, under the
stated positivity and time hypotheses. -/
theorem secondOrder_normalized_sample_error
    (I : Type) [Fintype I] [DecidableEq I] (kind : SecondOrderFamily)
    (X : Matrix I I ℂ) (b g t η : ℝ) (hb : 0 < b) (hg : 0 < g)
    (ht : 0 ≤ t) (hη : 0 ≤ η) (P : Polynomial ℂ)
    (hA : (b⁻¹ • X).IsHermitian)
    (hspec : ∀ i, orderedHermitianValues hA i ∈ Set.Icc g 1)
    (happrox : ∀ x ∈ Set.Icc g 1,
      ‖P.eval (x : ℂ) - secondOrderPropagator kind ((b * x : ℝ) : ℂ) t‖ ≤ η) :
    ‖secondOrderPropagator kind X t - aeval (b⁻¹ • X) (normalizedApproximation P η)‖ ≤
      2 * η := by
  have hrescale : (b : ℂ) • (b⁻¹ • X) = X := by
    ext i j
    simp only [Matrix.smul_apply, Complex.real_smul, smul_eq_mul]
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hb.ne', Complex.ofReal_one, one_mul]
  rw [← hrescale, ← secondOrder_hermitian_function_eq_series kind I _ hA b t]
  rw [hrescale]
  have herr : ‖hermitianFunction (b⁻¹ • X) hA
      (fun x => secondOrderPropagator kind ((b * x : ℝ) : ℂ) t) -
      aeval (b⁻¹ • X) (normalizedApproximation P η)‖ ≤ 2 * η / (1 + η) := by
    apply hermitian_complex_polynomial_error I _ hA _ _ _ (by positivity)
    intro i
    have hi := hspec i
    have hh := normalized_scalar_error (P.eval (orderedHermitianValues hA i : ℂ))
      (secondOrderPropagator kind ((b * orderedHermitianValues hA i : ℝ) : ℂ) t)
      η hη
      (secondOrder_scalar_pos_bound kind _ t (mul_nonneg hb.le (hg.le.trans hi.1)) ht)
      (happrox _ hi)
    rw [norm_sub_rev]
    simpa only [normalizedApproximation, Polynomial.eval_smul] using! hh
  exact herr.trans (div_le_self (by positivity) (by linarith))

/-- There exist uniform phase lists producing a valid encoding of the weighted second-order
sample propagators for every matrix instance satisfying the separate encoding and spectral
hypotheses. With the prescribed degree `D`, the normalization is `4 * coefficientMass c`,
the error is `2 * η * coefficientMass c`, and the circuit uses `8 * D + 2` queries per
oracle and `80 * D + 33` fixed gates. -/
theorem secondOrder_separate_uniform
    {J : Type} [Fintype J] [DecidableEq J]
    (kind : SecondOrderFamily) (t βL βH μL μH bmax η : ℝ)
    (c : J → ℂ) (j₀ : J) (s : J → ℝ)
    (ht : 0 ≤ t) (hβL : 0 < βL) (hβH : 0 < βH)
    (hμL : 0 < μL) (hμH : 0 < μH) (hη : 0 < η)
    (hc : 0 < coefficientMass c) (hs : ∀ j, 0 ≤ s j)
    (hbmax : ∀ j, βL + s j * βH ≤ bmax) :
    let κ := max (βL / μL) (βH / μH)
    let D := secondOrderDegreeBudget kind t bmax κ⁻¹ η
    ∃ (base : Fin 4 → J → ℂ) (zs : Fin 4 → List (J → ℂ)),
      (∀ k j, IsPhase (base k j)) ∧
      (∀ k, ∀ z ∈ zs k, ∀ j, IsPhase (z j)) ∧
      (∀ k, (zs k).length = uniformBranchDegree D k) ∧
      ∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
        (L H : Matrix I I ℂ) (UL UH : Matrix W W ℂ) (F : Matrix W I ℂ),
      L.IsHermitian → H.IsHermitian →
      (L - μL • (1 : Matrix I I ℂ)).PosSemidef →
      (H - μH • (1 : Matrix I I ℂ)).PosSemidef →
      BlockEncoding L UL F F βL 0 → BlockEncoding H UH F F βH 0 →
      PreparedCircuitValid (secondOrderWord c j₀ F D base zs βL βH s) ∧
      BlockEncoding (∑ j, c j • secondOrderPropagator kind (L + (s j : ℂ) • H) t)
        (evaluatePrepared
          (controlOracle (parallelOracle (J := PreparedPredicateLabels (Fin 4) J Bool) UH))
          (controlOracle (parallelOracle (J := PreparedPredicateLabels (Fin 4) J Bool) UL))
          (secondOrderWord c j₀ F D base zs βL βH s))
        (secondOrderFrame j₀ F) (secondOrderFrame j₀ F)
        (4 * coefficientMass c) (2 * η * coefficientMass c) ∧
      preparedDataQueries (secondOrderWord c j₀ F D base zs βL βH s) = 8 * D + 2 ∧
      preparedInputQueries (secondOrderWord c j₀ F D base zs βL βH s) = 8 * D + 2 ∧
      preparedFixedGates (secondOrderWord c j₀ F D base zs βL βH s) = 80 * D + 33 := by
  (try dsimp only)
  let κ := max (βL / μL) (βH / μH)
  let D := secondOrderDegreeBudget kind t bmax κ⁻¹ η
  have hκ : 0 < κ := lt_of_lt_of_le (div_pos hβL hμL) (le_max_left _ _)
  have hb (j : J) : 0 < βL + s j * βH := add_pos_of_pos_of_nonneg hβL (mul_nonneg (hs j) hβH.le)
  have hex := fun j => secondOrder_uniform_polynomial_exists kind t (βL + s j * βH)
    bmax κ⁻¹ η ht (hb j).le (hbmax j) (inv_pos.mpr hκ) hη
  choose P hd hbound happ using hex
  let Q := fun j => normalizedApproximation (P j) η
  have hQd (j : J) : (Q j).natDegree ≤ D :=
    (Polynomial.natDegree_smul_le ((1 + η)⁻¹ : ℝ) (P j)).trans (hd j)
  obtain ⟨base, zs, hbase, hzs, hlen, hactual⟩ := bounded_polynomial_family_phases Q D hQd
    (fun j => normalizedApproximation_bounded (P j) η hη.le (hbound j))
  refine ⟨base, zs, hbase, hzs, hlen, ?_⟩
  intro W I _ _ _ _ L H UL UH F hLH hHH hLlow hHlow hL hH
  let A := fun j => (βL + s j * βH)⁻¹ • (L + (s j : ℂ) • H)
  let U := fun j => separateSampleUnitary UL UH βL βH (s j)
  have hA (j : J) : (A j).IsHermitian :=
    normalized_separate_sample_isHermitian L H hLH hHH βL βH (s j)
  have hAU (j : J) : ProjectedUnitaryEncoding (A j) (U j) (tagFrame false F) (tagFrame false F) :=
    separate_oracles_sample_projectedEncoding L H UL UH F βL βH (s j) (hs j) hL hH
  have hpoly := flat_polynomial_family_encoding c j₀ hc Q D A U (tagFrame false F) base zs
    (hactual (Bool × W) I A U (tagFrame false F) hA hAU)
  have herrj (j : J) : ‖secondOrderPropagator kind (L + (s j : ℂ) • H) t -
      aeval (A j) (Q j)‖ ≤ 2 * η := by
    apply secondOrder_normalized_sample_error I kind _ _ κ⁻¹ t η (hb j)
      (inv_pos.mpr hκ) ht hη.le (P j) (hA j) _ (happ j)
    intro i
    exact separate_oracles_normalized_spectrum L H UL UH F βL βH (s j) μL μH κ
      (hs j) hμL hμH hκ (le_max_left _ _) (le_max_right _ _) hLlow hHlow hL hH (hA j) i
  have herr : ‖(∑ j, c j • secondOrderPropagator kind (L + (s j : ℂ) • H) t) -
      ∑ j, c j • aeval (A j) (Q j)‖ ≤ 2 * η * coefficientMass c := by
    rw [← Finset.sum_sub_distrib]
    calc
      _ = ‖∑ j, c j • (secondOrderPropagator kind (L + (s j : ℂ) • H) t -
          aeval (A j) (Q j))‖ := by simp only [smul_sub]
      _ ≤ ∑ j, ‖c j • (secondOrderPropagator kind (L + (s j : ℂ) • H) t -
          aeval (A j) (Q j))‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖c j‖ * (2 * η) := Finset.sum_le_sum fun j _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_left (herrj j) (norm_nonneg _)
      _ = _ := by rw [← Finset.sum_mul]; simp only [coefficientMass]; ring
  have hnonneg : 0 ≤ 2 * η * coefficientMass c := by positivity
  have henc := hpoly.perturb hnonneg herr
  simp only [zero_add] at henc
  have hraw := rawSecondOrderWord_valid c j₀ hc F hL.left_isometry D base hbase zs hzs
    βL βH s hβL hβH hs
  have hrawenc : BlockEncoding (∑ j, c j • secondOrderPropagator kind (L + (s j : ℂ) • H) t)
      (evaluatePrepared (preparedPredicateSource (J := J) (R := Bool) fourActive UH)
        (preparedPredicateSource (J := J) (R := Bool) fourActive UL)
        (rawSecondOrderWord c j₀ F D base zs βL βH s))
      (tagFrame (0, j₀) (averageFrame (tagFrame false F)))
      (tagFrame (0, j₀) (averageFrame (tagFrame false F)))
      (4 * coefficientMass c) (2 * η * coefficientMass c) := by
    rw [rawSecondOrderWord_evaluate]
    exact henc
  exact ⟨compiledPreparedPredicateWord_valid _ hraw,
    compiledPreparedPredicateWord_blockEncoding fourActive UH UL hH.unitary hL.unitary
      _ hraw _ _ _ _ hrawenc,
    secondOrderWord_cost c j₀ F D base zs hlen βL βH s⟩

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
