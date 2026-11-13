/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralCoefficients
import Qatlib.Concepts.NonNormalSpec.ResolventWord.NativeThresholdIntegralCutoff
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ThresholdIntegralConsumer

/-!
# Native threshold amplifier circuits

`nativeAmplifier_query_consumer` combines rational coefficient semantics, a computable cutoff,
and finite phase synthesis to construct an approximate block encoding of a scaled matrix. It
records query and gate counts together with explicit synthesis search counters in the singular
value transformation setting of [GilyenSuLowWiebe2019]

## Main statements

* `nativeAmplifier_query_consumer`: certifies successful phase synthesis, an error `ε` block
  encoding, and resource bounds.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord

set_option autoImplicit false
set_option maxHeartbeats 3000000

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.QspSimulation.Achievability

open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget

namespace Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib.Concepts.BlockEncoding Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib.Concepts.NonNormalSpec.ResolventWord Matrix Polynomial
open scoped Matrix.Norms.L2Operator

/-- For the stated rational parameter bounds and a projected unitary encoding with `‖A‖ ≤ (1 -
δ) / γ`, native synthesis returns phases whose circuit block encodes `γ • A` with error `ε`,
using `D` adjoint queries and `D + 1` adjoint gates. It also bounds `D` and the phase
search, response, coefficient, and table counters. -/
theorem nativeAmplifier_query_consumer
    (H I O : Type) [Fintype H] [DecidableEq H] [Fintype I] [DecidableEq I]
    [Fintype O] [DecidableEq O] (A : Matrix O I ℂ) (U : Matrix H H ℂ)
    (L : Matrix H O ℂ) (R : Matrix H I ℂ) (γ δ ε : ℚ)
    (henc : ProjectedUnitaryEncoding A U L R)
    (hγ : 1 ≤ γ) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 2)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 2)
    (hA : ‖A‖ ≤ (1 - (δ : ℝ)) / (γ : ℝ)) :
    let D := nativeAmplifierDegree γ δ ε
    let result := nativeAmplifierPhaseResult γ δ ε
    let N := 2 ^ phaseGridBits D (phaseToleranceBits (ε / 2))
    ∃ data : PhaseData, result.value = some data ∧
      let cs := computedPhaseWord (rangeProjector R) (rangeProjector L) data
      WellFormedAdjointCircuit cs ∧ adjointQueryCount cs = D ∧
      adjointGateCount cs = D + 1 ∧
      BlockEncoding ((γ : ℂ) • A)
        (evaluate (parallelOracle U) cs)
        (averageFrame L) (averageFrame R) 1 (ε : ℝ) ∧
      (D : ℝ) ≤ 1 + 8192 * (γ : ℝ) ^ 8 / (δ : ℝ) ^ 4 *
        (nativeAmplifierLogBudget γ δ ε : ℝ) ^ 2 ∧
      1 ≤ result.tested ∧ result.tested ≤ 1 + N ^ (D + 1) ∧
      result.responseRounds = result.tested * D ∧
      result.coefficientVisits = result.tested * (D + 1) ∧
      (result.backendCalls = 0 ∧ result.tableMultiplications = 0 ∨
        result.backendCalls = 1 ∧ result.tableMultiplications = N - 1) := by
  let k := nativeAmplifierCutoff γ δ ε
  let D := nativeAmplifierDegree γ δ ε
  let xs := rationalIntegratedThresholdCoefficients γ δ k
  let p := integratedThresholdPolynomial (γ : ℝ) (δ : ℝ) k
  have hp : realTarget xs = p := rationalIntegratedThresholdCoefficients_semantics γ δ k
  have hγr : (1 : ℝ) ≤ γ := by exact_mod_cast hγ
  have hδr : (0 : ℝ) < δ := by exact_mod_cast hδ
  have hδr1 : (δ : ℝ) ≤ 1 / 2 := by
    have hh := Rat.cast_le (K := ℝ) |>.mpr hδ1
    norm_num at hh
    exact hh
  have hεr : (0 : ℝ) < ε := by exact_mod_cast hε
  have heps : (0 : ℚ) < ε / 2 := div_pos hε (by norm_num)
  obtain ⟨hres, hbudget, _⟩ := nativeAmplifierCutoff_bounds γ δ ε hγ hδ hδ1 hε hε1
  obtain ⟨hglobal, hinner⟩ := integratedThresholdPolynomial_scalar_bounds
    (γ : ℝ) (δ : ℝ) (ε : ℝ) k hγr hδr hδr1 hεr hres
  have hd : p.natDegree ≤ D := integratedThresholdPolynomial_natDegree_le _ _ _
  have hodd : ∀ x : ℝ, p.eval (-x) = -p.eval x :=
    integratedThresholdPolynomial_odd _ _ _
  have hpar : HasRealParity D (realTarget xs) := by
    rw [hp]
    unfold HasRealParity
    apply Polynomial.funext
    intro x
    simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C]
    simpa [D, nativeAmplifierDegree, pow_add, pow_mul] using hodd x
  have hdegree : (realTarget xs).degree ≤ (D : WithBot ℕ) := by
    rw [hp]
    exact Polynomial.degree_le_of_natDegree_le hd
  have hb : ∀ x ∈ Set.Icc (-1 : ℝ) 1, |(realTarget xs).eval x| ≤ 1 := by
    rw [hp]
    intro x hx
    exact (hglobal x hx).trans (by linarith)
  obtain ⟨data, hdata, hw, hquery, hgate, hblock, _⟩ :=
    computed_phase_word_actual_matrix_transform H I O A U L R xs D (ε / 2)
      henc heps hdegree hpar hb
  have hDodd : D % 2 = 1 := by dsimp [D, nativeAmplifierDegree]; omega
  have herr : ‖(γ : ℂ) • A -
      oddSingularTransform A (fun x : ℝ => (((realTarget xs).eval x : ℝ) : ℂ))‖ ≤
        (ε : ℝ) / 2 := by
    rw [hp, norm_sub_rev]
    have hlinear : oddSingularTransform A (fun x : ℝ => (((γ : ℝ) * x : ℝ) : ℂ)) =
        (γ : ℂ) • A := by
      simpa only [Complex.ofReal_ratCast] using oddSingularTransform_linear A (γ : ℝ)
    rw [← hlinear]
    apply oddSingularTransform_error_le_positive A _ _ (by positivity)
    intro i _
    have hx : |matrixSingularValues A i| ≤ (1 - (δ : ℝ)) / (γ : ℝ) := by
      rw [abs_of_nonneg (matrixSingularValues_nonneg A i)]
      exact (matrixSingularValues_le_spectralNorm A i).trans hA
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact hinner _ hx
  have hactual := (hblock hDodd).perturb (by positivity : (0 : ℝ) ≤ (ε : ℝ) / 2) herr
  obtain ⟨_, _, _, _, _, _, _, htlow, htupper, hrounds, hvisits, htables⟩ :=
    finite_rational_phase_synthesis_terminates xs D (ε / 2) heps hdegree hpar hb
  refine ⟨data, hdata, hw, hquery, hgate, ?_, ?_, htlow, htupper, hrounds, hvisits, htables⟩
  · convert hactual using 1
    norm_num [Rat.cast_div]
  · simpa only [D, nativeAmplifierDegree, k, Nat.cast_add, Nat.cast_mul,
      Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using hbudget

end Qatlib.Concepts.NonNormalSpec.ResolventWord
