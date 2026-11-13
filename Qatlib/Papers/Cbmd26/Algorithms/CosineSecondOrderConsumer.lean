/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.SeparateSecondOrderConsumer
import Qatlib.Papers.Cbmd26.Algorithms.CosineQueryBudget

/-!
# Cosine sample circuits for second-order propagators

Instantiates the cosine contour expansion with the second-order propagator families through
`cosineCoefficients`, `cosineScales`, and `secondOrderNumerator`. The chosen finite sum
approximates the target propagator, and `cosine_secondOrder_operator` compiles it into a valid
circuit using separate Hermitian-component encodings. These results support the contour-based
algorithms of [WangEtAl2026].

## Main statements

* `cosine_secondOrder_chosen_error`: bounds the chosen finite-sample approximation error.
* `cosine_secondOrder_operator`: constructs a block encoding with exact circuit counts.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

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
set_option maxHeartbeats 800000
noncomputable section
namespace CBMD
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- Defines the optional retained-sample labels at the chosen cosine truncation accuracy. -/
abbrev CosineSampleLabels (γ τ δ : ℝ) :=
    Option (Fin (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ δ))

/-- Assigns the regulator coefficient to the optional base label and the negative regulated
sample coefficient to each retained sample. -/
def cosineCoefficients (γ τ : ℝ) (N : ℕ) : Option (Fin N) → ℂ
  | none => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRegulator γ τ 1
  | some k => -(_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRegulator γ τ 1 * _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineSampleCoefficient γ τ k)

/-- Assigns scale zero to the base label and the cosine sample scale to each retained sample. -/
def cosineScales (γ τ : ℝ) (N : ℕ) : Option (Fin N) → ℝ
  | none => 0
  | some k => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineSampleScale γ τ k

/-- The absolute mass of the cosine coefficients equals the finite cosine weight mass. -/
theorem cosineCoefficients_mass (γ τ : ℝ) (N : ℕ) :
    coefficientMass (cosineCoefficients γ τ N) = _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineFiniteWeightMass γ τ N := by
  simp only [coefficientMass, Fintype.sum_option, cosineCoefficients, norm_neg, norm_mul]
  rw [← Finset.mul_sum]
  rw [Fin.sum_univ_eq_sum_range (fun k => ‖_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineSampleCoefficient γ τ k‖) N]
  simp only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineFiniteWeightMass]
  ring

/-- All cosine sample scales are nonnegative for positive `γ` and `τ`. -/
theorem cosineScales_nonneg {γ τ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ)
    (N : ℕ) (j : Option (Fin N)) : 0 ≤ cosineScales γ τ N j := by
  cases j with
  | none => exact le_rfl
  | some k => exact (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineSampleScale_pos hγ hτ k).le

/-- Defines the complex-parameter numerator by applying the second-order propagator to `L + (i *
z) • H`. -/
def secondOrderNumerator {E : Type*} [NormedRing E] [NormedAlgebra ℂ E] [CompleteSpace E]
    (kind : SecondOrderFamily) (L H : E) (t : ℝ) (z : ℂ) : E :=
  secondOrderPropagator kind (L + (Complex.I * z) • H) t

/-- The finite weighted sum of real-parameter second-order propagators equals the cosine
approximation of the complex-parameter numerator. -/
theorem cosine_secondOrder_sum {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (L H : Matrix I I ℂ) (t γ τ : ℝ) (N : ℕ) :
    (∑ j : Option (Fin N), cosineCoefficients γ τ N j •
      secondOrderPropagator kind (L + (cosineScales γ τ N j : ℂ) • H) t) =
    _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineApproximation γ τ N (secondOrderNumerator kind L H t) := by
  simp only [Fintype.sum_option, cosineCoefficients, cosineScales, Complex.ofReal_zero,
    zero_smul, add_zero, neg_smul, mul_smul, Finset.sum_neg_distrib, ← Finset.smul_sum,
    ]
  simp only [_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineApproximation, _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineLCUSum,
    _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineSample, secondOrderNumerator, mul_zero, zero_smul, add_zero,
    _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosinePencil_sample, sub_eq_add_neg]
  rw [Fin.sum_univ_eq_sum_range (fun k => _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineSampleCoefficient γ τ k •
    secondOrderPropagator kind (L + (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineSampleScale γ τ k : ℂ) • H) t) N]

/-- The chosen finite cosine sample sum approximates the second-order propagator of `L + iH`
within operator error `δ` under the stated positivity and norm assumptions [WangEtAl2026]. -/
theorem cosine_secondOrder_chosen_error {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (L H : Matrix I I ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t δ : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hδ : 0 < δ) (hγH : ‖H‖ ≤ γ) :
    let τ := secondOrderTimeScale kind t
    let N := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ δ
    ‖secondOrderPropagator kind (L + Complex.I • H) t -
      ∑ j : Option (Fin N), cosineCoefficients γ τ N j •
        secondOrderPropagator kind (L + (cosineScales γ τ N j : ℂ) • H) t‖ ≤ δ := by
  (try dsimp only)
  rw [cosine_secondOrder_sum]
  cases kind
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wave_cbmd_chosen_error L H hL hH hγ ht hδ hγH
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.bessel_cbmd_chosen_error L H hL hH hγ ht hδ hγH
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airy_cbmd_chosen_error L H hL hH hγ ht hδ hγH

/-- Defines the uniform cosine sample scale bound from component norm bounds and truncation
accuracy. -/
def cosineSampleUpperScale (βL βH γ τ δ : ℝ) : ℝ :=
  βL + 169 * βH * Real.exp (τ * Real.sqrt (γ / 2)) / δ

/-- Every chosen cosine sample has component scale at most `cosineSampleUpperScale`. -/
theorem cosineScales_bound {γ τ δ : ℝ} (hγ : 0 < γ) (hτ : 0 < τ) (hδ : 0 < δ)
    (βL βH : ℝ) (hβH : 0 ≤ βH) (j : CosineSampleLabels γ τ δ) :
    βL + cosineScales γ τ (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ δ) j * βH ≤
      cosineSampleUpperScale βL βH γ τ δ := by
  cases j with
  | none =>
    simp only [cosineScales, zero_mul, add_zero, cosineSampleUpperScale]
    exact le_add_of_nonneg_right (by positivity)
  | some k =>
    have hh := mul_le_mul_of_nonneg_right
      (_root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetained_sampleScale_le hγ hτ hδ k k.isLt) hβH
    dsimp only [cosineScales, cosineSampleUpperScale]
    convert! add_le_add_left hh βL using 1 <;> ring

/-- Constructs phase data for a valid separate-oracle encoding of the second-order propagator
with scale four times the chosen mass, error `ε * η / 4`, `8 * D + 2` queries to each
component oracle, and `80 * D + 33` fixed gates [WangEtAl2026]. -/
theorem cosine_secondOrder_operator
    (kind : SecondOrderFamily) (t βL βH μL μH γ ε η : ℝ)
    (ht : 0 < t) (hβL : 0 < βL) (hβH : 0 < βH)
    (hμL : 0 < μL) (hμH : 0 < μH) (hγ : 0 < γ) (hε : 0 < ε) (hη : 0 < η) :
    let τ := secondOrderTimeScale kind t
    let N := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ (ε * η / 8)
    let c := cosineCoefficients γ τ N
    let s := cosineScales γ τ N
    let δq := cosineWeightedAccuracy γ τ ε η
    let κ := max (βL / μL) (βH / μH)
    let D := secondOrderDegreeBudget kind t (cosineSampleUpperScale βL βH γ τ (ε * η / 8)) κ⁻¹ δq
    ∃ (base : Fin 4 → Option (Fin N) → ℂ) (zs : Fin 4 → List (Option (Fin N) → ℂ)),
      (∀ k j, IsPhase (base k j)) ∧
      (∀ k, ∀ z ∈ zs k, ∀ j, IsPhase (z j)) ∧
      (∀ k, (zs k).length = uniformBranchDegree D k) ∧
      ∀ (W I : Type) [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
        (L H : Matrix I I ℂ) (UL UH : Matrix W W ℂ) (F : Matrix W I ℂ),
      L.PosSemidef → H.PosDef → ‖H‖ ≤ γ →
      (L - μL • (1 : Matrix I I ℂ)).PosSemidef →
      (H - μH • (1 : Matrix I I ℂ)).PosSemidef →
      BlockEncoding L UL F F βL 0 → BlockEncoding H UH F F βH 0 →
      PreparedCircuitValid (secondOrderWord c none F D base zs βL βH s) ∧
      BlockEncoding (secondOrderPropagator kind (L + Complex.I • H) t)
        (evaluatePrepared
          (controlOracle (parallelOracle (J := PreparedPredicateLabels (Fin 4) (Option (Fin N)) Bool) UH))
          (controlOracle (parallelOracle (J := PreparedPredicateLabels (Fin 4) (Option (Fin N)) Bool) UL))
          (secondOrderWord c none F D base zs βL βH s))
        (secondOrderFrame none F) (secondOrderFrame none F)
        (4 * cosineChosenMass γ τ ε η) (ε * η / 4) ∧
      preparedDataQueries (secondOrderWord c none F D base zs βL βH s) = 8 * D + 2 ∧
      preparedInputQueries (secondOrderWord c none F D base zs βL βH s) = 8 * D + 2 ∧
      preparedFixedGates (secondOrderWord c none F D base zs βL βH s) = 80 * D + 33 := by
  (try dsimp only)
  let τ := secondOrderTimeScale kind t
  let N := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ (ε * η / 8)
  have hτ : 0 < τ := secondOrderTimeScale_pos kind ht
  have hδ : 0 < ε * η / 8 := by positivity
  have hm : coefficientMass (cosineCoefficients γ τ N) = cosineChosenMass γ τ ε η :=
    cosineCoefficients_mass γ τ N
  obtain ⟨base, zs, hb, hz, hl, ha⟩ := secondOrder_separate_uniform kind t βL βH μL μH
    (cosineSampleUpperScale βL βH γ τ (ε * η / 8)) (cosineWeightedAccuracy γ τ ε η)
    (cosineCoefficients γ τ N) none (cosineScales γ τ N) ht.le hβL hβH hμL hμH
    (cosineWeightedAccuracy_pos hγ hτ hε hη)
    (by rw [hm]; exact cosineChosenMass_pos hγ hτ ε η)
    (cosineScales_nonneg hγ hτ N) (cosineScales_bound hγ hτ hδ βL βH hβH.le)
  refine ⟨base, zs, hb, hz, hl, ?_⟩
  intro W I _ _ _ _ L H UL UH F hL hH hγH hLlow hHlow hUL hUH
  obtain ⟨hw, he, hq⟩ := ha W I L H UL UH F hL.isHermitian hH.isHermitian hLlow hHlow hUL hUH
  have herr := cosine_secondOrder_chosen_error kind L H hL hH hγ ht hδ hγH
  have he' := he.perturb hδ.le herr
  rw [hm, cosineWeightedAccuracy_error hγ hτ ε η] at he'
  have hsum : ε * η / 8 + ε * η / 8 = ε * η / 4 := by ring
  rw [hsum] at he'
  exact ⟨hw, he', hq⟩

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
