/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.SecondOrderComputationalFrame
import Qatlib.Papers.Cbmd26.Algorithms.ThreeOracleWorstCase

/-!
# Amplified cosine-based second-order algorithms

Combines the cosine sample construction with computational postselection and randomized
amplitude amplification for the second-order propagator families. The predicate
`ThreeOracleOutputCertificate` separates the two matrix-oracle costs from state preparation and
records successful normalized output accuracy up to phase. These results support the
contour-based algorithms of [WangEtAl2026].

## Main statements

* `ThreeOracleOutputCertificate`: records three-oracle cost and output guarantees.
* `cosine_secondOrder_amplified`: produces an amplified second-order output certificate.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.LcuPostselect.ScaledLCU
open Qatlib.Concepts.LocalMachine.LocalTransport
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QsvtCore.QueryLowerBound
open Qatlib.Concepts.SignalPrimitive.HermitianQSVT
open Qatlib.Concepts.SpectralReadout.PhaseReadout Qatlib.Foundations.InstrumentCore.Measurement
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.BlockEncoding.EncodingCore
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing

namespace Qatlib.Papers.Cbmd26.Algorithms

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CBMD
open Matrix Polynomial
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder ENNReal

/-- At truncation accuracy `ε * η / 8`, the cosine sample upper scale equals the selected
uniform scale bound. -/
theorem cosineSampleUpperScale_at_budget (βL βH γ τ ε η : ℝ) :
    cosineSampleUpperScale βL βH γ τ (ε * η / 8) =
      cosineSelectedBmax βL βH γ τ ε η := by
  unfold cosineSampleUpperScale cosineSelectedBmax cosineRelativeEnvelope
  ring

/-- For a positive semidefinite matrix and nonnegative time, every supported second-order
propagator has operator norm at most one. -/
theorem secondOrder_posSemidef_norm_le_one {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (A : Matrix I I ℂ) (hA : A.PosSemidef) (t : ℝ) (ht : 0 ≤ t) :
    ‖secondOrderPropagator kind A t‖ ≤ 1 := by
  cases kind
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.wavePropagator_posSemidef_norm_le_one A hA t
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.besselPropagator_posSemidef_norm_le_one A hA t
  · exact _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.airyPropagator_posSemidef_norm_le_one A hA t ht

/-- A positive lower bound `η` on the second-order output norm is at most twice the chosen
cosine coefficient mass under the stated matrix and accuracy assumptions. -/
theorem cosine_mass_ge_half_from_output {I : Type} [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (L H : Matrix I I ℂ) (hL : L.PosSemidef) (hH : H.PosDef)
    {γ t ε η : ℝ} (hγ : 0 < γ) (ht : 0 < t) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hη : 0 < η) (hγH : ‖H‖ ≤ γ) (ψ : QState I) (hψ : Normalized ψ)
    (houtput : η ≤ ‖stateVector (secondOrderPropagator kind (L + Complex.I • H) t *ᵥ ψ)‖) :
    η ≤ 2 * cosineChosenMass γ (secondOrderTimeScale kind t) ε η := by
  let τ := secondOrderTimeScale kind t
  let N := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ (ε * η / 8)
  let c := cosineCoefficients γ τ N
  let s := cosineScales γ τ N
  let V := ∑ j : Option (Fin N), c j • secondOrderPropagator kind (L + (s j : ℂ) • H) t
  have hτ := secondOrderTimeScale_pos kind ht
  have hsample (j : Option (Fin N)) : ‖secondOrderPropagator kind (L + (s j : ℂ) • H) t‖ ≤ 1 := by
    apply secondOrder_posSemidef_norm_le_one kind _ _ t ht.le
    have hh := hH.posSemidef.smul (cosineScales_nonneg hγ hτ N j)
    convert! hL.add hh using 1
  have hV : ‖V‖ ≤ cosineChosenMass γ τ ε η := by
    calc
      _ ≤ ∑ j, ‖c j • secondOrderPropagator kind (L + (s j : ℂ) • H) t‖ := norm_sum_le _ _
      _ ≤ ∑ j, ‖c j‖ := Finset.sum_le_sum fun j _ => by
        rw [norm_smul]
        simpa only [mul_one] using! mul_le_mul_of_nonneg_left (hsample j) (norm_nonneg _)
      _ = _ := cosineCoefficients_mass γ τ N
  have herr : ‖secondOrderPropagator kind (L + Complex.I • H) t - V‖ ≤ ε * η / 8 :=
    cosine_secondOrder_chosen_error kind L H hL hH hγ ht (by positivity) hγH
  have hop := stateVector_mulVec_norm_le (secondOrderPropagator kind (L + Complex.I • H) t) ψ
  rw [(normalized_iff_stateVector_norm ψ).mp hψ, mul_one] at hop
  have hh : ‖secondOrderPropagator kind (L + Complex.I • H) t‖ ≤
      ‖secondOrderPropagator kind (L + Complex.I • H) t - V‖ + ‖V‖ := by
    calc
      _ = ‖(secondOrderPropagator kind (L + Complex.I • H) t - V) + V‖ := by simp
      _ ≤ _ := norm_add_le _ _
  nlinarith

instance cosineAAOrder_neZero (γ τ ε η : ℝ) : NeZero (cosineAAOrder γ τ ε η) :=
  ⟨(cosineAAOrder_pos γ τ ε η).ne'⟩

/-- Records valid three-oracle amplification with success probability at least `1/8`, expected
and per-choice matrix and state query budgets, circuit semantics, and successful normalized
output accuracy up to phase. -/
def ThreeOracleOutputCertificate {W I : Type} [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] (target : Matrix I I ℂ)
    (O1 O2 B : Matrix W W ℂ) (cs : List (PreparedStep W)) (F : Matrix W I ℂ)
    (zero : W) (S : Finset W) (ψ : QState I) (ε : ℝ) (m : ℕ) [NeZero m]
    (matrixBudget stateBudget : ℝ) : Prop :=
  let A := evaluatePrepared O1 O2 cs * B
  PreparedCircuitValid cs ∧ ∃ hA : A ∈ Matrix.unitaryGroup W ℂ,
    ENNReal.ofReal (1/8 : ℝ) ≤
      Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.event (randomizedAAHerald A hA zero S m) (fun x => x.2 = true) ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (threeFirstQueries (threeAAWord cs zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
      ENNReal.ofReal matrixBudget ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (threeSecondQueries (threeAAWord cs zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
      ENNReal.ofReal matrixBudget ∧
    Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw.expectation (randomizedAAHerald A hA zero S m)
      (fun x => (threeStateQueries (threeAAWord cs zero S (aaRounds x.1)) : ℝ≥0∞)) ≤
      ENNReal.ofReal stateBudget ∧
    (∀ choice : Bool × Fin m,
      (threeFirstQueries (threeAAWord cs zero S (aaRounds choice)) : ℝ) ≤ 4 * matrixBudget ∧
      (threeSecondQueries (threeAAWord cs zero S (aaRounds choice)) : ℝ) ≤ 4 * matrixBudget ∧
      (threeStateQueries (threeAAWord cs zero S (aaRounds choice)) : ℝ) ≤ 4 * stateBudget) ∧
    (∀ k, ThreeCircuitValid (threeAAWord cs zero S k) ∧
      ApplyGate (evaluateThree O1 O2 B (threeAAWord cs zero S k)) (Ket zero) =
        Run (preparedMark S) (preparedAACircuit A zero k) (Ket zero)) ∧
    (∀ choice : Bool × Fin m,
      (choice, true) ∈ (randomizedAAHerald A hA zero S m).support →
      ∃ (y : QState I) (z : ℂ),
        ConditionalState (Fᴴ *ᵥ Run (preparedMark S)
          (preparedAACircuit A zero (aaRounds choice)) (Ket zero)) = some y ∧
        ‖z‖ = 1 ∧ Normalized y ∧ IsNormalizedApplication target ψ ((star z) • y) ε)

/-- Constructs uniform phase data yielding a three-oracle output certificate for the
second-order propagator, with the displayed matrix and state query budgets under the stated
exact encoding and output-norm assumptions [WangEtAl2026]. -/
theorem cosine_secondOrder_amplified
    {Anc I : Type} [Fintype Anc] [DecidableEq Anc] [Fintype I] [DecidableEq I]
    (kind : SecondOrderFamily) (a₀ : Anc) (t βL βH μL μH γ ε η : ℝ)
    (ht : 0 < t) (hβL : 0 < βL) (hβH : 0 < βH) (hμL : 0 < μL) (hμH : 0 < μH)
    (hγ : 0 < γ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    let τ := secondOrderTimeScale kind t
    let N := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ (ε * η / 8)
    let c := cosineCoefficients γ τ N
    let s := cosineScales γ τ N
    let κ := max (βL / μL) (βH / μH)
    let D := secondOrderDegreeBudget kind t (cosineSelectedBmax βL βH γ τ ε η) κ⁻¹
      (cosineWeightedAccuracy γ τ ε η)
    let m := cosineAAOrder γ τ ε η
    ∃ (base : Fin 4 → (Option (Fin N)) → ℂ) (zs : Fin 4 → List ((Option (Fin N)) → ℂ)),
      ∀ (L H : Matrix I I ℂ) (UL UH : Matrix (Anc × I) (Anc × I) ℂ),
      L.PosSemidef → H.PosDef → ‖H‖ ≤ γ →
      (L - μL • (1 : Matrix I I ℂ)).PosSemidef →
      (H - μH • (1 : Matrix I I ℂ)).PosSemidef →
      BlockEncoding L UL (tagFrame a₀ 1) (tagFrame a₀ 1) βL 0 →
      BlockEncoding H UH (tagFrame a₀ 1) (tagFrame a₀ 1) βH 0 →
      ∀ (B : Matrix I I ℂ), B ∈ Matrix.unitaryGroup I ℂ → ∀ (i₀ : I) (ψ : QState I),
      Normalized ψ → ApplyGate B (Ket i₀) = ψ →
      η ≤ ‖stateVector (secondOrderPropagator kind (L + Complex.I • H) t *ᵥ ψ)‖ →
      let cs := decodedSecondOrderWord c none (tagFrame a₀ (1 : Matrix I I ℂ)) D base zs βL βH s
      let O1 :
          Matrix (SecondOrderSpace (Option (Fin N)) (Anc × I))
          (SecondOrderSpace (Option (Fin N)) (Anc × I)) ℂ :=
          controlOracle
          (parallelOracle (J := PreparedPredicateLabels (Fin 4) (Option (Fin N)) Bool) UH)
      let O2 :
          Matrix (SecondOrderSpace (Option (Fin N)) (Anc × I))
          (SecondOrderSpace (Option (Fin N)) (Anc × I)) ℂ :=
          controlOracle
          (parallelOracle (J := PreparedPredicateLabels (Fin 4) (Option (Fin N)) Bool) UL)
      let B' :
          Matrix (SecondOrderSpace (Option (Fin N)) (Anc × I))
          (SecondOrderSpace (Option (Fin N)) (Anc × I)) ℂ :=
          secondOrderInputLift (J := (Option (Fin N))) (Anc := Anc) B
      let zero : SecondOrderSpace (Option (Fin N)) (Anc × I) :=
          (false,(((0,none),(false,false)),(a₀,i₀)))
      let S := secondOrderSuccessEvent (I := I) (none : (Option (Fin N))) a₀
      ThreeOracleOutputCertificate (secondOrderPropagator kind (L + Complex.I • H) t)
        O1 O2 B' cs (secondOrderDecodedFrame none (tagFrame a₀ (1 : Matrix I I ℂ)))
        zero S ψ ε m
        ((112 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2)) *
          (8 * cosineDisplayedDegreeBound βL βH γ τ ε η κ + 2))
        (112 * cosineRelativeEnvelope γ τ η * Real.log (2 + γ * τ ^ 2)) := by
  (try dsimp only)
  let τ := secondOrderTimeScale kind t
  let N := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount γ τ (ε * η / 8)
  let J := Option (Fin N)
  letI : Fintype J := inferInstanceAs (Fintype (Option (Fin N)))
  letI : DecidableEq J := inferInstanceAs (DecidableEq (Option (Fin N)))
  let κ := max (βL / μL) (βH / μH)
  let D := secondOrderDegreeBudget kind t (cosineSelectedBmax βL βH γ τ ε η) κ⁻¹
    (cosineWeightedAccuracy γ τ ε η)
  let c := cosineCoefficients γ τ N
  let s := cosineScales γ τ N
  let F := tagFrame a₀ (1 : Matrix I I ℂ)
  obtain ⟨base,zs,hb,hz,hl,ha⟩ := cosine_secondOrder_operator kind t βL βH μL μH γ ε η
    ht hβL hβH hμL hμH hγ hε hη
  rw [cosineSampleUpperScale_at_budget] at hl ha
  refine ⟨base, zs, ?_⟩
  intro L H UL UH hL hH hγH hLlow hHlow hUL hUH B hB i₀ ψ hψ hprepare houtput
  have hF : IsIsometry F := hUL.left_isometry
  obtain ⟨hw,he,_⟩ := ha (Anc × I) I L H UL UH F hL hH hγH hLlow hHlow hUL hUH
  let cs := decodedSecondOrderWord c none F D base zs βL βH s
  let O1 := controlOracle (parallelOracle (J := PreparedPredicateLabels (Fin 4) J Bool) UH)
  let O2 := controlOracle (parallelOracle (J := PreparedPredicateLabels (Fin 4) J Bool) UL)
  let B' := secondOrderInputLift (J := J) (Anc := Anc) B
  let zero : SecondOrderSpace J (Anc × I) := (false,(((0,none),(false,false)),(a₀,i₀)))
  let S := secondOrderSuccessEvent (I := I) (none : J) a₀
  let m := cosineAAOrder γ τ ε η
  have hw' : PreparedCircuitValid cs := decodedSecondOrderWord_valid c none F D base zs βL βH s hw
  have he' := decodedSecondOrderWord_blockEncoding c none F hF D base zs βL βH s O1 O2 _ _ _ he
  have hO1 : O1 ∈ Matrix.unitaryGroup _ ℂ :=
      controlOracle_unitary (parallelOracle_unitary hUH.unitary)
  have hO2 : O2 ∈ Matrix.unitaryGroup _ ℂ :=
      controlOracle_unitary (parallelOracle_unitary hUL.unitary)
  have hB' : B' ∈ Matrix.unitaryGroup _ ℂ := secondOrderInputLift_unitary B hB
  have hp : ApplyGate B' (Ket zero) = secondOrderDecodedFrame none F *ᵥ ψ :=
    secondOrderInputLift_prepare B none a₀ i₀ ψ hprepare
  have hproj : rangeProjector (secondOrderDecodedFrame none F) = Projector S :=
    secondOrderDecodedFrame_rangeProjector none a₀
  have herr : ε * η / 4 ≤ η / 2 := by nlinarith only [hε1, hη]
  have hwindow : 2 * (4 * cosineChosenMass γ τ ε η) / η ≤ (m : ℝ) := by
    convert! cosineAAOrder_threshold γ τ ε η using 1; ring
  have haa := three_oracle_blockEncoding_amplification _ O1 O2 B' cs hw' hO1 hO2 hB'
    _ _ (4 * cosineChosenMass γ τ ε η) (ε * η / 4) η he' zero S ψ hψ hp hproj
    hη houtput herr m hwindow
  have hcounts := decodedSecondOrderWord_cost c none F D base zs hl βL βH s
  have hηS := cosine_mass_ge_half_from_output kind L H hL hH hγ ht hε hε1 hη hγH ψ hψ houtput
  have hκ : 0 < κ := lt_of_lt_of_le (div_pos hβL hμL) (le_max_left _ _)
  have hbound := cosineExpectedSourceQueries_le kind hβL.le hβH.le hγ ht hε hε1 hη hκ hηS
  have hstate := cosineAAMeanMultiplicity_le hγ (secondOrderTimeScale_pos kind ht) hη hηS
  letI : Fintype (SecondOrderSpace J (Anc × I)) :=
    inferInstanceAs (Fintype (Bool × (((Fin 4 × J) × (Bool × Bool)) × (Anc × I))))
  letI : DecidableEq (SecondOrderSpace J (Anc × I)) :=
    inferInstanceAs (DecidableEq (Bool × (((Fin 4 × J) × (Bool × Bool)) × (Anc × I))))
  have hA : evaluatePrepared O1 O2 cs * B' ∈
      Matrix.unitaryGroup (SecondOrderSpace J (Anc × I)) ℂ :=
    (Matrix.unitaryGroup (SecondOrderSpace J (Anc × I)) ℂ).mul_mem
      (hw'.evaluate_unitary hO1 hO2) hB'
  refine ⟨hw',hA,
    haa.1, ?_, ?_, ?_, ?_, haa.2.2.2.2.1, ?_⟩
  · rw [haa.2.1, hcounts.1]
    exact ENNReal.ofReal_le_ofReal hbound
  · rw [haa.2.2.1, hcounts.2.1]
    exact ENNReal.ofReal_le_ofReal hbound
  · rw [haa.2.2.2.1]
    exact ENNReal.ofReal_le_ofReal hstate
  · intro choice
    apply threeAAWord_worst_case_from_mean cs zero S m _ _ _ _ hstate choice
    · rw [hcounts.1]
      exact hbound
    · rw [hcounts.2.1]
      exact hbound
  intro choice hsuc
  obtain ⟨y,z,hy,hz,hn,happ⟩ := haa.2.2.2.2.2 choice hsuc
  refine ⟨y,z,hy,hz,hn,happ.1,happ.2.1,happ.2.2.trans ?_⟩
  apply (div_le_iff₀ (hη.trans_le houtput)).mpr
  have hh := mul_le_mul_of_nonneg_left houtput hε.le
  nlinarith only [hh, mul_pos hε hη]

end CBMD

end
end Qatlib.Papers.Cbmd26.Algorithms
