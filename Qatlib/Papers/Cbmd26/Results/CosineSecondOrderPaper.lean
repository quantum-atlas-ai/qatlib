/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.Cbmd26.Algorithms.ThreeOracleCombinedCost
import Qatlib.Papers.Cbmd26.Algorithms.SecondOrderPaperNormalization
import Qatlib.Papers.Cbmd26.Algorithms.CosineConditionNumberBudget
import Qatlib.Papers.Cbmd26.Algorithms.SecondOrderZeroTime

/-!
# Paper statements for second-order preparation

`SecondOrderPaperStatement` packages uniform phase choices and a three-oracle output certificate
for the wave, Bessel, and Airy families. The query budgets use the paper output norm and the
true condition estimates, with factors recording the supplied spectral and output estimates in
[WangEtAl2026].

## Main statements

* `secondOrder_paper_theorem`: proves the shared statement for every family.
* `theorem5_wave`, `theorem6_bessel`, and `theorem7_airy`: specialize it to the three paper
  propagators.

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

open Qatlib.Papers.Cbmd26.Algorithms.CBMD

namespace Qatlib.Papers.Cbmd26.Results

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace CBMD
open Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- The uniform second-order preparation specification requiring common phase data and a
three-oracle output certificate for positive-definite matrix parts with exact separate
encodings and fixed-factor spectral and output estimates. Its matrix and state budgets are
expressed using the paper output norm and true condition maximum. -/
def SecondOrderPaperStatement {Anc I : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (kind : SecondOrderFamily) (a₀ : Anc) (t βL βH μL μH ε η cout cκ : ℝ) : Prop :=
  let τ := secondOrderTimeScale kind t
  let N := _root_.Qatlib.Foundations.CbmdAnalysis.Core.CBMD.cosineRetainedCount βH τ (ε * η / 8)
  let c := cosineCoefficients βH τ N
  let s := cosineScales βH τ N
  let κ := max (βL / μL) (βH / μH)
  let D := secondOrderDegreeBudget kind t (cosineSelectedBmax βL βH βH τ ε η) κ⁻¹
    (cosineWeightedAccuracy βH τ ε η)
  let m := cosineAAOrder βH τ ε η
  let cR := secondOrderOutputEstimateFactor kind cout
  ∃ (base : Fin 4 → Option (Fin N) → ℂ) (zs : Fin 4 → List (Option (Fin N) → ℂ)),
    ∀ (L H : Matrix I I ℂ) (hL : L.PosDef) (hH : H.PosDef)
      (UL UH : Matrix (Anc × I) (Anc × I) ℂ),
    ‖L‖ = βL → ‖H‖ = βH →
    (L - μL • (1 : Matrix I I ℂ)).PosSemidef →
    (H - μH • (1 : Matrix I I ℂ)).PosSemidef →
    matrixLeastEigenvalue hL.isHermitian ≤ cκ * μL →
    matrixLeastEigenvalue hH.isHermitian ≤ cκ * μH →
    BlockEncoding L UL (tagFrame a₀ 1) (tagFrame a₀ 1) βL 0 →
    BlockEncoding H UH (tagFrame a₀ 1) (tagFrame a₀ 1) βH 0 →
    ∀ (B : Matrix I I ℂ), B ∈ Matrix.unitaryGroup I ℂ → ∀ (i₀ : I) (ψ : QState I),
    Normalized ψ → ApplyGate B (Ket i₀) = ψ →
    η ≤ ‖stateVector (secondOrderPropagator kind (L + Complex.I • H) t *ᵥ ψ)‖ →
    ‖stateVector (secondOrderPropagator kind (L + Complex.I • H) t *ᵥ ψ)‖ ≤ cout * η →
    let ν := secondOrderPaperOutputNorm kind (L + Complex.I • H) t ψ
    let κtrue := matrixTrueConditionMax hL.isHermitian hH.isHermitian
    let cs := decodedSecondOrderWord c none (tagFrame a₀ (1 : Matrix I I ℂ)) D base zs βL βH s
    let O1 :=
        controlOracle
        (parallelOracle (J := PreparedPredicateLabels (Fin 4) (Option (Fin N)) Bool) UH)
    let O2 :=
        controlOracle
        (parallelOracle (J := PreparedPredicateLabels (Fin 4) (Option (Fin N)) Bool) UL)
    let B' := secondOrderInputLift (J := Option (Fin N)) (Anc := Anc) B
    let zero : SecondOrderSpace (Option (Fin N)) (Anc × I) :=
        (false,(((0,none),(false,false)),(a₀,i₀)))
    let S := secondOrderSuccessEvent (I := I) (none : Option (Fin N)) a₀
    ThreeOracleOutputCertificate (secondOrderPropagator kind (L + Complex.I • H) t)
      O1 O2 B' cs (secondOrderDecodedFrame none (tagFrame a₀ (1 : Matrix I I ℂ))) zero S ψ ε m
      ((cκ * (cR * cosineOutputDegreeFactor cR)) *
        ((112 * cosineRelativeEnvelope βH τ ν * Real.log (2 + βH * τ ^ 2)) *
          (8 * cosineDisplayedDegreeBound βL βH βH τ ε ν κtrue + 2)))
      (cR * (112 * cosineRelativeEnvelope βH τ ν * Real.log (2 + βH * τ ^ 2)))

/-- For positive time, scales, spectral lower estimates, and output lower estimate, with `0 < ε
< 1/2` and estimate factors at least one, every family satisfies `SecondOrderPaperStatement`
as used in [WangEtAl2026]. -/
theorem secondOrder_paper_theorem {Anc I : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (kind : SecondOrderFamily) (a₀ : Anc) (t βL βH μL μH ε η cout cκ : ℝ)
    (ht : 0 < t) (hβL : 0 < βL) (hβH : 0 < βH) (hμL : 0 < μL) (hμH : 0 < μH)
    (hε : 0 < ε) (hε1 : ε < 1 / 2) (hη : 0 < η) (_hout : 1 ≤ cout) (hcκ : 1 ≤ cκ) :
    SecondOrderPaperStatement (I := I) kind a₀ t βL βH μL μH ε η cout cκ := by
  obtain ⟨base,zs,ha⟩ := cosine_secondOrder_amplified (I := I) kind a₀ t βL βH μL μH βH ε η
    ht hβL hβH hμL hμH hβH hε (by linarith only [hε1]) hη
  refine ⟨base,zs,?_⟩
  intro L H hL hH UL UH hLn hHn hLlow hHlow hMinL hMinH hUL hUH B hB i₀ ψ hψ hprep hlo hup
  have hcert := ha L H UL UH hL.posSemidef hH (le_of_eq hHn) hLlow hHlow hUL hUH
    B hB i₀ ψ hψ hprep hlo
  let τ := secondOrderTimeScale kind t
  let ν := secondOrderPaperOutputNorm kind (L + Complex.I • H) t ψ
  let κ := max (βL / μL) (βH / μH)
  let cR := secondOrderOutputEstimateFactor kind cout
  have hτ : 0 ≤ τ := secondOrderTimeScale_nonneg kind ht.le
  have hν : 0 < ν := secondOrderPaperOutputNorm_pos kind _ t ψ hη hlo
  have hcR : 1 ≤ cR := secondOrderOutputEstimateFactor_ge_one kind cout
  have hcR0 : 0 ≤ cR := zero_le_one.trans hcR
  have hκ : 0 ≤ κ := (div_pos hβL hμL).le.trans (le_max_left _ _)
  have hR := secondOrderPaperRatio_compare kind _ t ψ βH τ η cout hη hlo hup
  have hcond := (matrix_condition_estimate hL.isHermitian hH.isHermitian hμL hμH
    hLlow hHlow hMinL hMinH hcκ).2
  rw [hLn,hHn] at hcond
  have hb1 := cosineDisplayedSourceBound_ratio_compare hβL.le hβH.le hβH.le hτ hε hη hν hκ hcR hR
  have hb2 := cosineDisplayedSourceBound_condition_compare hβL.le hβH.le hβH.le hτ hε hν hcκ hcond
  have hf : 0 ≤ cR * cosineOutputDegreeFactor cR :=
    mul_nonneg hcR0 (zero_le_one.trans (cosineOutputDegreeFactor_ge_one hcR))
  have hbudget := hb1.trans (mul_le_mul_of_nonneg_left hb2 hf)
  have hbudget' : (112 * cosineRelativeEnvelope βH τ η * Real.log (2 + βH * τ ^ 2)) *
      (8 * cosineDisplayedDegreeBound βL βH βH τ ε η κ + 2) ≤
      (cκ * (cR * cosineOutputDegreeFactor cR)) *
        ((112 * cosineRelativeEnvelope βH τ ν * Real.log (2 + βH * τ ^ 2)) *
          (8 * cosineDisplayedDegreeBound βL βH βH τ ε ν
            (matrixTrueConditionMax hL.isHermitian hH.isHermitian) + 2)) := by
    convert! hbudget using 1; ring
  have hlog : 0 ≤ Real.log (2 + βH * τ ^ 2) := by
    apply Real.log_nonneg
    have hterm := mul_nonneg hβH.le (sq_nonneg τ)
    linarith only [hterm]
  have hs := mul_le_mul_of_nonneg_right hR (mul_nonneg (by norm_num : (0 : ℝ) ≤ 112) hlog)
  have hs' : 112 * cosineRelativeEnvelope βH τ η * Real.log (2 + βH * τ ^ 2) ≤
      cR * (112 * cosineRelativeEnvelope βH τ ν * Real.log (2 + βH * τ ^ 2)) := by
    convert! hs using 1 <;> ring
  exact hcert.mono hbudget' hs'

/-- The wave family satisfies `SecondOrderPaperStatement` under the stated positive parameter,
error, and estimate-factor hypotheses, providing the preparation certificate for [Wang et
al., Theorem 5][WangEtAl2026]. -/
theorem theorem5_wave {Anc I : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (a₀ : Anc) (t βL βH μL μH ε η cout cκ : ℝ)
    (ht : 0 < t) (hβL : 0 < βL) (hβH : 0 < βH) (hμL : 0 < μL) (hμH : 0 < μH)
    (hε : 0 < ε) (hε1 : ε < 1 / 2) (hη : 0 < η) (hout : 1 ≤ cout) (hcκ : 1 ≤ cκ) :
    SecondOrderPaperStatement (I := I) .wave a₀ t βL βH μL μH ε η cout cκ :=
  secondOrder_paper_theorem .wave a₀ t βL βH μL μH ε η cout cκ ht hβL hβH hμL hμH hε hε1 hη hout hcκ

/-- The Bessel family satisfies `SecondOrderPaperStatement` under the stated positive parameter,
error, and estimate-factor hypotheses, providing the preparation certificate for [Wang et
al., Theorem 6][WangEtAl2026]. -/
theorem theorem6_bessel {Anc I : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (a₀ : Anc) (t βL βH μL μH ε η cout cκ : ℝ)
    (ht : 0 < t) (hβL : 0 < βL) (hβH : 0 < βH) (hμL : 0 < μL) (hμH : 0 < μH)
    (hε : 0 < ε) (hε1 : ε < 1 / 2) (hη : 0 < η) (hout : 1 ≤ cout) (hcκ : 1 ≤ cκ) :
    SecondOrderPaperStatement (I := I) .bessel a₀ t βL βH μL μH ε η cout cκ :=
  secondOrder_paper_theorem .bessel a₀ t βL βH μL μH ε η cout cκ ht hβL hβH hμL hμH hε hε1 hη hout hcκ

/-- The Airy family satisfies `SecondOrderPaperStatement` under the stated positive parameter,
error, and estimate-factor hypotheses, providing the preparation certificate for [Wang et
al., Theorem 7][WangEtAl2026]. -/
theorem theorem7_airy {Anc I : Type} [Fintype Anc] [DecidableEq Anc]
    [Fintype I] [DecidableEq I] [Nonempty I]
    (a₀ : Anc) (t βL βH μL μH ε η cout cκ : ℝ)
    (ht : 0 < t) (hβL : 0 < βL) (hβH : 0 < βH) (hμL : 0 < μL) (hμH : 0 < μH)
    (hε : 0 < ε) (hε1 : ε < 1 / 2) (hη : 0 < η) (hout : 1 ≤ cout) (hcκ : 1 ≤ cκ) :
    SecondOrderPaperStatement (I := I) .airy a₀ t βL βH μL μH ε η cout cκ :=
  secondOrder_paper_theorem .airy a₀ t βL βH μL μH ε η cout cκ ht hβL hβH hμL hμH hε hε1 hη hout hcκ

end CBMD

end
end Qatlib.Papers.Cbmd26.Results
