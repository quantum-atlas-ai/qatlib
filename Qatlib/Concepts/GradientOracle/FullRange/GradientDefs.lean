/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GradientOracle.FullRange.FullRangeCharacterKickbackFast
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeFixedPointPrecisionFast
import Qatlib.Concepts.GradientOracle.FullRange.FullRangeGradientReadoutFast
import Qatlib.Concepts.GradientOracle.C2GradientAlg.NumericalGradientAlgorithmFast
import Qatlib.Concepts.GradientOracle.StationaryPhase.StationaryPhaseVarianceFast
import Qatlib.Concepts.GradientOracle.StepSizes.ClassicalQuantumStepSizesFast
import Qatlib.Concepts.GradientOracle.GradientAlgo.AlmostAffineGradientOpti
import Qatlib.Concepts.GradientOracle.GradientAlgo.AnalyticCentralDifferenceGridErrorOpti
import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceDirectionalErrorOpti
import Qatlib.Concepts.GradientOracle.DifferenceError.CentralDifferenceOneDimErrorOpti
import Qatlib.Concepts.GradientOracle.ReadoutTools.ExceptionalPhaseGradientTransportOpti
import Qatlib.Concepts.GradientOracle.ReadoutTools.PureStateEventLipschitzOpti
import Qatlib.Concepts.GradientOracle.GradientAlgo.GradientOracle
import Qatlib.Concepts.GateVocabulary.FiniteGateDescription
import Qatlib.Concepts.GradientOracle.ReadoutTools.AlmostAffineVectorMedianOpti

/-!
# Specifications of collected gradient guarantees

This module defines three conjunctions organizing full-range gradient correctness, analytic
error bounds, and implementation resources. The specifications connect the gradient setting of
[Jordan2005Gradient] to robust approximation and median amplification as in
[GilyenArunachalamWiebe2019].

## Main definitions

* `stageB_fourier_gradient_gext1_spec`: encoding, readout, variance, and step-size
  specifications.
* `stageB_fourier_gradient_gext2_spec`: almost-affine approximation and phase-transport
  specifications.
* `stageB_fourier_gradient_gext3_spec`: Fourier readout and implementation guarantees with
  median amplification and character kickback.

## References

* [Jordan, 2005][Jordan2005Gradient]
* [Gilyen, Arunachalam and Wiebe, 2019][GilyenArunachalamWiebe2019]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist

open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement Qatlib.Concepts.PhaseErrorBound.PhaseErrorSum
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralFilter.PhaseReadout
open Qatlib.Foundations.BornMetrics.EventProbability Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.ShadowModels.SampleBudget
open Qatlib.Concepts.GradientOracle.C2GradientAlg
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.GradientOracle.ReadoutTools
open Qatlib.Concepts.QftPreparation.LocalQFTImplementation

open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.GradientOracle.FullRange

open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.GradientOracle.StationaryPhase
open Qatlib.Concepts.GradientOracle.StepSizes
open Qatlib.Concepts.GradientOracle.CentralDiff
open Qatlib.Concepts.GradientOracle.DifferenceError
open Qatlib.Concepts.GradientOracle.GradientAlgo
open Qatlib
open Qatlib
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.GradientAlgo

/-- The conjunction of full-range encoding and readout, numerical gradient estimation,
stationary-phase variance, and classical/quantum step-size specifications. -/
def stageB_fourier_gradient_gext1_spec : Prop :=
  FullRangeCharacterKickback ∧
  FullRangeFixedPointPrecision ∧
  FullRangeGradientReadout ∧
  NumericalGradientAlgorithm ∧
  StationaryPhaseVariance ∧
  ClassicalQuantumStepSizes

/-- The conjunction of almost-affine gradient estimation, central-difference error
specifications, exceptional phase transport, pure-state event stability, and full-range
character kickback. -/
def stageB_fourier_gradient_gext2_spec : Prop :=
  SourceAlmostAffineGradient ∧
  AnalyticCentralDifferenceGridError ∧
  CentralDifferenceDirectionalError ∧
  CentralDifferenceOneDimError ∧
  ExceptionalPhaseGradientTransport ∧
  PureStateEventLipschitz ∧
  FullRangeCharacterKickback

/-- The conjunction collecting Fourier readout and implementation bounds, finite-code matrix
unitarity, vector-median amplification, and full-range character kickback. -/
def stageB_fourier_gradient_gext3_spec : Prop :=
  (
    (∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c : ℝ),
      gradientReadout d M hM (fun x => c + ∑ j : Fin d, g j * (x j).val) =
        Complex.exp (2 * Real.pi * Complex.I * (c : ℂ)) •
          gridProductState (fun j => qpeKernel M (g j))) ∧
    (∀ (d M : ℕ) (hM : 0 < M) (q : GradientGrid d M) (c : ℝ),
      gradientReadout d M hM
          (fun x => c + ∑ j : Fin d, (q j).val * (x j).val / (M : ℝ)) =
        Complex.exp (2 * Real.pi * Complex.I * (c : ℂ)) • Ket q) ∧
    ((∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w : ℝ),
        2 ≤ M → 0 < w →
          MeasureProb
              (gradientReadout d M hM (fun x => c + ∑ j : Fin d, g j * (x j).val))
              (Finset.univ.filter (fun z => ∀ j : Fin d,
                phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)) ≥
            1 - 16 * (d : ℝ) / ((M : ℝ) * w)) ∧
      (∀ (M : ℕ) (φ w : ℝ) (hM : 0 < M) (hw : 0 < w),
        (∑ y ∈ Finset.univ.filter (fun y : Fin M =>
          w < phaseDistance φ ((y.val : ℝ) / (M : ℝ))), ‖qpeKernel M φ y‖ ^ 2) ≤
          16 / ((M : ℝ) * w))) ∧
    ((∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q] (v : GradientGrid d M → ZMod Q)
        (S : Finset (GradientGrid d M)),
        MeasureProb
            (Run (gradientValueOracle Q v) (gradientValueWord d M Q)
              (fun xy => Ket (gradientZero d M hM) xy.1 * gradientKickState Q xy.2))
            (S ×ˢ Finset.univ) =
          MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) S) ∧
      (∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q] (v : GradientGrid d M → ZMod Q)
          (φ : GradientGrid d M → ℝ) (δ : ℝ) (S : Finset (GradientGrid d M)),
        0 ≤ δ →
          (∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ) →
            |MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) S -
              MeasureProb (gradientReadout d M hM φ) S| ≤ 4 * Real.pi * δ)) ∧
    (∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q] (w δ : ℝ) (g : Fin d → ℝ) (c : ℝ)
        (v : GradientGrid d M → ZMod Q),
      2 ≤ M → 0 < w → 0 ≤ δ →
        (∀ x, ∃ k : ℤ,
          |gradientValuePhase Q v x - (c + ∑ j : Fin d, g j * (x j).val) - k| ≤ δ) →
          MeasureProb (gradientReadout d M hM (gradientValuePhase Q v))
              (Finset.univ.filter (fun z => ∀ j : Fin d,
                phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w)) ≥
            1 - readoutErrorBudget d M w δ) ∧
    (∀ (d M : ℕ) (hM : 0 < M) (K k : ℕ),
      IsUnitaryCircuit (fullRangeGradientProgram d M K k) ∧
      QueryCount (fullRangeGradientProgram d M K k) = 1 ∧
      GateCount (fullRangeGradientProgram d M K k) = 2 * d + 1) ∧
    ((∀ (d M : ℕ) (hM : 0 < M) (K k : ℕ) (f : GradientGrid d M → ℝ) (lo s : ℝ),
        fullRangeGradientOutput d M hM K k f lo s =
          TensorState
            (gradientReadout d M hM (fullRangePhase K k (fullRangeValueTable K k f lo s)))
            (fullRangeKickState K k)) ∧
      (∀ (X : Type) (K k : ℕ) (f : X → ℝ) (lo s R : ℝ),
        0 < s → 0 ≤ R → s * R < 2 ^ K → (∀ x, lo ≤ f x ∧ f x ≤ lo + R) →
        ∀ x, |fullRangePhase K k (fullRangeValueTable K k f lo s) x - s * (f x - lo)| ≤
          1 / (2 : ℝ) ^ k) ∧
      (∀ (X : Type) (K k : ℕ) (f : X → ℝ) (lo s R : ℝ),
        0 < s → 0 ≤ R → s * R < 2 ^ K → (∀ x, lo ≤ f x ∧ f x ≤ lo + R) →
        ∀ x, 0 ≤ f x - dyadicDecode lo s K k (fullRangeValueTable K k f lo s x) ∧
          f x - dyadicDecode lo s K k (fullRangeValueTable K k f lo s x) <
            1 / (s * (2 : ℝ) ^ k)) ∧
      (∀ (X : Type) (K k : ℕ) (v : X → ZMod (2 ^ (K + k))) (x : X),
        HasDyadicRecord k (fullRangePhase K k v x)) ∧
      (∀ k : ℕ, ¬ HasDyadicRecord k (1 / 3))) ∧
    ((∀ (d M r : ℕ) (ω : Fin (2 * r + 1) → GradientGrid d M),
        medianComparisonCount d M r ω ≤ d * 10000 * (2 * r + 1)) ∧
      AlmostAffineVectorMedian) ∧
    (∀ (d M r : ℕ) (ω : Fin (2 * r + 1) → GradientGrid d M) (j : Fin d),
      gradientMedianCounted r ω j =
        qSelect (List.ofFn fun t => gradientSignedValueQ M (ω t j)) r) ∧
    (∀ (K k : ℕ) (v : ZMod (2 ^ (K + k))) (lo s : ℝ),
      dyadicDecode lo s K k v = lo + (v.val : ℝ) / (s * (2 : ℝ) ^ k)) ∧
    (∀ n : ℕ,
      GateCount (localProgramCircuit (localQFT n)) = n + n * (n - 1) / 2 + n / 2 ∧
      QueryCount (localProgramCircuit (localQFT n)) = 0) ∧
    (∀ n b : ℕ,
      GateCount (localProgramCircuit (approxLocalQFT n b)) ≤ n + n * (b + 1) + n / 2) ∧
    (∀ (n b : ℕ) (ψ : QState (Reg n)) (S : Finset (Reg n)),
      Normalized ψ →
      |MeasureProb (Run 1 (localProgramCircuit (approxLocalQFT n b)) ψ) S -
          MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))) ψ) S| ≤
        Real.pi * (n : ℝ) / (2 : ℝ) ^ b ∧
      |MeasureProb (Run 1 (localProgramCircuit (localProgramAdjoint (approxLocalQFT n b))) ψ) S -
          MeasureProb (ApplyGate (relabelGate (bitVecEquiv n).symm (QFTMatrix (2 ^ n))).conjTranspose ψ) S| ≤
        Real.pi * (n : ℝ) / (2 : ℝ) ^ b) ∧
    (∀ (d M K k : ℕ),
      readoutIntegerBits K k = K + k ∧
      readoutSpaceBits d M K k = d * Nat.clog 2 (max 2 M) + K + k)
  ) ∧
  (∀ (n : ℕ) (g : FiniteGateCode), finiteCodeLegal n g = true → finiteCodeMatrix n g ∈ Matrix.unitaryGroup (Reg n) ℂ) ∧
  AlmostAffineVectorMedian ∧
  FullRangeCharacterKickback

end Qatlib.Concepts.GradientOracle.FullRange
