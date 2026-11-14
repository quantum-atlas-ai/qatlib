/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord
public import Qatlib.Concepts.CoherentSim.CoherentOAA.Amplification
public import Qatlib.Concepts.CoherentSim.CoherentOAA.BlockRobustness
public import Qatlib.Concepts.CoherentSim.CoherentOAA.CoherentSimulationDefs
public import Qatlib.Concepts.CoherentSim.CoherentOAA.ObliviousAmplification
public import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
public import Qatlib.Foundations.OperatorErrors.OperatorError
public import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse
public import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
public import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
public import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
public import Qatlib.Concepts.CoherentSim.CoherentOAA.Qubitization
public import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
public import Qatlib.Concepts.CoherentSim.CoherentOAA.Realization
public import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation
public import Qatlib.Concepts.CoherentSim.CoherentOAA.ScaleEightCoherentAmplification
public import Qatlib.Concepts.CoherentSim.CoherentOAA.SingularPolynomial
public import Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower
public import Qatlib.Concepts.MbqcFlow.FlowDecision.BiasedPauliShadowConsumers
public import Qatlib.Concepts.MbqcFlow.FlowDecision.CertifiedPilotCore
public import Qatlib.Concepts.MbqcFlow.FlowDecision.CoarseAcceptance
public import Qatlib.Concepts.MbqcFlow.FlowDecision.DegenerateEnergyInstrument
public import Qatlib.Concepts.MbqcFlow.FlowDecision.DiagonalTraceDistance
public import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccess
public import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessExt
public import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessRefined
public import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveNumericPrepareChain
public import Qatlib.Concepts.MbqcFlow.FlowDecision.EnergyReadoutConsumers
public import Qatlib.Concepts.MbqcFlow.FlowDecision.EnsembleUStatisticHigherMoments
public import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess
public import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatistics
public import Qatlib.Concepts.MbqcFlow.FlowDecision.StoppingReference
public import Qatlib.Concepts.MbqcFlow.FlowDecision.GramSquareRootBound
public import Qatlib.Concepts.MbqcFlow.FlowDecision.IsingClusterResource
public import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetwork
public import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkBranch
public import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkCore
public import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkInstrument
public import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkRouting
public import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkTransport
public import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalShadowConfidenceConsumers
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlow
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowClause2
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowExt
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCore
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCounterexamples
public import Qatlib.Concepts.MbqcFlow.FlowDecision.FlowExtended
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowPreentangled
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatistics
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatisticsDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCC
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNative
public import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNativeDefs
public import Qatlib.Foundations.PureStateMath.MixedState
public import Qatlib.Concepts.MbqcFlow.FlowDecision.NoisyHadamardMixture
public import Qatlib.Concepts.MbqcFlow.FlowDecision.PauliShadowConsumers
public import Qatlib.Concepts.MbqcFlow.FlowDecision.Physlib
public import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurement
public import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurementData
public import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurementFrame
public import Qatlib.Concepts.MbqcFlow.FlowDecision.ProposalUnitary
public import Qatlib.Concepts.MbqcFlow.FlowDecision.PureEnsemblePGM
public import Qatlib.Concepts.MbqcFlow.FlowDecision.PureStateOverlap
public import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional
public import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditionalDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.PurificationProduct
public import Qatlib.Concepts.MbqcFlow.FlowDecision.QuadraticObservableConsumers
public import Qatlib.Concepts.MbqcFlow.FlowDecision.QuadraticTraceDistance
public import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsRefinedDefs
public import Qatlib.Foundations.PureStateMath.Qubit
public import Qatlib.Concepts.MbqcFlow.FlowDecision.RectangularSchattenHolder
public import Qatlib.Concepts.MbqcFlow.FlowDecision.SchattenDiamond
public import Qatlib.Concepts.MbqcFlow.FlowDecision.SchattenDiamondDefs
public import Qatlib.Concepts.MbqcFlow.FlowDecision.SparseAccessProgram
public import Qatlib.Foundations.PureStateMath.Tensor
public import Qatlib.Concepts.MbqcFlow.FlowDecision.TensorShadowConsumers
public import Qatlib.Concepts.MbqcFlow.FlowDecision.TetrahedralShadowConsumers
public import Qatlib.Concepts.MbqcFlow.FlowDecision.TetrahedralShadowInstrument
public import Qatlib.Concepts.MbqcFlow.FlowDecision.TetrahedralShadowStatistics
public import Qatlib.Concepts.SignalPrimitive.GridGradient.GradientSourceContinuationDefs
public import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic
public import Qatlib.Concepts.SignalPrimitive.GridGradient.GridGradientConsumers
public import Qatlib.Foundations.QueryWordCore.Circuit
public import Qatlib.Concepts.ReferenceError.MixturePaths
public import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
public import Qatlib.Concepts.HspRecovery.Reduction.ReductionDefs
public import Qatlib.Concepts.HspRecovery.Reduction.AlgebraicRecovery
public import Qatlib.Concepts.HspRecovery.Reduction.AlgebraicRecoveryDefs
public import Qatlib.Concepts.HspRecovery.Reduction.AlgebraicRecoveryRefinedDefs
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardFourierBridge
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardSampling
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardSamplingEvent
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanQuotientRecovery
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryHitting
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryRank
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryTail
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanSimonRecovery
public import Qatlib.Concepts.HspRecovery.Reduction.BooleanSimonSampling
public import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecovery
public import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecoveryDefs
public import Qatlib.Concepts.HspRecovery.Reduction.CountedSimonDecoder
public import Qatlib.Concepts.HspRecovery.Reduction.CyclicRecoveryConsumers
public import Qatlib.Concepts.HspRecovery.Reduction.DistinctFourierNoiseConsumers
public import Qatlib.Concepts.HspRecovery.Reduction.FourierEffectiveRecovery
public import Qatlib.Concepts.HspRecovery.Reduction.FourierEffectiveRecoveryDefs
public import Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
public import Qatlib.Concepts.HspRecovery.Reduction.GradientOracleDefs
public import Qatlib.Concepts.HspRecovery.Reduction.KnownQubitPhaseReadout
public import Qatlib.Concepts.HspRecovery.Reduction.ModularReversibleWord
public import Qatlib.Concepts.HspRecovery.Reduction.NativeEndpoint
public import Qatlib.Concepts.HspRecovery.Reduction.PairLCMFactorConsumers
public import Qatlib.Concepts.HspRecovery.Reduction.PhaseReadoutSynthesisDefs
public import Qatlib.Concepts.HspRecovery.Reduction.PowerTwoSlopeProgram
public import Qatlib.Concepts.HspRecovery.Reduction.RandomBaseFactorConsumers
public import Qatlib.Concepts.HspRecovery.Reduction.ReversibleBandClassifier
public import Qatlib.Concepts.HspRecovery.Reduction.SmithWholePivotRun
public import Qatlib.Concepts.HspRecovery.Reduction.DescentQueryGrowthDihe
public import Qatlib.Concepts.HspRecovery.Reduction.DescentQueryGrowthStat
public import Qatlib.Concepts.HspRecovery.Reduction.OracleReductionsDihe
public import Qatlib.Concepts.HspRecovery.Reduction.OracleReductionsStat
public import Qatlib.Concepts.HspRecovery.Reduction.OracleTwirling
public import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentDihe
public import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentStat
public import Qatlib.Concepts.HspRecovery.Reduction.Reductions
public import Qatlib.Concepts.HspRecovery.Reduction.TwirlingCounterexample
public import Qatlib.Concepts.GradientOracle.ValueKickback
public import Qatlib.Concepts.QspSimulation.Achievability.AchievableNecessitySourceFormLowc
public import Qatlib.Concepts.QspSimulation.Achievability.AchievableNecessitySourceFormStat
public import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
public import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedStat
public import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
public import Qatlib.Concepts.QspSimulation.Achievability.CleanSignalSimulation
public import Qatlib.Concepts.QspSimulation.Achievability.ComputedSignalConsumers
public import Qatlib.Concepts.QspSimulation.Achievability.CountedHamiltonian
public import Qatlib.Concepts.QspSimulation.Achievability.ExponentialPolynomial
public import Qatlib.Concepts.QspSimulation.Achievability.Compilation
public import Qatlib.Concepts.QspSimulation.Achievability.HamiltonianSimulation
public import Qatlib.Concepts.QspSimulation.Achievability.SimQsp
public import Qatlib.Concepts.QspSimulation.Achievability.SimQspDefs
public import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxContractObstructions
public import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxEndpointNormalization
public import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxReal
public import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
public import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceWord
public import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSufficiencyObstruction
public import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxTransfer
public import Qatlib.Concepts.QspSimulation.Achievability.LcuQsvt
public import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation
public import Qatlib.Concepts.QspSimulation.Achievability.OraclePerturbation
public import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedLowc
public import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedStat
public import Qatlib.Concepts.QspSimulation.Achievability.QspSimulationDefs
public import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
public import Qatlib.Concepts.QspSimulation.Achievability.RealPartResponse
public import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
public import Qatlib.Concepts.QspSimulation.Achievability.ResponseFactorization
public import Qatlib.Concepts.QspSimulation.Achievability.SimQspRefined
public import Qatlib.Concepts.QspSimulation.Achievability.TrigApproximation
public import Qatlib.Concepts.QspSimulation.JacobiAnger.ComputedSignalSimulation
public import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
public import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeStat
public import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncationLowc
public import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncationStat
public import Qatlib.Concepts.QspSimulation.JacobiAnger.SimQspDefs
public import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
public import Qatlib.Concepts.CopyEvolution.Discriminate.ConditionalOutput
public import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution
public import Qatlib.Concepts.CopyEvolution.Discriminate.CopyEvolutionConsumer
public import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
public import Qatlib.Concepts.CopyEvolution.Discriminate.DiamondMeasurementSuccessHelstrom
public import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationQuan
public import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationStat
public import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteTwoSpeciesSignReadoutQuan
public import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteTwoSpeciesSignReadoutStat
public import Qatlib.Concepts.BlockEncoding.LCU
public import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
public import Qatlib.Concepts.CopyEvolution.Discriminate.PartialSwapEvolution
public import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
public import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
public import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
public import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
public import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesCopyPhaseReadout
public import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesSpectralReadoutQuan
public import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesSpectralReadoutStat
public import Qatlib.Concepts.CopyEvolution.Discriminate.TrainingSetFiniteDiscriminationQuan
public import Qatlib.Concepts.CopyEvolution.Discriminate.TrainingSetFiniteDiscriminationStat
public import Qatlib.Concepts.CopyEvolution.Discriminate.TwoSpeciesCopyExponential
public import Qatlib.Concepts.CopyEvolution.Discriminate.TwoSpeciesDiscriminationSubgoalQuan
public import Qatlib.Concepts.CopyEvolution.Discriminate.TwoSpeciesDiscriminationSubgoalStat
public import Qatlib.Concepts.CopyEvolution.Discriminate.UnitaryExponentialRemainder
public import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation

@[expose] public section

/-!
# Oracle phase conventions and readout specifications

This module defines the diagonal probability phase operator, converts its radian phase to the
Fourier gradient convention, and defines the signed `readoutDecoder`. These interfaces support
numerical gradient estimation in the setting of [Jordan2005Gradient].

The two specification propositions package value kickback semantics, probability phase
implementation and perturbation bounds, and actual Fourier readout guarantees, including
accuracy, dyadic outputs, and resource counts.

## Main statements

* `probabilityPhaseOperator`: diagonal coefficients `exp (i * p x)`.
* `probabilityReadoutPhase`: division by `2 * π` for the gradient phase convention.
* `stageB_gradient_oracle_clause2_spec` and `stageB_gradient_oracle_clause8_spec`: oracle and
  readout contracts.

## References

* [Jordan, 2005][Jordan2005Gradient]
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.MbqcFlow.FlowDecision Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.SignalPrimitive.GridGradient
open Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
open Qatlib.Concepts.GradientOracle.ValueKickback
open Qatlib.Concepts.QspSimulation.Achievability
open Qatlib.Concepts.QspSimulation.JacobiAnger
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SignalPrimitive.GridGradient

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexConjugate

/-- The diagonal operator with coefficient `exp (i * p x)` at each basis label. -/
noncomputable def probabilityPhaseOperator {X : Type} [Fintype X] [DecidableEq X]
    (p : X → ℝ) : Matrix X X ℂ :=
  Matrix.diagonal (fun x => Complex.exp (Complex.I * (p x : ℂ)))

/-- Converts a phase measured in radians to the gradient phase convention by division by `2 *
π`. -/
noncomputable def probabilityReadoutPhase {X : Type} (p : X → ℝ) : X → ℝ :=
  fun x => p x / (2 * Real.pi)

/-- Decodes each Fourier grid coordinate using its signed grid value. -/
noncomputable def readoutDecoder {d M : ℕ} (z : GradientGrid d M) : Fin d → ℝ :=
  fun j => signedGridValue M (z j)

/-- The specification combining value kickback semantics and costs, phase perturbation bounds,
probability phase semantics, and framed probability phase implementation. -/
def stageB_gradient_oracle_clause2_spec : Prop :=
  (∀ (d M Q : ℕ) [NeZero Q] (v : GradientGrid d M → ZMod Q) (x : GradientGrid d M),
      (evaluate (gradientValueOracle Q v) (valueComputeKickbackUncomputeWord d M Q)) *ᵥ
          (Qatlib.Foundations.PureStateMath.Ket (x, (0 : ZMod Q))) =
        valuePhaseCoeff Q (v x) • Qatlib.Foundations.PureStateMath.Ket (x, (0 : ZMod Q))) ∧
  (∀ (d M Q : ℕ) (hM : 0 < M) [NeZero Q],
      WellFormedAdjointCircuit (valueComputeKickbackUncomputeWord d M Q) ∧
      adjointQueryCount (valueComputeKickbackUncomputeWord d M Q) = 2 ∧
      adjointGateCount (valueComputeKickbackUncomputeWord d M Q) = 1 ∧
      QueryCount (gradientValueWord d M Q) = 1) ∧
  (∀ (d M Q : ℕ) [NeZero Q] (v : GradientGrid d M → ZMod Q)
      (φ : GradientGrid d M → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
      (herror : ∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ),
      ‖gradientPhase d M (gradientValuePhase Q v) - gradientPhase d M φ‖ ≤ 2 * Real.pi * δ) ∧
  (∀ (d M Q : ℕ) [NeZero Q] (hM : 0 < M)
      (v : GradientGrid d M → ZMod Q) (φ : GradientGrid d M → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
      (herror : ∀ x, ∃ k : ℤ, |gradientValuePhase Q v x - φ x - k| ≤ δ)
      (S : Finset (GradientGrid d M)),
      |MeasureProb (gradientReadout d M hM (gradientValuePhase Q v)) S -
        MeasureProb (gradientReadout d M hM φ) S| ≤ 4 * Real.pi * δ) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] (p : X → ℝ),
      probabilityPhaseOperator p ∈ Matrix.unitaryGroup X ℂ) ∧
  (∀ (d M : ℕ) (p : GradientGrid d M → ℝ),
      probabilityPhaseOperator p = gradientPhase d M (probabilityReadoutPhase p)) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (p : GradientGrid d M → ℝ),
      gradientReadout d M hM (probabilityReadoutPhase p) =
        Run (probabilityPhaseOperator p) (gradientWord d M) (Ket (gradientZero d M hM))) ∧
  (∀ (X A : Type) [Fintype X] [Fintype A] [DecidableEq X] [DecidableEq A]
      (U : Matrix (X × A) (X × A) ℂ) (hU : U ∈ Matrix.unitaryGroup (X × A) ℂ)
      (a₀ : A) (good : Finset A)
      (hlabel : ∀ (x y : X) (a : A), x ≠ y → U (x,a) (y,a₀) = 0) (k : ℕ),
      WellFormedAdjointCircuit (probabilityPhaseWord (X := X) a₀ good k) ∧
        adjointQueryCount (probabilityPhaseWord (X := X) a₀ good k)
          = 54 * (4 * computedSignalCutoff (1/2) k + 1) ∧
        adjointGateCount (probabilityPhaseWord (X := X) a₀ good k)
          = 1 + (27 * (4 * computedSignalCutoff (1/2) k + 6) + 79)
            + 27 * (4 * computedSignalCutoff (1/2) k + 1) ∧
        ∀ ψ : QState X,
          ‖toEuclidean_fromVec
              (evaluate (probabilityPrimitiveOracle U) (probabilityPhaseWord (X := X) a₀ good k) *ᵥ
                  (scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀)) *ᵥ ψ) -
                scaleEightFrame (hamiltonianFrame (cleanFrame (X := X) a₀)) *ᵥ
                  (probabilityPhaseOperator (probabilityMass U a₀ good) *ᵥ ψ))‖
            ≤ (1/2 : ℝ)^k * ‖toEuclidean_fromVec ψ‖)

/-- The specification combining the actual Fourier readout word, signed decoding accuracy, joint
success probability, dyadic outputs, a zero precision obstruction, and bit and circuit
ledgers. -/
def stageB_gradient_oracle_clause8_spec : Prop :=
  (∀ (d M : ℕ) (hM : 0 < M) (φ : GradientGrid d M → ℝ),
      gradientReadout d M hM φ =
        Run (gradientPhase d M φ) (gradientWord d M) (Ket (gradientZero d M hM))) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (w : ℝ)
      (hg : ∀ j : Fin d, |g j| ≤ 1 / 4) (hw : w ≤ 1 / 8)
      (z : GradientGrid d M)
      (hgood : ∀ j : Fin d, phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w),
      ∀ j : Fin d, |readoutDecoder z j - g j| ≤ w) ∧
  (∀ (d M : ℕ) (hM : 0 < M) (g : Fin d → ℝ) (c w B : ℝ) (φ : GradientGrid d M → ℝ)
      (hM2 : 2 ≤ M) (hw : 0 < w) (hB : 0 ≤ B)
      (herror : ∀ x, |φ x - (c + ∑ j : Fin d, g j * (x j).val)| ≤ B),
      MeasureProb (gradientReadout d M hM φ)
        (Finset.univ.filter (fun z => ∀ j : Fin d,
          phaseDistance ((z j).val / (M : ℝ)) (g j) ≤ w))
        ≥ 1 - 16 * (d : ℝ) / ((M : ℝ) * w) - 4 * Real.pi * B) ∧
  (∀ (m : ℕ) (z : Fin (2 ^ m)),
      ∃ n : ℤ, readoutDecoder (d := 1) (fun _ => z) 0 = (n : ℝ) / (2 : ℝ) ^ m) ∧
  (¬ GeneralRealRecord 0 (1 / 3)) ∧
  (∀ (d M K k : ℕ) (hM : 0 < M),
      readoutIntegerBits K k = K + k ∧
        readoutSpaceBits d M K k = d * Nat.clog 2 (max 2 M) + K + k ∧
        QueryCount (gradientWord d M) = 1 ∧
        GateCount (gradientWord d M) = 2 * d)

end Qatlib.Concepts.FourierRecovery.ModularFourier
