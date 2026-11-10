/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.CoherentOAA.AdjointWord
import Qatlib.Concepts.CoherentSim.CoherentOAA.Amplification
import Qatlib.Concepts.CoherentSim.CoherentOAA.BlockRobustness
import Qatlib.Concepts.CoherentSim.CoherentOAA.CoherentSimulationDefs
import Qatlib.Concepts.CoherentSim.CoherentOAA.ObliviousAmplification
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.CoherentSim.CoherentOAA.OperatorResponse
import Qatlib.Foundations.InstrumentCore.ProjectiveMeasurementLaws
import Qatlib.Concepts.CoherentSim.CoherentOAA.Pseudoinverse
import Qatlib.Concepts.CoherentSim.CoherentOAA.QSVT
import Qatlib.Concepts.CoherentSim.CoherentOAA.Qubitization
import Qatlib.Concepts.CoherentSim.CoherentOAA.QueryCircuit
import Qatlib.Concepts.CoherentSim.CoherentOAA.Realization
import Qatlib.Concepts.CoherentSim.CoherentOAA.RobustCoherentImplementation
import Qatlib.Concepts.CoherentSim.CoherentOAA.ScaleEightCoherentAmplification
import Qatlib.Concepts.CoherentSim.CoherentOAA.SingularPolynomial
import Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower
import Qatlib.Concepts.MbqcFlow.FlowDecision.BiasedPauliShadowConsumers
import Qatlib.Concepts.MbqcFlow.FlowDecision.CertifiedPilotCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.CoarseAcceptance
import Qatlib.Concepts.MbqcFlow.FlowDecision.DegenerateEnergyInstrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.DiagonalTraceDistance
import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccess
import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessExt
import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessRefined
import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveNumericPrepareChain
import Qatlib.Concepts.MbqcFlow.FlowDecision.EnergyReadoutConsumers
import Qatlib.Concepts.MbqcFlow.FlowDecision.EnsembleUStatisticHigherMoments
import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccess
import Qatlib.Concepts.MbqcFlow.FlowDecision.FiniteDataAccessDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatistics
import Qatlib.Concepts.MbqcFlow.FlowDecision.StoppingReference
import Qatlib.Concepts.MbqcFlow.FlowDecision.GramSquareRootBound
import Qatlib.Concepts.MbqcFlow.FlowDecision.IsingClusterResource
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetwork
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkBranch
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkInstrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkRouting
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalClusterNetworkTransport
import Qatlib.Concepts.MbqcFlow.FlowDecision.LocalShadowConfidenceConsumers
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlow
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowClause2
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowExt
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCounterexamples
import Qatlib.Concepts.MbqcFlow.FlowDecision.FlowExtended
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowCoreDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MbqcFlowPreentangled
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatistics
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasuredStatisticsDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetwork
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCC
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementNetworkLOCCDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsExt
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNative
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatisticsNativeDefs
import Qatlib.Foundations.PureStateMath.MixedState
import Qatlib.Concepts.MbqcFlow.FlowDecision.NoisyHadamardMixture
import Qatlib.Concepts.MbqcFlow.FlowDecision.PauliShadowConsumers
import Qatlib.Concepts.MbqcFlow.FlowDecision.Physlib
import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurement
import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurementData
import Qatlib.Concepts.MbqcFlow.FlowDecision.PrettyGoodMeasurementFrame
import Qatlib.Concepts.MbqcFlow.FlowDecision.ProposalUnitary
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureEnsemblePGM
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureStateOverlap
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditional
import Qatlib.Concepts.MbqcFlow.FlowDecision.PureToMixedConditionalDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.PurificationProduct
import Qatlib.Concepts.MbqcFlow.FlowDecision.QuadraticObservableConsumers
import Qatlib.Concepts.MbqcFlow.FlowDecision.QuadraticTraceDistance
import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbs
import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.QuantumGibbsRefinedDefs
import Qatlib.Foundations.PureStateMath.Qubit
import Qatlib.Concepts.MbqcFlow.FlowDecision.RectangularSchattenHolder
import Qatlib.Concepts.MbqcFlow.FlowDecision.SchattenDiamond
import Qatlib.Concepts.MbqcFlow.FlowDecision.SchattenDiamondDefs
import Qatlib.Concepts.MbqcFlow.FlowDecision.SparseAccessProgram
import Qatlib.Foundations.PureStateMath.Tensor
import Qatlib.Concepts.MbqcFlow.FlowDecision.TensorShadowConsumers
import Qatlib.Concepts.MbqcFlow.FlowDecision.TetrahedralShadowConsumers
import Qatlib.Concepts.MbqcFlow.FlowDecision.TetrahedralShadowInstrument
import Qatlib.Concepts.MbqcFlow.FlowDecision.TetrahedralShadowStatistics
import Qatlib.Concepts.SignalPrimitive.GridGradient.GradientSourceContinuationDefs
import Qatlib.Concepts.SignalPrimitive.GridGradient.Basic
import Qatlib.Concepts.SignalPrimitive.GridGradient.GridGradientConsumers
import Qatlib.Foundations.QueryWordCore.Circuit
import Qatlib.Concepts.ReferenceError.MixturePaths
import Qatlib.Concepts.SpectralReadout.OffGridPhaseReadout
import Qatlib.Concepts.HspRecovery.Reduction.ReductionDefs
import Qatlib.Concepts.HspRecovery.Reduction.AlgebraicRecovery
import Qatlib.Concepts.HspRecovery.Reduction.AlgebraicRecoveryDefs
import Qatlib.Concepts.HspRecovery.Reduction.AlgebraicRecoveryRefinedDefs
import Qatlib.Concepts.HspRecovery.Reduction.BooleanGaussianDecoder
import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardFourierBridge
import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardSampling
import Qatlib.Concepts.HspRecovery.Reduction.BooleanHadamardSamplingEvent
import Qatlib.Concepts.HspRecovery.Reduction.BooleanQuotientRecovery
import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryHitting
import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryRank
import Qatlib.Concepts.HspRecovery.Reduction.BooleanRecoveryTail
import Qatlib.Concepts.HspRecovery.Reduction.BooleanSimonRecovery
import Qatlib.Concepts.HspRecovery.Reduction.BooleanSimonSampling
import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecovery
import Qatlib.Concepts.HspRecovery.Reduction.CompactPresentationRecoveryDefs
import Qatlib.Concepts.HspRecovery.Reduction.CountedSimonDecoder
import Qatlib.Concepts.HspRecovery.Reduction.CyclicRecoveryConsumers
import Qatlib.Concepts.HspRecovery.Reduction.DistinctFourierNoiseConsumers
import Qatlib.Concepts.HspRecovery.Reduction.FourierEffectiveRecovery
import Qatlib.Concepts.HspRecovery.Reduction.FourierEffectiveRecoveryDefs
import Qatlib.Concepts.HspRecovery.Reduction.GradientOracle
import Qatlib.Concepts.HspRecovery.Reduction.GradientOracleDefs
import Qatlib.Concepts.HspRecovery.Reduction.KnownQubitPhaseReadout
import Qatlib.Concepts.HspRecovery.Reduction.ModularReversibleWord
import Qatlib.Concepts.HspRecovery.Reduction.NativeEndpoint
import Qatlib.Concepts.HspRecovery.Reduction.PairLCMFactorConsumers
import Qatlib.Concepts.HspRecovery.Reduction.PhaseReadoutSynthesisDefs
import Qatlib.Concepts.HspRecovery.Reduction.PowerTwoSlopeProgram
import Qatlib.Concepts.HspRecovery.Reduction.RandomBaseFactorConsumers
import Qatlib.Concepts.HspRecovery.Reduction.ReversibleBandClassifier
import Qatlib.Concepts.HspRecovery.Reduction.SmithWholePivotRun
import Qatlib.Concepts.HspRecovery.Reduction.DescentQueryGrowthDihe
import Qatlib.Concepts.HspRecovery.Reduction.DescentQueryGrowthStat
import Qatlib.Concepts.HspRecovery.Reduction.OracleReductionsDihe
import Qatlib.Concepts.HspRecovery.Reduction.OracleReductionsStat
import Qatlib.Concepts.HspRecovery.Reduction.OracleTwirling
import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentDihe
import Qatlib.Concepts.HspRecovery.Reduction.ParityDescentStat
import Qatlib.Concepts.HspRecovery.Reduction.Reductions
import Qatlib.Concepts.HspRecovery.Reduction.TwirlingCounterexample
import Qatlib.Concepts.GradientOracle.ValueKickback
import Qatlib.Concepts.QspSimulation.Achievability.AchievableNecessitySourceFormLowc
import Qatlib.Concepts.QspSimulation.Achievability.AchievableNecessitySourceFormStat
import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedLowc
import Qatlib.Concepts.QspSimulation.Achievability.AchievableSufficiencyRestrictedStat
import Qatlib.Concepts.QspSimulation.Achievability.CircuitWellFormed
import Qatlib.Concepts.QspSimulation.Achievability.CleanSignalSimulation
import Qatlib.Concepts.QspSimulation.Achievability.ComputedSignalConsumers
import Qatlib.Concepts.QspSimulation.Achievability.CountedHamiltonian
import Qatlib.Concepts.QspSimulation.Achievability.ExponentialPolynomial
import Qatlib.Concepts.QspSimulation.Achievability.Compilation
import Qatlib.Concepts.QspSimulation.Achievability.HamiltonianSimulation
import Qatlib.Concepts.QspSimulation.Achievability.SimQsp
import Qatlib.Concepts.QspSimulation.Achievability.SimQspDefs
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxContractObstructions
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxEndpointNormalization
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxReal
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceCompilation
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSourceWord
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxSufficiencyObstruction
import Qatlib.Concepts.QspSimulation.Achievability.Lc17AuxTransfer
import Qatlib.Concepts.QspSimulation.Achievability.LcuQsvt
import Qatlib.Concepts.QspSimulation.Achievability.MatrixExponentialApproximation
import Qatlib.Concepts.QspSimulation.Achievability.OraclePerturbation
import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedLowc
import Qatlib.Concepts.QspSimulation.Achievability.QspCompilationRestrictedStat
import Qatlib.Concepts.QspSimulation.Achievability.QspSimulationDefs
import Qatlib.Concepts.QspSimulation.Achievability.RealPartQSVT
import Qatlib.Concepts.QspSimulation.Achievability.RealPartResponse
import Qatlib.Concepts.QspSimulation.Achievability.RealPolynomial
import Qatlib.Concepts.QspSimulation.Achievability.ResponseFactorization
import Qatlib.Concepts.QspSimulation.Achievability.SimQspRefined
import Qatlib.Concepts.QspSimulation.Achievability.TrigApproximation
import Qatlib.Concepts.QspSimulation.JacobiAnger.ComputedSignalSimulation
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeLowc
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerCorrectedDegreeStat
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncationLowc
import Qatlib.Concepts.QspSimulation.JacobiAnger.JacobiAngerTruncationStat
import Qatlib.Concepts.QspSimulation.JacobiAnger.SimQspDefs
import Qatlib.Foundations.PureStateMath.BornBridge.BornDistribution
import Qatlib.Concepts.CopyEvolution.Discriminate.ConditionalOutput
import Qatlib.Concepts.CopyEvolution.Discriminate.ControlledCopyEvolution
import Qatlib.Concepts.CopyEvolution.Discriminate.CopyEvolutionConsumer
import Qatlib.Concepts.CopyEvolution.Discriminate.CopyExponentialPrecision
import Qatlib.Concepts.CopyEvolution.Discriminate.DiamondMeasurementSuccessHelstrom
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationQuan
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationStat
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteTwoSpeciesSignReadoutQuan
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteTwoSpeciesSignReadoutStat
import Qatlib.Concepts.BlockEncoding.LCU
import Qatlib.Concepts.CopyEvolution.Discriminate.ParallelQSVT
import Qatlib.Concepts.CopyEvolution.Discriminate.PartialSwapEvolution
import Qatlib.Foundations.PureStateMath.BornBridge.PartialTraceCovariance
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates
import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
import Qatlib.Foundations.PureStateMath.BornBridge.RepresentationBridge
import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesCopyPhaseReadout
import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesSpectralReadoutQuan
import Qatlib.Concepts.CopyEvolution.Discriminate.TimedTwoSpeciesSpectralReadoutStat
import Qatlib.Concepts.CopyEvolution.Discriminate.TrainingSetFiniteDiscriminationQuan
import Qatlib.Concepts.CopyEvolution.Discriminate.TrainingSetFiniteDiscriminationStat
import Qatlib.Concepts.CopyEvolution.Discriminate.TwoSpeciesCopyExponential
import Qatlib.Concepts.CopyEvolution.Discriminate.TwoSpeciesDiscriminationSubgoalQuan
import Qatlib.Concepts.CopyEvolution.Discriminate.TwoSpeciesDiscriminationSubgoalStat
import Qatlib.Concepts.CopyEvolution.Discriminate.UnitaryExponentialRemainder
import Qatlib.Concepts.FourierRecovery.ModularFourier.GradientSourceContinuation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
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
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator ComplexConjugate

noncomputable def probabilityPhaseOperator {X : Type} [Fintype X] [DecidableEq X]
    (p : X → ℝ) : Matrix X X ℂ :=
  Matrix.diagonal (fun x => Complex.exp (Complex.I * (p x : ℂ)))

noncomputable def probabilityReadoutPhase {X : Type} (p : X → ℝ) : X → ℝ :=
  fun x => p x / (2 * Real.pi)

noncomputable def readoutDecoder {d M : ℕ} (z : GradientGrid d M) : Fin d → ℝ :=
  fun j => signedGridValue M (z j)

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
