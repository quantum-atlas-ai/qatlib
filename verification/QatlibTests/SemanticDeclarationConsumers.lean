/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ActualRestartExpectation
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AePaddingOutputTransport
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.HeuristicQSearchReceipt
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.RecordedMedianProgram
import Qatlib.Concepts.AdversaryBounds.AdvDuality.DisjointWorkspaceComposition
import Qatlib.Concepts.AdversaryBounds.AdvDuality.EffectiveCoinReceiptProgram
import Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost
import Qatlib.Concepts.AdversaryBounds.AdvDuality.TmCopyRunResetCompiler
import Qatlib.Concepts.AmpTransform.ErrorStream.AmplifiedNoiseExt
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.ClockMinimumExecutor
import Qatlib.Concepts.CliffordTheory.TableauSim
import Qatlib.Concepts.ClusterPatterns.ClusterCompile.MeasurementPatterns
import Qatlib.Concepts.CompressedQuery.BosonicNorm
import Qatlib.Concepts.CopyEvolution.Discriminate.DiamondMeasurementSuccessHelstrom
import Qatlib.Concepts.DyadicOverlap.ArithLedger.MatrixOptimization
import Qatlib.Concepts.Entanglement.Separability.EntanglementBoundaryConsumers
import Qatlib.Concepts.Entanglement.Separability.LoccAverageEntropy
import Qatlib.Concepts.Entanglement.Separability.LoccEntropyAverageStep
import Qatlib.Concepts.FiniteLocc.LOCCProgram.LayerStrippingCertifiedStability
import Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementNetwork
import Qatlib.Concepts.FiniteLocc.LOCCProgram.SchattenDiamond
import Qatlib.Concepts.HspRecovery.OpenSieve.NonabelianSieve
import Qatlib.Concepts.HspRecovery.Reduction.ModularReversibleWord
import Qatlib.Concepts.HspRecovery.Reduction.ReversibleBandClassifier
import Qatlib.Concepts.HspRecovery.Reduction.SmithWholePivotRun
import Qatlib.Concepts.LocalMachine.LocalTransport.MwUniformVerifierCompiler
import Qatlib.Concepts.LocalMachine.LocalTransport.QcmaDephasingAcceptProbability
import Qatlib.Concepts.MatrixAccess.CircuitPipeline.AdaptiveQueryLower
import Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower
import Qatlib.Concepts.MbqcFlow.FlowDecision.CertifiedPilotCore
import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessExt
import Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveNumericPrepareChain
import Qatlib.Concepts.MbqcFlow.FlowDecision.EnsembleUStatisticHigherMoments
import Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatistics
import Qatlib.Concepts.MbqcFlow.FlowDecision.RectangularSchattenHolder
import Qatlib.Concepts.MbqcFlow.FlowDecision.SparseAccessProgram
import Qatlib.Concepts.MbqcFlow.PreEntanglement
import Qatlib.Concepts.MonteCarloMean.PayoffRotation.LayerStrippingCertifiedStability
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.DualMixtureDensityInput
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.FiniteTensorTableCodec
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.ProgramRoundedWitness
import Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetwork
import Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu
import Qatlib.Concepts.NonNormalSpec.ResolventWord.OracleBlockHybridLowerBound
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.AdaptiveCutUnionBound
import Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellCorrection
import Qatlib.Concepts.PauliClifford.PauliAlgebra.CliffordStabilizerExt
import Qatlib.Concepts.ProbabilityCore.Concentration.CountingHash
import Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesExt
import Qatlib.Concepts.QspSimulation.Achievability.Compilation
import Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow
import Qatlib.Concepts.QsvtCore.ApproxToolkit.QsvtCore
import Qatlib.Concepts.QsvtCore.PhaseExistence.ContinuousModulusSvt
import Qatlib.Concepts.QsvtCore.PhaseExistence.EffectiveBesselCutoff
import Qatlib.Concepts.QsvtCore.PhaseExistence.QsvtCore
import Qatlib.Concepts.QsvtCore.QueryLowerBound.ApproximationAlgorithms
import Qatlib.Concepts.QsvtLinearSolve.Angles.QlsQsvt
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.DepolarizingEntropySpectrum
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ExplicitNeighborSetupProgram
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.LindbladSemigroup
import Qatlib.Concepts.QuantumGibbs.FormAlgebra.ReversibleBusyDiscriminant
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.BooleanQueryMinimumBounds
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanPermutationLayerAverage
import Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs
import Qatlib.Concepts.QueryComplexity.DegreeMethod.CoinTmLaw
import Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence
import Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain
import Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeFourthComparison
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionBase
import Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MonotoneFourthQueryComparison
import Qatlib.Concepts.QueryComplexity.DegreeMethod.MwActualTwoProjectors
import Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper
import Qatlib.Concepts.QueryComplexity.DegreeMethod.QuerySpace
import Qatlib.Concepts.QueryComplexity.DegreeMethod.SmithPivotRunBitBound
import Qatlib.Concepts.QueryComplexity.DegreeMethod.StoppingReference
import Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease
import Qatlib.Concepts.QueryComplexity.Reflections.AdaptiveQueryLower
import Qatlib.Concepts.RandCompile.ChannelBudget.InstrumentPerturbationPostselection
import Qatlib.Concepts.ReferenceError.RefTraceError.NoisyValuePhaseKickback
import Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBounds
import Qatlib.Concepts.RiskEstimation.PopulationGap.RecordedMedianProgram
import Qatlib.Concepts.SdpDuality.ConeSeparation.MmwBornStatistics
import Qatlib.Concepts.SdpDuality.ConeSeparation.SharedMatrixOptimization
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedHermitianSpectrum
import Qatlib.Concepts.SpectralSketch.SpectrumPerturb.FiniteResolventCertificate
import Qatlib.Concepts.TrotterFormula.GeneralOrder.GroupedOrderedRemainder
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterLowerBoundFamily
import Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSupportRouting
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.CertifiedPilotCore
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis
import Qatlib.Concepts.UnbiasedBases.ThreeBasis.MiddleWindowFixedWord
import Qatlib.Concepts.UniformBqp.Phi3Compile.NativeUniformEmitterCodec
import Qatlib.Concepts.WalkSearch.FrameSpectral.SpectralFilterWord
import Qatlib.Concepts.WalkSearch.MnrsAmplify.CorrectSinePacketReflection
import Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBandCertificateProgram
import Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBracketCertifiedSearch
import Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver
import Qatlib.Concepts.Waterfill.LevelFidelity.WaterfillZeroSigmaBoundary
import Qatlib.Papers.AlgGeomCode25.MainResults.StatementBank
import Qatlib.Papers.AnnealingDNN15.MainResults.Benchmark.SourceCgMnistBenchmark
import Qatlib.Papers.AnnealingDNN15.MainResults.Chimera.SourceChimeraEmbedding
import Qatlib.Papers.BettiNumber25.MainResults.StatementBank
import Qatlib.Papers.DetEstimate25.MainResults.StatementBank
import Qatlib.Papers.DissipDESolve25.MainResults.StatementBank
import Qatlib.Papers.FixedPtSearch14.FixedPoint.OptimalFixedPoint
import Qatlib.Papers.GenerativeAdv25.MainResults.Source.ProvedResults
import Qatlib.Papers.GenerativeAdv25.MainResults.StatementBank
import Qatlib.Papers.HamDecodedQI25.MainResults.StatementBank
import Qatlib.Papers.LocalHam06.MainResults.QmaCompleteness
import Qatlib.Papers.LowRankMatrix19.SQFramework.RationalAliasPreprocessorSQ
import Qatlib.Papers.LowRankSolve25.MainResults.StatementBank
import Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ModularReversibleWord
import Qatlib.Papers.NoisyNonlin25.MainResults.StatementBank
import Qatlib.Papers.OGPQAOAGoh25.MainResults.StatementBank
import Qatlib.Papers.QDecoding25.MainResults.StatementBank
import Qatlib.Papers.QLSBeyondCond25.MainResults.StatementBank
import Qatlib.Papers.QMAvsQCMA25.Forrelation.AdaptiveXorDatabaseTransport
import Qatlib.Papers.QMAvsQCMA25.Forrelation.XorCompressedDatabaseIntertwining
import Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.Basic
import Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization
import Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization
import Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport
import Qatlib.Papers.QuantumPCA14.FeatureReadout.CopyQpca
import Qatlib.Papers.QuantumPCPs25.MainResults.Model
import Qatlib.Papers.RandCertLiu25.MainResults.StatementBank
import Qatlib.Papers.RepMultiplic25.MainResults.SytCore.StatementBank
import Qatlib.Papers.RiemannQITE25.MainResults.GateCount
import Qatlib.Papers.SparseUnitary09.MainResults.ContainedModels.SourceContainedModels
import Qatlib.Papers.SparseUnitary09.MainResults.Dilation.SourceSparseDilation
import Qatlib.Papers.SparseUnitary09.MainResults.Model.SourceSparseUnitaryModel
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeExt
import Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StoppedHistoryMoment

/-! The declarations below elaborate as ordinary public imports. -/

set_option autoImplicit false
set_option warningAsError true

#guard_msgs (drop info) in #check Qatlib.Concepts.AEMeanReadout.LocalAEBackend.ActualRestartExpectation.measured_restart_cost_limits_and_optimal_angle
#guard_msgs (drop info) in #check Qatlib.Concepts.AEMeanReadout.LocalAEBackend.AePaddingOutputTransport.padded_ae_output_law_counts_and_accuracy
#guard_msgs (drop info) in #check Qatlib.Concepts.AEMeanReadout.LocalAEBackend.HeuristicQSearchReceipt.heuristic_qsearch_receipt_and_expected_cost_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw.adaptive_ae_cumulative_cost_and_fine_stage_stopping
#guard_msgs (drop info) in #check Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw.adaptive_ae_window_accuracy_and_stopping_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.AEMeanReadout.LocalAEBackend.PreparedRelativeAeAdaptiveLaw.adaptive_ae_zero_amplitude_certification
#guard_msgs (drop info) in #check Qatlib.Concepts.AEMeanReadout.LocalAEBackend.output1.signed_trial_median_error_and_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.AdversaryBounds.AdvDuality.DisjointWorkspaceComposition.disjoint_clean_words_commute_and_release_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.AdversaryBounds.AdvDuality.SqRationalMachineCost.exists_batch_rational_machine_with_polynomial_cost
#guard_msgs (drop info) in #check Qatlib.Concepts.AdversaryBounds.AdvDuality.TmCopyRunResetCompiler.computable₂_copyRunResetCode
#guard_msgs (drop info) in #check Qatlib.Concepts.AdversaryBounds.AdvDuality.TmCopyRunResetCompiler.copyRunResetCode
#guard_msgs (drop info) in #check Qatlib.Concepts.AdversaryBounds.AdvDuality.TmCopyRunResetCompiler.tmCopyRunResetCompile_run
#guard_msgs (drop info) in #check Qatlib.Concepts.AdversaryBounds.AdvDuality.output1.compiled_race_endpoint_run_and_coin_counts
#guard_msgs (drop info) in #check Qatlib.Concepts.AmpTransform.ErrorStream.amplified_noise_transport_and_resampling_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.AmplitudeSearch.InterruptMin.source_timeout_success_and_expected_payoff
#guard_msgs (drop info) in #check Qatlib.Concepts.CliffordTheory.TableauSim.exists_physical_execution_of_valid_tableau_program
#guard_msgs (drop info) in #check Qatlib.Concepts.ClusterPatterns.ClusterCompile.reflection_graph_instrument_subset_mass_and_output
#guard_msgs (drop info) in #check Qatlib.Concepts.CompressedQuery.BosonicNorm.bosonic_bad_record_norm_and_born_mass_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.CopyEvolution.Discriminate.channel_measurement_helstrom_optimality_and_diamond_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.DyadicOverlap.ArithLedger.stopped_dual_output_law_and_read_cost
#guard_msgs (drop info) in #check Qatlib.Concepts.Entanglement.Separability.EntanglementBoundaryConsumers.dimension_one_product_states_and_bell_family
#guard_msgs (drop info) in #check Qatlib.Concepts.Entanglement.Separability.LoccAverageEntropy.two_outcome_branch_mass_entropy_and_marginal
#guard_msgs (drop info) in #check Qatlib.Concepts.Entanglement.Separability.LoccEntropyAverageStep.alternating_locc_entropy_and_execution_law
#guard_msgs (drop info) in #check Qatlib.Concepts.FiniteLocc.LOCCProgram.LayerStrippingCertifiedStability.certified_layer_strip_cost_and_error_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.FiniteLocc.LOCCProgram.LayerStrippingCertifiedStability.certified_phase_recovery_cost_and_error_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.FiniteLocc.LOCCProgram.MeasurementNetwork.qubit_teleportation_branch_and_auxiliary_account
#guard_msgs (drop info) in #check Qatlib.Concepts.FiniteLocc.LOCCProgram.SchattenDiamond.finiteDiamondNorm_le_cbNormDual
#guard_msgs (drop info) in #check Qatlib.Concepts.HspRecovery.OpenSieve.nonabelian_sieve_transport_and_extraction
#guard_msgs (drop info) in #check Qatlib.Concepts.HspRecovery.ReductionCore.ModularReversibleWord.clean_modular_arithmetic_word_correctness_and_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.HspRecovery.ReductionCore.output1.rectangular_smith_run_correctness_and_bit_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.HspRecovery.ReductionCore.reversible_band_classifier_sign_and_fourier_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.LocalMachine.LocalTransport.MwUniformVerifierCompiler.uniform_alternating_verifier_semantics_and_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.LocalMachine.LocalTransport.QcmaDephasingAcceptProbability.dephaseProgram_acceptProb_eq_diagonal_sum
#guard_msgs (drop info) in #check Qatlib.Concepts.MatrixAccess.CircuitPipeline.exists_unitary_tni_trace_simulation_with_same_queries
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.AdaptiveQueryLower.toInstrument_wellFormed_and_mixed_traces
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.CertifiedPilotCore.clipped_pilot_error_mass_le_add
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.EffectiveAccessExt.inverse_preparation_semantics_and_uncomputation_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.EnsembleUStatisticHigherMoments.povm_u_statistic_overlap_moment_and_deviation_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.EnsembleUStatisticHigherMoments.u_statistic_overlap_moment_and_deviation_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatistics.povm_u_statistic_unbiasedness_overlap_variance_and_deviation
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.MeasurementStatistics.u_statistic_unbiasedness_overlap_variance_and_deviation
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.RectangularSchattenHolder.rectangular_schatten_holder_and_operator_norm_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.SparseAccessProgram.sparse_record_resolution_lookup_and_compilation
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.output1.dense_table_preparation_error_and_cost
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.FlowDecision.output1.normalized_scaled_bracket_preparation_error_and_cost
#guard_msgs (drop info) in #check Qatlib.Concepts.MbqcFlow.PreEntanglement.flow_decision_and_preentangled_execution
#guard_msgs (drop info) in #check Qatlib.Concepts.MonteCarloMean.PayoffRotation.exists_layer_strip_certificate_of_coefficient_margin
#guard_msgs (drop info) in #check Qatlib.Concepts.MonteCarloMean.PayoffRotation.exists_positive_threshold_layer_strip_certificate_of_head_margin
#guard_msgs (drop info) in #check Qatlib.Concepts.MonteCarloMean.PayoffRotation.exists_zero_threshold_layer_strip_certificate
#guard_msgs (drop info) in #check Qatlib.Concepts.MpsAdaptation.MpsTransfer.DualMixtureDensityInput.capped_dual_mixture_receipts_and_l1_error
#guard_msgs (drop info) in #check Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionExt.fermionic_covariance_propagation_and_measurement_updates
#guard_msgs (drop info) in #check Qatlib.Concepts.MpsAdaptation.MpsTransfer.FermionMatchgateConjugation.matchgate_covariance_and_untouched_mode_conditioning
#guard_msgs (drop info) in #check Qatlib.Concepts.MpsAdaptation.MpsTransfer.FiniteTensorTableCodec.half_edge_permutation_preserves_tensor_decoding_and_contraction
#guard_msgs (drop info) in #check Qatlib.Concepts.MpsAdaptation.MpsTransfer.ProgramRoundedWitness.rounded_witness_feasibility_and_optimality_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.MpsAdaptation.MpsTransfer.TensorNetwork.half_edge_relabel_contraction_and_inner_product
#guard_msgs (drop info) in #check Qatlib.Concepts.NonNormalSpec.ResolventWord.ComplexFourRouteLcu.four_route_lcu_compression_error_and_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.NonNormalSpec.ResolventWord.scalar_oracle_block_hybrid_and_leakage_lower_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.OrderedBayes.BayesRatioCore.AdaptiveCutUnionBound.truth_driven_learner_ratio_bounds_and_calibration
#guard_msgs (drop info) in #check Qatlib.Concepts.OrderedBayes.BayesRatioCore.AdaptiveCutUnionBound.union_absorbing_kernel_ratio_bounds_and_calibration
#guard_msgs (drop info) in #check Qatlib.Concepts.OrderedBayes.BayesRatioCore.RankBayesEqualCellCorrection.equal_cell_joint_law_conditioning_and_posterior_odds
#guard_msgs (drop info) in #check Qatlib.Concepts.PauliClifford.PauliAlgebra.clifford_run_preserves_stabilizer_projector_and_expectation
#guard_msgs (drop info) in #check Qatlib.Concepts.ProbabilityCore.Concentration.CountingHash.hash_charge_time_coins_and_seed_decoding
#guard_msgs (drop info) in #check Qatlib.Concepts.ProbabilityCore.Concentration.CountingHash.hash_collision_average_and_sampler_failure_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.ProbabilityCore.Concentration.ProbabilityInterfacesExt.independent_record_joint_law_and_moments
#guard_msgs (drop info) in #check Qatlib.Concepts.QspSimulation.Achievability.exists_qsp_phases_of_even_odd_approximants
#guard_msgs (drop info) in #check Qatlib.Concepts.QsvtCore.ApproxToolkit.NearoptimalSignWindow.nearoptimal_sign_and_rectangle_degree_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QsvtCore.ApproxToolkit.exists_odd_gap_sign_approximation_with_degree_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.QsvtCore.PhaseExistence.ContinuousModulusSvt.singular_transform_continuity_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QsvtCore.PhaseExistence.EffectiveBesselCutoff.effective_bessel_cutoff_degree_error_and_radius
#guard_msgs (drop info) in #check Qatlib.Concepts.QsvtCore.PhaseExistence.exists_rectangle_approximation_of_gap_sign
#guard_msgs (drop info) in #check Qatlib.Concepts.QsvtCore.PhaseExistence.exists_rectangle_approximation_of_half_error_sign
#guard_msgs (drop info) in #check Qatlib.Concepts.QsvtCore.QueryLowerBound.oracle_word_interior_and_uniform_perturbation_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QsvtLinearSolve.AnglesCore.absorb_first_angle_preserves_word_and_scales_response
#guard_msgs (drop info) in #check Qatlib.Concepts.QuantumGibbs.FormAlgebra.CertifiedStage.GraphAccessSetup.bipartite_neighbor_setup_correctness_and_cost
#guard_msgs (drop info) in #check Qatlib.Concepts.QuantumGibbs.FormAlgebra.DepolarizingEntropySpectrum.qubit_depolarizing_entropy_decay_and_trace_distance
#guard_msgs (drop info) in #check Qatlib.Concepts.QuantumGibbs.FormAlgebra.LindbladSemigroup.relative_entropy_decay_and_trace_distance_mixing
#guard_msgs (drop info) in #check Qatlib.Concepts.QuantumGibbs.FormAlgebra.ReversibleBusyDiscriminant.exists_busy_szegedy_frame_of_positive_absolute_gap
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.AdaptiveQuery.query_minima_block_sensitivity_and_deterministic_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanPermutationLayerAverage.permutation_average_eq_hamming_layer_and_polynomial
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.exact_bounded_query_minima_attainment_and_degree_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.BooleanQueryMinimumDefs.zero_error_query_minima_attainment_and_order
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.CoinTmLaw.output2.race_machine_counts_mass_and_timeout_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.DegreeVariableDependence.all_coordinates_degree_and_exact_query_lower_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.TrialEmit.trial_emission_machine_correctness_and_bisection_agreement
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.incremental_bisection_invariants_and_binary_word_correctness
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.integer_sqrt_bracket_midpoint_and_size_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.EffectiveNumericPrepareChain.output2.rational_word_sqrt_bracket_and_tm_realization
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.ExactDegreeFourthComparison.deterministic_query_le_fourth_powers_of_degree_and_exact_queries
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionBase.exists_uniform_quotient_machine_with_family_size_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.FinitePrecisionCore.exists_rational_quotient_machine_with_size_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.MajorityAndRestriction.odd_majority_query_program_and_minimum_lower_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.MonotoneFourthQueryComparison.monotone_certificate_and_fourth_power_query_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.MwActualTwoProjectors.exists_clean_subspace_frame_for_alternating_record_law
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.OrAndSearchUpper.first_marked_search_and_or_and_query_minima
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.QuerySpace.exists_bare_phase_simulation_with_query_and_gate_counts
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.SmithPivotRunBitBound.output2.binary_smith_pivot_correctness_and_bit_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.StoppingReference.conditional_stopping_output_density_and_convergence
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.StoppingReference.stopping_execution_limit_and_mass_conservation
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease.clean_word_compilation_traces_and_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.DegreeMethod.WorkspaceCleanRelease.stopping_program_trace_count_and_unique_rejection
#guard_msgs (drop info) in #check Qatlib.Concepts.QueryComplexity.Reflections.adaptive_tni_adversary_lower_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.RandCompile.ChannelBudget.instrument_error_controls_branch_mass_and_postselection
#guard_msgs (drop info) in #check Qatlib.Concepts.ReferenceError.RefTraceError.noisy_value_phase_kickback_correctness_and_error
#guard_msgs (drop info) in #check Qatlib.Concepts.ResourceBounds.AsymBounds.ResourceBounds.search_upper_and_parity_query_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.RiskEstimation.PopulationGap.output2.risk_cdf_median_error_and_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.SdpDuality.ConeSeparation.SdpDuality.psd_farkas_geometry_and_nonclosed_corner_image
#guard_msgs (drop info) in #check Qatlib.Concepts.SdpDuality.ConeSeparation.clause4_refuted
#guard_msgs (drop info) in #check Qatlib.Concepts.SdpDuality.ConeSeparation.gibbs_updates_born_statistics_and_regret_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage.CertifiedHermitianSpectrum.radius_spectral_certificate_soundness_and_completeness
#guard_msgs (drop info) in #check Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage.CertifiedHermitianSpectrum.real_spectral_certificate_generation_and_checking_cost
#guard_msgs (drop info) in #check Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage.CertifiedHermitianSpectrum.spectral_certificate_generation_cost_and_witness_height
#guard_msgs (drop info) in #check Qatlib.Concepts.SpectralSketch.SpectrumPerturb.CertifiedStage.CertifiedHermitianSpectrum.spectral_certificate_soundness_and_completeness
#guard_msgs (drop info) in #check Qatlib.Concepts.SpectralSketch.SpectrumPerturb.resolvent_quadrature_error_and_certificate_cost
#guard_msgs (drop info) in #check Qatlib.Concepts.TrotterFormula.GeneralOrder.GroupedOrderedRemainder.grouped_trotter_remainder_and_tagged_word_error
#guard_msgs (drop info) in #check Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterLowerBoundFamily.cubic_trotter_error_two_sided_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSupportRouting.exists_disjoint_support_layer_routing_within_swap_budget
#guard_msgs (drop info) in #check Qatlib.Concepts.TrotterFormula.GeneralOrder.TrotterSupportRouting.scheduled_support_layers_have_disjoint_routings
#guard_msgs (drop info) in #check Qatlib.Concepts.UnbiasedBases.ThreeBasis.CertifiedPilotCore.bounded_payoff_pilot_error_mass_le_add
#guard_msgs (drop info) in #check Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis.transported_segment_accepted_of_positive_precision
#guard_msgs (drop info) in #check Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis.transported_segment_extra_wires_le_one
#guard_msgs (drop info) in #check Qatlib.Concepts.UnbiasedBases.ThreeBasis.FixedGateSynthesis.transported_segment_polynomial_gate_ledger_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.UnbiasedBases.ThreeBasis.MiddleWindowFixedWord.htc_segment_approximation_ancilla_and_length
#guard_msgs (drop info) in #check Qatlib.Concepts.UnbiasedBases.ThreeBasis.MiddleWindowFixedWord.solovay_kitaev_segment_accepted_of_positive_precision
#guard_msgs (drop info) in #check Qatlib.Concepts.UnbiasedBases.ThreeBasis.MiddleWindowFixedWord.solovay_kitaev_segment_explicit_length_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.UnbiasedBases.ThreeBasis.MiddleWindowFixedWord.solovay_kitaev_segment_extra_wires_le_one
#guard_msgs (drop info) in #check Qatlib.Concepts.UnbiasedBases.ThreeBasis.MiddleWindowFixedWord.solovay_kitaev_segment_uniform_polynomial_length_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.UniformBqp.Phi3Compile.native_machine_codec_emitter_and_window_simulation
#guard_msgs (drop info) in #check Qatlib.Concepts.WalkSearch.FrameSpectral.envelope_reflection_error_and_exact_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.WalkSearch.MnrsAmplify.CorrectSinePacketReflection.aligned_sine_packet_reflection_error_and_resources
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBandCertificateProgram.fidelity_band_rate_and_ambiguity_certificates
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelityBracketCertifiedSearch.fidelity_bracket_accuracy_and_exact_work
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.ambiguous_upper_endpoint_gap_and_lower_grid_point_certificate
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.certified_run_normalization_preserves_fidelity_and_bounds_schedule
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.chain_gap_weighted_sum_and_slope_lower_bound
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.cross_piece_gap_rate_and_interval_band_rate
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.entrywise_rounding_error_and_round_budget_stability
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.fidelity_search_margin_and_success_existence
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.fidelity_target_monotonicity_and_bracket_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.interval_bit_budget_fidelity_mass_and_dot_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.interval_decision_propagation_and_ambiguity_precision_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.joint_budget_fidelity_mass_and_round_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.normalized_mass_bounds_imply_amplitude_round_and_sine_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.plateau_ambiguity_and_error_bounds_of_joint_termination
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.plateau_fidelity_and_search_ambiguity_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.plateau_gap_growth_and_interval_search_cost_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.sequential_rounding_error_and_round_budget_stability
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.successful_fidelity_search_bracket_accuracy_and_work
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.three_piece_gap_growth_of_chain_rate_lower
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.two_piece_gap_decomposition_and_lower_bound_of_segment_slopes
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.two_piece_gap_growth_of_cross_piece_rate_lower
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.FidelitySearchDriver.upper_bracket_fidelity_error_and_resampling_bounds
#guard_msgs (drop info) in #check Qatlib.Concepts.Waterfill.LevelFidelity.WaterfillZeroBoundary.exists_checked_fill_with_regularized_endpoint_limits
#guard_msgs (drop info) in #check Qatlib.Papers.AlgGeomCode25.MainResults.ag_code_dual_family_membership_statement
#guard_msgs (drop info) in #check Qatlib.Papers.AlgGeomCode25.MainResults.hermitian_code_dual_index_statement
#guard_msgs (drop info) in #check Qatlib.Papers.AlgGeomCode25.MainResults.hopi_dqi_expected_satisfaction_formula_statement
#guard_msgs (drop info) in #check Qatlib.Papers.AlgGeomCode25.MainResults.nonzero_principal_divisor_degree_zero_statement
#guard_msgs (drop info) in #check Qatlib.Papers.AlgGeomCode25.MainResults.riemann_roch_dimension_relation_statement
#guard_msgs (drop info) in #check Qatlib.Papers.AnnealingDNN15.MainResults.Benchmark.exists_mnist_runs_with_fewer_iterations_of_accuracy_le
#guard_msgs (drop info) in #check Qatlib.Papers.AnnealingDNN15.MainResults.Benchmark.mnist_quantum_iteration_budgets_at_most_half
#guard_msgs (drop info) in #check Qatlib.Papers.AnnealingDNN15.MainResults.Benchmark.reported_run_iteration_and_accuracy_comparison
#guard_msgs (drop info) in #check Qatlib.Papers.AnnealingDNN15.MainResults.Chimera.chimera_rbm32_coupler_counts_and_fault_tolerance
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.bernoulli_trace_sample_mean_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.chebyshev_filter_squared_norm_two_sided_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.chebyshev_gap_filter_accuracy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.classical_chebyshev_betti_trace_error_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.classical_chebyshev_estimator_failure_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.classical_chebyshev_filter_norm_upper_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.classical_chebyshev_sample_complexity_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.classical_power_estimator_sample_and_failure_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.classical_power_sample_complexity_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.quantum_and_chebyshev_sample_complexity_comparison_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.quantum_chebyshev_estimator_failure_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.quantum_chebyshev_sample_query_complexity_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.quantum_power_estimator_degree_sample_and_failure_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.quantum_power_sample_query_complexity_statement
#guard_msgs (drop info) in #check Qatlib.Papers.BettiNumber25.MainResults.spectral_filter_betti_trace_error_statement
#guard_msgs (drop info) in #check Qatlib.Papers.DetEstimate25.MainResults.logdet_estimation_step_bound_assembly
#guard_msgs (drop info) in #check Qatlib.Papers.DissipDESolve25.MainResults.dissipative_final_state_log_cubed_query_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.DissipDESolve25.MainResults.history_state_squared_norm_sum_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.DissipDESolve25.MainResults.propagator_normalization_product_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.DissipDESolve25.MainResults.robust_block_encoding_amplification_statement
#guard_msgs (drop info) in #check Qatlib.Papers.FixedPtSearch14.FixedPoint.fixed_point_word_run_eq_response_state
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.Source.eq_meanData_of_lsLoss_isCriticalPoint
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.Source.exists_swap_parameters_realizing_target_up_to_phase
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.Source.lsLoss_isGlobalMin_of_isLocalMin
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.Source.lsLoss_stronglyConvex2
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.Source.meanData_isUniqueGlobalMin_lsLoss
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.benign_landscape_component_and_restart_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.compressed_circuit_classical_hardness_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.compressed_simulation_generation_advantage_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.conditional_generative_learning_advantage_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.conditional_qnn_total_variation_approximation_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.divide_and_conquer_convex_or_bounded_minimum_regions_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.heisenberg_pauli_estimation_samples_and_confidence_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.idqnn_deep_random_circuit_distribution_eq_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.idqnn_generative_learning_advantage_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.idqnn_realization_distribution_and_qubit_overhead_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.idqnn_sampling_bounded_depth_and_polynomial_cost_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.joint_sampling_hardness_of_nonuniform_ph_noncollapse_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.local_inversion_sewing_norm_error_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.local_measurement_learning_vanishing_error_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.parameterized_swap_target_realization_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.shallow_circuit_learning_diamond_error_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.swap_landscape_exponential_suboptimal_minima_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.swap_landscape_suboptimal_minima_gap_and_basin_statement
#guard_msgs (drop info) in #check Qatlib.Papers.GenerativeAdv25.MainResults.tomographic_generative_learning_advantage_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.coherent_bell_label_unitary_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.commuting_hdqi_single_decode_call_cost_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.exponential_relative_polynomial_approximation_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.gibbs_polynomial_preparation_degree_and_error_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.hdqi_energy_semicircle_limit_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.mps_pilot_preparation_component_size_cost_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.nearly_independent_hdqi_normalization_and_preparation_cost_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.pilot_state_hdqi_single_decode_call_cost_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.semiclassical_spin_glass_gibbs_preparation_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.stabilizer_mixture_classical_sampling_cost_statement
#guard_msgs (drop info) in #check Qatlib.Papers.HamDecodedQI25.MainResults.weyl_bell_orthonormality_statement
#guard_msgs (drop info) in #check Qatlib.Papers.LocalHam06.MainResults.qma_history_locality_description_and_energy_bounds
#guard_msgs (drop info) in #check Qatlib.Papers.LowRankMatrix19.SQFramework.rational_alias_preprocessing_correctness_and_resources
#guard_msgs (drop info) in #check Qatlib.Papers.LowRankSolve25.MainResults.compressed_solver_relative_error_and_access_cost_statement
#guard_msgs (drop info) in #check Qatlib.Papers.LowRankSolve25.MainResults.compressed_solver_sparsity_and_build_cost_statement
#guard_msgs (drop info) in #check Qatlib.Papers.LowRankSolve25.MainResults.diagonal_scaled_matvec_second_moment_statement
#guard_msgs (drop info) in #check Qatlib.Papers.LowRankSolve25.MainResults.diagonal_scaled_rhs_second_moment_statement
#guard_msgs (drop info) in #check Qatlib.Papers.LowRankSolve25.MainResults.iterated_solution_expected_squared_error_statement
#guard_msgs (drop info) in #check Qatlib.Papers.LowRankSolve25.MainResults.sampled_gradient_centering_and_second_moment_statement
#guard_msgs (drop info) in #check Qatlib.Papers.LowRankSolve25.MainResults.sampling_parameter_high_probability_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.LowRankSolve25.MainResults.scaled_matvec_rhs_difference_second_moment_statement
#guard_msgs (drop info) in #check Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.ModularReversibleWord.clean_modular_arithmetic_program_correctness_and_resources
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.dilation_quadratic_form_comparison_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.drift_off_diagonal_matrix_element_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.drift_operators_skew_adjoint_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.evolution_moment_and_integral_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.first_moment_commutator_sqrt_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.higher_order_moment_commutator_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.kolmogorov_initial_value_solution_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.kolmogorov_trajectory_derivative_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.linear_sde_circuit_encoding_resource_and_error_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.noisy_observable_approximation_runtime_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.power_weighted_drift_relative_norm_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.spectral_projection_error_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.truncated_drift_commutator_defect_vanishes_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.truncated_drift_sparsity_and_norm_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.truncated_evolution_convergence_and_error_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.truncated_evolution_moment_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.truncated_generator_convergence_statement
#guard_msgs (drop info) in #check Qatlib.Papers.NoisyNonlin25.MainResults.weighted_coupling_coefficient_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.OGPQAOAGoh25.MainResults.hypergraph_regularization_removed_edges_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.OGPQAOAGoh25.MainResults.log_depth_qaoa_tree_formula_transfer_statement
#guard_msgs (drop info) in #check Qatlib.Papers.OGPQAOAGoh25.MainResults.qaoa_overlap_gap_bound_below_parisi_statement
#guard_msgs (drop info) in #check Qatlib.Papers.OGPQAOAGoh25.MainResults.qaoa_value_le_local_classical_value_statement
#guard_msgs (drop info) in #check Qatlib.Papers.OGPQAOAGoh25.MainResults.treelike_neighborhood_fraction_tends_to_one_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.average_typical_pgm_success_of_entropy_gap_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.decoding_failure_in_upper_rate_interval_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.distinguishing_success_perturbation_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.general_function_decoding_above_entropy_failure_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.general_function_decoding_below_entropy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.hirschman_entropy_sum_lower_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.holevo_capacity_lower_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.per_codeword_pgm_success_of_entropy_gap_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.pgm_failure_upper_bound_of_entropy_gap_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.pgm_success_deviation_from_typical_average_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.pgm_success_eq_normalized_square_sum_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.random_dual_code_tail_event_high_probability_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.rank_metric_decoding_above_entropy_failure_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.rank_metric_decoding_below_entropy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.rank_metric_dual_sampling_below_entropy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.rank_metric_tail_sum_upper_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.regev_application_success_below_entropy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.tensor_decoding_above_fourier_entropy_failure_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.tensor_decoding_below_fourier_entropy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.tensor_dual_sampling_success_below_fourier_entropy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.tensor_pgm_success_eq_normalized_square_sum_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.truncated_coset_state_norm_error_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.typical_fourier_weight_expectation_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.typical_fourier_weight_variance_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.typical_set_cardinality_lower_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.typical_set_entropy_uniqueness_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QDecoding25.MainResults.typical_set_sequence_decoding_below_entropy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.augmented_condition_number_sqrt_two_comparison_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.boolean_polynomial_solution_recovery_runtime_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.boolean_solution_measurement_success_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.composed_qls_trace_error_and_runtime_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.initial_state_eq_scaled_solution_sub_projector_residual_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.kernel_projection_error_and_query_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.phase_zero_solution_state_query_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.planted_independent_set_polynomial_recovery_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.potential_vector_fixed_by_second_projector_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.qls_solution_state_electrical_runtime_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.solution_direction_fixed_by_alternating_reflections_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.weighted_macaulay_condition_number_exponential_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QLSBeyondCond25.MainResults.welded_tree_electrical_flow_cost_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QMAvsQCMA25.Forrelation.AdaptiveXorDatabaseTransport.adaptive_xor_failure_leaf_transport_and_mass_bound
#guard_msgs (drop info) in #check Qatlib.Papers.QMAvsQCMA25.Forrelation.AdaptiveXorDatabaseTransport.adaptive_xor_leaf_transport_mass_and_update_witnesses
#guard_msgs (drop info) in #check Qatlib.Papers.QMAvsQCMA25.Forrelation.XorCompressedDatabaseIntertwining.xor_database_intertwining_and_involutive_oracles
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.assemblage_message_bit_length_lower_bound
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.assemblage_message_count_lower_bound
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.bell_merged_branch_no_go
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.bell_message_alphabet_card_lower_bound
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.bell_message_fiber_of_noninjective_encoding
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.bell_message_injective_of_exact_recovery
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.bell_prearrival_message_guessing
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.qudit_merged_branch_no_go
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.qudit_message_alphabet_capacity_lower_bound
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.qudit_message_bit_length_lower_bound
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.qudit_message_injective_of_exact_recovery
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.redundant_coding_midpoint_reliability
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ClassicalChannelBound.unitary_correction_communication_bounds
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization.qudit_decoded_weyl_branches_and_corrections
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization.qudit_fixed_width_message_encoding
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization.qudit_instrument_identity_and_conditional_recovery
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization.qudit_kraus_completeness_and_corrected_branch
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization.qudit_program_well_formed_and_leaf_costs
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization.qudit_reference_branch_scaling_and_recovery
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization.qudit_resource_normalized_and_weyl_gates_unitary
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.QuditGeneralization.qutrit_and_one_dimensional_teleportation_examples
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.exists_qudit_orthonormal_families_of_fixed_corrections
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.orthonormal_pair_resource_has_mixed_marginals
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.orthonormal_pair_resource_unitary_corrections
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.pure_qubit_resource_form_of_four_fixed_corrections
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.pure_qubit_resource_form_of_mixed_marginal
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.pure_qudit_resource_max_entangled_of_fixed_corrections
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.qubit_mixed_marginal_of_four_fixed_corrections
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.qudit_correction_is_unitary_and_recovers_of_max_entangled
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.qudit_max_entangled_resource_iff_mixed_marginal
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.qudit_max_entangled_resource_unitary_corrections
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.qudit_max_entangled_teleportation_resource_characterization
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.ResourceCharacterization.qudit_mixed_marginal_of_fixed_corrections
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.bell_corrected_branch_mass_and_identity_channel
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.bell_decode_unitary_and_branch_operators
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.bell_density_operator_conditional_recovery
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.bell_outcome_two_bit_message_encoding
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.bell_pauli_correction_mul_kraus_eq_half_identity
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.bell_program_branch_eq_corrected_instrument_branch
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.bell_reference_branch_scaling_and_recovery
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.bell_resource_and_preparation_frame
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.singlet_to_bell_convention_branch_bridge
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.uncorrected_bell_density_operator_maximally_mixed
#guard_msgs (drop info) in #check Qatlib.Papers.QTeleport93.MainResults.SpinHalfTeleport.uncorrected_teleportation_depolarizing
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCA14.FeatureReadout.qpca_evolution_eigenvectors_sampling_and_learning
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.classical_phase_marking_distinction_query_lower_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.classical_phase_marking_oracle_separation_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.density_matrix_epsilon_net_cardinality_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.local_hamiltonian_gap_under_locality_doubling_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.local_hamiltonian_qpcp_membership_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.multiprover_qpcp_in_qma_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.qma_and_composition_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.qpcp_acceptance_approximated_by_local_energy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.qpcp_acceptance_eq_one_sub_local_energy_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.qpcp_fixed_hamiltonian_acceptance_approximation_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.qpcp_proof_discretization_threshold_loss_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.qpcp_same_proof_repetition_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.qpcp_simulation_with_quarter_gap_loss_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.quantum_marking_distinction_query_lower_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.quantum_marking_oracle_separation_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.single_prover_qpcp_repetition_error_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.single_query_qpcp_in_qcma_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.subsampled_hamiltonian_gap_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.weighted_energy_estimation_identity_statement
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.weighted_energy_sub_abs_le_of_perturbation
#guard_msgs (drop info) in #check Qatlib.Papers.QuantumPCPs25.MainResults.Model.weighted_rejection_eq_one_sub_energy
#guard_msgs (drop info) in #check Qatlib.Papers.RandCertLiu25.MainResults.collision_union_probability_lower_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RandCertLiu25.MainResults.exists_adjacent_grid_thresholds_with_expectation_gap_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RandCertLiu25.MainResults.exists_rational_threshold_with_tail_gap_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RandCertLiu25.MainResults.heavy_hitter_yes_expectation_lower_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RandCertLiu25.MainResults.lxeb_heavy_hitter_mass_lower_bound_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RandCertLiu25.MainResults.threshold_acceptance_probability_bounds_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RepMultiplic25.MainResults.SytCore.long_row_or_column_of_polynomial_dimension_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RepMultiplic25.MainResults.SytCore.tableaux_dimension_bounds_of_aft_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RepMultiplic25.MainResults.SytCore.tableaux_dimension_growth_of_large_durfee_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RepMultiplic25.MainResults.SytCore.tableaux_dimension_ratio_of_positive_lr_coefficient_statement
#guard_msgs (drop info) in #check Qatlib.Papers.RiemannQITE25.MainResults.GateCount.dbqite_entangling_and_phase_gate_counts_statement
#guard_msgs (drop info) in #check Qatlib.Papers.SparseUnitary09.MainResults.ContainedModels.permutation_gate_family_contained_in_sparse_unitaries
#guard_msgs (drop info) in #check Qatlib.Papers.SparseUnitary09.MainResults.ContainedModels.qtm_window_and_sparse_permutation_containment
#guard_msgs (drop info) in #check Qatlib.Papers.SparseUnitary09.MainResults.ContainedModels.qtm_window_simulation_by_phi3
#guard_msgs (drop info) in #check Qatlib.Papers.SparseUnitary09.MainResults.ContainedModels.walk_shift_permutation_family_contained_in_sparse_unitaries
#guard_msgs (drop info) in #check Qatlib.Papers.SparseUnitary09.MainResults.Dilation.unitary_dilation_evolution_implements_with_ancilla_flip
#guard_msgs (drop info) in #check Qatlib.Papers.SparseUnitary09.MainResults.Model.sparse_realizable_iff_unitary_realizable_poly_steps
#guard_msgs (drop info) in #check Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.CoherentVariableTimeExt.exists_clean_paid_word_for_coherent_prefix
#guard_msgs (drop info) in #check Qatlib.Papers.VarTimeAmpAmp10.VTAAAlgorithm.StoppedHistoryMoment.stopped_history_decomposition_moment_and_resources

#eval IO.println "PUBLIC_DECLARATION_CONSUMERS_OK declarations=379"
