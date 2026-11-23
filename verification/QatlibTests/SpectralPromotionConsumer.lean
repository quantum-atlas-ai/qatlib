/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

import Qatlib.Papers.SpectralGap11.MainResults.AmplifiedRegister
import Qatlib.Papers.SpectralGap11.MainResults.EigenReduction
import Qatlib.Papers.SpectralGap11.MainResults.GapReduction
import Qatlib.Papers.SpectralGap11.MainResults.GroundLift
import Qatlib.Papers.SpectralGap11.MainResults.InvariantBlocks
import Qatlib.Papers.SpectralGap11.MainResults.InvariantLift
import Qatlib.Papers.SpectralGap11.MainResults.KernelBridge
import Qatlib.Papers.SpectralGap11.MainResults.KernelLift
import Qatlib.Papers.SpectralGap11.MainResults.Nullity
import Qatlib.Papers.SpectralGap11.MainResults.SearchFamily
import Qatlib.Papers.SpectralGap11.MainResults.SimulationCost
import Qatlib.Papers.SpectralGap11.MainResults.SimulationWord
import Qatlib.Papers.SpectralGap11.MainResults.SourceExamples
import Qatlib.Papers.SpectralGap11.MainResults.SourceLemma2TrotterSimulation
import Qatlib.Papers.SpectralGap11.MainResults.SourceTheorem1GapAmplification
import Qatlib.Papers.SpectralGap11.MainResults.SpectrumLift
import Qatlib.Papers.ProdFormSpec21.MainResults.PhaseErrorBudget
import Qatlib.Papers.SparseHam05.MainResults.OneSparseDecomposition
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.FlowEnergy
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.GraphEdges
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.GraphSpectrum
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairAdjoint
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairBridge
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairData
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairEnergy
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairFlow
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PairIsoper
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PathBridge
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PathEdges
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.PathModel
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.RayleighMin
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.RepairModel
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.SectorKernel
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.SectorPredicates
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.SectorSpectralBounds
import Qatlib.Papers.KhovanovHom25.MainResults.Section8.WeightedForm
import Qatlib.Papers.LogConcave22.MainResults.Markov.EffectiveGap

import Mathlib.Tactic.NormNum

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

/-! Ordinary-module consumers for the Stage #604 spectral mathematics batch. -/

#check Qatlib.Papers.SpectralGap11.MainResults.doubled_register_gap_and_nullity
#check Qatlib.Papers.SparseHam05.MainResults.one_sparse_decomposition_of_hermitian
#check Qatlib.Papers.ProdFormSpec21.MainResults.step_count_ge_of_step_size_budget
#check Qatlib.Papers.KhovanovHom25.MainResults.repair_cost_decomposition_and_bound
#check Qatlib.Papers.LogConcave22.MainResults.Markov.effective_gap
