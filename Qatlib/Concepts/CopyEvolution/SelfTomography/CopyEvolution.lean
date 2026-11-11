/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.CopyEvolutionCompletionModelCore
import Qatlib.Concepts.CopyEvolution.SelfTomography.EpsilonCubedSelfTomographyQuan
import Qatlib.Concepts.CopyEvolution.SelfTomography.SelfTomographyOnGridOutputQuan
import Qatlib.Concepts.CopyEvolution.CopyExponent.LowRankExponentiationRestrictedQuan
import Qatlib.Concepts.CopyEvolution.CopyExponent.SupNormTightCopyBudgetQuan
import Qatlib.Concepts.CopyEvolution.CopyExponent.StateDependentCopyPrecisionQuan
import Qatlib.Concepts.CopyEvolution.CopyExponent.CommutingCopyExactTightnessQuan
import Qatlib.Concepts.CopyEvolution.Discriminate.FiniteCopyHelstromDiscriminationQuan
import Qatlib.Concepts.CopyEvolution.Discriminate.TrainingSetFiniteDiscriminationQuan
import Qatlib.Concepts.CopyEvolution.SelfTomography.GramFirstRegisterDensityQuan

/-!
# Copy evolution and self-tomography

This module assembles the copy-evolution guarantees into `StageACopyEvolutionPaidWalk` and
`StageACopyEvolutionClause16`. The results combine legal QRAM loading, explicit resource
accounting, fresh-copy simulation bounds, spectral self-tomography, Gram-state density
operators, and finite-copy discrimination.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `stageA_copy_evolution_walkGoal`: the paid loading and copy-evolution specification.
* `stageA_copy_evolution_clause16`: the self-tomography and discrimination specification.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.LinearLearning.ConcisePipeline

open Qatlib.Concepts.FreshCopyExec.QpeConsumers
open Qatlib.Foundations.BornMetrics.EventProbability
open Qatlib.Concepts.GateVocabulary.FiniteGateDescription
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LinearCombination Qatlib.Concepts.WalkFind.QRAMModel
open Qatlib.Concepts.CopyEvolution.CopyExponent
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.CopyEvolution.Discriminate

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Qatlib.Concepts.CopyEvolution.SelfTomography

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.QueryWordCore.AdjointCircuits
open Qatlib
open Qatlib.Concepts.CoherentSim.CoherentOAA.SignalProcessing
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.SignalPrimitive.PhaseFrontend
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.PhaseGeometry.Phase Qatlib.Concepts.QspSimulation.WordModel
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
open Qatlib
open Qatlib.Concepts.NonNormalSpec.ResolventWord
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.CopyEvolution.SelfTomography
open Qatlib
open Qatlib.Concepts.WalkFind.GroverInterp
open Qatlib
open Qatlib.Concepts.WalkFind.UniqueCollision
open Qatlib.Concepts.WalkFind.WalkSpectrum
open Qatlib.Concepts.CopyEvolution.SelfTomography
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

/-- Establishes `StageACopyEvolutionPaidWalk`, combining legal loading and resource accounting
with fresh-copy error bounds and exact partial-swap identities. -/
theorem stageA_copy_evolution_walkGoal : StageACopyEvolutionPaidWalk := by
  refine ⟨fun hg ψ => legal_qram_preserves_address hg ψ,
          fun hg ψ => legal_qram_target_bounds hg ψ,
          fun hg => legal_qram_involutive hg,
          codeBits_le_description_length,
          sourceWord_description_budget,
          qRAMImplementation_of_effective,
          fun n g hg => finiteCodeMatrix_unitary n g hg,
          fun n b => rfl,
          copy_state_dependent_fresh_global_error,
          supNormTightCopyBudget,
          commutingCopyExactTightness,
          fun D r T k ρ t X hρ hX ht =>
            copy_precision_same_protocol_and_four_resource_counts D r T k ρ t X hρ hX ht,
          copy_qpe_same_path_fresh_resource_counts,
          copyQPEFixedMacros_eq,
          copy_zero_projector_one_step,
          copy_zero_projector_repeated_coherence,
          copy_noncommuting_mixed_consumer,
          copy_entangled_reference_swap_consumer,
          fun ρ hρ σ => copy_zero_and_full_swap_limits ρ hρ σ⟩

/-- Establishes `StageACopyEvolutionClause16`, including self-tomography, positivity and trace
preservation, Gram-state density operators, and finite-copy discrimination
[LloydMohseniRebentrost2014]. -/
theorem stageA_copy_evolution_clause16 : StageACopyEvolutionClause16 := by
  refine ⟨epsilonCubedSelfTomography,
          selfTomographyOnGridOutput,
          copyQPEProgram_positive_trace,
          copyQPEQuery_positive_trace,
          copyQPELabelMass_sum,
          lowRankExponentiationRestricted,
          fun r d ψ hψ w hw hsumw => gramFirstRegisterDensity r d ψ hψ w hw hsumw,
          trainingSetFiniteDiscrimination,
          fun d m φ hφ hm => pureStateMixture_density d m φ hφ hm,
          finiteCopyHelstromDiscrimination,
          fun M n γ => rfl⟩

end Qatlib.Concepts.CopyEvolution.SelfTomography
