/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CopyEvolution.SelfTomography.QpcaDefs
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
# Stage-B copy-based QPCA guarantees

This module assembles the stage-B QPCA propositions from copy-evolution results. The three
theorems cover legal loading and simulation precision, self-tomography and Gram density
operators, and finite-copy training-set discrimination with explicit sign-error and resource
formulas.

The mathematical background is described in [LloydMohseniRebentrost2014].

## Main statements

* `stageB_copy_qpca_clause16`: loading, simulation, and QPE resources.
* `stageB_copy_qpca_clause17`: self-tomography and Gram-state guarantees.
* `stageB_copy_qpca_clause19`: finite-copy discrimination guarantees.

## References

* [Lloyd, Mohseni, and Rebentrost, 2014][LloydMohseniRebentrost2014]
-/

set_option backward.isDefEq.respectTransparency false

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
open Qatlib.Concepts.CopyEvolution.SelfTomography
open scoped ComplexOrder BigOperators Classical Matrix.Norms.L2Operator

/-- Establishes `StageBCopyQpcaClause16`, combining legal loading, copy-evolution precision, and
QPE resource counts. -/
theorem stageB_copy_qpca_clause16 : StageBCopyQpcaClause16 := by
  refine ⟨fun hg ψ => legal_qram_preserves_address hg ψ,
          fun hg ψ => legal_qram_target_bounds hg ψ,
          fun hg => legal_qram_involutive hg,
          qRAMImplementation_of_effective,
          fun n g hg => finiteCodeMatrix_unitary n g hg,
          fun n b => rfl,
          copy_state_dependent_fresh_global_error,
          supNormTightCopyBudget,
          commutingCopyExactTightness,
          fun D r T k ρ t X hρ hX ht =>
            copy_precision_same_protocol_and_four_resource_counts D r T k ρ t X hρ hX ht,
          copy_qpe_same_path_fresh_resource_counts,
          copyQPEFixedMacros_eq⟩

/-- Establishes `StageBCopyQpcaClause17`, including self-tomography, QPE positivity and trace
preservation, restricted low-rank evolution, and Gram density operators
[LloydMohseniRebentrost2014]. -/
theorem stageB_copy_qpca_clause17 : StageBCopyQpcaClause17 := by
  refine ⟨epsilonCubedSelfTomography,
          selfTomographyOnGridOutput,
          copyQPEProgram_positive_trace,
          copyQPEQuery_positive_trace,
          copyQPELabelMass_sum,
          lowRankExponentiationRestricted,
          fun r d ψ hψ w hw hsumw => gramFirstRegisterDensity r d ψ hψ w hw hsumw⟩

/-- Establishes `StageBCopyQpcaClause19`, including training-set and Helstrom discrimination,
the sign-error budget, and two-species QPE resources [LloydMohseniRebentrost2014]. -/
theorem stageB_copy_qpca_clause19 : StageBCopyQpcaClause19 := by
  refine ⟨trainingSetFiniteDiscrimination,
          fun d m φ hφ hm => pureStateMixture_density d m φ hφ hm,
          finiteCopyHelstromDiscrimination,
          fun M n γ => rfl,
          twoSpeciesQPEResources_same_path⟩

end Qatlib.Concepts.CopyEvolution.SelfTomography
