/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.DetectionDefs
import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkSpectralBounds
import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNormQuan
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainQuan
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGroverQuan
import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4WalkOracleQuan
import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchCompilation
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Theorem3
import Qatlib.Concepts.WalkSearch.MnrsAmplify.Proposition3
import Qatlib.Concepts.WalkFind.UniformThree.PhaseReflectionSearch
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TauEmbedding
open Qatlib.Concepts.WalkSearch.Detection

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.WalkDetector
open Qatlib
open Qatlib.Concepts.WalkSearch.Th4Expander
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem stageB_szegedy_source_detection_clause5 : Clause20Spec := by
  refine ⟨fun I _ _ _ P S hP => ⟨graph_setup P S hP, reachable_span_invariant P hP, reachable_two_plane P hP⟩,
          no_exact_gate_cover,
          szegedyTheorem4ExpanderChain,
          szegedyTheorem4ExpanderGrover,
          szegedyTheorem4WalkOracle,
          graph_bit_access_zero_workspace,
          fun I _ _ _ P S δ ε L j U hδ hδ1 hP hε hεp hL hscale hU hp =>
            corrected_szegedy_actual_random_power_detection I P S δ ε L j U hδ hδ1 hP hε hεp hL hscale hU hp,
          mnrs_search_theorem_three_abstract,
          szegedyTheorem5InteriorNorm⟩

theorem stageB_szegedy_source_detection_clause6 : Clause21Spec := by
  refine ⟨fun I _ _ _ P Sc Uc Cc bound => not_empty_find P Sc Uc Cc bound,
          fun I _ _ P Sc Uc Cc bound => not_empty_walk_find P Sc Uc Cc bound,
          fun I _ _ P Mq k t => by simp [walkFindSuccessProb, edgeMarkedSet, MeasureProb],
          fun M k t hM => phase_search_fresh_access_ledger M k t hM,
          mnrs_search_theorem_three_abstract,
          szegedyTheorem5InteriorNorm,
          fun I _ _ _ P S δ ε L j U hδ hδ1 hP hε hεp hL hscale hU hp =>
            (corrected_szegedy_actual_random_power_detection I P S δ ε L j U hδ hδ1 hP hε hεp hL hscale hU hp).1⟩

theorem stageB_szegedy_source_detection_clause7 : Clause22Spec := by
  refine ⟨szegedyTheorem5InteriorNorm,
          bipartiteTauEndpointVanishes_proof,
          fun I _ _ _ P S δ hδ hδ1 hP =>
            unmarked_principal_gram_and_gap I P S δ hδ hδ1 hP,
          search_via_quantum_walk_proposition3,
          mnrs_search_theorem_three_abstract,
          fun I _ _ _ P S δ ε L j U hδ hδ1 hP hε hεp hL hscale hU hp =>
            (corrected_szegedy_actual_random_power_detection I P S δ ε L j U hδ hδ1 hP hε hεp hL hscale hU hp).1⟩

end Qatlib.Concepts.WalkSearch.FrameSpectral
