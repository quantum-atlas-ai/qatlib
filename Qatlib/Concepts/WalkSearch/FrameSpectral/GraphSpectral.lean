/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.FrameSpectral.GraphSpectralDefs
import Qatlib.Concepts.GraphStationary.StationaryLaw
import Qatlib.Concepts.GraphLaplacian.LaplacianPsd.GraphLaplacian
import Qatlib.Concepts.DirichletForm.EnergyIdentity
import Qatlib.Concepts.GraphCutTrial.CutEnergyBound
import Qatlib.Concepts.GraphEnergy.ZeroEnergy.GraphEnergyKernelConsumers
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainQuan
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGroverQuan
import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4WalkOracleQuan
import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchCompilation
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option linter.unusedVariables false

open Qatlib.Concepts.WalkSearch.ProjectorCS

namespace Qatlib.Concepts.WalkSearch.FrameSpectral

open Matrix
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib.Concepts.GraphStationary.StationaryLaw
open Qatlib.Concepts.DirichletForm.EnergyIdentity
open Qatlib.Concepts.GraphCutTrial.CutEnergyBound
open Qatlib.Concepts.GraphEnergy.ZeroEnergy
open Qatlib
open Qatlib.Concepts.WalkSearch.MnrsAmplify
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.WalkDetector
open Qatlib
open Qatlib.Concepts.WalkSearch.Th4Expander
open scoped Classical BigOperators Matrix.Norms.L2Operator

theorem stageA_graph_spectral_clause2 : Clause13Spec := by
  refine ⟨fun (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) =>
            detailed_balance G x y,
          fun (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (x : V) =>
            kernel_sum G x,
          fun (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) =>
            g1 V G f,
          fun (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ) =>
            edge_constant_iff_reachable_constant G f,
          ⟨twoDisjointEdges_energy_eq_zero, twoDisjointEdges_not_constant⟩,
          fun (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) =>
            variance_mass G S,
          fun (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (P : I → I → ℝ) (S : Finset I) (δ : ℝ) hδ hδ1 hP =>
            unmarked_principal_gram_and_gap I P S δ hδ hδ1 hP⟩

theorem stageA_graph_spectral_clause3 : Clause14Spec := by
  refine ⟨szegedyTheorem4ExpanderChain,
          szegedyTheorem4ExpanderGrover,
          szegedyTheorem4WalkOracle,
          graph_bit_access_zero_workspace⟩

end Qatlib.Concepts.WalkSearch.FrameSpectral
