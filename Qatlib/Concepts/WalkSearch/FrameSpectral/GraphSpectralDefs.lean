/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.GraphStationary.StationaryLaw
import Qatlib.Concepts.GraphLaplacian.LaplacianPsd.GraphLaplacian
import Qatlib.Concepts.DirichletForm.EnergyIdentity
import Qatlib.Concepts.GraphCutTrial.CutEnergyBound
import Qatlib.Concepts.GraphEnergy.ZeroEnergy.GraphEnergyKernelConsumers
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainStat
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGroverStat
import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4WalkOracleStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.WalkSearchDefs

/-!
# Graph spectral specifications

This module defines two bundles of graph and walk spectral statements. `Clause13Spec` records
reversible kernel identities, energy and variance formulas, a disconnected graph example, and
the unmarked principal bound; `Clause14Spec` records expander and graph access requirements. The
quantum walk spectral framework is developed in [Szegedy2004].

## Main statements

* `Clause13Spec`: Graph identities and unmarked principal spectral bounds.
* `Clause14Spec`: Expander search and graph bit access requirements.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.WalkSearch.ProjectorCS
open Qatlib.Concepts.WalkSearch.TwoLevelLower

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
open Qatlib
open Qatlib
open Qatlib.Concepts.WalkSearch.WalkDetector
open Qatlib
open Qatlib.Concepts.WalkSearch.Th4Expander
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- The conjunction of detailed balance and stochasticity for the graph kernel, Dirichlet energy
and reachability identities, a disconnected zero energy example, the centered indicator
variance formula, and the unmarked frame norm estimate. -/
def Clause13Spec : Prop :=
  (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V),
    stationary G x * kernel G x y = stationary G y * kernel G y x) ∧
  (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (x : V),
    (∑ y, kernel G x y) = 1) ∧
  (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ),
    energy G f = (1 / 2 : ℝ) * ∑ x, ∑ y, stationary G x * kernel G x y * (f x - f y) ^ 2) ∧
  (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℝ),
    (∀ x y, G.Adj x y → f x = f y) ↔ ∀ x y, G.Reachable x y → f x = f y) ∧
  (energy twoDisjointEdges (fun x : Fin 4 => if x.val ≤ 1 then (0 : ℝ) else 1) = 0 ∧
    ¬ ∃ c : ℝ, ∀ x : Fin 4, (if x.val ≤ 1 then (0 : ℝ) else 1) = c) ∧
  (∀ (V : Type) [Fintype V] [DecidableEq V] [Nonempty V] (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V),
    variance G (centeredIndicator G S) = mass G S * (1 - mass G S)) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (P : I → I → ℝ) (S : Finset I) (δ : ℝ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ →
      IsIsometry (unmarkedRowFrame P S) ∧
      (unmarkedRowFrame P S)ᴴ * (SwapGate : Matrix (I × I) (I × I) ℂ) * (unmarkedRowFrame P S) = unmarkedPrincipal P S ∧
      ‖unmarkedPrincipal P S‖ ≤ 1 - δ * markedFraction S)

/-- The conjunction of Szegedy's expander chain, Grover, and walk oracle statements together
with existence of graph bit access for the stated finite graph parameters. -/
def Clause14Spec : Prop :=
  SzegedyTheorem4ExpanderChain ∧
  SzegedyTheorem4ExpanderGrover ∧
  SzegedyTheorem4WalkOracle ∧
  (∀ (n d : ℕ) (hdn : d ≤ n) (adj : Fin n → Fin n → Bool) (M : Fin n → Bool),
    HasGraphBitAccess n d hdn adj M)

end Qatlib.Concepts.WalkSearch.FrameSpectral
