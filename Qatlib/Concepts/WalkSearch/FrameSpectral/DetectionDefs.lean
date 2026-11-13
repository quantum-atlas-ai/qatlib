/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.WalkSearch.Spectral.SzegedySpectral
import Qatlib.Concepts.WalkSearch.Detection.CorrectedSzegedyDetector
import Qatlib.Concepts.WalkSearch.ProjectorCS
import Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNormStat
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderChainStat
import Qatlib.Concepts.WalkSearch.Th4Expander.SzegedyTheorem4ExpanderGroverStat
import Qatlib.Concepts.WalkSearch.WalkDetector.SzegedyTheorem4WalkOracleStat
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.WalkSearchDefs
import Qatlib.Concepts.WalkSearch.MnrsAmplify.WalkSearchCompilationDefs
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3
import Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Proposition3
import Qatlib.Concepts.WalkSearch.FrameSpectral.WalkSpectralDefs

/-!
# Source detection endpoint specifications

The propositions `Clause20Spec`, `Clause21Spec`, and `Clause22Spec` collect the requirements
used to connect graph access, source geometry, corrected detection, and quantum walk search.
They retain the explicit gap, marked fraction, and access hypotheses needed by the component
results. The quantum walk spectral framework is developed in [Szegedy2004].

## Main statements

* `Clause20Spec`: Graph setup, reachable dynamics, and source detection requirements.
* `Clause21Spec`: Empty marked set obstructions and amplification requirements.
* `Clause22Spec`: Source norm, endpoint, and spectral gap requirements.

## References

* [Szegedy, 2004][Szegedy2004]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.WalkSearch.TwoLevelLower

open Qatlib.Concepts.AEMeanReadout.LocalAEBackend
open Qatlib.Concepts.WalkFind.UniformThree
open Qatlib.Concepts.WalkSearch.ProjectorCS
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

/-- The conjunction of graph setup and reachable space laws, the countable exact gate cover
obstruction, expander and graph access results, corrected detection with resource counts,
local amplification, and the interior norm correspondence. -/
def Clause20Spec : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (S : Finset I),
    IsTransitionMatrix P →
      GraphSetupAccount P S ∧
      WalkPreservesReachableSpan P ∧
      ReachableTwoPlaneLaw P) ∧
  noCountableExactGateCover ∧
  SzegedyTheorem4ExpanderChain ∧
  SzegedyTheorem4ExpanderGrover ∧
  SzegedyTheorem4WalkOracle ∧
  (∀ (n d : ℕ) (hdn : d ≤ n) (adj : Fin n → Fin n → Bool) (M : Fin n → Bool),
    HasGraphBitAccess n d hdn adj M) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (L : ℕ) (j : I)
      (U : Matrix (I × I) (I × I) ℂ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ →
    0 < ε → ε ≤ markedFraction S →
    0 < L → 1000 / Real.sqrt (δ * ε) ≤ (L : ℝ) →
    U ∈ unitaryGroup (I × I) ℂ →
    (∀ i, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i) →
    (1 / 32 : ℝ) ≤ (∑ k : Fin L, detectionProbability U S j (k.val + 1)) / (L : ℝ) ∧
    (∀ k : Fin L, (detectionCounts (detectionProgram j (k.val + 1))).1 ≤ 4 * L + 1 ∧
      (detectionCounts (detectionProgram j (k.val + 1))).2.1 ≤ 4 * L + 1 ∧
      (detectionCounts (detectionProgram j (k.val + 1))).2.2 ≤ 4 * L + 2)) ∧
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3.{0} ∧
  Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNorm

/-- The conjunction of empty marked set search obstructions, zero success probability, phase
search accounting, local amplification, the interior norm correspondence, and the specified
corrected detection guarantee. -/
def Clause21Spec : Prop :=
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (Sc Uc Cc bound : ℝ),
    ¬ HasRealElementFind P ∅ Sc Uc Cc bound) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (P : I → I → ℝ) (Sc Uc Cc bound : ℝ),
    ¬ HasWalkFind P ∅ Sc Uc Cc bound) ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I]
      (P : I → I → ℝ) (Mq k t : ℕ),
    walkFindSuccessProb (SzegedyWalk P) (detectionInitial P)
      (edgeMarkedSet (∅ : Finset I)) Mq k t = 0) ∧
  (∀ (M k t : ℕ), 2 ≤ M → phaseSearchLedger M k t = (2 * k * t * (M - 1), t, 1)) ∧
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3.{0} ∧
  Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNorm ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (L : ℕ) (j : I)
      (U : Matrix (I × I) (I × I) ℂ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ →
    0 < ε → ε ≤ markedFraction S →
    0 < L → 1000 / Real.sqrt (δ * ε) ≤ (L : ℝ) →
    U ∈ unitaryGroup (I × I) ℂ →
    (∀ i, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i) →
    (1 / 32 : ℝ) ≤ (∑ k : Fin L, detectionProbability U S j (k.val + 1)) / (L : ℝ))

/-- The conjunction of the interior norm and endpoint properties, unmarked discriminant bounds,
uniqueness of the unit singular value under the stated Markov chain hypotheses, and the
accompanying amplification and detection requirements. -/
def Clause22Spec : Prop :=
  Qatlib.Concepts.WalkSearch.TauEmbedding.SzegedyTheorem5InteriorNorm ∧
  BipartiteTauEndpointVanishes ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I] (P : I → I → ℝ) (S : Finset I) (δ : ℝ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ →
      Qatlib.Concepts.Execution.WorkspaceCP.IsIsometry (unmarkedRowFrame P S) ∧
      (unmarkedRowFrame P S)ᴴ * (SwapGate : Matrix (I × I) (I × I) ℂ) * (unmarkedRowFrame P S) = unmarkedPrincipal P S ∧
      ‖unmarkedPrincipal P S‖ ≤ 1 - δ * markedFraction S) ∧
  (∀ (X : Type) [Fintype X] [DecidableEq X] [Nonempty X] (P : Matrix X X ℝ) (π : X → ℝ),
    P.IsIrreducible →
    (∀ x, ∑ y, P x y = 1) →
    (∀ x, 0 < P x x) →
    (∀ x, 0 ≤ π x) →
    (∑ x, π x) = 1 →
    (∀ y, ∑ x, π x * P x y = π y) →
    ∃! k : ℕ,
      (Matrix.toEuclideanLin (mnrsDiscriminant P π)).singularValues k = 1) ∧
  Qatlib.Concepts.AEMeanReadout.LocalAEBackend.Theorem3.{0} ∧
  (∀ (I : Type) [Fintype I] [DecidableEq I] [Nonempty I]
      (P : I → I → ℝ) (S : Finset I) (δ ε : ℝ) (L : ℕ) (j : I)
      (U : Matrix (I × I) (I × I) ℂ),
    0 < δ → δ ≤ 1 → SymmetricChainGap P δ →
    0 < ε → ε ≤ markedFraction S →
    0 < L → 1000 / Real.sqrt (δ * ε) ≤ (L : ℝ) →
    U ∈ unitaryGroup (I × I) ℂ →
    (∀ i, U *ᵥ TensorState (Qatlib.Foundations.PureStateMath.Ket i) (Qatlib.Foundations.PureStateMath.Ket j) = SzegedyIsometry P *ᵥ Qatlib.Foundations.PureStateMath.Ket i) →
    (1 / 32 : ℝ) ≤ (∑ k : Fin L, detectionProbability U S j (k.val + 1)) / (L : ℝ))

end Qatlib.Concepts.WalkSearch.FrameSpectral
