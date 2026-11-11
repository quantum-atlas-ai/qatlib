/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

/-!
# Slack Promise

Slack Promise constructions and identities for Query Complexity.
-/
open Qatlib Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open scoped BigOperators Classical ComplexOrder
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
/-- Construction for slack Constructor Promise in the slack promise model. -/
def slackConstructorPromise {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (τ : ℝ) (r0 : Fin D) : Prop :=
  ∃ G : Finset (Path P),
    5/8 ≤ (∑ p∈G,(preparedLaw (fun mode => unitaryChannel (O mode) (hO mode)) S r0 P).prob p) ∧
    ∀ p∈G,BlockEncoding T (wordMatrix O (words p)) (basisFrame (φ p)) (basisFrame (φ p)) 1 (τ/100)


end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
