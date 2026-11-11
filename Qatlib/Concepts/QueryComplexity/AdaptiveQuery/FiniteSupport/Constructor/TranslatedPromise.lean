/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.ConstructorPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

/-!
# Translated Promise

The full finite record translation satisfies `translated_constructorPromise` without requiring an injective answer map.
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
/-- The full finite record translation satisfies `translated_constructorPromise` without requiring an injective answer map. -/
theorem translated_constructorPromise {D R R' : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (decode : ℝ → Fin R' → Fin R)
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R')
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (τ : ℝ) (r0 : Fin D)
    (hc : constructorPromise O hO (fun a => decode a (S a)) P words φ T τ r0) :
    constructorPromise O hO S (translateAnswerMap decode P)
      (fun q => words (translatedPath decode P q))
      (fun q => φ (translatedPath decode P q)) T τ r0 := by
  rcases hc with ⟨G,hG,hgood⟩
  refine ⟨Finset.univ.filter (fun q => translatedPath decode P q∈G),?_,?_⟩
  · change 2/3 ≤ ∑ q∈Finset.univ.filter (fun q => translatedPath decode P q∈G),
      (pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
        (translateAnswerMap decode P) (basisDensity r0) (basisDensity_pos r0) (basisDensity_trace_re r0)).prob q
    rw [translated_event]
    exact hG
  · intro q hq
    exact hgood _ (Finset.mem_filter.mp hq).2


end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
