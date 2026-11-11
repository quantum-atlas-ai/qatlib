/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor.SlackPromise
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.ExpectedCost

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge
open Qatlib.Concepts.BlockEncoding.EncodingCore

open Qatlib.Foundations.PureStateMath

/-!
# Truncated Promise

The actual truncated finite protocol satisfies `truncated_constructorPromise` while retaining its failure paths.
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
/-- The actual truncated finite protocol satisfies `truncated_constructorPromise` while retaining its failure paths. -/
theorem truncated_constructorPromise {D R : ℕ} {I : Type} [Fintype I] [DecidableEq I]
    (O : Bool → Operator D) (hO : ∀ mode,O mode∈Matrix.unitaryGroup (Fin D) ℂ) (S : ℝ → Fin R)
    (P : Program D R) (words : Path P → List (OutputGate D)) (φ : Path P → I → Fin D)
    (T : Matrix I I ℂ) (τ : ℝ) (r0 : Fin D) (B : ℝ) (K : ℕ)
    (hc : constructorPromise O hO S P words φ T τ r0)
    (hcost : expectedCost (fun mode => unitaryChannel (O mode) (hO mode)) S r0 P
      (fun p => wordQueries (words p)) ≤ B) (hK : 24*B ≤ (K : ℝ)) :
    slackConstructorPromise O hO S (truncateProgram P K K)
      (truncatedWords P words K) (truncatedFrame P φ r0 K) T τ r0 := by
  rcases hc with ⟨G,hG,hgood⟩
  let cost := pathTotalCost P (fun p => wordQueries (words p))
  let E : Path P → Prop := fun p => p∈G ∧ cost p ≤ K
  let Gcut := Finset.univ.filter (fun r => ∃ p,finishPath P K K r=some p ∧ E p)
  refine ⟨Gcut,?_,?_⟩
  · have he := truncate_event (fun mode => unitaryChannel (O mode) (hO mode)) S P K K
      (basisDensity r0) (basisDensity_pos r0) (basisDensity_trace_re r0) E
    have hsets : Finset.univ.filter (fun p => withinBudget P K K p ∧ E p)=
        G.filter (fun p => cost p ≤ K) := by
      ext p
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,E]
      constructor
      · rintro ⟨_,hp,hc⟩
        exact ⟨hp,hc⟩
      · rintro ⟨hp,hc⟩
        exact ⟨(pathTotalCost_caps P _ K p hc).1,hp,hc⟩
    rw [hsets] at he
    change 5/8 ≤ ∑ r∈Gcut,(pathLaw (fun mode => unitaryChannel (O mode) (hO mode)) S
      (truncateProgram P K K) (basisDensity r0) (basisDensity_pos r0) (basisDensity_trace_re r0)).prob r
    rw [he]
    exact retained_good_mass (preparedLaw (fun mode => unitaryChannel (O mode) (hO mode)) S r0 P)
      cost G B K hG hcost hK
  · intro r hr
    rcases (Finset.mem_filter.mp hr).2 with ⟨p,hp,hG,hC⟩
    have hw := (pathTotalCost_caps P _ K p hC).2
    simpa only [truncatedWords,truncatedFrame,hp,hw,ite_true] using hgood p hG



end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Constructor
