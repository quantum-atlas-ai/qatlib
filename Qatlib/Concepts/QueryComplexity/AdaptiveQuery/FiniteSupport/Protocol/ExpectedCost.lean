/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.BudgetTruncation
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.PreparedRepeat
import Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol.AnswerTransport

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Expected Cost

Each occurrence is charged, even if its matrix effect cancels.
-/

open Qatlib Matrix
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open scoped BigOperators Classical ComplexOrder
set_option autoImplicit false
set_option maxRecDepth 2048
noncomputable section

namespace Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
open Qatlib Matrix
open scoped BigOperators Classical ComplexOrder

/-- Each occurrence is charged, even if its matrix effect cancels. -/
def pathTotalCost {D R : ℕ} (P : Program D R) (use : Path P → ℕ) (p : Path P) : ℕ :=
  (pathCharge P p).1+use p+(pathCharge P p).2

/-- Construction for expected Cost in the expected cost model. -/
def expectedCost {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r0 : Fin D) (P : Program D R) (use : Path P → ℕ) : ℝ :=
  (preparedLaw O S r0 P).expect (fun p => (pathTotalCost P use p : ℝ))

/-- The unconditional full-path expectation satisfies `expectedCost_nonneg` with all displayed input and cost assumptions. -/
theorem expectedCost_nonneg {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r0 : Fin D) (P : Program D R) (use : Path P → ℕ) : 0 ≤ expectedCost O S r0 P use :=
  Finset.sum_nonneg (fun p _ => mul_nonneg ((preparedLaw O S r0 P).nonneg p) (Nat.cast_nonneg _))

/-- The finite protocol identity or bound `pathTotalCost_caps` holds under exactly the displayed hypotheses. -/
theorem pathTotalCost_caps {D R : ℕ} (P : Program D R) (use : Path P → ℕ) (K : ℕ)
    (p : Path P) (h : pathTotalCost P use p ≤ K) : withinBudget P K K p ∧ use p ≤ K := by
  unfold pathTotalCost at h
  unfold withinBudget
  omega

/-- Cut descriptions use the empty legal word. Complete descriptions over the
use budget also fall back, without removing their constructor record. -/
def truncatedWords {D R : ℕ} (P : Program D R) (words : Path P → List (OutputGate D))
    (K : ℕ) (r : Path (truncateProgram P K K)) : List (OutputGate D) :=
  match finishPath P K K r with
  | none => []
  | some p => if wordQueries (words p) ≤ K then words p else []

/-- Construction for truncated Frame in the expected cost model. -/
def truncatedFrame {D R : ℕ} {I : Type} (P : Program D R) (φ : Path P → I → Fin D)
    (r0 : Fin D) (K : ℕ) (r : Path (truncateProgram P K K)) : I → Fin D :=
  match finishPath P K K r with
  | none => fun _ => r0
  | some p => φ p

/-- The actual truncated finite protocol satisfies `truncatedWords_queries` while retaining its failure paths. -/
theorem truncatedWords_queries {D R : ℕ} (P : Program D R)
    (words : Path P → List (OutputGate D)) (K : ℕ) (r : Path (truncateProgram P K K)) :
    wordQueries (truncatedWords P words K r) ≤ K := by
  unfold truncatedWords
  cases finishPath P K K r with
  | none => exact Nat.zero_le _
  | some p =>
    change wordQueries (if wordQueries (words p) ≤ K then words p else []) ≤ K
    split_ifs with h
    · exact h
    · exact Nat.zero_le _

/-- Classical answer transport preserves the expected total cost exactly.
It is an identity on actual laws for every real reward, not a coupling premise. -/
theorem translated_expectedCost {D R R' : ℕ} (decode : ℝ → Fin R' → Fin R)
    (O : Bool → QuantumChannel D D) (S : ℝ → Fin R') (r0 : Fin D) (P : Program D R)
    (use : Path P → ℕ) :
    expectedCost O S r0 (translateAnswerMap decode P) (fun q => use (translatedPath decode P q))=
      expectedCost O (fun a => decode a (S a)) r0 P use := by
  unfold expectedCost Qatlib.Concepts.MonteCarloMean.FinDistBounds.FinDist.expect preparedLaw
  simp only [pathLaw]
  simpa only [pathTotalCost,translatedPath_charge] using
    translated_weight_sum decode O S P (basisDensity r0) (fun p => (pathTotalCost P use p : ℝ))

/-- The unconditional full-path expectation satisfies `expectedCost_mono` with all displayed input and cost assumptions. -/
theorem expectedCost_mono {D R : ℕ} (O : Bool → QuantumChannel D D) (S : ℝ → Fin R)
    (r0 : Fin D) (P : Program D R) (use use' : Path P → ℕ) (hle : ∀ p,use p ≤ use' p) :
    expectedCost O S r0 P use ≤ expectedCost O S r0 P use' := by
  apply Finset.sum_le_sum
  intro p _
  apply mul_le_mul_of_nonneg_left _ ((preparedLaw O S r0 P).nonneg p)
  have hnat : pathTotalCost P use p ≤ pathTotalCost P use' p := by
    have h := hle p
    unfold pathTotalCost
    omega
  change (pathTotalCost P use p : ℝ) ≤ (pathTotalCost P use' p : ℝ)
  exact Nat.cast_le.mpr hnat


end Qatlib.Concepts.QueryComplexity.AdaptiveQuery.FiniteSupport.Protocol
