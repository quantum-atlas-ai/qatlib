/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSourceSchedule
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchBudget
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchTimeout
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchQueryCost

/-!
# Statement of the unknown-count search family

Defines `Theorem3SourceFamily`, the search guarantee for every growth factor `1 < l < 4 / 3`. It
gives uniform marked output, separate expected iteration and paid costs, finite-budget
correctness, and a timeout estimate using the coefficient `l / (l - 1)`. For the quantum-search
analysis, see [BoyerEtAl1998].

## Main statements

* `Theorem3SourceFamily`: The proposition collecting termination, uniform marked output,
  explicit expected iteration, Boolean-query, and lookup bounds, finite-budget correctness, and
  uniform geometric timeout guarantees for every schedule factor `1 < l < 4 / 3`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Concepts.SearchStopping.UnknownCount

open scoped BigOperators
universe u

/-- The proposition collecting termination, uniform marked output, explicit expected iteration,
Boolean-query, and lookup bounds, finite-budget correctness, and uniform geometric timeout
guarantees for every schedule factor `1 < l < 4 / 3`. -/
def Theorem3SourceFamily : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    ∀ l : ℝ, 1 < l → l < 4 / 3 →
    let sizes := SourceSizes (Fintype.card I) l
    (∀ A : Finset I, 0 < A.card →
      HasSum (TerminalMass A sizes) 1 ∧
      (∀ x : TerminalTrace I sizes, 0 ≤ TerminalMass A sizes x ∧
        (TerminalOutput x ∉ A → TerminalMass A sizes x = 0)) ∧
      (∀ i : I, HasSum (fun x : TerminalTrace I sizes =>
        if TerminalOutput x = i then TerminalMass A sizes x else 0)
        (if i ∈ A then 1 / (A.card : ℝ) else 0)) ∧
      (∃ q : ℝ, HasSum (fun x : TerminalTrace I sizes =>
        TerminalMass A sizes x * (TerminalCost sizes x : ℝ)) q ∧
        0 ≤ q ∧ q ≤ (l / 4) * (1 / (l - 1) + 4 / (4 - 3 * l)) *
          Real.sqrt ((Fintype.card I : ℝ) / A.card)) ∧
      (∃ q : ℝ, HasSum (fun x : TerminalTrace I sizes =>
        TerminalMass A sizes x * (TerminalBooleanQueries sizes x : ℝ)) q ∧
        0 ≤ q ∧ q ≤ (1 + 3 * (l / 4 * (1 / (l - 1) + 4 / (4 - 3 * l)))) *
          Real.sqrt ((Fintype.card I : ℝ) / A.card)) ∧
      (∃ q : ℝ, HasSum (fun x : TerminalTrace I sizes =>
        TerminalMass A sizes x * (SourceLookupClock sizes x : ℝ)) q ∧
        0 ≤ q ∧ q ≤ (1 + 4 * (l / 4 * (1 / (l - 1) + 4 / (4 - 3 * l)))) *
          Real.sqrt ((Fintype.card I : ℝ) / A.card))) ∧
    (∀ (A : Finset I) (stage budget : ℕ),
      (∀ out, 0 ≤ FiniteBudgetMass A sizes stage budget out) ∧
      (∑ out : Option I, FiniteBudgetMass A sizes stage budget out) = 1 ∧
      ∀ i : I, i ∉ A → FiniteBudgetMass A sizes stage budget (some i) = 0) ∧
    (∀ stage budget : ℕ, FiniteBudgetMass (∅ : Finset I) sizes stage budget none = 1) ∧
    (∃ K : ℕ, (K : ℝ) ≤ l / (l - 1) * Real.sqrt (Fintype.card I) ∧ ∀ k : ℕ,
      (WorstPrefixIterations sizes (K+k) : ℝ) ≤
        (l / (l - 1) + (k : ℝ)) * Real.sqrt (Fintype.card I) ∧
      ∀ A : Finset I, 0 < A.card → RetryReach A sizes (K+k) ≤ (3 / 4 : ℝ)^k)

end Qatlib.Concepts.SearchStopping.UnknownCount
