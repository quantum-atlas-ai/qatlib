/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.SearchBudget
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchTimeout

/-!
# Statement of corrected unknown-count search guarantees

Defines `Theorem3Corrected`, collecting termination, uniform marked output, and expected costs
for the factor `6 / 5` schedule. It includes finite-budget correctness and a uniform timeout
bound, with separate constants for Grover iterations, Boolean queries, and lookup cost. For the
quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `Theorem3Corrected`: The proposition collecting the factor `6 / 5` search guarantees:
  normalized terminal traces and uniform marked output, expected iteration, Boolean-query, and
  lookup costs bounded by `9 / 2`, `29 / 2`, and `19` times `√(N / t)`, finite-budget
  correctness, and uniform geometric timeout bounds.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.AmplitudeSearch.InterruptMin

namespace Qatlib.Concepts.SearchStopping.UnknownCount
open scoped BigOperators
universe u

/-- The proposition collecting the factor `6 / 5` search guarantees: normalized terminal traces
and uniform marked output, expected iteration, Boolean-query, and lookup costs bounded by `9
/ 2`, `29 / 2`, and `19` times `√(N / t)`, finite-budget correctness, and uniform geometric
timeout bounds. -/
def Theorem3Corrected : Prop :=
  ∀ {I : Type u} [Fintype I] [DecidableEq I], 0 < Fintype.card I →
    let sizes := ExponentialSizes (Fintype.card I)
    (∀ A : Finset I, 0 < A.card →
      HasSum (TerminalMass A sizes) 1 ∧
      (∀ x : TerminalTrace I sizes, 0 ≤ TerminalMass A sizes x ∧
        (TerminalOutput x ∉ A → TerminalMass A sizes x = 0)) ∧
      (∀ i : I, HasSum (fun x : TerminalTrace I sizes =>
        if TerminalOutput x = i then TerminalMass A sizes x else 0)
        (if i ∈ A then 1 / (A.card : ℝ) else 0)) ∧
      (∃ q : ℝ, HasSum (fun x : TerminalTrace I sizes =>
        TerminalMass A sizes x * (TerminalCost sizes x : ℝ)) q ∧
        0 ≤ q ∧ q ≤ (9/2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card)) ∧
      (∃ q : ℝ, HasSum (fun x : TerminalTrace I sizes =>
        TerminalMass A sizes x * (TerminalBooleanQueries sizes x : ℝ)) q ∧
        0 ≤ q ∧ q ≤ (29/2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / A.card)) ∧
      (∃ q : ℝ, HasSum (fun x : TerminalTrace I sizes =>
        TerminalMass A sizes x * (SourceLookupClock sizes x : ℝ)) q ∧
        0 ≤ q ∧ q ≤ 19 * Real.sqrt ((Fintype.card I : ℝ) / A.card))) ∧
    (∀ (A : Finset I) (stage budget : ℕ),
      (∀ out, 0 ≤ FiniteBudgetMass A sizes stage budget out) ∧
      (∑ out : Option I, FiniteBudgetMass A sizes stage budget out) = 1 ∧
      ∀ i : I, i ∉ A → FiniteBudgetMass A sizes stage budget (some i) = 0) ∧
    (∀ stage budget : ℕ, FiniteBudgetMass (∅ : Finset I) sizes stage budget none = 1) ∧
    (∃ K : ℕ, (K : ℝ) ≤ 6 * Real.sqrt (Fintype.card I) ∧ ∀ k : ℕ,
      (WorstPrefixIterations sizes (K+k) : ℝ) ≤
        (6 + (k : ℝ)) * Real.sqrt (Fintype.card I) ∧
      ∀ A : Finset I, 0 < A.card → RetryReach A sizes (K+k) ≤ (3/4 : ℝ)^k)

end Qatlib.Concepts.SearchStopping.UnknownCount
