/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ReadManyQry11.MainResults.SourceModel
import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3CorrectedTigh

set_option backward.isDefEq.respectTransparency false

/-!
# ReadManyQry11 — Lemma 1 (unknown-count marked-item search)

Fixed paper: arXiv:1112.0548v1 (2 December 2011), Lemma 1, p. 4 (text line 88):

> Given an oracle for a string `x ∈ {0,1}^N`, there exists a quantum algorithm that
> outputs with high probability the index of a marked item in `x` if it exists, making
> `O(√(N/t))` queries in expectation when there are `t` marked items.  If there are no
> marked items the algorithm runs indefinitely.

The established `Qatlib.Concepts.SearchStopping.UnknownCount.theorem3Corrected`
(BBHT, quant-ph/9605034v1, §4, claim 1443) is exactly this result: it fixes the explicit
schedule `ExponentialSizes N`, proves exact uniform output on the marked set, gives the
explicit constants `(9/2)√(N/t)` (expected Grover iterations) and `(29/2)√(N/t)`
(Boolean-query clock), and replaces the paper's nonterminating run on the empty marked
set by a finite-budget timeout.  The declarations below reuse that contract; the first is
the bridge, the others spell the paper's `N`/`t` conclusions out for the paper Block.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators Real
open Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib.Concepts.SearchStopping.UnknownCount

namespace Qatlib.Papers.ReadManyQry11.MainResults

/-- Paper Lemma 1 (p. 4, line 88), by reuse of the BBHT contract
`Qatlib.Concepts.SearchStopping.UnknownCount.theorem3Corrected`
(quant-ph/9605034v1, §4).  With `N = Fintype.card I` and `t = A.card`, `sizes` is the
paper's fixed doubling schedule `ExponentialSizes N` (`m₀ = 1`, `m_{k+1} = min((6/5)m_k, √N)`):

* the terminal distribution has total mass one;
* it never outputs an index outside the marked set `A`;
* each marked index is output with probability exactly `1/t`;
* the expected accumulated Grover-iteration cost is at most `(9/2)√(N/t)`;
* the expected Boolean-query cost is at most `(29/2)√(N/t)`, the paper's `O(√(N/t))`;
* the empty marked set has finite-budget termination with the timeout outcome;
* the `k`-retry schedule has prefix work `≤ (6+k)√N` and false-negative probability
  `≤ (3/4)^k`, the paper's "with high probability". -/
theorem lemma1_unknown_count_search :
    Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3Corrected :=
  Qatlib.Concepts.SearchStopping.UnknownCount.theorem3Corrected

/-- The cost and correctness conclusions of Lemma 1 (p. 4, line 88) for a nonempty
marked set `A`, extracted from the BBHT contract; the paper's `O(√(N/t))` is the
explicit `(29/2)√(N/t)` Boolean-query clock and `(9/2)√(N/t)` expected iterations. -/
theorem lemma1_search_conclusions
    {I : Type} [Fintype I] [DecidableEq I] (hN : 0 < Fintype.card I)
    (A : Finset I) (hA : 0 < A.card) :
    let sizes := ExponentialSizes (Fintype.card I)
    HasSum (TerminalMass A sizes) 1 ∧
    (∀ x : TerminalTrace I sizes, 0 ≤ TerminalMass A sizes x ∧
      (TerminalOutput x ∉ A → TerminalMass A sizes x = 0)) ∧
    (∀ i : I, HasSum (fun x : TerminalTrace I sizes =>
      if TerminalOutput x = i then TerminalMass A sizes x else 0)
      (if i ∈ A then 1 / (A.card : ℝ) else 0)) ∧
    (∃ q : ℝ, HasSum (fun x : TerminalTrace I sizes =>
      TerminalMass A sizes x * (TerminalCost sizes x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (9 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / (A.card : ℝ))) ∧
    (∃ q : ℝ, HasSum (fun x : TerminalTrace I sizes =>
      TerminalMass A sizes x * (TerminalBooleanQueries sizes x : ℝ)) q ∧
      0 ≤ q ∧ q ≤ (29 / 2 : ℝ) * Real.sqrt ((Fintype.card I : ℝ) / (A.card : ℝ))) := by
  have h := lemma1_unknown_count_search (I := I) hN
  obtain ⟨h1, h2, h3, h4, h5, _⟩ := h.1 A hA
  exact ⟨h1, h2, h3, h4, h5⟩

/-- The empty-marked-set clause of Lemma 1 (p. 4, line 88): every finite-budget run
terminates with the timeout outcome (the paper's "runs indefinitely", made a
terminating distribution). -/
theorem lemma1_empty_set_timeout
    {I : Type} [Fintype I] [DecidableEq I] (hN : 0 < Fintype.card I)
    (stage budget : ℕ) :
    FiniteBudgetMass (∅ : Finset I) (ExponentialSizes (Fintype.card I)) stage budget none = 1 := by
  have h := lemma1_unknown_count_search (I := I) hN
  exact h.2.2.1 stage budget

end Qatlib.Papers.ReadManyQry11.MainResults
