/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SearchStopping.UnknownCount.Theorem3SourceFamilyStat
import Qatlib.Concepts.SearchStopping.UnknownCount.SearchSourceFamily

/-!
# Unknown-count quantum search for a family of schedules

Proves `theorem3SourceFamily` by assembling the parameterized schedule, terminal trace, cost,
budget, and timeout laws. The theorem covers every growth factor in `(1, 4 / 3)` through the
proposition `Theorem3SourceFamily`. For the quantum-search analysis, see [BoyerEtAl1998].

## Main statements

* `theorem3SourceFamily`: Establishes `Theorem3SourceFamily`, the full unknown-count search
  guarantee with explicit costs and timeout bounds for every `1 < l < 4 / 3`.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false

namespace Qatlib.Concepts.SearchStopping.UnknownCount

universe u

/-- Establishes `Theorem3SourceFamily`, the full unknown-count search guarantee with explicit
costs and timeout bounds for every `1 < l < 4 / 3`. See [BoyerEtAl1998]. -/
theorem theorem3SourceFamily : Theorem3SourceFamily.{u} := by
  intro I _ _ hN l hl hl4
  (try dsimp only)
  have hsizes := (search_source_schedule_laws _ hN l hl.le).2.1
  refine ⟨?_, ?_, ?_, search_source_uniform_timeout l hl hl4 hN⟩
  · intro A hA
    have hlaw := search_source_terminal_law_nonempty l hl hl4 A hA
    exact ⟨hlaw.1, hlaw.2, search_source_terminal_output_nonempty l hl hl4 A hA,
      search_source_terminal_cost_nonempty l hl hl4 A hA,
      search_source_terminal_boolean_cost l hl hl4 A hA,
      search_source_terminal_lookup_cost l hl hl4 A hA⟩
  · intro A stage budget
    have hlaw := search_finite_budget_law hN A _ hsizes stage budget
    exact ⟨hlaw.1, hlaw.2, fun i hi =>
      search_finite_budget_no_false_positive hN A _ hsizes stage budget i hi⟩
  · exact search_empty_budget_timeout hN _ hsizes

end Qatlib.Concepts.SearchStopping.UnknownCount
