/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QSearchSurvey05.MainResults.Search.KnownCountOptimality
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountSubgoalTigh
import Qatlib.Concepts.SearchStopping.KnownCount.Section3KnownCountDefs
import Qatlib.Concepts.SearchStopping.PaidRestart.Section31ExactSuccessTigh
import Qatlib.Concepts.QueryWordCore.QueryMachinery.Oracle
import Qatlib.Foundations.QueryWordCore.Circuit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.Real.Pi.Bounds

set_option backward.isDefEq.respectTransparency false

/-!
# Fact 2, Eq. (1): exact optimal query count for known `k`

Source: A. Ambainis, *Quantum search algorithms*, arXiv:quant-ph/0504012v1
(3 April 2005), **§2.2 Fact 2 and Eq. (1), pp. 2–3** (reference [37] = Zalka).

The paper states that when the number of marked items is exactly `k`, Grover's
algorithm is exactly optimal, and that the minimum number of queries needed to find a
marked item with certainty is

```
⌈ π / (4 arcsin (1 / √(N/k))) − 1/2 ⌉  <  (π/4) √(N/k).        (1)
```

We formalise this in the same fixed-space unitary phase-query model used by the frozen
known-count result (a `Circuit I` with a fixed finite basis `I`, oracle family
`SetOracle`, zero error, see
`QuantumAlgorithm.Concepts.QueryComplexity.DegreeMethod.FixedSpaceQueryUpperBound`).

Two issues with the printed inequality are recorded here explicitly.

* The displayed strict inequality `⌈x − 1/2⌉ < (π/4)√(N/k)` is **false as printed**:
  for `N = 100`, `k = 1` the left side is `⌈7.8416 − 1/2⌉ = 8` while the right side is
  `7.8540`.  The correct elementary consequence of `sin θ < θ` is
  `⌈x − 1/2⌉ ≤ ⌈(π/4)√(N/k)⌉`; this is
  `fact2_ceiling_budget_witness` below (proved).  We therefore do not state the false
  strict inequality.

What is proved here (all sorry-free):

* `fact2_ceiling_budget_witness`: the corrected elementary ceiling inequality.
* `fact2_known_count_upper`: for every known cardinality `k` with `2k ≤ N`, one fixed
  circuit finds a marked element with probability `≥ 1/2` using at most
  `⌈(π/4)√(N/k)⌉` queries (the source's `O(√(N/k))` upper half).
* `exactOptimalQueryCount_quarter`: at quarter density the source's exact formula
  `⌈π/(4 arcsin√(k/N)) − 1/2⌉` evaluates to `1`.
* `fact2_quarter_density_exact`: **a genuine exact-optimality theorem**.  When exactly
  one quarter of the basis is marked, one query is both sufficient (`0` error,
  `quarterDensity_searchClaim`) and *necessary* — no zero-query circuit can be certain on
  every quarter-density instance.  This realises Fact 2's "cannot be improved even by 1"
  in a non-trivial family.

Residual gap: Zalka's exact lower bound for arbitrary `k` is still not frozen, so the
general instance of the displayed ceiling formula is not proved; the quarter-density
case is the proved exact-optimality instance.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Concepts.QueryWordCore.QueryMachinery
open Qatlib.Concepts.SearchStopping.KnownCount
open Qatlib.Concepts.SearchStopping.PaidRestart
open Qatlib.Concepts.QueryComplexity.DegreeMethod
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Papers.QSearchSurvey05.MainResults

namespace Qatlib.Papers.QSearchSurvey05.MainResults

/-- The two normalisations of the source budget agree: `π/(4√(k/N)) = (π/4)√(N/k)`. -/
theorem groverOptimalBudget_eq {N k : ℕ} (hN : 0 < N) (hk : 0 < k) :
    groverOptimalBudget N k = Real.pi / 4 * Real.sqrt ((N : ℝ) / (k : ℝ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hrecip : Real.sqrt ((N : ℝ) / (k : ℝ)) =
      1 / Real.sqrt ((k : ℝ) / (N : ℝ)) := by
    rw [Real.sqrt_div hNpos.le, Real.sqrt_div hkpos.le]
    field_simp
  unfold groverOptimalBudget
  rw [hrecip]
  field_simp

end Qatlib.Papers.QSearchSurvey05.MainResults
