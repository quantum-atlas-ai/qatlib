/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QChemImprove14.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Claim c002 — `Θ(N)` parallel-depth improvement

Hastings--Wecker--Bauer--Troyer, fixed arXiv:1403.1539v2, Sec. 2
("parallelization / nesting"), Fig. 7 and Fig. 9, and the abstract.

With the ancilla circuit and nesting, up to `Θ(N)` of the `N^4` terms can be
executed in parallel, so the parallel depth equals the serial gate count
divided by `Θ(N)`: a `Θ(N)` reduction relative to the serial gate count and a
total `Θ(N²)` reduction relative to the original circuit (combining this with
the `Θ(N)` Jordan–Wigner gain of c001).
-/

set_option autoImplicit false
open scoped BigOperators

namespace Qatlib.Papers.QChemImprove14.MainResults

/-- **Claim c002 (nesting)**: `N^4` terms scheduled `N`-wide need exactly `N^3`
rounds.  (The ceiling `⌈N^4/N⌉` collapses because `N ∣ N^4`.) -/
theorem roundCount_twoBody (N : ℕ) (hN : 1 ≤ N) :
    roundCount (twoBodyTermCount N) (termsPerRound N) = N ^ 3 := by
  unfold roundCount twoBodyTermCount termsPerRound
  have hpow : N ^ 4 = N ^ 3 * N := by ring
  have hsplit : N ^ 4 + N - 1 = N ^ 3 * N + (N - 1) := by
    rw [hpow]; omega
  rw [hsplit, show N ^ 3 * N = N * N ^ 3 by ring]
  rw [Nat.mul_add_div (m := N) (by omega) (N ^ 3) (N - 1),
    Nat.div_eq_of_lt (by omega : N - 1 < N)]
  simp

/-- **Claim c002 (parallel depth)**: the parallel depth of the nested circuit
is `N^3`, `Θ(N)` smaller than the serial work `N^4`. -/
theorem parallelDepth_eq (N : ℕ) (hN : 1 ≤ N) :
    parallelDepth N = N ^ 3 := by
  unfold parallelDepth
  exact roundCount_twoBody N hN

/-- **Claim c002 (Θ(N) improvement)**: relative to the serial gate count, the
parallel depth improves by a factor `serialWork / parallelDepth = N = Θ(N)`. -/
theorem parallel_depth_improvement (N : ℕ) (hN : 1 ≤ N) :
    (serialWork N : ℝ) / (parallelDepth N : ℝ) = (N : ℝ) := by
  unfold serialWork
  rw [parallelDepth_eq N hN, twoBodyTermCount]
  push_cast
  have hN' : (N : ℝ) ≠ 0 := by positivity
  have hpow : (N : ℝ) ^ 4 = (N : ℝ) ^ 3 * (N : ℝ) := by ring
  rw [hpow]
  field_simp

/-- **Claim c002 (total Θ(N²) improvement)**: combining the original
`Θ(N)` Jordan–Wigner overhead (`N^5` serial work) with the `Θ(N)` nesting
gain (`N^3` parallel depth) gives a total factor `N² = Θ(N²)`. -/
theorem total_improvement (N : ℕ) (hN : 1 ≤ N) :
    ((N : ℝ) ^ 5) / (parallelDepth N : ℝ) = (N : ℝ) ^ 2 := by
  rw [parallelDepth_eq N hN]
  push_cast
  have hpow : (N : ℝ) ^ 5 = (N : ℝ) ^ 3 * (N : ℝ) ^ 2 := by ring
  rw [hpow]
  field_simp

end Qatlib.Papers.QChemImprove14.MainResults
