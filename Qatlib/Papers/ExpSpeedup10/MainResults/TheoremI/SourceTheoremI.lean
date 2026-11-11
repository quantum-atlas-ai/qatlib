/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ExpSpeedup10.MainResults.Model.SourceComplexity

set_option backward.isDefEq.respectTransparency false

/-!
# ExpSpeedup10 — Theorem I (exponential separation)

Brandão–Horodecki, *Exponential Quantum Speed-ups are Generic*,
fixed arXiv:1010.3654**v2** (16 Apr 2013).
Theorem I, Section I p. 4 (line 196); proof Section IV pp. 11–12.

Statement: for every `n`-qubit circuit family `U` with `C(U) = Ω(n)`,
`U`-circuit checking has an exponential separation between the quantum and
the postselected classical query complexities.  The quantum algorithm of
Section II A uses four queries; the postselected classical lower bound is
`2^{C(U)/7}` (Propositions IV.1 and IV.3).

This file proves the quantitative content: a circuit with `C(U) ≥ c·n` has a
postselected classical lower bound at least `2^{c·n/7}`.
-/

set_option autoImplicit false
noncomputable section

open Matrix BigOperators
open scoped Classical

namespace Qatlib.Papers.ExpSpeedup10.MainResults
namespace TheoremI

open Model

/-- Theorem I (Section I p. 4, proof Section IV pp. 11–12): the explicit
quantum algorithm uses 4 queries, and if `C(U) ≥ c·n` then the postselected
classical query complexity is at least `2^{c·n/7}`. -/
theorem theorem_I_exponential_separation
    (n : ℕ) (hn : 1 ≤ n)
    (U : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)
    (c : ℝ) (hc : 0 < c) (hC : c * (n : ℝ) ≤ sourceC U) :
    sourceQuantumQueryCost = 4 ∧
      (2 : ℝ) ^ (c * (n : ℝ) / 7) ≤ sourcePostselectedLowerBound U := by
  refine ⟨rfl, ?_⟩
  unfold sourcePostselectedLowerBound
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  linarith

end TheoremI
end Qatlib.Papers.ExpSpeedup10.MainResults
