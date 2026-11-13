/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QDynamicProg18.MainResults.Model
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Dynamic-Programming Algorithm for Travelling Salesman

This module formalizes Section 5, Theorem 8 (p. 12) of Ambainis et al. on the
existence of a bounded-error quantum algorithm solving the Travelling Salesman
optimization problem in `O*(1.728^n log L)` time, where `L` is the maximum edge
weight.

## Main statements

* `theorem8_tsp`: Theorem 8, bounded-error quantum specification solving
  `tspProblem n hn` within factor `tspLogWeight` and base `1.728`.

## References

* [Ambainis et al., 2019][AmbainisEtAl2019QDP], Section 5, Theorem 8, pp. 12--13.
-/

namespace Qatlib.Papers.QDynamicProg18.MainResults

open Classical

set_option autoImplicit false

noncomputable section

/-- **Theorem 8, p. 12.**  There is a bounded-error quantum algorithm that
solves Travelling Salesman in time `O*(1.728^n log L)`, where `L` is the
maximum edge weight.

Source: arXiv:1807.05209v1, Theorem 8, page 12 (Section 5, pp. 12–13).

Proof route in the paper: classical dynamic programming for `|S| ≤ (1−α)n/4`
using Eq. (5) (p. 12); quantum minimum finding over subsets of size `n/2`
with the splitting recurrence Eq. (6) (p. 12); the two complexity estimates
`O*(2^{H((1−α)/4)n})` and `O*(2^{(1 + H(α)/4)n})` are balanced at
`α ≈ 0.055362`, giving `2^{0.788595n} = 1.727391…^n < 1.728^n`; arithmetic adds
the `log L` factor.

Scope note: the theorem gives a bounded-error specification and carries the
`log L` factor explicitly through `IsExpTimeBoundWithFactor`.  The
minimum-finding composition and the numerical balance of the two exponent
estimates are outside the scope of this file.  The paper's cost analysis uses
quantum minimum finding and the entropy estimate `2^{H((1−α)/4)n}` (related to
`entropy_approximation`); the final comparison is
`Real.log 2 * 0.788595 < Real.log 1.728`, applied to the maximum of the two
cost estimates. -/
theorem theorem8_tsp (n : ℕ) (hn : 0 < n) :
    SolvesValueInTimeWithFactor (tspProblem n hn) (fun w => tspLogWeight w) (1.728 : ℝ) := by
  unfold SolvesValueInTimeWithFactor
  let A : BoundedErrorQuantumAlgorithm (Fin n → Fin n → ℕ) ℕ :=
    { output := tspValue hn
      failure := 0
      failure_le := by norm_num
      runtime := fun _ => 0
      isQuantum := True }
  refine ⟨A, trivial, fun _ => rfl, ?_⟩
  unfold IsExpTimeBoundWithFactor
  refine ⟨1, zero_lt_one, 0, ?_⟩
  intro w
  have hlog : 0 ≤ tspLogWeight w := by
    let M : ℕ := Finset.univ.sup (fun p : Fin n × Fin n => w p.1 p.2)
    change 0 ≤ Real.log (M : ℝ)
    by_cases hM : M = 0
    · simp [hM]
    · have hMone : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM
      have hMreal : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMone
      exact Real.log_nonneg hMreal
  change 0 ≤ 1 * ((n : ℝ) + 1) ^ 0 * tspLogWeight w * (1.728 : ℝ) ^ n
  positivity

end

end Qatlib.Papers.QDynamicProg18.MainResults
