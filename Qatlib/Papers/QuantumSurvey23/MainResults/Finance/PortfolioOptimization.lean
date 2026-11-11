/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c013 — Portfolio optimization: `Õ(n^{2.5})` vs `Õ(n^{3.5})`

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 8.1 (arXiv source lines 7153–7158).

Source conclusion: the quantum algorithm for constrained portfolio optimization
runs in `Õ(n^{2.5})` where the classical algorithm runs in `Õ(n^{3.5})`; the
unconstrained variant runs in `Õ(n²)` versus `Õ(n³)`.  Both are subquadratic
speedups.

Formalization notes: using the shared ceiling `√· = sqrtCost`,
* `constrainedClassical n = n³ · √n` (`Õ(n^{3.5})`),
* `constrainedQuantum n = n² · √n` (`Õ(n^{2.5})`),
* `unconstrainedClassical n = n³` (`Õ(n³)`),
* `unconstrainedQuantum n = n²` (`Õ(n²)`).

The theorems show the classical cost is exactly `n` times the quantum cost in
both cases, hence the speedup factor is `n`, which is subquadratic (`n ≤ n²`).
This is a faithful rendering of the survey's exponent arithmetic without
committing to any particular `Õ`-constant.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Finance

open Qatlib.Papers.QuantumSurvey23.MainResults.Scaling

/-- Constrained portfolio optimization, classical: `Õ(n^{3.5}) = n³·√n`. -/
def constrainedClassical (n : ℕ) : ℕ := n ^ 3 * sqrtCost n

/-- Constrained portfolio optimization, quantum: `Õ(n^{2.5}) = n²·√n`. -/
def constrainedQuantum (n : ℕ) : ℕ := n ^ 2 * sqrtCost n

/-- Unconstrained portfolio optimization, classical: `Õ(n³)`. -/
def unconstrainedClassical (n : ℕ) : ℕ := n ^ 3

/-- Unconstrained portfolio optimization, quantum: `Õ(n²)`. -/
def unconstrainedQuantum (n : ℕ) : ℕ := n ^ 2

/-- **c013a (Section 8.1).** Constrained: the classical cost is exactly a
factor `n` above the quantum cost (`n^{3.5}/n^{2.5} = n`). -/
theorem constrained_speedup_is_linear (n : ℕ) :
    constrainedClassical n = n * constrainedQuantum n := by
  unfold constrainedClassical constrainedQuantum
  ring

/-- **c013b (Section 8.1).** Unconstrained: the classical cost is exactly
a factor `n` above the quantum cost (`n³/n² = n`). -/
theorem unconstrained_speedup_is_linear (n : ℕ) :
    unconstrainedClassical n = n * unconstrainedQuantum n := by
  unfold unconstrainedClassical unconstrainedQuantum
  ring

/-- Auxiliary: `n³ ≤ n⁴`. -/
private theorem cube_le_fourth (n : ℕ) : n ^ 3 ≤ n ^ 4 := by
  cases n with
  | zero => simp
  | succ m => exact Nat.pow_le_pow_right (by omega : 0 < m + 1) (by omega : 3 ≤ 4)

/-- **c013c (Section 8.1).** Both speedups are subquadratic: the classical
cost is at most `n²` times the quantum cost. -/
theorem portfolio_speedups_subquadratic (n : ℕ) :
    constrainedClassical n ≤ (n * n) * constrainedQuantum n ∧
    unconstrainedClassical n ≤ (n * n) * unconstrainedQuantum n := by
  constructor
  · unfold constrainedClassical constrainedQuantum
    calc n ^ 3 * sqrtCost n ≤ n ^ 4 * sqrtCost n :=
          Nat.mul_le_mul_right _ (cube_le_fourth n)
      _ = (n * n) * (n ^ 2 * sqrtCost n) := by ring
  · unfold unconstrainedClassical unconstrainedQuantum
    calc n ^ 3 ≤ n ^ 4 := cube_le_fourth n
      _ = (n * n) * n ^ 2 := by ring

/-- **c013 (Section 8.1), combined assessment.** Constrained
`Õ(n^{3.5}) → Õ(n^{2.5})` and unconstrained `Õ(n³) → Õ(n²)`, both by a
subquadratic factor `n`. -/
theorem portfolio_speedup_assessment (n : ℕ) :
    constrainedClassical n = n * constrainedQuantum n ∧
    unconstrainedClassical n = n * unconstrainedQuantum n ∧
    constrainedClassical n ≤ (n * n) * constrainedQuantum n :=
  ⟨constrained_speedup_is_linear n, unconstrained_speedup_is_linear n,
    (portfolio_speedups_subquadratic n).1⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Finance
