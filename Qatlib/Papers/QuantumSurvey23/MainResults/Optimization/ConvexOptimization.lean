/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QuantumSurvey23.MainResults.Scaling.CostScaling

set_option backward.isDefEq.respectTransparency false

/-!
# c009 — Convex optimization: linear speedup, `O(n⁴) → O(n³)`

Fixed source: Dalzell et al., *Quantum algorithms: A survey of applications and
end-to-end complexities*, arXiv:2310.03011, Section 5.3 (arXiv source lines 5065–5073).

Source conclusion: for generic convex optimization the quantum speedup is at
most linear (`O(n)`), the best known improvement being `O(n⁴) → O(n³)`; the
maximal power is obtained when the function-evaluation cost `C_f` and the
gradient cost `C_K` are both of order `n²`.

Formalization notes: `convexClassical n = n⁴` and `convexQuantum n = n³`; the
theorem `linear_convex_speedup` shows the classical cost is exactly `n` times
the quantum cost, and `convex_speedup_subquadratic` shows that ratio is at most
`n²` — i.e. the speedup is *subquadratic* (indeed linear).
-/

set_option autoImplicit false

namespace Qatlib.Papers.QuantumSurvey23.MainResults.Optimization

/-- Classical convex-optimization cost `O(n⁴)`. -/
def convexClassical (n : ℕ) : ℕ := n ^ 4

/-- Quantum convex-optimization cost `O(n³)`. -/
def convexQuantum (n : ℕ) : ℕ := n ^ 3

/-- **c009a (Section 5.3).** The improvement is exactly a factor `n`:
`n⁴ = n · n³`. -/
theorem linear_convex_speedup (n : ℕ) :
    convexClassical n = n * convexQuantum n := by
  unfold convexClassical convexQuantum
  ring

/-- **c009b (Section 5.3).** The speedup is subquadratic: the classical
cost is at most `n²` times the quantum cost. -/
theorem convex_speedup_subquadratic (n : ℕ) :
    convexClassical n ≤ (n * n) * convexQuantum n := by
  unfold convexClassical convexQuantum
  -- n⁴ ≤ n² · n³ = n⁵ (with the `n = 0` case trivial)
  rcases Nat.eq_zero_or_pos n with h0 | hpos
  · subst h0; simp
  · have h : n ^ 4 ≤ n ^ 5 := Nat.pow_le_pow_right hpos (by omega)
    calc n ^ 4 ≤ n ^ 5 := h
      _ = (n * n) * n ^ 3 := by ring

/-- **c009c (Section 5.3).** When both function and gradient evaluation
costs are `n²`, the total cost is `O(n⁴)` classically, whose `n³` quantum
variant is the claimed best improvement.  We record the resulting scale:
`convexClassical` bounds `n² · n²` and `convexQuantum` bounds `n² · n`. -/
theorem convex_evaluation_model (n : ℕ) :
    n ^ 2 * n ^ 2 = convexClassical n ∧ n ^ 2 * n = convexQuantum n := by
  constructor
  · unfold convexClassical; ring
  · unfold convexQuantum; ring

/-- **c009 (Section 5.3), combined assessment.** Exactly linear gain
`n⁴ → n³`, subquadratic. -/
theorem convex_optimization_linear_speedup (n : ℕ) :
    convexClassical n = n * convexQuantum n ∧
    convexClassical n ≤ (n * n) * convexQuantum n :=
  ⟨linear_convex_speedup n, convex_speedup_subquadratic n⟩

end Qatlib.Papers.QuantumSurvey23.MainResults.Optimization
