/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Tactic

/-!
# Modeled PDE term and gate counts

Defines the arithmetic cost model `modeledTermCount` and its repetition cost `modeledGateCount`.
The resulting gate-count expression has a linear bound in the dimension parameter for each fixed
repetition count. See [ArrazolaEtAl2019].

## Main statements

* `modeledGateCount_eq`: the modeled cost is K(4N + 1).
* `modeled_polynomial_dimension`: the cost has a polynomial bound in N for fixed K.

## References

* [Arrazola et al., 2019][ArrazolaEtAl2019]
-/

set_option autoImplicit false

namespace Qatlib.Papers.NonhomogPDE18.CostModels

/-- The modeled number of terms, `1 + 4 * N`, at dimension parameter `N`. -/
def modeledTermCount (N : ℕ) : ℕ := 1 + 4 * N

/-- The modeled gate count for `K` repetitions of `modeledTermCount N` terms. -/
def modeledGateCount (N K : ℕ) : ℕ := K * modeledTermCount N

/-- The modeled gate count is `K * (4 * N + 1)`. See [ArrazolaEtAl2019]. -/
theorem modeledGateCount_eq (N K : ℕ) :
    modeledGateCount N K = K * (4 * N + 1) := by
  unfold modeledGateCount modeledTermCount
  ring

/-- The modeled gate count is bounded above by `5 * K * (N + 1)`. See [ArrazolaEtAl2019]. -/
theorem modeled_linear_bound (N K : ℕ) :
    modeledGateCount N K ≤ (5 * K) * (N + 1) := by
  rw [modeledGateCount_eq]
  have h1 : 4 * N + 1 ≤ 5 * (N + 1) := by omega
  calc
    K * (4 * N + 1) ≤ K * (5 * (N + 1)) := Nat.mul_le_mul_left K h1
    _ = (5 * K) * (N + 1) := by ring

/-- For fixed `K`, natural constants give a polynomial upper bound on the modeled gate count as
a function of `N`. See [ArrazolaEtAl2019]. -/
theorem modeled_polynomial_dimension (K : ℕ) :
    ∃ c k : ℕ, ∀ N : ℕ, modeledGateCount N K ≤ c * (N + 1) ^ k := by
  refine ⟨5 * K, 1, fun N => ?_⟩
  rw [pow_one]
  exact modeled_linear_bound N K

end Qatlib.Papers.NonhomogPDE18.CostModels
