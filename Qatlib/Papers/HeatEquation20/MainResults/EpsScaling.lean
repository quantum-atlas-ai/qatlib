/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HeatEquation20.MainResults.ClassicalMethods

@[expose] public section


/-!
# HeatEquation20 — explicit `ε`-scaling of the displayed bounds (Table I, pp. 2, 11, 23)

Fixed source: arXiv:2004.06516v2.

* **Theorem 6** (p. 11) displays the plain time-stepping bound
  `O(3^{-d/2} T^{d/2+2} L^d α^{d/2+2} d^{d/2+3} (ζ/ε)^{d/2+1})`.  Row
  "Time-stepping" of Table I (p. 2) prints the same bound in the form
  `Õ(ε^{-d/2-1})`; the algebraic content of that row is the identity
  `(ζ/ε)^p = ζ^p ε^{-p}` at `p = d/2+1`, recorded below.
* **Theorem 21** (p. 23) uses `m = 2 T² d² α² ζ / (3ε)` time steps, so the
  spatial-size factor `O(m)` (the `poly(1/ε)` footnote of Table I, p. 2) is
  `Θ(ε^{-1})`: multiplying by `ε` leaves the `ε`-independent constant
  `2 T² d² α² ζ / 3`.

Both statements are pure real-arithmetic identities for the `rpow` expressions
already fixed in `Qatlib/Papers/HeatEquation20/MainResults/ClassicalMethods.lean` and `Qatlib/Papers/HeatEquation20/MainResults/Approximation.lean`; no algorithm
is modelled and no definition is changed.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open Qatlib.Papers.HeatEquation20.MainResults

/-- **Theorem 6, Table I row** (arXiv:2004.06516v2, p. 11 and p. 2).  The
displayed time-stepping bound, with every factor separated,
`3^{-d/2} T^{d/2+2} L^d α^{d/2+2} d^{d/2+3} (ζ/ε)^{d/2+1}`, equals
`3^{-d/2} T^{d/2+2} L^d α^{d/2+2} d^{d/2+3} ζ^{d/2+1} ε^{-(d/2+1)}`, whose
`ε`-dependence is the `Õ(ε^{-d/2-1})` of the "Time-stepping" row of Table I.
The proof is the `rpow` splitting `(ζ/ε)^p = ζ^p ε^{-p}` for `ζ, ε > 0`. -/
theorem thm6Bound_eps_scaling (d : ℕ) (T L α ζ ε : ℝ) (_hT : 0 < T) (_hL : 0 < L)
    (_hα : 0 < α) (hζ : 0 < ζ) (hε : 0 < ε) :
    thm6Bound d T L α ζ ε
      = (3 : ℝ) ^ (-(d : ℝ) / 2) * T ^ ((d : ℝ) / 2 + 2) * L ^ d
        * α ^ ((d : ℝ) / 2 + 2) * (d : ℝ) ^ ((d : ℝ) / 2 + 3)
        * ζ ^ ((d : ℝ) / 2 + 1) * ε ^ (-((d : ℝ) / 2 + 1)) := by
  have hp : (ζ / ε) ^ ((d : ℝ) / 2 + 1)
      = ζ ^ ((d : ℝ) / 2 + 1) * ε ^ (-((d : ℝ) / 2 + 1)) := by
    rw [Real.div_rpow hζ.le hε.le, Real.rpow_neg hε.le, div_eq_mul_inv]
  unfold thm6Bound
  rw [hp]
  ring

/-- **Theorem 21, space cost** (arXiv:2004.06516v2, p. 23, Table I footnote
p. 2).  With the Corollary 2 parameter choice the spatial-size factor of
Theorem 21 is `m = 2 T² d² α² ζ / (3ε)`, so `ε · m` is the `ε`-independent
constant `2 T² d² α² ζ / 3`.  Consequently the space cost is `Θ(ε^{-1})`
with the two-sided comparison constants `c = C = 2 T² d² α² ζ / 3`. -/
theorem space21_eps_scaling (d : ℕ) (hd : 0 < d) (T α ζ : ℝ) (hT : 0 < T) (hα : 0 < α)
    (hζ : 0 < ζ) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ ε : ℝ, 0 < ε →
      c ≤ ε * cor2M d α ζ T ε ∧ ε * cor2M d α ζ T ε ≤ C := by
  refine ⟨2 * T ^ 2 * (d : ℝ) ^ 2 * α ^ 2 * ζ / 3,
    2 * T ^ 2 * (d : ℝ) ^ 2 * α ^ 2 * ζ / 3,
    by positivity, by positivity, ?_⟩
  intro ε hε
  have hmul : ε * cor2M d α ζ T ε = 2 * T ^ 2 * (d : ℝ) ^ 2 * α ^ 2 * ζ / 3 := by
    unfold cor2M
    field_simp
  rw [hmul]
  exact ⟨le_rfl, le_rfl⟩

end Qatlib.Papers.HeatEquation20.MainResults
