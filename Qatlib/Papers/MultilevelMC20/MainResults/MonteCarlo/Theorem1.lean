/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultilevelMC20.MainResults.CostModel.CostAsymptotics

set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1: quantum-accelerated Monte Carlo for a strong-order scheme

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

Paper Theorem 1 (p. 7):

> Let `A` be an algorithm that generates a sample of the numerical solution `X̂_n` of the
> SDE with time step size `h` using an `r`-th order scheme in the sense that
> `E|X̂_n − X_T| = O(h^r)`. Assume that `P(X̂_n)` has bounded variance independent of `h`.
> Then there exists a quantum algorithm that achieves the accuracy of additive error `ε`
> with probability at least `0.99`, with computational complexity `Õ(ε^{-1-1/r})`.

Formalisation.  Lemma 1 (Montanaro's `O((σ/ε)(log σ/ε)^{3/2} log log(σ/ε))` quantum
estimator) and Lemma 2 (median repetition to failure probability `δ`) are represented by
the hypothesis `hq : CostTildeClass 1 qcost`: a quantum estimator of `E[P(X̂_n)]` at
additive accuracy `ε` has cost `Õ(ε^{-1})`.  Each query to the scheme at step `h` costs
`1/h` time steps, and the bias `O(h^r)` is made `≤ ε/2` by `h = (ε/(2B))^{1/r}`, i.e.
`1/h = (2B)^{1/r} ε^{-1/r}`.  Hence the total cost is `Õ(ε^{-1-1/r})`.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- The inverse step size `(ε/(2B))^{-1/r}` is in the cost class `(1/r, 0, 0)`. -/
theorem inv_step_costClass {r B : ℝ} (hr : 0 < r) (hB : 0 < B) :
    CostClass (1 / r) 0 0 (fun ε => ((ε / (2 * B)) ^ (1 / r))⁻¹) := by
  have hEq : (fun ε : ℝ => ((ε / (2 * B)) ^ (1 / r))⁻¹)
      =ᶠ[epsZero] fun ε => (2 * B) ^ (1 / r) * ε ^ (-(1 / r)) := by
    filter_upwards [eventually_pos_epsZero] with ε hε
    have h2B : 0 < 2 * B := by positivity
    rw [Real.div_rpow hε.le h2B.le, div_eq_mul_inv, mul_inv_rev, inv_inv,
      ← Real.rpow_neg hε.le]
  exact hEq.trans_isBigO (costClass_const_rpow (1 / r) ((2 * B) ^ (1 / r)))

/-- Theorem 1 (p. 7, (2.9)--(2.10)): quantum-accelerated MC with a strong-order-`r`
scheme attains additive error `ε` with probability `0.99` at cost `Õ(ε^{-1-1/r})`. -/
theorem theorem1
    {r B σ : ℝ} (hr : 0 < r) (hB : 0 < B) (hσ : 0 < σ) {qcost : ℝ → ℝ}
    (hq : CostTildeClass 1 qcost) :
    ∃ cost : ℝ → ℝ,
      CostTildeClass (1 + 1 / r) cost ∧
      ∀ᶠ ε : ℝ in epsZero,
        cost ε = qcost ε * ((ε / (2 * B)) ^ (1 / r))⁻¹ := by
  refine ⟨fun ε => qcost ε * ((ε / (2 * B)) ^ (1 / r))⁻¹,
    costTildeClass_mul hq (costClass_toTilde (inv_step_costClass hr hB)), ?_⟩
  filter_upwards with ε
  rfl

end Qatlib.Papers.MultilevelMC20.MainResults
