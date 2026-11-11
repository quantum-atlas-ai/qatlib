/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultilevelMC20.MainResults.Multilevel.Proposition3
import Qatlib.Papers.MultilevelMC20.MainResults.Multilevel.Theorem3

set_option backward.isDefEq.respectTransparency false

/-!
# Corollaries 1 and 2: payoffs of the form (4.16)

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

Assumption 4 (4.16)--(4.18) allows payoffs
`P = P(X_T, ∫_0^T f(X_t) dt, ∫_0^T g(X_t) dW_t)` that are piecewise Lipschitz in the
triple `(X, y, z)`.  Extending the state by `Y_t = ∫_0^t f(X_s) ds`, `Z_t = ∫_0^t g(X_s) dW_s`
turns the payoff into a function of the final value of the higher-dimensional diffusion
`X̃_t = (X_t, Y_t, Z_t)`, so the level model of Proposition 2/Theorem 2 applies to `X̃`.
For this extended system the improvement of Proposition 2's global-Lipschitz branch is
available (the payoff is Lipschitz in `(y, z)` and only the `X`-discontinuities survive,
introducing one factor of `h` in the bias), which is why the thresholds in (4.20) and
(4.22) drop to `r > 1/2` and `r > 1` respectively.

We formalise Corollaries 1 and 2 as the substitution statements: from the cost-class
hypotheses supplied by Proposition 3/Theorem 3 at the two rate pairs
`(α, β, γ) = (r, r, 1)` (general) and `(α, β, γ) = (r, 2r, 1)` (Assumption 4 /
global-Lipschitz) we derive the four displays (4.19)--(4.22).
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- Corollary 1 (p. 17, (4.19)--(4.20)): classical MLMC for a payoff satisfying
Assumption 4, under Assumptions 1 and 2. -/
theorem corollary1 {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ} {q s : ℝ}
    (hGen : CostClass (classicalMLMCExponent r r 1) q s cost)
    (hLip : CostClass (classicalMLMCExponent r (2 * r) 1) q s cost) :
    (1 < r → CostClass 2 q s cost) ∧
      (r ≤ 1 → CostClass (1 + 1 / r) q s cost) ∧
      (1 / 2 < r → CostClass 2 q s cost) ∧
      (r < 1 / 2 → CostClass (1 / r) q s cost) := by
  have hg := proposition3_general hr hGen
  have hl := proposition3_lipschitz hr hLip
  exact ⟨hg.1, hg.2, hl.1, hl.2⟩

/-- Corollary 2 (p. 17, (4.21)--(4.22)): QA-MLMC for a payoff satisfying Assumption 4,
under Assumptions 1 and 2.  The `q`, `s` are the Theorem 2 poly-logarithmic exponents
(`q = 3/2` in the `r > 2` and `r ≤ 2` lines); the exceptional `r = 1` line of (4.22)
carries `(log 1/ε)^{7/2}` and enters through the separate hypothesis `hEq`. -/
theorem corollary2 {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ} {q s : ℝ}
    (hGen : ∀ δ : ℝ, 0 < δ →
      CostClass (quantumMLMCExponent (r - δ) ((r - δ) / 2) 1) q s cost)
    (hLip : CostClass (quantumMLMCExponent r r 1) q s cost)
    (hEq : CostClass 1 (7 / 2) 2 cost) :
    (2 < r → CostClass 1 q s cost) ∧
      (r ≤ 2 → ∀ δ : ℝ, 0 < δ → CostClass (1 / 2 + 1 / r + δ) q s cost) ∧
      (1 < r → CostClass 1 q s cost) ∧
      (r = 1 → CostClass 1 (7 / 2) 2 cost) ∧
      (r < 1 → CostClass (1 / r) q s cost) := by
  have hg := theorem3_general hr hGen
  have hl := theorem3_lipschitz hr hLip
  exact ⟨hg.1, hg.2, hl.1, fun _ => hEq, fun hr1 => hl.2 (le_of_lt hr1)⟩

end Qatlib.Papers.MultilevelMC20.MainResults
