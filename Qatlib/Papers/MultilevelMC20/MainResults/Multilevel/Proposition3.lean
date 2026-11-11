/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultilevelMC20.MainResults.CostModel.CostAsymptotics

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 3: complexity of classical MLMC

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

Paper Proposition 3 (p. 15, display (4.12)--(4.13)):

> Consider Problem 1 for the SDE (2.1) under Assumptions 1--3.  Then MLMC with a numerical
> scheme of strong order `r` estimates `E[P]` up to additive error `ε` with probability at
> least `0.99` in cost `O(ε^{-2})` for `r > 1`, and `O(ε^{-1-1/r-o(1)})` for `r ≤ 1`.

The proof is "a straightforward result from Lemma 3 and Proposition 2": by Proposition 2
the level model has `α = r - o(1)`, `β = r - o(1)`, `γ = 1`, and Giles' multilevel
cost formula (Lemma 3 of the paper, quoted in Section 3) gives, at the polynomial
exponent level,

* `2` when `β > γ` (Giles' case `β > γ`),
* `2 + (γ - β)/α` otherwise.

`classicalMLMCExponent` records this formula.  The theorem below performs the substitution
`β = r`, `α = r` (the global-Lipschitz branch of Proposition 2, where the exponents are
exact) and derives both lines of (4.12)/(4.13) as cost-class statements; the
poly-logarithmic parameters `q`, `s` are carried along unchanged.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- The polynomial exponent of the classical MLMC cost (Lemma 3 / Giles) for a level
model with bias, variance and cost exponents `α`, `β`, `γ`. -/
def classicalMLMCExponent (α β γ : ℝ) : ℝ :=
  if γ < β then 2 else 2 + (γ - β) / α

/-- Proposition 3 (p. 15, (4.12)): with the exponents of Proposition 2 substituted, the
classical MLMC cost is `O(ε^{-2})` when `r > 1` and `O(ε^{-1-1/r})` (up to `o(1)`) when
`r ≤ 1`.

The hypothesis `h` is the cost-class statement of Giles' multilevel theorem instantiated
at the level model `(α, β, γ) = (r, r, 1)` supplied by Proposition 2. -/
theorem proposition3_general {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ} {q s : ℝ}
    (h : CostClass (classicalMLMCExponent r r 1) q s cost) :
    (1 < r → CostClass 2 q s cost) ∧ (r ≤ 1 → CostClass (1 + 1 / r) q s cost) := by
  constructor
  · intro hr1
    have hexp : classicalMLMCExponent r r 1 = 2 := by
      unfold classicalMLMCExponent
      rw [if_pos hr1]
    rwa [hexp] at h
  · intro hr1
    have hexp : classicalMLMCExponent r r 1 = 1 + 1 / r := by
      unfold classicalMLMCExponent
      rw [if_neg (not_lt.mpr hr1)]
      field_simp
      ring
    rw [hexp] at h
    exact h

/-- Proposition 3, global-Lipschitz improvement (p. 15, (4.13)): with `α = r`,
`β = 2r`, `γ = 1` the classical MLMC cost is `O(ε^{-2})` for `r > 1/2` and
`O(ε^{-1/r})` for `r < 1/2` (the boundary `r = 1/2` is `O(ε^{-2}(log ε)²)`). -/
theorem proposition3_lipschitz {r : ℝ} (hr : 0 < r) {cost : ℝ → ℝ} {q s : ℝ}
    (h : CostClass (classicalMLMCExponent r (2 * r) 1) q s cost) :
    (1 / 2 < r → CostClass 2 q s cost) ∧
      (r < 1 / 2 → CostClass (1 / r) q s cost) := by
  constructor
  · intro hr1
    have hexp : classicalMLMCExponent r (2 * r) 1 = 2 := by
      unfold classicalMLMCExponent
      rw [if_pos (by linarith)]
    rwa [hexp] at h
  · intro hr1
    have hexp : classicalMLMCExponent r (2 * r) 1 = 1 / r := by
      unfold classicalMLMCExponent
      rw [if_neg (not_lt.mpr (by linarith))]
      field_simp
      ring
    rw [hexp] at h
    exact h

end Qatlib.Papers.MultilevelMC20.MainResults
