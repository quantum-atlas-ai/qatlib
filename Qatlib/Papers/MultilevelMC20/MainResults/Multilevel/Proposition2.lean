/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MultilevelMC20.MainResults.CostModel.RateVocabulary

set_option backward.isDefEq.respectTransparency false

/-!
# Proposition 2: the exponents `α`, `β`, `γ` for SDE schemes

An, Linden, Liu, Montanaro, Shao, Wang,
*Quantum-accelerated multilevel Monte Carlo methods for stochastic differential equations
in mathematical finance*, fixed arXiv:2012.06283v2 (accepted in Quantum 2021-06-16).

Paper Proposition 2 (p. 13):

> Under Assumption 1, Assumption 2 and Assumption 3, for QA-MLMC with a numerical scheme
> of strong order `r`, we have `α = r − o(1)`, `β = r − o(1)`, `γ = 1`.  Furthermore, if
> the payoff function `P` is globally Lipschitz continuous, then the estimates improve to
> `α = r`, `β = 2r`, `γ = 1`.

Formalisation.  Assumptions 1--3 fix the coefficients and the piecewise-Lipschitz payoff;
the only output of the analysis needed downstream is the family of exponential rates, so
they are the conclusion of this file:

* `proposition2_general` turns the `m`-parametrised bounds (4.10)--(4.11) into
  `ExpRate (r − δ) bias` and `ExpRate (2(r − δ)) var` for every `δ > 0` (the `o(1)`),
  using `ExpRate_of_forall_mul_div`;
* `proposition2_lipschitz` records the global-Lipschitz improvement `α = r`, `β = 2r`
  from the pointwise bounds `|bias l| ≤ B 2^{-rl}`, `var l ≤ V 2^{-2rl}`;
* in both cases `γ = 1` is `growthRate_twoPow`, justified by the paragraph after the
  statement: level `l` uses `2^l` time steps of equal cost, so `C_{l+1} = 2 C_l`.
-/

set_option autoImplicit false
noncomputable section

open Filter Asymptotics
open scoped Topology BigOperators

namespace Qatlib.Papers.MultilevelMC20.MainResults

/-- Proposition 2, general payoff (p. 13): `α = r − o(1)`, `β = r − o(1)`, `γ = 1`.
The hypotheses `hbias`, `hvar` are the bounds (4.10)--(4.11) at the `m`-parametrised
rates `r·m/(m+1)` and `2·r·m/(m+1)`. -/
theorem proposition2_general {r : ℝ} (hr : 0 < r) {bias var : ℕ → ℝ}
    (hbias : ∀ m : ℕ, 1 ≤ m → ExpRate (r * (m : ℝ) / ((m : ℝ) + 1)) bias)
    (hvar : ∀ m : ℕ, 1 ≤ m → ExpRate (2 * (r * (m : ℝ) / ((m : ℝ) + 1))) var) :
    (∀ δ : ℝ, 0 < δ → ExpRate (r - δ) bias) ∧
      (∀ δ : ℝ, 0 < δ → ExpRate (2 * (r - δ)) var) ∧
      GrowthRate 1 (fun l : ℕ => twoPow (l : ℝ)) := by
  refine ⟨ExpRate_of_forall_mul_div hr hbias, ?_, growthRate_twoPow⟩
  have hvar' : ∀ m : ℕ, 1 ≤ m → ExpRate ((2 * r) * (m : ℝ) / ((m : ℝ) + 1)) var := by
    intro m hm
    have heq : (2 * r) * (m : ℝ) / ((m : ℝ) + 1)
        = 2 * (r * (m : ℝ) / ((m : ℝ) + 1)) := by ring
    rw [heq]
    exact hvar m hm
  intro δ hδ
  have h2 : 2 * (r - δ) = 2 * r - 2 * δ := by ring
  rw [h2]
  exact ExpRate_of_forall_mul_div (by positivity) hvar' (2 * δ) (by linarith)

/-- Proposition 2, global-Lipschitz improvement (p. 13): `α = r`, `β = 2r`, `γ = 1`. -/
theorem proposition2_lipschitz {r B V : ℝ} (hr : 0 < r) (hB : 0 ≤ B) (hV : 0 ≤ V)
    {bias var : ℕ → ℝ}
    (hbias : ∀ l, |bias l| ≤ B * twoPow (-r * (l : ℝ)))
    (hvar0 : ∀ l, 0 ≤ var l)
    (hvar : ∀ l, var l ≤ V * twoPow (-(2 * r) * (l : ℝ))) :
    ExpRate r bias ∧ ExpRate (2 * r) var ∧
      GrowthRate 1 (fun l : ℕ => twoPow (l : ℝ)) :=
  rates_of_pointwise_bounds hr hB hV hbias hvar0 hvar

end Qatlib.Papers.MultilevelMC20.MainResults
