/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# FermEigState17 Claim c003 — partial eigenstate projection rejection

Fixed paper version: **arXiv:1711.10460**, Section III, p. 4, Eq. (2).

The paper prepares a ground state from a state `|φ⟩` with ground-state overlap
`α₀`.  Given an upper bound `Ẽ₀` on the ground energy with `E₀ ≤ Ẽ₀ < E₁`, it
runs phase estimation only to the resolution `g := E₁ − Ẽ₀` needed to reject
excited states, and restarts whenever the estimated energy is above `Ẽ₀`.  The
paper's argument (quoted): "if we restart every time the energy is found to be
above `Ẽ₀`, then the contribution to the complexity is `1/[α₀(E₁−Ẽ₀)]`. There
will be an additional contribution to the complexity of `1/ε_f` ... giving an
overall scaling of the complexity of `O(1/[α₀(E₁−Ẽ₀)] + 1/ε_f)`" (Eq. (2)).

We model the elementary probabilistic content exactly:

* each trial independently succeeds (returns the ground-state branch) with
  probability `α₀`, so the expected number of trials is the geometric mean
  `∑_{k≥0} (1 − α₀)^k = 1/α₀`
  (`expectedTrials_eq_inv`, via `tsum_geometric_of_lt_one`);
* a rejection-resolution trial costs `1/g` (evolution time `1/g`) and the final
  `ε_f`-accurate estimate costs `1/ε_f`, so the expected total complexity is
  `1/(α₀ g) + 1/ε_f`, exactly Eq. (2);
* under the paper's separation condition `α₀ g > ε_f`, this is `< 2/ε_f`, i.e.
  the `1/α₀` overhead is eliminated, in contrast with full-accuracy repeated
  estimation whose cost is `1/(α₀ ε_f)`.

The literal phrase "eliminate the overhead from α₀" is made precise as the
bound `< 2/ε_f`, which contains no `α₀` factor once `α₀ g > ε_f`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.FermEigState17.MainResults.RestartRejection

/-- Expected number of independent trials until the first success, with
per-trial success probability `p`, written as the survival sum
`∑_{k≥0} (1 − p)^k`. -/
noncomputable def expectedTrials (p : ℝ) : ℝ := ∑' k : ℕ, (1 - p) ^ k

/-- The geometric mean of the number of trials is `1/p` (`0 < p < 1`). -/
theorem expectedTrials_eq_inv (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    expectedTrials p = p⁻¹ := by
  unfold expectedTrials
  have h0 : 0 ≤ 1 - p := by linarith
  have h1 : 1 - p < 1 := by linarith
  rw [tsum_geometric_of_lt_one h0 h1]
  have hp : 1 - (1 - p) = p := by ring
  rw [hp]

/-- Expected total complexity of the restart strategy: `(1/α₀)` trials at
rejection cost `1/g`, plus one final `ε_f`-accurate estimate at cost `1/ε_f`.
Here `g = E₁ − Ẽ₀` is the energy gap that determines the rejection resolution. -/
noncomputable def restartComplexity (α0 g εf : ℝ) : ℝ :=
  expectedTrials α0 * (1 / g) + 1 / εf

/-- Cost of repeated *full-accuracy* phase estimation: `1/(α₀ ε_f)`, the
baseline the paper compares against. -/
noncomputable def fullAccuracyComplexity (α0 εf : ℝ) : ℝ := 1 / (α0 * εf)

/-- **Eq. (2) (arXiv:1711.10460 §III p. 4).**  The expected complexity of the
partial-projection-restart strategy is `1/(α₀ (E₁ − Ẽ₀)) + 1/ε_f`, i.e.
`1/(α₀ g) + 1/ε_f` with `g = E₁ − Ẽ₀`. -/
theorem restartComplexity_eq (α0 g εf : ℝ) (hα0 : 0 < α0) (hα1 : α0 < 1)
    (hg : 0 < g) :
    restartComplexity α0 g εf = 1 / (α0 * g) + 1 / εf := by
  unfold restartComplexity
  rw [expectedTrials_eq_inv α0 hα0 hα1]
  congr 1
  field_simp

/-- **"Eliminating the overhead from α₀" (arXiv:1711.10460 §III p. 4).**  Under
the paper's separation condition `α₀ (E₁ − Ẽ₀) > ε_f`, the restart complexity is
strictly below `2/ε_f`: the `1/α₀` factor disappears from the bound, whereas
full-accuracy repeated estimation still costs `1/(α₀ ε_f)`. -/
theorem restart_eliminates_overlap_overhead (α0 g εf : ℝ)
    (hα0 : 0 < α0) (hα1 : α0 < 1) (hg : 0 < g) (hεf : 0 < εf)
    (hsep : εf < α0 * g) :
    restartComplexity α0 g εf < 2 / εf := by
  rw [restartComplexity_eq α0 g εf hα0 hα1 hg]
  have hpos : 0 < α0 * g := mul_pos hα0 hg
  have hinv : 1 / (α0 * g) < 1 / εf := by
    rw [div_lt_div_iff₀ hpos hεf, one_mul, one_mul]
    exact hsep
  have htwo : (2 : ℝ) / εf = 1 / εf + 1 / εf := by ring
  linarith [hinv, htwo]

/-- The full-accuracy baseline has the paper's `1/(α₀ ε_f)` scaling. -/
theorem fullAccuracyComplexity_eq (α0 εf : ℝ) :
    fullAccuracyComplexity α0 εf = 1 / (α0 * εf) := rfl

end Qatlib.Papers.FermEigState17.MainResults.RestartRejection
