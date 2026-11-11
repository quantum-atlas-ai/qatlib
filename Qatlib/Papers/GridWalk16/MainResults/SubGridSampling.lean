/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option backward.isDefEq.respectTransparency false

/-!
# GridWalk16 — sub-grid sampling: Lemma 11 (claim c007)

Fixed paper: arXiv:1612.08958v1, §4 p. 10 (proved p. 10).

**Lemma 11** (p. 10): *if a random walk of `T` steps on the torus of size `N` finds a
marked vertex with probability at least `p`, for `p ≥ 1/74`, then the probability `pG`
that a random sub-grid, sampled from the `Θ(N/T)` sub-grids, contains at least one marked
vertex is at least `p/5`.*

The paper proves this by introducing three probabilities and three inequalities
(p. 10):

```
pml  = Pr[the sampled walk is localized and visits a marked vertex],
pGl  = Pr[the sampled walk is localized and visits a vertex of a sub-grid that
        contains a marked vertex],
pG   = Pr[a random sub-grid contains at least one marked vertex],
```

and establishes

```
p − 2/745 ≤ pml ≤ pGl ≤ 4·pG .        (†)
```

Then `p ≥ 1/74` gives `pG ≥ p/5`.  This file formalises the arithmetic reduction: the
three scalar inequalities (†) are taken as hypotheses (they are the paper's own
intermediate results), and the conclusion `p/5 ≤ pG` is proved.  The `pml ≤ pGl` step is
"clearly" true because every localized walk visiting a marked vertex visits a vertex of a
sub-grid containing a marked vertex (p. 10).

Model note.  Formalising (†) itself requires the torus, the stationary distribution and
the sub-grid decomposition as a probability space; those are not present in the library,
so the reduction is stated over the paper's real-valued probabilities `pml`, `pGl`, `pG`.
No `sorry` in this file.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Qatlib.Papers.GridWalk16.MainResults

/-- The paper's second inequality (p. 10, "clearly, `pml ≤ pGl`"): the probability that a
localized walk visits a marked vertex is at most the probability that it visits a vertex
of a sub-grid that contains a marked vertex.  Stated over the two real probabilities. -/
lemma lemma11_pml_le_pGl (pml pGl : ℝ) (h : pml ≤ pGl) : pml ≤ pGl := h

/-- **Lemma 11 (c007).** Let `p` be the probability that a `T`-step torus walk finds a
marked vertex, and let `pml`, `pGl`, `pG` be the localized/global/sub-grid probabilities of
the proof.  Given the paper's three inequalities `p − 2/745 ≤ pml ≤ pGl ≤ 4·pG` and
`p ≥ 1/74`, the sub-grid probability satisfies `p/5 ≤ pG`.
Paper arXiv:1612.08958v1, Lemma 11, §4 p. 10 (proved p. 10).

Proof (paper p. 10): chaining (†) gives `p − 2/745 ≤ 4·pG`, and `p ≥ 1/74 > 10/745`
gives `(p − 2/745)/4 ≥ p/5`. -/
theorem lemma11_subgrid_probability (p pml pGl pG : ℝ)
    (hp : 1 / 74 ≤ p)
    (h_ml : p - 2 / 745 ≤ pml)
    (h_loc : pml ≤ pGl)
    (h_four : pGl ≤ 4 * pG) :
    p / 5 ≤ pG := by
  -- chain the three inequalities into `p − 2/745 ≤ 4·pG`
  have hchain : p - 2 / 745 ≤ 4 * pG := le_trans h_ml (le_trans h_loc h_four)
  -- from `p ≥ 1/74` get `p ≥ 10/745`
  have hp' : (10 : ℝ) / 745 ≤ p := by
    have hc : (10 : ℝ) / 745 < 1 / 74 := by norm_num
    linarith
  nlinarith [hchain, hp']

end Qatlib.Papers.GridWalk16.MainResults
