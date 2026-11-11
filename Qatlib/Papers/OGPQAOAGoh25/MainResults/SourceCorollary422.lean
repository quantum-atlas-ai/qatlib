/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OGPQAOAGoh25.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# Corollary 4.2.2 — swapping limits yields sub-optimal solutions under OGP

Fixed source: arXiv:2404.06087v6, Corollary 4.2.2 (p. 12, lines 586–590).

> If the OGP exists in a spin glass type problem, then the swapping of limits
> results in a sub-optimal solution for both random regular graphs and
> Erdős–Rényi graphs. In other words, a necessary condition for the validity of
> limit swapping is that the problem does not exhibit the OGP.

The formal content: if the swap-first performance (`erPerf` for the
Erdős–Rényi ensemble, `regPerf` for the random regular ensemble) is bounded by
`ηOGP`, and `ηOGP < ηOPT` is the strict OGP gap, then both values are strictly
below the optimal value. Consequently, validity of limit swapping (equality
with `ηOPT`) is incompatible with the OGP gap.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OGPQAOAGoh25.MainResults

/-- **Corollary 4.2.2** (arXiv:2404.06087v6, p. 12, lines 586–590).

Under the OGP gap `ηOGP < ηOPT`, the limit-swapped QAOA performance is strictly
sub-optimal both on the Erdős–Rényi ensemble (`erPerf`) and on the random
regular ensemble (`regPerf`). -/
theorem corollary422
    (erPerf regPerf ηOGP ηOPT : ℝ)
    (hER : erPerf ≤ ηOGP) (hReg : regPerf ≤ ηOGP) (hgap : ηOGP < ηOPT) :
    erPerf < ηOPT ∧ regPerf < ηOPT := by
  constructor <;> linarith

/-- **Corollary 4.2.2, necessary-condition form**
(arXiv:2404.06087v6, p. 12, lines 586–590).

If the limit-swapped performance attained `ηOPT` exactly (the swapping of limits
were "valid"), this would contradict the OGP gap `ηOGP < ηOPT`. Hence absence of
the OGP is necessary for the validity of limit swapping. -/
theorem corollary422_necessary
    (perfSwap ηOGP ηOPT : ℝ)
    (hOGP : perfSwap ≤ ηOGP) (hgap : ηOGP < ηOPT)
    (hvalid : perfSwap = ηOPT) : False := by
  linarith

end Qatlib.Papers.OGPQAOAGoh25.MainResults
