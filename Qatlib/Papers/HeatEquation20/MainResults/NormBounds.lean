/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeatEquation20.MainResults.Model

/-!
# HeatEquation20 — norm bounds on `L^τ |0⟩` (Lemma 14, p. 17; Lemma 28, p. 34)

Fixed source: arXiv:2004.06516v2.

* **Lemma 14** (p. 17, eq. (64); proof in Appendix D, pp. 33–36): with
  `Δt = Δx²/(2dα)` and any integer `τ ≥ 1`,
  `max{1/n^d, 1/(4√τ)^d} ≤ ‖L^τ|0⟩‖₂² ≤ d e^{−τ/(4d)} + (4/n + √(d/(πτ)))^d`.
* **Lemma 28** (p. 34, eq. (D4)): in `d = 1` the return probability satisfies
  `max{1/n, 1/(2√τ)} ≤ ⟨0|L^{2τ}|0⟩ ≤ 4/n + 1/√(πτ)`.

The state `|0⟩` is the indicator of the origin of the grid, and `L^τ` is the
`τ`-fold iterate of the random-walk operator of (13); `‖L^τ|0⟩‖₂²` equals the
return probability `⟨0|L^{2τ}|0⟩` (D3).  Lemmas 14 and 28 were not carried
into this port: their earlier formalisations rested on the unreproduced
Fourier analysis of Appendix D (equation (D2) and the Chernoff bound (D16)),
contained unproven gaps, and were dropped; only the model definitions below
are retained, and the claims remain registered in
`metadata/papers/HeatEquation20.json`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators

/-- The origin state `|0⟩` of the grid (Appendix D, p. 33). -/
def delta0 {d n : ℕ} [NeZero n] (x : Grid d n) : ℝ := if x = 0 then 1 else 0

/-- The state `L^τ |0⟩` after `τ` random-walk steps. -/
def iterHeat {d n : ℕ} [NeZero n] (τ : ℕ) : Grid d n → ℝ :=
  (heatStep (d := d) (n := n))^[τ] (delta0 (d := d) (n := n))

end Qatlib.Papers.HeatEquation20.MainResults
