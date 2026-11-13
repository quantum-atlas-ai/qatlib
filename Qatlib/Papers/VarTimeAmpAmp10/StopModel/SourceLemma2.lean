/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.VariableTimeAmplification

set_option backward.isDefEq.respectTransparency false

/-!
# Source Lemma 2 — the per-stage running-time recurrence (Eq. (5))

Fixed source: Ambainis, *Variable time amplitude amplification and a faster
quantum algorithm for solving systems of linear equations*, fixed preprint
**arXiv:1010.4458v2** (14 Nov 2010).  Lemma 2 is printed on p.6, proof on
p.6–7.

Source statement.  Let `Tᵢ` be the running time of the stage algorithm `Aᵢ`,
`rᵢ ≥ rᵢ′` the success weights of the amplified stage `Aᵢ` and of the base
stage `Bᵢ`.  Then

  `Tᵢ ≤ (1 + 1/(3m−1))·√(rᵢ/rᵢ′)·(Tᵢ₋₁ + 2^{i−1})`.   (5)

The source proof splits into `Aᵢ = Bᵢ` (same state, `rᵢ = rᵢ′`, same time) and
`Aᵢ = Amplify(Bᵢ, k)` (time `(2k+1)(Tᵢ₋₁ + 2^{i−1})` with `2k+1` extracted from
Lemma 1's `rᵢ ≥ (1 − 1/(3m))(2k+1)²rᵢ′`).

The stage model `VtStageChain` carries exactly this data: the stage
records with `ampWeight = rᵢ`, `baseWeight = rᵢ′`, the odd multiplier, the
exact time recurrence `timeRec`, and the Algorithm 2 gain window.  The
paper-layer theorem below states (5) in source notation and derives it from
the theorem `clause89_endpoint`, whose proof uses `g89_event_bounds`:
`Qatlib.Papers.VarTimeAmpAmp10.MainTheorem.clause89_endpoint`.
-/

set_option autoImplicit false
noncomputable section

open Qatlib.Papers.VarTimeAmpAmp10.CoherentAA
open Qatlib.Papers.VarTimeAmpAmp10.MainTheorem

namespace Qatlib.Papers.VarTimeAmpAmp10.StopModel

/-- Fixed arXiv:1010.4458v2, Lemma 2 (printed p.6, eq. (5)).

For the actual stage chain of Algorithms 1–2 with `m ≥ 1` stages, the running
time of stage `i` (for `1 ≤ i ≤ m`) is bounded by the source's
`(1 + 1/(3m−1))·√(rᵢ/rᵢ′)·(Tᵢ₋₁ + 2^{i−1})`, where `rᵢ` and `rᵢ′` are the
stage's amplified and base success weights and `Tᵢ₋₁` is the previous stage's
time. -/
theorem source_lemma2 {m : ℕ} (chain : VtStageChain m) (hm : 1 ≤ m) {i : ℕ}
    (h1 : 1 ≤ i) (h2 : i ≤ m) :
    chain.time i ≤ (1 + 1 / (3 * (m : ℝ) - 1)) *
      (Real.sqrt ((chain.stage i).ampWeight) / Real.sqrt ((chain.stage i).baseWeight)) *
      (chain.time (i - 1) + (2 : ℝ) ^ ((i : ℕ) - 1)) := by
  have h := (clause89_endpoint chain hm).1 i h1 h2
  simpa [eq5StageTimeBound, gainRatio] using h

end Qatlib.Papers.VarTimeAmpAmp10.StopModel
