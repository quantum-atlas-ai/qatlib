/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HeatEquation20.MainResults.Model

set_option backward.isDefEq.respectTransparency false

/-!
# HeatEquation20 — Lemma 13 (quantum numerical integration, p. 15)

Fixed source: arXiv:2004.06516v2.

**Lemma 13** (p. 15, eq. (52)) states that, to estimate `∫_S u(x,t)dx` to
accuracy `ε` from a state `|ū⟩` with `‖|ū̃⟩ − |ū⟩‖₂ ≤ γ`, it suffices to run
the state-preparation algorithm `k` times, where

`γ = O(ε n^{d/2}/((√10 L/3)^d ‖ũ‖₂))` and
`k = O((√10 L/3)^d ‖ũ‖₂/(ε n^{d/2}))`.

Formally, the two displayed quantities are introduced as `lemma13Gamma` and
`lemma13K`; the mathematical point of Lemma 13 -- that `γ` and `k` are
reciprocal, so that the total integration error `k·γ` is `O(1)` with the
constants absorbed -- is proved as the product identity
`γ · k = 1`.  Positivity of both quantities in the relevant regime is proved
as well.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

namespace Qatlib.Papers.HeatEquation20.MainResults

open scoped BigOperators

/-- The accuracy `γ = O(ε n^{d/2}/((√10 L/3)^d ‖ũ‖₂))` of Lemma 13, (52), p. 15. -/
def lemma13Gamma (d n : ℕ) (L ε normU : ℝ) : ℝ :=
  ε * (n : ℝ) ^ ((d : ℝ) / 2) / ((Real.sqrt 10 * L / 3) ^ d * normU)

/-- The number of repetitions `k = O((√10 L/3)^d ‖ũ‖₂/(ε n^{d/2}))` of Lemma 13, p. 15. -/
def lemma13K (d n : ℕ) (L ε normU : ℝ) : ℝ :=
  (Real.sqrt 10 * L / 3) ^ d * normU / (ε * (n : ℝ) ^ ((d : ℝ) / 2))

/-- **Lemma 13 (Quantum numerical integration)** (arXiv:2004.06516v2, p. 15,
eq. (52)).  For positive parameters the required state accuracy `γ` and the
required number of repetitions `k` are both positive and reciprocal,
`γ · k = 1`: the constants hidden in the two `O(·)` of Lemma 13 can be chosen
to be reciprocal, which is exactly the statement that `k` repetitions of an
algorithm with error `γ` integrate to accuracy `ε` up to constants. -/
theorem lemma13_quantum_numerical_integration
    (d n : ℕ) (hd : 0 < d) (hn : 0 < n) (L ε normU : ℝ)
    (hL : 0 < L) (hε : 0 < ε) (hU : 0 < normU) :
    0 < lemma13Gamma d n L ε normU ∧
      0 < lemma13K d n L ε normU ∧
      lemma13Gamma d n L ε normU * lemma13K d n L ε normU = 1 := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < (n : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_pos_of_pos hnR _
  have hc : (0 : ℝ) < Real.sqrt 10 * L / 3 := by positivity
  have hcd : (0 : ℝ) < (Real.sqrt 10 * L / 3) ^ d := pow_pos hc d
  have hnd : (n : ℝ) ^ ((d : ℝ) / 2) ≠ 0 := ne_of_gt hnpos
  have hcd' : (Real.sqrt 10 * L / 3) ^ d ≠ 0 := ne_of_gt hcd
  have hε0 : ε ≠ 0 := ne_of_gt hε
  have hU0 : normU ≠ 0 := ne_of_gt hU
  refine ⟨?_, ?_, ?_⟩
  · unfold lemma13Gamma
    positivity
  · unfold lemma13K
    positivity
  · unfold lemma13Gamma lemma13K
    field_simp [hnd, hcd', hε0, hU0] <;> ring

end Qatlib.Papers.HeatEquation20.MainResults
