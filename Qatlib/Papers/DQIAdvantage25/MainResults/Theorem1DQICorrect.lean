/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.DQIAdvantage25.MainResults.Model.CutGirthModel
public import Qatlib.Papers.DQIAdvantage25.MainResults.Lemma2ParityInjective

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Theorem 1: DQI for MaxCut is correct and runs in polynomial time (paper p.8)

Source: Ojas Parekh, *No Quantum Advantage in Decoded Quantum Interferometry for MaxCut*,
arXiv:2509.19966v2 (2025-09-30), Theorem 1, Section 2.2, p.8.

> **Theorem 1.** DQI for MaxCut (Algorithm 2) is correct and runs in polynomial time on any input
> graph `G`.

**Paper proof** (p.7–8). Algorithm 2 sets `l = ⌊(g-1)/2⌋`, prepares the DQI state over
`ℰ_l`, measures in the computational basis, and decodes by solving the `𝔽₂` linear system
`Bᵀβ = Bᵀβ*` (Lemma 1). Correctness has two parts: (a) the decoder is well defined because `f`
is injective on `ℰ_l` at this choice of `l` (Lemma 2, since `2l+1 ≤ g`), and (b) the expected cut
of the resulting distribution is `(m + λmax(A^{(m,l)}))/2` (Lemma 3). Polynomial running time
follows because the DQI state preparation and the `𝔽₂` Gaussian elimination both take
`poly(n, m)` time.

**Formalisation boundary.** Decoder injectivity, the expected cut of the actual
output distribution, and the actual execution-cost envelope are explicit bridge
hypotheses. Defining `dqiExpectedCut` by the desired formula does not establish
that an implemented algorithm attains it. Likewise `dqiStepCount` is a proposed
polynomial envelope, not an execution trace. The theorem below transfers this
envelope to a supplied cost function; it does not construct Algorithm 2.
-/

open scoped BigOperators
open Qatlib.Papers.DQIAdvantage25.MainResults.Model

namespace Qatlib.Papers.DQIAdvantage25.MainResults

namespace Theorem1

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A proposed polynomial envelope for the arithmetic phases of Algorithm 2.
Two cubic phases motivate `N⁶ + 1`, but no execution-cost estimate is proved here;
`hsteps` in the conditional theorem must connect an actual implementation to this
envelope. The paper itself specifies no particular polynomial exponent. -/
def dqiStepCount (N : ℕ) : ℕ := N ^ 6 + 1

/-- `dqiStepCount` is polynomially bounded (witness `k = 6`, `c = 2`). -/
lemma polyBounded_dqiStepCount : PolyBounded dqiStepCount := by
  refine ⟨6, 2, fun N => ?_⟩
  have h1 : N ^ 6 ≤ (N + 1) ^ 6 := Nat.pow_le_pow_left (Nat.le_succ N) 6
  have h2 : 1 ≤ (N + 1) ^ 6 := by
    have hpos : 0 < (N + 1) ^ 6 := pow_pos (Nat.succ_pos N) 6
    omega
  unfold dqiStepCount
  calc N ^ 6 + 1 ≤ (N + 1) ^ 6 + (N + 1) ^ 6 := Nat.add_le_add h1 h2
    _ = 2 * (N + 1) ^ 6 := by ring

/-- Conditional reduction for Theorem 1. Correct decoder injectivity, the
expected cut of an actual output distribution, and the actual execution cost
must be supplied by structural bridges. `dqiStepCount` alone does not certify an
algorithm or its running time. -/
theorem theorem1_from_decoder_and_cost_bridge (G : SimpleGraph V) [DecidableRel G.Adj]
    (actualExpectedCut : ℝ) (steps : ℕ → ℕ)
    (hinj : Function.Injective (parityMap G ((G.girth - 1) / 2)))
    (hcut : actualExpectedCut =
      ((numEdges G : ℝ) + maxEigenvalue (dijMatrix (numEdges G) ((G.girth - 1) / 2))) / 2)
    (hsteps : ∀ N, steps N ≤ dqiStepCount N) :
    Function.Injective (parityMap G ((G.girth - 1) / 2)) ∧
    actualExpectedCut =
      ((numEdges G : ℝ) + maxEigenvalue (dijMatrix (numEdges G) ((G.girth - 1) / 2))) / 2 ∧
    PolyBounded steps := by
  obtain ⟨k, c, hbound⟩ := polyBounded_dqiStepCount
  exact ⟨hinj, hcut, k, c, fun N => (hsteps N).trans (hbound N)⟩

end Theorem1

end Qatlib.Papers.DQIAdvantage25.MainResults
