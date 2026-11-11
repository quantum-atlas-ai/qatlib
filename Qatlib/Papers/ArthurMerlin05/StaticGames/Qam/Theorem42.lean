/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Qam.BinomialTail

/-!
# Theorem 4.2 — error reduction for QAM

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Theorem 4.2 (page 15), proof pages 15--17 (equations (6)--(8)).

Statement (verbatim): let `a, b : ℕ → [0,1]` and `q ∈ poly` satisfy
`a(n) − b(n) ≥ 1/q(n)` for all `n ≥ N`.  Then
`QAM(a,b) ⊆ QAM(1 − 2^{−r}, 2^{−r})` for every `r ∈ poly`.

The proof plays `N` copies of the game in parallel and accepts iff at least
`N·(a+b)/2` repetitions accept.  The key structural claim is that playing the
repetitions independently is optimal: the winning probability for arbitrary
entangled strategies is the largest eigenvalue of
`Σ_{z: Σz_i ≥ N(a+b)/2} Q_{y₁}^{(z₁)} ⊗ ⋯ ⊗ Q_{y_N}^{(z_N)}` (eq. (7)); on a
shared eigenbasis this equals a multi-linear, coordinatewise nondecreasing `f`
(eq. (8)), whose maximum is the independent value (eq. (6)).

## What is formalised here

As for Theorem 3.3, the analytic content is the Chernoff tail estimate on the
number of accepting repetitions, which is proved in `BinomialTail`.  The
tensor-power/eigenbasis comparison (eqs. (6)--(8)) is not yet in the shared
library; see the block boundary notes.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.Qam

/-- Theorem 4.2 (page 15), quantitative core: with `N δ² ≥ 4 r log 2`, the
`N`-fold parallel-repetition majority test has completeness error `≤ 2^{-r}`
(lower tail, threshold `N(a−δ)`) and soundness error `≤ 2^{-r}` (upper tail,
threshold `N(b+δ)`).  This is the Chernoff estimate that drives the paper's
error reduction, proved from the moment-generating bound. -/
theorem theorem_4_2 (N r : ℕ) {a b δ : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 2)
    (hN : (r : ℝ) * Real.log 2 ≤ (N : ℝ) * δ ^ 2 / 4) :
    binomTailLower N a (N * (a - δ)) ≤ (1 / 2 : ℝ) ^ r ∧
      binomTail N b (N * (b + δ)) ≤ (1 / 2 : ℝ) ^ r :=
  ⟨binomTailLower_half_pow N ha0 ha1 hδ0 hδ2 hN,
   binomTail_half_pow N hb0 hb1 hδ0 hδ2 hN⟩

end Qatlib.Papers.ArthurMerlin05.StaticGames.Qam
