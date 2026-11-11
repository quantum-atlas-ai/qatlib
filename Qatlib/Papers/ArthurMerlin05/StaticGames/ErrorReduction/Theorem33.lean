/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ArthurMerlin05.StaticGames.Qam.BinomialTail

/-!
# Theorem 3.3 — strong error reduction for QMA without enlarging the witness

Source: Marriott--Watrous, *Quantum Arthur--Merlin Games*, arXiv:cs/0506068v1,
Theorem 3.3 (page 9), proof pages 9--13 (equations (2)--(5)).

Statement (verbatim): let `a, b : ℕ → [0,1]` and `q ∈ poly` satisfy
`a(n) − b(n) ≥ 1/q(n)` for all `n`.  Then
`QMAm(a, b) ⊆ QMAm(1 − 2^{−r}, 2^{−r})` for every `m, r ∈ poly`.

The mechanism is that the error can be driven exponentially small while Merlin's
message length `m(n)` stays **fixed**: the amplified verifier runs `N = 8 q² r`
alternating `A / A†` steps on the *same* `m`-qubit witness and majority-decides
the `N` measurement outcomes.

## What is formalised here

The quantitative heart of the paper's proof (equations (3)--(5)) is the
Chernoff estimate on the binomial tail: on a YES-instance, where each of the `N`
independent repetitions accepts with probability `≥ a`, the probability that the
majority test fails is the lower binomial tail and is at most `2^{-r}`; on a
NO-instance, where each accepts with probability `≤ b`, the probability that the
majority test passes is an upper binomial tail and is at most `2^{-r}`.  Both
bounds are proved from `BinomialTail.binomTail_half_pow` /
`binomTailLower_half_pow`, i.e. from a self-contained Chernoff argument, rather
than assumed.

The remaining construction (turning the `A ↦ B` acceptance-operator map and its
spectral analysis into the class inclusion) is not yet in the shared library;
see the block boundary notes.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ArthurMerlin05.StaticGames.ErrorReduction

open Qatlib.Papers.ArthurMerlin05.StaticGames
open Qatlib.Papers.ArthurMerlin05.StaticGames.Qam

/-- Theorem 3.3 (page 9), quantitative core.  Fix the repetition count `N`, the
gap parameter `δ > 0`, the completeness bound `a` and soundness bound `b`
(all in `[0,1]`).  When `N δ² ≥ 4 r log 2`, the `N`-fold majority test has
completeness error at most `2^{-r}` and soundness error at most `2^{-r}`:

* YES: the lower tail `binomTailLower N a (N(a−δ))` is `≤ (1/2)^r`;
* NO: the upper tail `binomTail N b (N(b+δ))` is `≤ (1/2)^r`.

These are exactly the two tail estimates of the paper's proof (eqs. (3)--(5)),
proved from the Chernoff bound rather than postulated. -/
theorem theorem_3_3 (N r : ℕ) {a b δ : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hδ0 : 0 ≤ δ) (hδ2 : δ ≤ 2)
    (hN : (r : ℝ) * Real.log 2 ≤ (N : ℝ) * δ ^ 2 / 4) :
    binomTailLower N a (N * (a - δ)) ≤ (1 / 2 : ℝ) ^ r ∧
      binomTail N b (N * (b + δ)) ≤ (1 / 2 : ℝ) ^ r :=
  ⟨binomTailLower_half_pow N ha0 ha1 hδ0 hδ2 hN,
   binomTail_half_pow N hb0 hb1 hδ0 hδ2 hN⟩

end Qatlib.Papers.ArthurMerlin05.StaticGames.ErrorReduction
