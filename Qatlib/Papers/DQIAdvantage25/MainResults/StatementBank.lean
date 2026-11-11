/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.DQIAdvantage25.MainResults.GirthInjectivity

set_option backward.isDefEq.respectTransparency false

/-! Statement bank for
"No Quantum Advantage in Decoded Quantum Interferometry for MaxCut"
(arXiv:2509.19966, 2025).

One core is proved in this block:

- `inj_iff_min_cycle_weight` (c003, Lemma 2): the DQI parity map is
  injective on the subgraphs with at most `l` edges if and only if
  every cycle has more than `2l` edges, i.e. the girth is at least
  `2l+1`. The complete F₂ core (`parityMap_add`, `hwt_add_le`,
  `injOn_of_kernel_min_weight`, `exists_small_kernel_of_ne`) is proved
  unconditionally; the two graph facts (nonzero even subgraphs contain
  cycles; short cycles split into two equal-parity arcs) enter as
  explicit hypotheses.

The remaining six claims are recorded as faithful `Prop` shapes:

- c001 (Theorem 2): if DQI cuts `(1/2 + ε)m` edges in expectation for
  a constant `ε > 0`, the girth must be linear in `m`.
- c002 (Theorem 3): for connected graphs with linear girth,
  `μ = m − n + 1` is constant.
- c004 (Theorem 1): DQI for MaxCut is correct and runs in polynomial
  time on any input graph.
- c005 (Lemma 4): for the tridiagonal DQI matrices with `l = o(m)`,
  `λ_max(A^(m,l)) = o(m)`.
- c006 (Lemma 5): linear-girth graphs partition into `O(1)` many
  vertex-disjoint trees with at most one edge between any two parts.
- c007 (Corollary 1): MaxCut is solvable in polynomial time on
  linear-girth graphs.

The asymptotic claims require graph-family limits, Hermite-polynomial
spectral asymptotics and dynamic-programming correctness accounting
absent from Mathlib and both repositories; they are recorded as
substantive obstacles (see the PR).

No axiom beyond the three standard ones, no `admit`. -/
set_option autoImplicit false

namespace Qatlib.Papers.DQIAdvantage25.MainResults

/-! ## Shared shapes -/

/-- Big-Ω along a family: `f` is eventually bounded below by a fixed
positive multiple of `g` — "linear in `m`", "girth `Ω(m)`". -/
def bigOmegaAt (f g : ℕ → ℝ) : Prop :=
  ∃ (c : ℝ), 0 < c ∧ ∃ N, ∀ n ≥ N, c * g n ≤ f n

/-- Little-o along a family: `f` is eventually dominated by every
positive multiple of `g` — "`l = o(m)`", "`λ_max = o(m)`". -/
def littleOAt (f g : ℕ → ℝ) : Prop :=
  ∀ (c : ℝ), 0 < c → ∃ N, ∀ n ≥ N, f n ≤ c * g n

/-- Family-constant: the quantity `x` is eventually bounded by a
constant independent of `n` — "`μ = m − n + 1` is constant". -/
def eventuallyBounded (x : ℕ → ℝ) : Prop :=
  ∃ (C : ℝ), ∃ N, ∀ n ≥ N, x n ≤ C

/-- Polynomial-time cost: `T` is bounded by a fixed monomial. -/
def polyTime (T : ℕ → ℝ) : Prop :=
  ∃ (C k : ℕ), ∀ n, T n ≤ C * (n : ℝ) ^ k

/-! ## Claim statements -/

/-- **c001 (Theorem 2), girth-barrier shape**: if the expected number
of edges cut by DQI in a graph family is `(1/2 + ε) m` for a constant
`ε > 0`, then the girth must be linear in `m`. -/
def c001_statement (expCut m girth : ℕ → ℝ) (ε : ℝ) : Prop :=
  0 < ε ∧ (∀ n, expCut n = (1 / 2 + ε) * m n)
    ∧ (∀ _n : ℕ, bigOmegaAt girth m)

/-- **c002 (Theorem 3), cycle-rank shape**: for a connected graph
family with girth `Ω(m)`, the cycle rank `μ = m − n + 1` is constant
along the family. -/
def c002_statement (m n μ girth : ℕ → ℝ) : Prop :=
  (∀ k, μ k = m k - n k + 1) ∧ bigOmegaAt girth m → eventuallyBounded μ

/-- **c004 (Theorem 1), DQI-correctness shape**: DQI for MaxCut is
correct (the sampled cut value matches the target polynomial
distribution) and runs in polynomial time on every input graph. -/
def c004_statement (correct : Prop) (T : ℕ → ℝ) : Prop :=
  correct ∧ polyTime T

/-- **c005 (Lemma 4), spectral shape**: for the DQI tridiagonal
matrices `A^(m,l)` with `a_k = √(k(m−k+1))` and `l = o(m)`, the
maximum eigenvalue is `o(m)`. -/
def c005_statement (l lamMax m : ℕ → ℝ) : Prop :=
  littleOAt l m → littleOAt lamMax m

/-- **c006 (Lemma 5), tree-partition shape**: a connected graph with
girth `g = Ω(m)` has a vertex partition into `t` vertex-disjoint
trees with `t = O(1)` and at most one graph edge between any two
parts. -/
def c006_statement (t interEdges m girth : ℕ → ℝ) : Prop :=
  bigOmegaAt girth m → eventuallyBounded t ∧ ∀ k, interEdges k ≤ 1

/-- **c007 (Corollary 1), classical-solvability shape**: MaxCut is
solvable exactly in polynomial time on graph families with girth
`Ω(m)`. -/
def c007_statement (T m girth : ℕ → ℝ) : Prop :=
  bigOmegaAt girth m → polyTime T ∧ ∀ k, m k ≥ 0

end Qatlib.Papers.DQIAdvantage25.MainResults
