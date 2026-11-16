/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.GraphConfiguration

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — Proposition `exclude:local-certificate`

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`exclusion.tex` lines 639--664 (Section 4.6), Proposition `exclude:local-certificate`.

Statement of the paper: assume the root certificate `exclude:root-data`--
`exclude:root-decomposition` and the arithmetic guarantees of Appendix A. If
Stage C returns a negative result for the Record, then no exact Hadamard matrix
`e(P+δ)` in its closed horizontal radius-`r` ball can be extended, together with
the coordinate basis, by two further mutually unbiased orthonormal bases.

The Lean statement below is the same implication with the Stage C certificate
data made explicit in the frozen interface: a set of candidate vectors
(`candidate source`), closed balls covering every candidate, retained `𝒪`/`𝒰`
edges that contain every genuine orthogonal/unbiased pair, and the certified
absence of the two-six-clique pattern. The four-basis family `B` has its last
two bases among those candidates and covered vectors; the conclusion `¬ IsFamily B`
is exactly the paper's "cannot be extended by two further mutually unbiased
orthonormal bases" (the first two bases of `B` are the fixed coordinate basis and
the Hadamard `H` in the paper's normalization, via `extraIndex`).

Reused FQN: `Mub6BallCover.ExclusionCheck.no_four_of_ball_graphs`
(`MUB6GlobalTwoCliques.lean`), whose proof composes `extra_pair_family`,
`two_bases_force_pattern`, `labels_injective` and `same_ball_gap`. That file's
docstring states it is the local Stage C interface for the original quartet and
not the Sun no-third criterion. The arithmetic and root-certificate conditions of
the paper enter through the retained-edge and coverage hypotheses; the binary64
the comparison margins require a separate verification.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ExclusionCheck
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- Proposition `exclude:local-certificate` (`exclusion.tex` lines 639--648):
if the Stage C certificate for a record is negative (no two-six-clique pattern in
the retained `𝒪`/`𝒰` graphs, with every genuine pair retaining its edge), then
no extension of the coordinate basis and `H` by two further mutually unbiased
orthonormal bases is possible for that record. -/
theorem local_exclusion_certificate {ι σ : Type*}
    (v : ι → Phase6) (s : ι → ℝ) (hs : ∀ a, 0 ≤ s a ∧ s a < 1 / 10)
    (O U : ι → ι → Prop) (candidate : σ → QState (Fin 6) → Prop) (source : σ)
    (hno : ¬ TwoSixPattern O U)
    (hO : ∀ src a b ψ φ, candidate src ψ → candidate src φ →
      InBall (v a) (s a) ψ → InBall (v b) (s b) φ → Inner ψ φ = 0 → O a b)
    (hU : ∀ src a b ψ φ, candidate src ψ → candidate src φ →
      InBall (v a) (s a) ψ → InBall (v b) (s b) φ →
      Complex.normSq (Inner ψ φ) = (1 : ℝ) / 6 → U a b)
    (B : Fin 4 → Fin 6 → QState (Fin 6))
    (hcan : ∀ p : Fin 2 × Fin 6, candidate source (B (extraIndex p.1) p.2))
    (cover : ∀ p : Fin 2 × Fin 6,
      ∃ a, InBall (v a) (s a) (B (extraIndex p.1) p.2)) :
    ¬ IsFamily B :=
  no_four_of_ball_graphs v s hs O U candidate source hno hO hU B hcan cover

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
