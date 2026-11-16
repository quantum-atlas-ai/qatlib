/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.MUBSixOpenAI26.CartanBridge.Definitions
public import Qatlib.Concepts.UnbiasedBases.ExclusionCheck.MUB6GlobalTwoCliques

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# MUBSixOpenAI26 — Lemma `exclude:distinct-labels`

Source: OpenAI, *The maximum number of mutually unbiased bases in dimension six*,
fixed Git source `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`,
`exclusion.tex` lines 307--386 (Section 4.2, "From bins to closed vector balls"),
Lemma `exclude:distinct-labels`.

The paper's closed vector ball is
`B_vec(v,s) = { λ e(v+x)/√6 : |λ| = 1, x ∈ ℝ^6, Σⱼ xⱼ = 0, ‖x‖ ≤ s }`.
Two vectors in the same ball with `s < .1` have, after removing global phases,
an unscaled inner-product sum `Σⱼ e(zⱼ)` with `‖z‖ ≤ 2s`, so its modulus is at
least `6 − 2π√6 ‖z‖ > 20/7 > √6`; hence they are neither orthogonal (magnitude
`0`) nor unbiased (magnitude `√6`). Consequently the twelve vectors in two
further MUB bases occupy twelve distinct retained balls.

Reused FQNs (read in full):
* `Mub6BallCover.ExclusionCheck.same_ball_gap`
  — the exact same-ball gap with arbitrary independent unit global phases;
* `Mub6BallCover.ExclusionCheck.labels_injective`
  — injectivity of the twelve slot labels, proved from `same_ball_gap` and from
  the fact that two distinct slots of a MUB family are orthogonal or unbiased.

The model here is the frozen `Phase6 = Fin 6 → ℝ`, `cycleVector v` (amplitude
`(1/√6) · e^{2πi vⱼ}`) and `InBall v s ψ` (zero-mean displacement with squared
norm ≤ `s²`, arbitrary unit global phase). It is the paper's ball with cycles
for phase coordinates.
-/

set_option autoImplicit false

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.UnbiasedBases.ExclusionCheck
open Qatlib.Concepts.UnbiasedBases.ThreeBasis
open Qatlib.Concepts.UnbiasedBases.ThreeBasis

namespace Qatlib.Papers.MUBSixOpenAI26.CartanBridge

/-- Lemma `exclude:distinct-labels` (`exclusion.tex` lines 365--386): two vectors
in the same closed phase ball of radius `s < 1/10` are neither orthogonal nor
mutually unbiased (squared overlap strictly bigger than `1/6`). -/
theorem same_ball_not_orth_or_unbiased
    (v : Phase6) (s : ℝ) (hs0 : 0 ≤ s) (hs : s < 1 / 10)
    (ψ φ : QState (Fin 6)) (hψ : InBall v s ψ) (hφ : InBall v s φ) :
    Inner ψ φ ≠ 0 ∧ Complex.normSq (Inner ψ φ) ≠ (1 : ℝ) / 6 := by
  have hgap := same_ball_gap v s hs0 hs ψ φ hψ hφ
  constructor
  · intro hzero
    rw [hzero, Complex.normSq_zero] at hgap
    norm_num at hgap
  · intro hunbiased
    rw [hunbiased] at hgap
    norm_num at hgap

/-- Lemma `exclude:distinct-labels`, second sentence (`exclusion.tex` lines
367--370): the twelve vectors of two further mutually unbiased orthonormal bases
occupy twelve distinct retained balls, i.e. the slot labelling is injective. -/
theorem twelve_distinct_ball_labels {ι : Type*} (v : ι → Phase6) (s : ι → ℝ)
    (hs : ∀ a, 0 ≤ s a ∧ s a < 1 / 10)
    (V : Fin 2 → Fin 6 → QState (Fin 6)) (hV : IsFamily V)
    (label : Fin 2 × Fin 6 → ι)
    (hcover : ∀ p, InBall (v (label p)) (s (label p)) (V p.1 p.2)) :
    Function.Injective label :=
  labels_injective v s hs V hV label hcover

end Qatlib.Papers.MUBSixOpenAI26.CartanBridge
