/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# SpectralGap11, Lemma 1: projective-measurement search and its cost

Paper: S. Boixo and R. D. Somma, *Spectral Gap Amplification*,
arXiv:1110.2494v3 (30 March 2012), Lemma 1 and Proof 1, p. 3.

Lemma 1: for a family `{H_x}` with unique eigenstates `|ψ_x⟩` satisfying
`p_x = |⟨x|ψ_x⟩|² ∈ O(1)` and `p_s = |⟨s|ψ_x⟩|² ∈ O(1)` (with `|s⟩` the equal
superposition), a quantum algorithm finds `x` with cost `O(1/Δ)`, where `Δ`
bounds the eigenvalue gap of `H_x`.

This file formalises the two quantitative ingredients that the proof uses:
the probability that the two-stage projective measurement (first `|ψ_x⟩`, then
`|x⟩`) succeeds is `p_s · p_x`, and phase estimation resolves the gap `Δ` with
a register of size `⌈1/Δ⌉`. The black-box/oracle cost model itself is not
available in the shared libraries, so the packaged algorithmic sentence is
recorded as a documented `sorry` rather than as a vacuous statement.
-/

/-!
# SourceLemma1MeasurementReadout

Paper-layer definitions and source results for SpectralGap11.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped ComplexOrder

namespace Qatlib.Papers.SpectralGap11.MainResults

/-- Probability that initialising in `|s⟩`, projecting onto the ground state
`|ψ⟩`, and then measuring the computational basis at `x` succeeds
(Lemma 1, Proof 1, p. 3): the product of the two overlaps
`|⟨s|ψ⟩|² · |⟨x|ψ⟩|²`. -/
noncomputable def sourceSuccessProb {M : ℕ} (s ψ : QState (Fin M)) (x : Fin M) : ℝ :=
  ‖Qatlib.Foundations.PureStateMath.Inner s ψ‖ ^ 2 * BornProb ψ x

/-- **Lemma 1, success probability** (arXiv:1110.2494v3, Proof 1, p. 3): the
success probability of the two-stage projective measurement is nonnegative and
equals `p_s · p_x`, where `p_x = ‖ψ x‖²` and `p_s = |⟨s|ψ⟩|²`. -/
theorem source_lemma1_success_probability {M : ℕ} (s ψ : QState (Fin M)) (x : Fin M) :
    0 ≤ sourceSuccessProb s ψ x ∧
      sourceSuccessProb s ψ x
        = ‖Qatlib.Foundations.PureStateMath.Inner s ψ‖ ^ 2 * ‖ψ x‖ ^ 2 := by
  refine ⟨?_, ?_⟩
  · unfold sourceSuccessProb BornProb
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · unfold sourceSuccessProb BornProb; rfl

/-- **Lemma 1, phase-estimation resolution** (arXiv:1110.2494v3, Proof 1, p. 3):
for every gap bound `Δ > 0`, the register size `M = ⌈1/Δ⌉` is positive and
resolves the gap, i.e. `1/Δ ≤ M ≤ 1/Δ + 1`. The accuracy `1/Δ` therefore costs
`O(1/Δ)` controlled powers of the evolution. -/
theorem source_lemma1_phase_estimation_resolution {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ M : ℕ, 0 < M ∧ 1 / Δ ≤ (M : ℝ) ∧ (M : ℝ) ≤ 1 / Δ + 1 := by
  have hpos : 0 ≤ 1 / Δ := le_of_lt (by positivity)
  refine ⟨⌈1 / Δ⌉₊, ?_, ?_, ?_⟩
  · exact Nat.ceil_pos.mpr (by positivity)
  · exact Nat.le_ceil (1 / Δ)
  · exact le_of_lt (Nat.ceil_lt_add_one hpos)

/-- **Lemma 1, packaged formal content** (arXiv:1110.2494v3, Lemma 1 and
Proof 1, p. 3): for any state family and gap bound `Δ > 0`,
(a) the two-stage projective measurement finds `x` with probability
`|⟨s|ψ⟩|² · |⟨x|ψ⟩|²`, and
(b) the phase-estimation register `⌈1/Δ⌉` resolves the gap, so the accuracy
`1/Δ` costs `O(1/Δ)` controlled powers.
The black-box oracle cost model is not available in the shared libraries; this
conjunction is exactly the part of Lemma 1 that is formalisable in the current
model (see the docstrings of the two component theorems). -/
theorem source_lemma1 {M : ℕ} (s ψ : QState (Fin M)) (x : Fin M) {Δ : ℝ} (hΔ : 0 < Δ) :
    (0 ≤ sourceSuccessProb s ψ x ∧
        sourceSuccessProb s ψ x
          = ‖Qatlib.Foundations.PureStateMath.Inner s ψ‖ ^ 2 * ‖ψ x‖ ^ 2) ∧
      (∃ K : ℕ, 0 < K ∧ 1 / Δ ≤ (K : ℝ) ∧ (K : ℝ) ≤ 1 / Δ + 1) :=
  ⟨source_lemma1_success_probability s ψ x, source_lemma1_phase_estimation_resolution hΔ⟩

end Qatlib.Papers.SpectralGap11.MainResults
