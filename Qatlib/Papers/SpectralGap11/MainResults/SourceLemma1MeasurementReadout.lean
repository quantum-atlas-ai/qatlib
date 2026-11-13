/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.Qubit

/-!
# SpectralGap11, Lemma 1: overlap expression and reciprocal-gap rounding

Paper: S. Boixo and R. D. Somma, *Spectral Gap Amplification*,
arXiv:1110.2494v3 (30 March 2012), Lemma 1 and Proof 1, p. 3.

This file defines the product `|⟨s|ψ⟩|² * ‖ψ x‖²`, proves its nonnegativity
and unfolds its definition. The vectors `s` and `ψ` are arbitrary `QState`
functions; normalization and eigenstate conditions are not assumed.

For any positive real `Δ`, it also proves the arithmetic fact that a positive
natural number lies between `1/Δ` and `1/Δ + 1`, using the natural ceiling.
The packaged theorem is exactly the conjunction of these two results.
No measurement protocol, phase-estimation correctness, Hamiltonian gap relation,
or algorithmic query-cost bound from Lemma 1 is proved here.
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Qatlib.Foundations.PureStateMath
open scoped ComplexOrder

namespace Qatlib.Papers.SpectralGap11.MainResults

/-- The scalar product `|⟨s|ψ⟩|² * BornProb ψ x`, motivated by the two-stage
measurement in Lemma 1, Proof 1, p. 3. Normalization and a measurement protocol
are not part of this definition. -/
noncomputable def sourceSuccessProb {M : ℕ} (s ψ : QState (Fin M)) (x : Fin M) : ℝ :=
  ‖Qatlib.Foundations.PureStateMath.Inner s ψ‖ ^ 2 * BornProb ψ x

/-- The defined overlap product is nonnegative and equals
`|⟨s|ψ⟩|² * ‖ψ x‖²` for arbitrary vectors, by unfolding `BornProb`. -/
theorem source_lemma1_success_probability {M : ℕ} (s ψ : QState (Fin M)) (x : Fin M) :
    0 ≤ sourceSuccessProb s ψ x ∧
      sourceSuccessProb s ψ x
        = ‖Qatlib.Foundations.PureStateMath.Inner s ψ‖ ^ 2 * ‖ψ x‖ ^ 2 := by
  refine ⟨?_, ?_⟩
  · unfold sourceSuccessProb BornProb
    exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
  · unfold sourceSuccessProb BornProb; rfl

/-- For `Δ > 0`, there is a positive natural `M` with
`1/Δ ≤ M ≤ 1/Δ + 1`, witnessed by `⌈1/Δ⌉₊`. This is an arithmetic rounding
bound only; no phase-estimation resolution or cost is asserted. -/
theorem source_lemma1_phase_estimation_resolution {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ M : ℕ, 0 < M ∧ 1 / Δ ≤ (M : ℝ) ∧ (M : ℝ) ≤ 1 / Δ + 1 := by
  have hpos : 0 ≤ 1 / Δ := le_of_lt (by positivity)
  refine ⟨⌈1 / Δ⌉₊, ?_, ?_, ?_⟩
  · exact Nat.ceil_pos.mpr (by positivity)
  · exact Nat.le_ceil (1 / Δ)
  · exact le_of_lt (Nat.ceil_lt_add_one hpos)

/-- Package the nonnegativity and definitional equality of the overlap product
with the positive-natural rounding bound for `1/Δ`. This conjunction contains
no algorithm existence, measurement correctness, or complexity assertion. -/
theorem source_lemma1 {M : ℕ} (s ψ : QState (Fin M)) (x : Fin M) {Δ : ℝ} (hΔ : 0 < Δ) :
    (0 ≤ sourceSuccessProb s ψ x ∧
        sourceSuccessProb s ψ x
          = ‖Qatlib.Foundations.PureStateMath.Inner s ψ‖ ^ 2 * ‖ψ x‖ ^ 2) ∧
      (∃ K : ℕ, 0 < K ∧ 1 / Δ ≤ (K : ℝ) ∧ (K : ℝ) ≤ 1 / Δ + 1) :=
  ⟨source_lemma1_success_probability s ψ x, source_lemma1_phase_estimation_resolution hΔ⟩

end Qatlib.Papers.SpectralGap11.MainResults
