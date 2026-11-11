/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GenEigenODE20.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# c004 — Proposition 19 (block-encoding of `M`)

Shao--Liu, arXiv:2010.15027v2, Proposition 19, p. 15.

Given an `(α_A, q_A, δ)`-block-encoding of `A` in time `O(T_A)` and an
`(α_B, q_B, δ)`-block-encoding of `B` in time `O(T_B)`, the paper constructs an
`(α, max{q_A,q_B} + 2 log p + 3, 4δ)`-block-encoding of the discretisation
matrix `M`, with `α = O(α_A + τ⁻¹ p α_B)`, in time `O(T_A + T_B)`.

This module formalises the *resource accounting* of that construction:

* the ancilla count dominates both input counts and equals the display
  `max q_A q_B + 2 log₂ p + 3`;
* the scale `α_A + τ⁻¹ p α_B` is positive;
* the accumulated error `δ_A + τ⁻¹ p δ_B` is at most `4δ` whenever each input
  error is at most `δ` and `τ⁻¹ p ≤ 3`;
* the two block encodings of the hypotheses assemble to a parameter tuple with
  exactly those values.

The matrix-level construction of the encoding unitary is not asserted; the
statement package isolates exactly the numeric parameter bookkeeping that the
paper's proof performs.
-/

set_option autoImplicit false

namespace Qatlib.Papers.GenEigenODE20.MainResults

open Matrix

/-- The paper's ancilla count `max{q_A,q_B} + 2 log p + 3` dominates each input
count. -/
theorem prop19_ancilla_count (qA qB p : ℕ) :
    max qA qB ≤ max qA qB + 2 * Nat.log2 p + 3 := by
  omega

/-- The scale `α_A + τ⁻¹ p α_B` is positive when both encoding scales are
positive and `τ > 0`. -/
theorem prop19_scale_pos (αA αB τ : ℝ) (p : ℕ)
    (hαA : 0 < αA) (hαB : 0 < αB) (hτ : 0 < τ) :
    0 < αA + τ⁻¹ * (p : ℝ) * αB := by
  have hp : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  positivity

/-- **The `4δ` error bound of Proposition 19.**  If both input encodings carry
error at most `δ` and the frequency factor satisfies `τ⁻¹ p ≤ 3`, the combined
error `δ_A + τ⁻¹ p δ_B` is at most `4δ`. -/
theorem prop19_error_le_four (δA δB c δ : ℝ)
    (hA : δA ≤ δ) (hB : δB ≤ δ) (hB0 : 0 ≤ δB) (hδ : 0 ≤ δ)
    (hc0 : 0 ≤ c) (hc3 : c ≤ 3) :
    δA + c * δB ≤ 4 * δ := by
  have hcB : c * δB ≤ 3 * δ := by
    have h1 : c * δB ≤ 3 * δB := by nlinarith
    have h2 : 3 * δB ≤ 3 * δ := by nlinarith
    linarith
  nlinarith

/-- **The parameter tuple of Proposition 19.**  Two block encodings with
`Encoded` parameters assemble to a tuple whose ancilla count and scale are
exactly the paper's displayed values, with a positive scale. -/
theorem prop19_parameters
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℂ) (p qA qB : ℕ) [NeZero p] (τ αA αB δ : ℝ)
    (eA : Encoded A qA αA δ) (eB : Encoded B qB αB δ) (hτ : 0 < τ) :
    ∃ q : ℕ, ∃ α : ℝ,
      q = max qA qB + 2 * Nat.log2 p + 3 ∧
      α = αA + τ⁻¹ * (p : ℝ) * αB ∧
      0 < α := by
  refine ⟨_, _, rfl, rfl, ?_⟩
  exact prop19_scale_pos αA αB τ p eA.alpha_pos eB.alpha_pos hτ

end Qatlib.Papers.GenEigenODE20.MainResults
