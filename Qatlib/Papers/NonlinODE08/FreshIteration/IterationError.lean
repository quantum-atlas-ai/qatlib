/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic

/-!
# IterationError — accumulated simulation error of the polynomial-iteration algorithm

Leyton--Osborne, *A quantum algorithm to solve nonlinear differential equations*,
fixed arXiv:0812.4423v1.

Source location: Appendix A.3, Proposition 2 and its proof, equations (30)--(33).
There `δ_m = ‖|φ⁽ᵐ⁾⟩ − |ψ⁽ᵐ⁾⟩‖` is the error after `m` rounds, `η` bounds the
error of the simulated evolution `e^{iεH}`, and `γ` is the `O(1)` constant that
depends on the sparsity `s`.  The paper derives the one-round recurrence

  `δ_j ≤ γ (3 δ_{j-1} + η)`,  `j = 1, …, m`,  with `δ_0 = 0`,

and solves it to

  `δ_m ≤ (η/3) (((3γ)^{m+1} − 1)/(3γ − 1) − 1)`.

This module formalises the recurrence contract `ErrorRecurrence` and its exact
closed-form solution.  The derivation of the recurrence from the posterior-state
estimates (30)--(31) is the paper's input to this contract and is not restated
here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NonlinODE08.FreshIteration

/-- Paper equation (32): the per-round error recurrence of the quantum
iteration algorithm, with a perfect initial pair (`δ_0 = 0`). -/
def ErrorRecurrence (δ : ℕ → ℝ) (γ η : ℝ) : Prop :=
  δ 0 = 0 ∧ ∀ j, 1 ≤ j → δ j ≤ γ * (3 * δ (j - 1) + η)

/-- Paper equations (32)--(33), geometric-sum form: a sequence obeying the
one-round recurrence is bounded by `γ η ∑_{i<m} (3γ)^i`. -/
theorem error_geometric_bound (δ : ℕ → ℝ) (γ η : ℝ)
    (hγ : 0 ≤ γ) (h : ErrorRecurrence δ γ η) :
    ∀ m : ℕ, δ m ≤ γ * η * ∑ i ∈ Finset.range m, (3 * γ) ^ i := by
  intro m
  induction m with
  | zero => simp [h.1]
  | succ m ih =>
      let S : ℝ := ∑ i ∈ Finset.range m, (3 * γ) ^ i
      have hstep : δ (m + 1) ≤ γ * (3 * δ m + η) := by
        simpa using h.2 (m + 1) (Nat.succ_le_succ (Nat.zero_le m))
      have hδ : 3 * δ m + η ≤ 3 * (γ * η * S) + η := by
        linarith
      have hmul : S * (3 * γ - 1) = (3 * γ) ^ m - 1 := geom_sum_mul (3 * γ) m
      have hgoal : γ * (3 * (γ * η * S) + η) = γ * η * (S + (3 * γ) ^ m) := by
        linear_combination (γ * η) * hmul
      calc
        δ (m + 1) ≤ γ * (3 * δ m + η) := hstep
        _ ≤ γ * (3 * (γ * η * S) + η) := mul_le_mul_of_nonneg_left hδ hγ
        _ = γ * η * (S + (3 * γ) ^ m) := hgoal
        _ = γ * η * ∑ i ∈ Finset.range (m + 1), (3 * γ) ^ i := by
              rw [Finset.sum_range_succ]

/-- Paper Proposition 2, equation (33): the accumulated error after `m`
iterations is bounded by the displayed closed form.  The hypothesis
`3γ ≠ 1` is exactly the definedness condition of the paper's denominator.
`γ ≥ 0` is the paper's sparsity constant; the algebraic bound is linear in
`η`, so nonnegativity of the simulation-error bound `η` is not needed. -/
theorem accumulated_error_bound (δ : ℕ → ℝ) (γ η : ℝ)
    (hγ : 0 ≤ γ) (h : ErrorRecurrence δ γ η)
    (hden : 3 * γ ≠ 1) (m : ℕ) :
    δ m ≤ (η / 3) * (((3 * γ) ^ (m + 1) - 1) / (3 * γ - 1) - 1) := by
  have hb := error_geometric_bound δ γ η hγ h m
  have hgeom' : ∑ i ∈ Finset.range (m + 1), (3 * γ) ^ i =
      ((3 * γ) ^ (m + 1) - 1) / (3 * γ - 1) := geom_sum_eq hden (m + 1)
  have hshift : (∑ i ∈ Finset.range (m + 1), (3 * γ) ^ i) - 1 =
      (3 * γ) * ∑ i ∈ Finset.range m, (3 * γ) ^ i := by
    rw [Finset.sum_range_succ]
    have hg := geom_sum_mul_add (3 * γ - 1) m
    rw [show (3 * γ - 1) + 1 = 3 * γ by ring] at hg
    nlinarith [hg]
  calc
    δ m ≤ γ * η * ∑ i ∈ Finset.range m, (3 * γ) ^ i := hb
    _ = (η / 3) * ((3 * γ) * ∑ i ∈ Finset.range m, (3 * γ) ^ i) := by ring_nf
    _ = (η / 3) * ((∑ i ∈ Finset.range (m + 1), (3 * γ) ^ i) - 1) := by rw [hshift]
    _ = (η / 3) * (((3 * γ) ^ (m + 1) - 1) / (3 * γ - 1) - 1) := by rw [hgeom']

end Qatlib.Papers.NonlinODE08.FreshIteration
