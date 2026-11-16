/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.ZeroSumGibbs23.MainResults.Model.SourceModel

@[expose] public section


/-!
# RejectCore deterministic core

This module preserves closed algebraic and finite-dimensional source results
from arXiv:2301.03763v1. It does not assert a circuit implementation, concentration
bound, or end-to-end algorithmic complexity.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Matrix
namespace Qatlib.Papers.ZeroSumGibbs23.MainResults.RejectCore
open Qatlib.Papers.ZeroSumGibbs23.MainResults.Model
variable {m n N : ℕ}

/-- The per-coordinate acceptance probability of the exact rejection sampler:
having drawn `j` from `q/ρ`, accept with probability `p_j Z / (Z̃ q_j)`. -/
def acceptProb (p q : Fin n → ℝ) (Z Zt : ℝ) (j : Fin n) : ℝ :=
  p j * Z / (Zt * q j)

/-- The accepted weight at `j` is exactly `p_j (Z/Z̃)`. -/
theorem accepted_weight (p q : Fin n → ℝ) (Z Zt : ℝ)
    (hq : ∀ j, 0 < q j) (hZt : 0 < Zt) (j : Fin n) :
    q j * acceptProb p q Z Zt j = p j * (Z / Zt) := by
  unfold acceptProb
  have hqj : q j ≠ 0 := ne_of_gt (hq j)
  have hZtne : Zt ≠ 0 := ne_of_gt hZt
  field_simp

/-- Total accepted mass: `∑_j q_j · acc_j = Z/Z̃`. -/
theorem accepted_mass (p q : Fin n → ℝ) (Z Zt : ℝ)
    (hp : ∑ j, p j = 1) (hq : ∀ j, 0 < q j) (hZt : 0 < Zt) :
    ∑ j, q j * acceptProb p q Z Zt j = Z / Zt := by
  calc
    ∑ j, q j * acceptProb p q Z Zt j = ∑ j, p j * (Z / Zt) :=
      Finset.sum_congr rfl fun j _ => accepted_weight p q Z Zt hq hZt j
    _ = (∑ j, p j) * (Z / Zt) := by rw [Finset.sum_mul]
    _ = Z / Zt := by rw [hp, one_mul]

/-- If `Z̃ ≤ C Z`, the ideal rejection sampler accepts with probability at least
`1/(Cρ)`; this is the `1/(72Cρ)` lower bound of Proposition 2 before the
constant `72` from polynomial approximation. -/
theorem acceptance_ge (p q : Fin n → ℝ) (Z Zt C ρ : ℝ)
    (hp : ∑ j, p j = 1) (hq : ∀ j, 0 < q j) (hZ : 0 < Z) (hZt : 0 < Zt)
    (hZtC : Zt ≤ C * Z) (hC : 0 < C) (hρ : 0 < ρ) :
    1 / (C * ρ) ≤ (1 / ρ) * ∑ j, q j * acceptProb p q Z Zt j := by
  have hsum := accepted_mass p q Z Zt hp hq hZt
  rw [hsum]
  have hratio : 1 / C ≤ Z / Zt := by
    rw [le_div_iff₀ hZt]
    calc
      (1 / C) * Zt = Zt / C := by ring
      _ ≤ (C * Z) / C := div_le_div_of_nonneg_right hZtC hC.le
      _ = Z := by field_simp
  calc
    1 / (C * ρ) = (1 / ρ) * (1 / C) := by field_simp
    _ ≤ (1 / ρ) * (Z / Zt) := mul_le_mul_of_nonneg_left hratio (by positivity)

/-- Conditioned on acceptance, the output law of the exact rejection sampler is
exactly `p`. -/
theorem accepted_dist (p q : Fin n → ℝ) (Z Zt : ℝ)
    (hp : ∑ j, p j = 1) (hq : ∀ j, 0 < q j) (hZ : 0 < Z) (hZt : 0 < Zt) (j : Fin n) :
    (q j * acceptProb p q Z Zt j) / (∑ k, q k * acceptProb p q Z Zt k) = p j := by
  have hsum := accepted_mass p q Z Zt hp hq hZt
  rw [accepted_weight p q Z Zt hq hZt j, hsum]
  have hne : Z / Zt ≠ 0 := div_ne_zero (ne_of_gt hZ) (ne_of_gt hZt)
  field_simp

end Qatlib.Papers.ZeroSumGibbs23.MainResults.RejectCore
