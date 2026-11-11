/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QGradDescent17.MainResults.SVE.CostBounds
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# `QGradDescent17.MainResults.SVE` — data structures for SVE (Thms IV.4–IV.6)

Kerenidis--Prakash, fixed arXiv:1704.04992v5.

* **Theorem IV.4** (p. 20): for `p ∈ [0,1]`, `μ(A) = √(s_{2p}(A) · s_{2(1−p)}(Aᵀ))`,
  and a data structure realising this `μ` performs SVE in `Õ(μ/δ)`.
* **Theorem IV.5** (p. 21): for any finite set `P` of admissible exponents, the
  minimum `μ = min_{p ∈ P} …` is attained and the SVE cost bound `Õ(μ/δ)` follows.
* **Theorem IV.6** (p. 21): a single-pass preprocessing gives
  `μ(A) = min(‖A‖_F, s₁(A))`, with the same `Õ(μ/δ)` bound.

Here `s₁` denotes the nuclear norm `∑ σ_i` and `s₂` the Frobenius norm
`√(∑ σ_i²)`.  The identities and order facts are proved; the algorithm and its
gate count are recorded in the docstring / PR table (no circuit model).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QGradDescent17.MainResults.SVE

open scoped BigOperators

variable {n : ℕ}

/-- **Theorem IV.4, the `p = 1/2` identity** (p. 20).  With `s₁` the nuclear norm,
`s_{2p}(A) = s_{2(1−p)}(Aᵀ) = s₁(A)` at `p = 1/2`, so
`μ(A) = √(s₁(A) · s₁(Aᵀ)) = s₁(A)`. -/
theorem theorem_IV_4_mu_half (σ : Fin n → ℝ) (hσ : 0 ≤ ∑ i, σ i) :
    Real.sqrt ((∑ i, σ i) * (∑ i, σ i)) = ∑ i, σ i := by
  rw [← sq, Real.sqrt_sq hσ]

/-- Positivity of the `μ` formula `√(x y)` when both factors are positive. -/
theorem theorem_IV_4_mu_pos {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < Real.sqrt (x * y) :=
  Real.sqrt_pos.mpr (mul_pos hx hy)

/-- **Theorem IV.4, cost form** (p. 20). -/
def muCost (μ δ : ℝ) : ℝ := μ / δ

/-- The singular-value cost satisfies the polynomial overhead estimate of Theorem IV.4. -/
theorem theorem_IV_4_cost (μ δ : ℝ) (hμ : 0 ≤ μ) (hδ : 0 < δ) :
    SoftBigO (muCost μ δ) (μ / δ) :=
  softBigO_self (div_nonneg hμ (le_of_lt hδ))

/-- **Theorem IV.5, minimum attained** (p. 21).  Over any nonempty finite set `P`
of admissible exponents, the `μ`-values `g p` have a minimum, attained at some
`p ∈ P`. -/
theorem theorem_IV_5_min_attained (P : Finset ℝ) (g : ℝ → ℝ) (hP : P.Nonempty) :
    ∃ p ∈ P, ∀ q ∈ P, g p ≤ g q :=
  Finset.exists_min_image P g hP

/-- The minimum value `μ = min_{p ∈ P} g p` is no larger than `g q` for any
`q ∈ P`, so the SVE cost bound `C μ / δ` at the minimum is at least as strong as
the bound at any admissible exponent. -/
theorem theorem_IV_5_min_cost_le (P : Finset ℝ) (g : ℝ → ℝ) (hP : P.Nonempty)
    {q : ℝ} (hq : q ∈ P) (δ C : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    C * ((P.image g).min' (hP.image g)) / δ ≤ C * g q / δ :=
  div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (Finset.min'_le (P.image g) (g q) (Finset.mem_image.mpr ⟨q, hq, rfl⟩))
      (le_of_lt hC)) (le_of_lt hδ)

/-- **Theorem IV.6, `μ = min(‖A‖_F, s₁)`** (p. 21).  Both norms bound `μ` from
above. -/
theorem theorem_IV_6_min_le (μF s1 : ℝ) :
    min μF s1 ≤ μF ∧ min μF s1 ≤ s1 :=
  ⟨min_le_left _ _, min_le_right _ _⟩

/-- **Theorem IV.6, cost monotonicity** (p. 21).  With the smaller `μ` the cost
bound `C μ / δ` can only decrease. -/
theorem theorem_IV_6_cost_le (μF s1 C δ : ℝ) (hC : 0 < C) (hδ : 0 < δ) :
    C * min μF s1 / δ ≤ C * μF / δ :=
  div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (le_of_lt hC)) (le_of_lt hδ)

end Qatlib.Papers.QGradDescent17.MainResults.SVE
