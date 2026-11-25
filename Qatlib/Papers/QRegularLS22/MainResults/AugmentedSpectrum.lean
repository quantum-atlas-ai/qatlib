/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.QRegularLS22.MainResults.Arithmetic

@[expose] public section

/-!
# QRegularLS22 — spectral bounds for the augmented matrix

Source: arXiv:2206.13143v2 (accepted in Quantum 2023-04-19), Lemma 31 (p.30), the
two norm bounds behind the condition number `κ_L(1 + ‖A‖ / (√λ ‖L‖))` of
Theorem 32 and Eqs. (35), (36), (50)–(52).

The paper's augmented matrix is `A_L = [[A, 0], [√λ L, 0]]`
(`Qatlib.Papers.QRegularLS22.MainResults.augmentedMatrix`).  Its columns are
indexed by `d ⊕ d` and its rows by `N ⊕ N`, so the second column block of `A_L`
is identically zero: `A_L` maps `(x₁, x₂)` to `(A x₁, √λ L x₁)`.

This module proves the two inequalities that the paper's condition-number
argument uses:

* `lemma31_augmented_norm_le`: `‖A_L‖ ≤ ‖A‖ + √λ ‖L‖`;
* `lemma31_augmented_lower_bound_L` and `lemma31_augmented_lower_bound_A`: the
  lower bounds `‖A_L x‖ ≥ (√λ ‖L‖ / κ_L) ‖x‖` and `‖A_L x‖ ≥ (‖A‖ / κ_A) ‖x‖`.

Boundary: the lower bounds hold **only on the first column block**, i.e. for
inputs `(x, 0)`; on the whole space `d ⊕ d` they are false, because a vector
`(0, x₂)` lies in the kernel of `A_L`.  Equivalently, they are the non-zero
singular-value bounds of `A_L`, which is the form the paper uses when it forms
`κ(A_L) = ‖A_L‖ ‖A_L⁺‖` from the pseudo-inverse.  A statement for an arbitrary
`x : d ⊕ d` would not be a paper statement but a false strengthening.  All
norms are the Euclidean (`ℓ²`) norms of `stateVector`, matching the `L2`
operator norm used throughout the paper; the sup-norm (`QState`) spelling of the
source hypothesis is not preserved by the min-max argument and is not used.
-/

set_option autoImplicit false
noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator BigOperators

namespace Qatlib.Papers.QRegularLS22.MainResults

open Qatlib.Papers.QRegularLS22.MainResults
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

/-! ## Euclidean norms on a binary sum of registers -/

/-- Nonnegative real numbers are ordered as their squares are. -/
theorem le_of_sq_le_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ^ 2 ≤ b ^ 2) : a ≤ b := by
  have h' : Real.sqrt (a ^ 2) ≤ Real.sqrt (b ^ 2) := Real.sqrt_le_sqrt h
  rwa [Real.sqrt_sq ha, Real.sqrt_sq hb] at h'

/-- Splitting a state on `I ⊕ J` into its two blocks preserves the Euclidean norm
squared as the sum of the two block norms squared. -/
theorem norm_toEuclidean_sum_sq {I J : Type*} [Fintype I] [Fintype J]
    (u : QState I) (w : QState J) :
    ‖toEuclidean_fromVec (Sum.elim u w)‖ ^ 2
      = ‖toEuclidean_fromVec u‖ ^ 2 + ‖toEuclidean_fromVec w‖ ^ 2 := by
  rw [norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq, norm_toEuclidean_fromVec_sq,
    Fintype.sum_sum_type]
  simp

/-- The Euclidean norm of a block state is at most the sum of the Euclidean norms of
its two blocks. -/
theorem norm_toEuclidean_sum_le {I J : Type*} [Fintype I] [Fintype J]
    (u : QState I) (w : QState J) :
    ‖toEuclidean_fromVec (Sum.elim u w)‖
      ≤ ‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec w‖ := by
  have hsq := norm_toEuclidean_sum_sq u w
  have hC : 0 ≤ ‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec w‖ := by positivity
  have h : ‖toEuclidean_fromVec (Sum.elim u w)‖ ^ 2
      ≤ (‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec w‖) ^ 2 := by
    rw [hsq]
    nlinarith [norm_nonneg (toEuclidean_fromVec u), norm_nonneg (toEuclidean_fromVec w)]
  calc ‖toEuclidean_fromVec (Sum.elim u w)‖
      = Real.sqrt (‖toEuclidean_fromVec (Sum.elim u w)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec w‖) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = ‖toEuclidean_fromVec u‖ + ‖toEuclidean_fromVec w‖ := Real.sqrt_sq hC

/-- The first block of a block state has Euclidean norm at most the norm of the whole
state. -/
theorem norm_toEuclidean_left_le {I J : Type*} [Fintype I] [Fintype J]
    (u : QState I) (w : QState J) :
    ‖toEuclidean_fromVec u‖ ≤ ‖toEuclidean_fromVec (Sum.elim u w)‖ := by
  have hsq := norm_toEuclidean_sum_sq u w
  refine le_of_sq_le_sq (norm_nonneg _) (norm_nonneg _) ?_
  rw [hsq]
  nlinarith [sq_nonneg ‖toEuclidean_fromVec w‖]

/-- The second block of a block state has Euclidean norm at most the norm of the whole
state. -/
theorem norm_toEuclidean_right_le {I J : Type*} [Fintype I] [Fintype J]
    (u : QState I) (w : QState J) :
    ‖toEuclidean_fromVec w‖ ≤ ‖toEuclidean_fromVec (Sum.elim u w)‖ := by
  have hsq := norm_toEuclidean_sum_sq u w
  refine le_of_sq_le_sq (norm_nonneg _) (norm_nonneg _) ?_
  rw [hsq]
  nlinarith [sq_nonneg ‖toEuclidean_fromVec u‖]

/-- A real scalar multiplies the Euclidean norm of a state by its absolute value. -/
theorem norm_toEuclidean_smul {I : Type*} [Fintype I] (c : ℝ) (v : QState I) :
    ‖toEuclidean_fromVec (c • v)‖ = |c| * ‖toEuclidean_fromVec v‖ := by
  have h : toEuclidean_fromVec (c • v) = c • toEuclidean_fromVec v := rfl
  rw [h, norm_smul, Real.norm_eq_abs]

/-! ## The action of the augmented matrix -/

/-- The augmented matrix acts on a pair of column blocks by `(x₁, x₂) ↦
(A x₁, √λ L x₁)`. -/
theorem augmentedMatrix_mulVec {N d : Type*} [Fintype d]
    (A L : Matrix N d ℂ) (lam : ℝ) (x₁ x₂ : QState d) :
    augmentedMatrix A L lam *ᵥ (Sum.elim x₁ x₂)
      = Sum.elim (A *ᵥ x₁) ((Real.sqrt lam) • (L *ᵥ x₁)) := by
  rw [augmentedMatrix, Matrix.fromBlocks_mulVec]
  simp only [Matrix.zero_mulVec, add_zero, Function.comp_def, Sum.elim_inl]
  rw [Matrix.smul_mulVec]

/-- The `L2` operator norm of the augmented matrix is at most `‖A‖ + √λ ‖L‖`. -/
theorem lemma31_augmented_norm_le {N d : Type*} [Fintype N] [Fintype d] [DecidableEq d]
    (A L : Matrix N d ℂ) (lam : ℝ) :
    ‖augmentedMatrix A L lam‖ ≤ ‖A‖ + Real.sqrt lam * ‖L‖ := by
  refine l2_opNorm_le_of_mulVec_le (by positivity) _ fun v => ?_
  set x : QState d := fun i => v (Sum.inl i)
  set y : QState d := fun j => v (Sum.inr j)
  have hv : Sum.elim x y = v := by
    funext w
    cases w <;> rfl
  have hmul : augmentedMatrix A L lam *ᵥ v
      = Sum.elim (A *ᵥ x) ((Real.sqrt lam) • (L *ᵥ x)) := by
    conv_lhs => rw [← hv]
    exact augmentedMatrix_mulVec A L lam x y
  rw [hmul]
  have h1 : ‖toEuclidean_fromVec (A *ᵥ x)‖ ≤ ‖A‖ * ‖toEuclidean_fromVec x‖ :=
    l2_norm_mulVec_fromVec_le A x
  have h2 : ‖toEuclidean_fromVec ((Real.sqrt lam) • (L *ᵥ x))‖
      = Real.sqrt lam * ‖toEuclidean_fromVec (L *ᵥ x)‖ := by
    rw [norm_toEuclidean_smul, abs_of_nonneg (Real.sqrt_nonneg lam)]
  have h3 : ‖toEuclidean_fromVec (L *ᵥ x)‖ ≤ ‖L‖ * ‖toEuclidean_fromVec x‖ :=
    l2_norm_mulVec_fromVec_le L x
  have hx : ‖toEuclidean_fromVec x‖ ≤ ‖toEuclidean_fromVec v‖ := by
    rw [← hv]
    exact norm_toEuclidean_left_le x y
  calc ‖toEuclidean_fromVec (Sum.elim (A *ᵥ x) ((Real.sqrt lam) • (L *ᵥ x)))‖
      ≤ ‖toEuclidean_fromVec (A *ᵥ x)‖
          + ‖toEuclidean_fromVec ((Real.sqrt lam) • (L *ᵥ x))‖ :=
        norm_toEuclidean_sum_le _ _
    _ = ‖toEuclidean_fromVec (A *ᵥ x)‖
          + Real.sqrt lam * ‖toEuclidean_fromVec (L *ᵥ x)‖ := by rw [h2]
    _ ≤ ‖A‖ * ‖toEuclidean_fromVec x‖
          + Real.sqrt lam * (‖L‖ * ‖toEuclidean_fromVec x‖) :=
        add_le_add h1 (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg lam))
    _ = (‖A‖ + Real.sqrt lam * ‖L‖) * ‖toEuclidean_fromVec x‖ := by ring
    _ ≤ (‖A‖ + Real.sqrt lam * ‖L‖) * ‖toEuclidean_fromVec v‖ :=
        mul_le_mul_of_nonneg_left hx (by positivity)

/-- The lower bound `‖A_L x‖ ≥ (√λ ‖L‖ / κ_L) ‖x‖` on the first column block, from the
paper's smallest-singular-value hypothesis on `L`. -/
theorem lemma31_augmented_lower_bound_L {N d : Type*} [Fintype N] [Fintype d]
    [DecidableEq d] (A L : Matrix N d ℂ) {lam κL : ℝ}
    (hLmin : ∀ x : QState d,
      ‖L‖ / κL * ‖toEuclidean_fromVec x‖ ≤ ‖toEuclidean_fromVec (L *ᵥ x)‖) :
    ∀ x : QState d,
      Real.sqrt lam * ‖L‖ / κL * ‖toEuclidean_fromVec x‖
        ≤ ‖toEuclidean_fromVec (augmentedMatrix A L lam *ᵥ (Sum.elim x 0))‖ := by
  intro x
  rw [augmentedMatrix_mulVec]
  have hw : ‖toEuclidean_fromVec ((Real.sqrt lam) • (L *ᵥ x))‖
      = Real.sqrt lam * ‖toEuclidean_fromVec (L *ᵥ x)‖ := by
    rw [norm_toEuclidean_smul, abs_of_nonneg (Real.sqrt_nonneg lam)]
  have hstep : ‖toEuclidean_fromVec ((Real.sqrt lam) • (L *ᵥ x))‖
      ≤ ‖toEuclidean_fromVec (Sum.elim (A *ᵥ x) ((Real.sqrt lam) • (L *ᵥ x)))‖ :=
    norm_toEuclidean_right_le _ _
  rw [hw] at hstep
  have hsplit : Real.sqrt lam * ‖L‖ / κL * ‖toEuclidean_fromVec x‖
      = Real.sqrt lam * (‖L‖ / κL * ‖toEuclidean_fromVec x‖) := by ring
  rw [hsplit]
  calc Real.sqrt lam * (‖L‖ / κL * ‖toEuclidean_fromVec x‖)
      ≤ Real.sqrt lam * ‖toEuclidean_fromVec (L *ᵥ x)‖ :=
        mul_le_mul_of_nonneg_left (hLmin x) (Real.sqrt_nonneg lam)
    _ ≤ ‖toEuclidean_fromVec (Sum.elim (A *ᵥ x) ((Real.sqrt lam) • (L *ᵥ x)))‖ := hstep

/-- The lower bound `‖A_L x‖ ≥ (‖A‖ / κ_A) ‖x‖` on the first column block, from the
paper's smallest-singular-value hypothesis on `A`. -/
theorem lemma31_augmented_lower_bound_A {N d : Type*} [Fintype N] [Fintype d]
    [DecidableEq d] (A L : Matrix N d ℂ) (lam : ℝ) {κA : ℝ}
    (hAmin : ∀ x : QState d,
      ‖A‖ / κA * ‖toEuclidean_fromVec x‖ ≤ ‖toEuclidean_fromVec (A *ᵥ x)‖) :
    ∀ x : QState d,
      ‖A‖ / κA * ‖toEuclidean_fromVec x‖
        ≤ ‖toEuclidean_fromVec (augmentedMatrix A L lam *ᵥ (Sum.elim x 0))‖ := by
  intro x
  rw [augmentedMatrix_mulVec]
  have hstep : ‖toEuclidean_fromVec (A *ᵥ x)‖
      ≤ ‖toEuclidean_fromVec (Sum.elim (A *ᵥ x) ((Real.sqrt lam) • (L *ᵥ x)))‖ :=
    norm_toEuclidean_left_le _ _
  exact (hAmin x).trans hstep

end Qatlib.Papers.QRegularLS22.MainResults
