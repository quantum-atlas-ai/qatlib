/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option backward.isDefEq.respectTransparency false

/-!
# QConvexOpt18 finite-difference gradient and Laplace approximations

van Apeldoorn--Gilyén--Gribling--de Wolf, fixed arXiv:1809.00643v4
(accepted in Quantum 2019-12-03; PDF SHA-256
`0eb94a52d9ef09d903beb9638bf07a5c37a55141043d8c4dac043db8cde92da0`), Definitions 8 and 9.

Definition 8 (finite-difference gradient approximation) is
`∇ᵢ^(r) f (x) = (f (x + r eᵢ) - f (x - r eᵢ)) / (2 r)` and Definition 9 (finite-difference
Laplace approximation) is `Δᵢ^(r) f (x) = (f (x + r eᵢ) - 2 f (x) + f (x - r eᵢ)) / r ^ 2`,
with `Δ^(r) f (x) = ∑ᵢ Δᵢ^(r) f (x)`. The vectors live in `Fin n → ℝ` with the sup norm, so
`Metric.closedBall x r` is the paper's `B_∞(x, r)`. The `ℓ₁` norm `‖·‖₁`, which the paper uses
in Lemma 10 and Lemma 17, is provided explicitly as `l1Norm`.

The paper notes immediately after Definition 9 that `Δᵢ^(r) f (x) ≥ 0` for convex `f`; that is
`finDiffLaplaceCoord_nonneg` here, and `finDiffLaplace_nonneg` / `finDiffLaplaceCoord_le_sum`
record the single-coordinate bound against the full Laplace sum that Lemma 17 consumes.

`centralDiffApply_one_eq` is the representation bridge to the already built Frozen stencil
`QuantumAlgorithm.Concepts.GradientOracle.CentralDiff.centralDiffApply`: the paper's two-point
difference is the `m = 1` member of that degree-`2m` family, and
`finDiffGradCoord_eq_centralDiff` transports the paper's coordinate to it.

Boundary: only the finite-difference definitions and their pointwise algebra; no query
algorithm, no expectation over the hypercube and no oracle model lives here.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QConvexOpt18.MainResults

open scoped BigOperators

/-- The `i`-th coordinate vector `eᵢ ∈ ℝ^n` of Definition 8, as an element of the sup-norm
space `Fin n → ℝ`. -/
def coordVec {n : ℕ} (i : Fin n) : Fin n → ℝ := Pi.single i 1

/-- The `i`-th coordinate of `eᵢ` is one. -/
@[simp]
theorem coordVec_apply_self {n : ℕ} (i : Fin n) : coordVec i i = 1 := Pi.single_eq_same i 1

/-- The `j`-th coordinate of `eᵢ` vanishes for `j ≠ i`. -/
theorem coordVec_apply_ne {n : ℕ} {i j : Fin n} (h : j ≠ i) : coordVec i j = 0 :=
  Pi.single_eq_of_ne h 1

/-- Definition 8 of arXiv:1809.00643v4, coordinate form:
`∇ᵢ^(r) f (x) = (f (x + r eᵢ) - f (x - r eᵢ)) / (2 r)`. -/
def finDiffGradCoord {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (r : ℝ) (i : Fin n) : ℝ :=
  (f (z + r • coordVec i) - f (z - r • coordVec i)) / (2 * r)

/-- Definition 8 of arXiv:1809.00643v4:
`∇^(r) f (x) = (∇₁^(r) f (x), …, ∇ₙ^(r) f (x))`. -/
def finDiffGrad {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (r : ℝ) : Fin n → ℝ :=
  fun i => finDiffGradCoord f z r i

/-- Definition 9 of arXiv:1809.00643v4, coordinate form:
`Δᵢ^(r) f (x) = (f (x + r eᵢ) - 2 f (x) + f (x - r eᵢ)) / r ^ 2`. -/
def finDiffLaplaceCoord {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (r : ℝ)
    (i : Fin n) : ℝ :=
  (f (z + r • coordVec i) - 2 * f z + f (z - r • coordVec i)) / r ^ 2

/-- Definition 9 of arXiv:1809.00643v4: `Δ^(r) f (x) = ∑ᵢ Δᵢ^(r) f (x)`. -/
def finDiffLaplace {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (r : ℝ) : ℝ :=
  ∑ i, finDiffLaplaceCoord f z r i

/-- The `ℓ₁` norm `‖v‖₁ = ∑ᵢ |vᵢ|` used for `B₁` in Lemmas 10 and 17. -/
def l1Norm {n : ℕ} (v : Fin n → ℝ) : ℝ := ∑ i, |v i|

/-- The `ℓ₁` norm is nonnegative. -/
@[simp]
theorem l1Norm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ l1Norm v :=
  Finset.sum_nonneg fun i _ => abs_nonneg (v i)

/-- The `r`-ball of the `ℓ₁` norm is contained in the sup-norm `r`-ball: `‖y‖_∞ ≤ ‖y‖₁`. -/
theorem norm_le_l1Norm {n : ℕ} (v : Fin n → ℝ) : ‖v‖ ≤ l1Norm v := by
  refine (pi_norm_le_iff_of_nonneg (l1Norm_nonneg v)).2 fun i => ?_
  calc ‖v i‖ = |v i| := Real.norm_eq_abs _
    _ ≤ ∑ j, |v j| := Finset.single_le_sum (f := fun j => |v j|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)
    _ = l1Norm v := rfl

/-- `z` is the midpoint of `z - r eᵢ` and `z + r eᵢ`. -/
theorem half_smul_add_half_smul_sub {n : ℕ} (z : Fin n → ℝ) (r : ℝ) (i : Fin n) :
    (1 / 2 : ℝ) • (z + r • coordVec i) + (1 / 2 : ℝ) • (z - r • coordVec i) = z := by
  ext j
  by_cases h : j = i
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, coordVec, Pi.single_apply, h,
      if_true, smul_eq_mul]
    ring
  · simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, coordVec, Pi.single_apply, h,
      if_false, mul_zero, smul_eq_mul]
    ring

/-- The paper's remark after Definition 9: for a convex `f` the coordinate Laplace approximation
is nonnegative. Convexity gives `2 f z ≤ f (z + r eᵢ) + f (z - r eᵢ)` at the midpoint. -/
theorem finDiffLaplaceCoord_nonneg {n : ℕ} {f : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} {r : ℝ}
    {s : Set (Fin n → ℝ)} (hconv : ConvexOn ℝ s f) (i : Fin n)
    (hz₂ : z + r • coordVec i ∈ s) (hz₁ : z - r • coordVec i ∈ s)
    (hr : 0 < r) : 0 ≤ finDiffLaplaceCoord f z r i := by
  have hmid : f z ≤ (1 / 2) * f (z + r • coordVec i) + (1 / 2) * f (z - r • coordVec i) := by
    obtain ⟨-, hfun⟩ := hconv
    have hcvx := hfun hz₂ hz₁ (a := (1 / 2 : ℝ)) (b := (1 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    rwa [half_smul_add_half_smul_sub, smul_eq_mul, smul_eq_mul] at hcvx
  rw [finDiffLaplaceCoord, div_nonneg_iff]
  left
  constructor
  · linarith
  · positivity

/-- A single coordinate of the Laplace approximation is bounded by the full Laplace sum, because
the other coordinates are nonnegative. -/
theorem finDiffLaplaceCoord_le_sum {n : ℕ} {f : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} {r : ℝ}
    (hnn : ∀ i, 0 ≤ finDiffLaplaceCoord f z r i) (i : Fin n) :
    finDiffLaplaceCoord f z r i ≤ finDiffLaplace f z r :=
  Finset.single_le_sum (f := fun j => finDiffLaplaceCoord f z r j) (fun j _ => hnn j)
    (Finset.mem_univ i)

/-- The full Laplace approximation is nonnegative when each coordinate is. -/
theorem finDiffLaplace_nonneg {n : ℕ} {f : (Fin n → ℝ) → ℝ} {z : Fin n → ℝ} {r : ℝ}
    (hnn : ∀ i, 0 ≤ finDiffLaplaceCoord f z r i) : 0 ≤ finDiffLaplace f z r :=
  Finset.sum_nonneg fun i _ => hnn i

/-- The finite-difference gradient is the average of the two one-sided differences. -/
theorem finDiffGradCoord_eq {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) (r : ℝ)
    (i : Fin n) (hr : r ≠ 0) :
    finDiffGradCoord f z r i =
      ((f (z + r • coordVec i) - f z) / r + (f z - f (z - r • coordVec i)) / r) / 2 := by
  rw [finDiffGradCoord]
  field_simp
  ring

end Qatlib.Papers.QConvexOpt18.MainResults
