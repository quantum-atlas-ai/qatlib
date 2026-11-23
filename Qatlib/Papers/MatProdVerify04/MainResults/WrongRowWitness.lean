/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# Parity instances with a single wrong product row

In [BuhrmanSpalek2006], Theorem 11, multiplication over `ZMod 2` by the
all-ones matrix repeats each row parity in every column. Comparing with
the proposed row values transfers the promise of a single mismatched parity
to the product. We also give the Euclidean geometry of row labels and the
operator norm of the diagonal projector onto the mismatched row.
-/

set_option autoImplicit false
noncomputable section

open scoped Matrix.Norms.L2Operator
open scoped ComplexInnerProductSpace
open scoped BigOperators

namespace Qatlib.Papers.MatProdVerify04.MainResults

/-- The parity reduction places the sum of each input row in every product column. -/
theorem parity_product_entry {n : ℕ} (x : Matrix (Fin n) (Fin n) (ZMod 2))
    (i j : Fin n) :
    (x * Matrix.of (fun _ _ : Fin n => (1 : ZMod 2))) i j = ∑ l, x i l := by
  simp [Matrix.mul_apply]

/-- Correct row parities yield a correct product for the repeated row values. -/
theorem parity_product_correct {n : ℕ} (x : Matrix (Fin n) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) (hy : ∀ i, (∑ l, x i l) = y i) :
    x * Matrix.of (fun _ _ : Fin n => (1 : ZMod 2)) =
      Matrix.of (fun i (_ : Fin n) => y i) := by
  ext i j
  exact (parity_product_entry x i j).trans (hy i)

/-- Under the single-mismatch promise, the wrong entries form exactly the row `r`. -/
theorem parity_product_wrong_row {n : ℕ} (x : Matrix (Fin n) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) (r : Fin n)
    (hy : ∀ i, (∑ l, x i l) ≠ y i ↔ i = r) (i j : Fin n) :
    (x * Matrix.of (fun _ _ : Fin n => (1 : ZMod 2))) i j ≠ y i ↔ i = r := by
  rw [parity_product_entry]
  exact hy i

/-- A row-error witness is the corresponding standard basis state. -/
def wrongRowState (n : ℕ) (r : Fin n) : EuclideanSpace ℂ (Fin n) :=
  EuclideanSpace.single r 1

/-- Each row-error witness is a Euclidean unit vector. -/
theorem wrongRowState_norm (n : ℕ) (r : Fin n) : ‖wrongRowState n r‖ = 1 := by
  simp [wrongRowState]

/-- Distinct row-error witnesses are orthogonal in the true Euclidean inner product. -/
theorem wrongRowState_inner (n : ℕ) (r s : Fin n) (hrs : r ≠ s) :
    inner ℂ (wrongRowState n r) (wrongRowState n s) = 0 := by
  simp [wrongRowState, EuclideanSpace.inner_single_left, hrs]

/-- The squared Euclidean separation of two distinct wrong-row witnesses is exactly two. -/
theorem wrongRowState_distance_sq (n : ℕ) (r s : Fin n) (hrs : r ≠ s) :
    ‖wrongRowState n r - wrongRowState n s‖ ^ 2 = 2 := by
  rw [@norm_sub_sq ℂ, wrongRowState_norm, wrongRowState_norm, wrongRowState_inner n r s hrs]
  norm_num

/-- The same separation has a dimension-independent positive constant fixed before all
universal quantifiers. -/
theorem wrongRowState_uniform_separation : ∃ C : ℝ, 0 < C ∧
    ∀ n : ℕ, ∀ r s : Fin n, r ≠ s →
      C ≤ ‖wrongRowState n r - wrongRowState n s‖ ^ 2 := by
  refine ⟨1, by norm_num, ?_⟩
  intro n r s hrs
  rw [wrongRowState_distance_sq n r s hrs]
  norm_num

/-- The diagonal projector onto the wrong rows of the parity-product instance. -/
def parityErrorProjection {n : ℕ} (x : Matrix (Fin n) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun i => if (∑ l, x i l) ≠ y i then 1 else 0

/-- On a single-mismatch instance the diagonal of the projector is the row witness. -/
theorem parity_error_projection_diag {n : ℕ} (x : Matrix (Fin n) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) (r : Fin n) (hy : ∀ i, (∑ l, x i l) ≠ y i ↔ i = r)
    (i : Fin n) :
    parityErrorProjection x y i i = wrongRowState n r i := by
  simp [parityErrorProjection, wrongRowState, PiLp.single_apply, hy]

/-- The projector for a single wrong row has Euclidean operator norm one. -/
theorem wrongRow_operator_norm {n : ℕ} (x : Matrix (Fin n) (Fin n) (ZMod 2))
    (y : Fin n → ZMod 2) (r : Fin n) (hy : ∀ i, (∑ l, x i l) ≠ y i ↔ i = r) :
    ‖parityErrorProjection x y‖ = 1 := by
  have hd : (fun i => if (∑ l, x i l) ≠ y i then (1 : ℂ) else 0) = Pi.single r 1 := by
    funext i
    by_cases hi : i = r
    · subst i
      simp [(hy r).mpr rfl]
    · simp [Pi.single_eq_of_ne hi, show (∑ l, x i l) = y i from
        not_ne_iff.mp fun h => hi ((hy i).mp h)]
  rw [parityErrorProjection, hd, Matrix.l2_opNorm_diagonal, Pi.norm_single]
  simp

end Qatlib.Papers.MatProdVerify04.MainResults
