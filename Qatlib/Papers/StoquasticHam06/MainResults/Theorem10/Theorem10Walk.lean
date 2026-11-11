/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

/-!
# Walk representation of the matrix-power ratio

Row and column sums express `ExpectedMu` as an average over normalized column weights. The real
transformation `pptMatrixR` has controlled row sums under a function-space norm bound, and
`blockF` extends a nonnegative matrix with row sums at most one to a stochastic matrix on two
Boolean sectors. See [BravyiEtAl2008Stoquastic].

## Main statements

* `expectedMu_eq_walk_expectation`: the successive-mass ratio is a weighted row-sum average.
* `pptRowSum_bounds`: the transformed row sums lie between `1 / 4` and one.
* `blockF_nonneg`: the Boolean-sector extension has nonnegative entries.
* `blockF_rowSum_false`: the false-sector rows sum to one.

## References

* [Bravyi et al., 2008][BravyiEtAl2008Stoquastic]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

open Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

namespace Qatlib.Papers.StoquasticHam06.MainResults.Theorem10

open Matrix

section Basic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sum of the entries in row `x` of `G`. -/
def rowSum (G : Matrix ι ι ℝ) (x : ι) : ℝ := ∑ y, G x y

/-- The sum of the entries in column `x` of `G`. -/
def colSum (G : Matrix ι ι ℝ) (x : ι) : ℝ := ∑ y, G y x

/-- The total mass of `G ^ (L + 1)` equals the sum of column sums of `G ^ L` times the
corresponding row sums of `G`. See [BravyiEtAl2008Stoquastic]. -/
theorem total_succ_eq_sum_col_row (G : Matrix ι ι ℝ) (L : ℕ) :
    (∑ x, ∑ y, (G ^ (L + 1)) x y) = ∑ x, colSum (G ^ L) x * rowSum G x := by
  have hLHS : (∑ x, colSum (G ^ L) x * rowSum G x)
      = ∑ x, ∑ y, ∑ z, (G ^ L) y x * G x z := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    unfold colSum rowSum
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [Finset.mul_sum]
  have hRHS : (∑ x, ∑ y, (G ^ (L + 1)) x y)
      = ∑ a, ∑ b, ∑ c, (G ^ L) a c * G c b := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [pow_succ, Matrix.mul_apply]
  rw [hRHS, hLHS]
  change (∑ a, ∑ c, ∑ b, (G ^ L) a b * G b c)
      = (∑ b, ∑ a, ∑ c, (G ^ L) a b * G b c)
  calc (∑ a, ∑ c, ∑ b, (G ^ L) a b * G b c)
      = (∑ a, ∑ b, ∑ c, (G ^ L) a b * G b c) := by
          refine Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
    _ = (∑ b, ∑ a, ∑ c, (G ^ L) a b * G b c) := Finset.sum_comm

end Basic

section Norm

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in

/-- A function-space operator bound `OperatorNormLE H p1` bounds the absolute value of every row
sum by `p1`. See [BravyiEtAl2008Stoquastic]. -/
theorem abs_rowSum_le (H : Matrix ι ι ℝ) (p1 : ℝ) (hop : OperatorNormLE H p1) (x : ι) :
    |rowSum H x| ≤ p1 := by
  have h := hop (fun _ : ι => (1:ℝ))
  have hnorm1 : ‖(fun _ : ι => (1:ℝ))‖ = 1 := by simp
  have h2 : |rowSum H x| ≤ ‖H.mulVec (fun _ : ι => (1:ℝ))‖ := by
    have hmv : rowSum H x = (H.mulVec (fun _ : ι => (1:ℝ))) x := by
      simp [rowSum, Matrix.mulVec, dotProduct]
    rw [hmv]
    simpa using norm_le_pi_norm (H.mulVec (fun _ : ι => (1:ℝ))) x
  calc |rowSum H x| ≤ ‖H.mulVec (fun _ : ι => (1:ℝ))‖ := h2
    _ ≤ p1 * ‖(fun _ : ι => (1:ℝ))‖ := h
    _ = p1 := by rw [hnorm1, mul_one]

/-- The real matrix `(I - H / q) / 2`, defined entrywise. -/
def pptMatrixR (H : Matrix ι ι ℝ) (q : ℝ) : Matrix ι ι ℝ :=
  fun x y => (1/2) * ((if x = y then 1 else 0) - H x y / q)

omit [Nonempty ι] in

/-- The row sum of `pptMatrixR H q` is `(1 - rowSum H x / q) / 2`. -/
theorem rowSum_pptMatrixR (H : Matrix ι ι ℝ) (q : ℝ) (x : ι) :
    rowSum (pptMatrixR H q) x = (1/2) * (1 - rowSum H x / q) := by
  unfold rowSum pptMatrixR
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_sub_distrib]
  have h1 : (∑ y, (if x = y then (1:ℝ) else 0)) = 1 := by simp
  rw [h1, Finset.sum_div]

/-- If `q > 0`, `OperatorNormLE H p1`, and `p1 ≤ q / 2`, then each row sum of `pptMatrixR H q`
lies in `[1 / 4, 1]`. See [BravyiEtAl2008Stoquastic]. -/
theorem pptRowSum_bounds (H : Matrix ι ι ℝ) (q p1 : ℝ) (hq : 0 < q)
    (hop : OperatorNormLE H p1) (hrow : p1 ≤ q / 2) (x : ι) :
    (1:ℝ)/4 ≤ rowSum (pptMatrixR H q) x ∧ rowSum (pptMatrixR H q) x ≤ 1 := by
  have h1 : |rowSum H x| ≤ p1 := abs_rowSum_le H p1 hop x
  have hlow : -(q/2) ≤ rowSum H x := by linarith [neg_abs_le (rowSum H x)]
  have hup : rowSum H x ≤ q/2 := by linarith [le_abs_self (rowSum H x)]
  rw [rowSum_pptMatrixR H q x]
  constructor
  · have hle : rowSum H x / q ≤ 1/2 := by
      rw [div_le_iff₀ hq]; linarith
    linarith
  · have hge : -(1/2) ≤ rowSum H x / q := by
      rw [le_div_iff₀ hq]; linarith
    linarith

end Norm

section Expectation

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The column sums of `G ^ L` divided by their nonzero total mass sum to one. -/
theorem walkWeight_sum_one (G : Matrix ι ι ℝ) (L : ℕ)
    (hS : (∑ x, ∑ y, (G ^ L) x y) ≠ 0) :
    ∑ x, colSum (G ^ L) x / (∑ x, ∑ y, (G ^ L) x y) = 1 := by
  rw [← Finset.sum_div]
  have hcol : (∑ x, colSum (G ^ L) x) = ∑ x, ∑ y, (G ^ L) x y := by
    unfold colSum
    rw [Finset.sum_comm]
  rw [hcol, div_self hS]

/-- The ratio `ExpectedMu G L` is the sum of row sums of `G` weighted by normalized column sums
of `G ^ L`. See [BravyiEtAl2008Stoquastic]. -/
theorem expectedMu_eq_walk_expectation (G : Matrix ι ι ℝ) (L : ℕ) :
    ExpectedMu G L =
      ∑ x, (colSum (G ^ L) x / (∑ x, ∑ y, (G ^ L) x y)) * rowSum G x := by
  unfold ExpectedMu
  rw [total_succ_eq_sum_col_row]
  have hcongr : (∑ x, (colSum (G ^ L) x / (∑ x, ∑ y, (G ^ L) x y)) * rowSum G x)
      = ∑ x, (colSum (G ^ L) x * rowSum G x) / (∑ x, ∑ y, (G ^ L) x y) := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    ring
  rw [hcongr, Finset.sum_div]

end Expectation

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The matrix on two Boolean sectors with `G` on each diagonal block and the diagonal row
deficits `1 - rowSum G x` on the off-diagonal blocks. -/
def blockF (G : Matrix ι ι ℝ) (a b : Bool × ι) : ℝ :=
  match a, b with
  | (false, x), (false, y) => G x y
  | (false, x), (true, y) => if x = y then 1 - rowSum G x else 0
  | (true, x), (false, y) => if x = y then 1 - rowSum G x else 0
  | (true, x), (true, y) => G x y

/-- If `G` is entrywise nonnegative and has row sums at most one, then every entry of `blockF G`
is nonnegative. See [BravyiEtAl2008Stoquastic]. -/
theorem blockF_nonneg (G : Matrix ι ι ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (hrow : ∀ x, rowSum G x ≤ 1) :
    ∀ a b, 0 ≤ blockF G a b := by
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩
  cases a1 <;> cases b1 <;> simp only [blockF]
  · exact hG _ _
  · split_ifs with h
    · linarith [hrow a2]
    · rfl
  · split_ifs with h
    · linarith [hrow a2]
    · rfl
  · exact hG _ _

/-- Every row of `blockF G` in the false Boolean sector sums to one. See
[BravyiEtAl2008Stoquastic]. -/
theorem blockF_rowSum_false (G : Matrix ι ι ℝ) (x : ι) :
    ∑ b : Bool × ι, blockF G (false, x) b = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have h0 : (∑ y, blockF G (false, x) (false, y)) = rowSum G x := rfl
  have h1 : (∑ y, blockF G (false, x) (true, y)) = 1 - rowSum G x := by
    simp [blockF]
  rw [h0, h1]
  ring

/-- Every row of `blockF G` in the true Boolean sector sums to one. -/
theorem blockF_rowSum_true (G : Matrix ι ι ℝ) (x : ι) :
    ∑ b : Bool × ι, blockF G (true, x) b = 1 := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  have h0 : (∑ y, blockF G (true, x) (false, y)) = 1 - rowSum G x := by
    simp [blockF]
  have h1 : (∑ y, blockF G (true, x) (true, y)) = rowSum G x := rfl
  rw [h0, h1]
  ring

end Block

end Qatlib.Papers.StoquasticHam06.MainResults.Theorem10
