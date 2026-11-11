/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.StoquasticHam06.MainResults.Theorem10.Theorem10Walk

/-!
# Postselection mass and endpoint weights

For an entrywise nonnegative matrix with row sums at least `1 / 4`, the row sums and total mass
of its powers have explicit lower bounds. `walkDist` normalizes column sums of a power, and
`expectedMu_eq_walkDist` expresses the successive-mass ratio as a weighted row-sum average. See
[BravyiEtAl2008Stoquastic].

## Main statements

* `rowSum_pow_ge`: each row sum of `G ^ L` is at least `(1 / 4) ^ L`.
* `postselect_prob_ge`: the repeated normalized mass has an explicit lower bound.
* `expectedMu_eq_walkDist`: `ExpectedMu` is the row-sum average with weights `walkDist`.

## References

* [Bravyi et al., 2008][BravyiEtAl2008Stoquastic]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.StoquasticHam06.MainResults.Theorem10

open Matrix
open Qatlib.Papers.StoquasticHam06.MainResults.Model.HamiltonianDefs

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Natural powers of an entrywise nonnegative real matrix are entrywise nonnegative. See
[BravyiEtAl2008Stoquastic]. -/
theorem pow_entry_nonneg (G : Matrix ι ι ℝ) (hG : ∀ x y, 0 ≤ G x y) (L : ℕ) :
    ∀ x y, 0 ≤ (G ^ L) x y := by
  induction L with
  | zero =>
      intro x y
      rw [pow_zero]
      by_cases h : x = y
      · subst h; simp
      · simp [h]
  | succ L ih =>
      intro x y
      rw [pow_succ, Matrix.mul_apply]
      exact Finset.sum_nonneg (fun z _ => mul_nonneg (ih x z) (hG z y))

/-- The row sum of `G ^ (L + 1)` at `x` is the sum of `(G ^ L) x z * rowSum G z` over `z`. See
[BravyiEtAl2008Stoquastic]. -/
theorem rowSum_pow_succ (G : Matrix ι ι ℝ) (L : ℕ) (x : ι) :
    rowSum (G ^ (L + 1)) x = ∑ z, (G ^ L) x z * rowSum G z := by
  unfold rowSum
  simp only [pow_succ, Matrix.mul_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [Finset.mul_sum]

/-- If `G` is entrywise nonnegative and each row sum is at least `1 / 4`, then every row sum of
`G ^ L` is at least `(1 / 4) ^ L`. See [BravyiEtAl2008Stoquastic]. -/
theorem rowSum_pow_ge (G : Matrix ι ι ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (hrow : ∀ x, (1 : ℝ) / 4 ≤ rowSum G x) (L : ℕ) (x : ι) :
    ((1 : ℝ) / 4) ^ L ≤ rowSum (G ^ L) x := by
  induction L with
  | zero =>
      rw [pow_zero, pow_zero]
      unfold rowSum
      rw [Finset.sum_eq_single x]
      · simp
      · intro b _ hb
        rw [Matrix.one_apply, if_neg (Ne.symm hb)]
      · intro h; exact absurd (Finset.mem_univ _) h
  | succ L ih =>
      rw [rowSum_pow_succ]
      have hnonneg : ∀ z, 0 ≤ (G ^ L) x z := fun z => pow_entry_nonneg G hG L x z
      have hstep : ∑ z, (G ^ L) x z * ((1 : ℝ) / 4)
          ≤ ∑ z, (G ^ L) x z * rowSum G z :=
        Finset.sum_le_sum (fun z _ => mul_le_mul_of_nonneg_left (hrow z) (hnonneg z))
      have hconst : (∑ z, (G ^ L) x z * ((1 : ℝ) / 4))
          = ((1 : ℝ) / 4) * rowSum (G ^ L) x := by
        unfold rowSum
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun z _ => by ring)
      rw [hconst] at hstep
      calc ((1 : ℝ) / 4) ^ (L + 1) = ((1 : ℝ) / 4) * ((1 : ℝ) / 4) ^ L := by ring
        _ ≤ ((1 : ℝ) / 4) * rowSum (G ^ L) x := by
            exact mul_le_mul_of_nonneg_left ih (by norm_num)
        _ ≤ ∑ z, (G ^ L) x z * rowSum G z := hstep

/-- For an entrywise nonnegative matrix on `2 ^ n` indices with row sums at least `1 / 4`, the
sum of all entries of `G ^ L` is at least `2 ^ n * (1 / 4) ^ L`. See
[BravyiEtAl2008Stoquastic]. -/
theorem total_mass_ge (G : Matrix ι ι ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (hrow : ∀ x, (1 : ℝ) / 4 ≤ rowSum G x) (n L : ℕ)
    (hcard : Fintype.card ι = 2 ^ n) :
    ((2 : ℝ) ^ n) * ((1 : ℝ) / 4) ^ L ≤ ∑ x, ∑ y, (G ^ L) x y := by
  have hsum : (∑ x, ∑ y, (G ^ L) x y) = ∑ x, rowSum (G ^ L) x := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    rfl
  rw [hsum]
  calc ((2 : ℝ) ^ n) * ((1 : ℝ) / 4) ^ L
      = (Fintype.card ι : ℝ) * ((1 : ℝ) / 4) ^ L := by rw [hcard, Nat.cast_pow, Nat.cast_ofNat]
    _ = ∑ _x : ι, ((1 : ℝ) / 4) ^ L := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ ≤ ∑ x, rowSum (G ^ L) x :=
        Finset.sum_le_sum (fun x _ => rowSum_pow_ge G hG hrow L x)

/-- Under entrywise nonnegativity and row sums at least `1 / 4` on `2 ^ n` indices, the `w`th
power of the normalized mass of `G ^ L` is at least `(1 / 4) ^ (w * L)`. See
[BravyiEtAl2008Stoquastic]. -/
theorem postselect_prob_ge (G : Matrix ι ι ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (hrow : ∀ x, (1 : ℝ) / 4 ≤ rowSum G x) (n w L : ℕ)
    (hcard : Fintype.card ι = 2 ^ n) :
    ((1 : ℝ) / 4) ^ (w * L) ≤
      ((((2 : ℝ) ^ n)⁻¹) * ∑ x, ∑ y, (G ^ L) x y) ^ w := by
  have hmass := total_mass_ge G hG hrow n L hcard
  have hpos : (0 : ℝ) < (2 : ℝ) ^ n := by positivity

  have hdiv : ((1 : ℝ) / 4) ^ L ≤ ((2 : ℝ) ^ n)⁻¹ * ∑ x, ∑ y, (G ^ L) x y := by
    rw [← div_eq_inv_mul]
    rw [le_div_iff₀ hpos]
    rw [mul_comm]
    exact hmass
  have hpow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ L) hdiv w

  calc ((1 : ℝ) / 4) ^ (w * L) = (((1 : ℝ) / 4) ^ L) ^ w := by
        rw [mul_comm w L, pow_mul]
    _ ≤ ((((2 : ℝ) ^ n)⁻¹) * ∑ x, ∑ y, (G ^ L) x y) ^ w := hpow

/-- The column sum of `G ^ L` at `y`, divided by the total sum of entries of `G ^ L`. -/
def walkDist (G : Matrix ι ι ℝ) (L : ℕ) (y : ι) : ℝ :=
  colSum (G ^ L) y / (∑ x, ∑ y, (G ^ L) x y)

/-- The weights `walkDist G L` sum to one whenever their common denominator is nonzero. See
[BravyiEtAl2008Stoquastic]. -/
theorem walkDist_sum_one (G : Matrix ι ι ℝ) (L : ℕ)
    (hS : (∑ x, ∑ y, (G ^ L) x y) ≠ 0) :
    ∑ y, walkDist G L y = 1 := by
  unfold walkDist
  rw [← Finset.sum_div]
  have hcol : (∑ y, colSum (G ^ L) y) = ∑ x, ∑ y, (G ^ L) x y := by
    unfold colSum
    rw [Finset.sum_comm]
  rw [hcol, div_self hS]

/-- The ratio `ExpectedMu G L` equals the sum of the row sums of `G` weighted by `walkDist G L`.
See [BravyiEtAl2008Stoquastic]. -/
theorem expectedMu_eq_walkDist (G : Matrix ι ι ℝ) (L : ℕ) :
    ExpectedMu G L = ∑ y, walkDist G L y * rowSum G y := by
  unfold walkDist
  exact expectedMu_eq_walk_expectation G L

end Qatlib.Papers.StoquasticHam06.MainResults.Theorem10
