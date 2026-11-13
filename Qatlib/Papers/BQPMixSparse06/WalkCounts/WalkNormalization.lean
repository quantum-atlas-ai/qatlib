/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.BQPMixSparse06.WalkCounts.MomentSupport
import Qatlib.Papers.BQPMixSparse06.MainResults.Theorem3DecayIdentity

/-!
# Normalization of walk matrices and moment gaps

The matrix `randomWalkMatrix G d` scales `G` by `d⁻¹`. Its power identities transfer differences
of walk counts to differences of normalized matrix entries, and constant row or column sums
become one after normalization by a nonzero `d`.

For a symmetric zero-one matrix with constant row sums, `second_moment_difference` expresses the
diagonal-minus-off-diagonal second moment as a nonnegative overlap deficit. Distinct rows give a
lower bound of one, as used in the walk-count reductions of [JanzingWocjan2006].

## Main statements

* `randomWalk_delta_eq`: normalization scales a length-`m` entry difference by `(d⁻¹) ^ m`.
* `second_moment_ge_one`: distinct rows force a second-moment difference of at least one.
* `walkCount_thresholds_disjoint`: ordered thresholds at positive scale are incompatible.

## References

* [Janzing and Wocjan, 2006][JanzingWocjan2006]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.BQPMixSparse06.WalkCounts

open Finset Matrix

/-- The normalized matrix `d⁻¹ • G`. -/
def randomWalkMatrix {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) :
    Matrix (Fin N) (Fin N) ℝ :=
  d⁻¹ • G

/-- An entry of `randomWalkMatrix G d` is `d⁻¹ * G i j`. -/
theorem randomWalkMatrix_apply {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (i j : Fin N) : randomWalkMatrix G d i j = d⁻¹ * G i j := by
  simp [randomWalkMatrix, Matrix.smul_apply, smul_eq_mul]

/-- The `m`th power of the normalized matrix is `(d⁻¹) ^ m • G ^ m`. -/
theorem randomWalkMatrix_pow {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (m : ℕ) : (randomWalkMatrix G d) ^ m = (d⁻¹) ^ m • G ^ m := by
  induction m with
  | zero => simp [randomWalkMatrix]
  | succ m ih =>
      rw [pow_succ, ih, pow_succ, randomWalkMatrix]
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      rw [pow_succ]

/-- Every entry of the `m`th power is the corresponding entry of `G ^ m` multiplied by `(d⁻¹) ^
m`. -/
theorem randomWalkMatrix_pow_apply {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (m : ℕ) (i j : Fin N) :
    ((randomWalkMatrix G d) ^ m) i j = (d⁻¹) ^ m * (G ^ m) i j := by
  rw [randomWalkMatrix_pow, Matrix.smul_apply, smul_eq_mul]

/-- The diagonal-minus-off-diagonal difference for the normalized `m`th power is `(d⁻¹) ^ m`
times the corresponding difference for `G ^ m` [JanzingWocjan2006]. -/
theorem randomWalk_delta_eq {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (m : ℕ) (q r : Fin N) :
    ((randomWalkMatrix G d) ^ m) q q - ((randomWalkMatrix G d) ^ m) q r =
      (d⁻¹) ^ m * ((G ^ m) q q - (G ^ m) q r) := by
  rw [randomWalkMatrix_pow_apply, randomWalkMatrix_pow_apply]
  ring

/-- A natural power of the reciprocal of `d` is the reciprocal of the same power of `d`. -/
theorem inv_pow_eq {d : ℝ} (m : ℕ) : (d⁻¹) ^ m = (d ^ m)⁻¹ :=
  inv_pow d m

/-- If each row of `G` sums to the nonzero value `d`, every row of its normalized matrix sums to
one [JanzingWocjan2006]. -/
theorem randomWalkMatrix_row_sum {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hd : d ≠ 0) (hrow : ∀ i, ∑ j, G i j = d) (i : Fin N) :
    ∑ j, randomWalkMatrix G d i j = 1 := by
  simp only [randomWalkMatrix_apply]
  rw [← Finset.mul_sum, hrow, inv_mul_cancel₀ hd]

/-- If each column of `G` sums to the nonzero value `d`, every column of its normalized matrix
sums to one [JanzingWocjan2006]. -/
theorem randomWalkMatrix_col_sum {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : ℝ)
    (hd : d ≠ 0) (hcol : ∀ j, ∑ i, G i j = d) (j : Fin N) :
    ∑ i, randomWalkMatrix G d i j = 1 := by
  simp only [randomWalkMatrix_apply]
  rw [← Finset.mul_sum, hcol, inv_mul_cancel₀ hd]

/-- The negative of the graph Laplacian expression is `G - d • 1` [JanzingWocjan2006]. -/
theorem neg_graphLaplacian_eq {N : ℕ} (G : Matrix (Fin N) (Fin N) ℝ) (d : ℝ) :
    -Qatlib.Papers.BQPMixSparse06.MainResults.graphLaplacian G d =
      G - d • (1 : Matrix (Fin N) (Fin N) ℝ) := by
  unfold Qatlib.Papers.BQPMixSparse06.MainResults.graphLaplacian
  rw [neg_sub]

/-- For a symmetric zero-one matrix with constant row sums, the diagonal-minus-off-diagonal
second moment equals `∑ k, G q k * (1 - G r k)` after casting to real numbers. -/
theorem second_moment_difference {N : ℕ} (G : Matrix (Fin N) (Fin N) ℤ) (d : ℝ)
    (h01 : ∀ i j, G i j = 0 ∨ G i j = 1)
    (hsym : ∀ i j, G i j = G j i)
    (hrow : ∀ i, ∑ j, (G i j : ℝ) = d) (q r : Fin N) :
    ((Qatlib.Papers.BQPMixSparse06.MainResults.realCast G) ^ 2) q q -
        ((Qatlib.Papers.BQPMixSparse06.MainResults.realCast G) ^ 2) q r =
      ∑ k, (G q k : ℝ) * (1 - (G r k : ℝ)) := by
  classical
  have hqq : ((Qatlib.Papers.BQPMixSparse06.MainResults.realCast G) ^ 2) q q
      = ∑ k, (G q k : ℝ) * (G k q : ℝ) := by
    rw [pow_two, Matrix.mul_apply]
    simp [Qatlib.Papers.BQPMixSparse06.MainResults.realCast,
      Matrix.map_apply]
  have hqr : ((Qatlib.Papers.BQPMixSparse06.MainResults.realCast G) ^ 2) q r
      = ∑ k, (G q k : ℝ) * (G k r : ℝ) := by
    rw [pow_two, Matrix.mul_apply]
    simp [Qatlib.Papers.BQPMixSparse06.MainResults.realCast,
      Matrix.map_apply]
  rw [hqq, hqr, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hsym1 : (G k q : ℝ) = (G q k : ℝ) := by rw [hsym k q]
  have hsym2 : (G k r : ℝ) = (G r k : ℝ) := by rw [hsym k r]
  rw [hsym1, hsym2]
  have hq : (G q k : ℝ) = 0 ∨ (G q k : ℝ) = 1 := by
    rcases h01 q k with h | h <;> simp [h]
  rcases hq with h | h <;> rw [h] <;> ring

/-- Two distinct rows of a zero-one matrix with equal row sums have an index where the first
entry is one and the second is zero. -/
theorem exists_one_zero_of_differ {N : ℕ} (G : Matrix (Fin N) (Fin N) ℤ) (d : ℝ)
    (h01 : ∀ i j, G i j = 0 ∨ G i j = 1)
    (hrow : ∀ i, ∑ j, (G i j : ℝ) = d)
    (q r : Fin N) (hdiffer : ∃ k, G q k ≠ G r k) :
    ∃ k, G q k = 1 ∧ G r k = 0 := by
  classical
  set h : Fin N → ℝ := fun k => (G q k : ℝ) - (G r k : ℝ) with hh
  have hsum : ∑ k, h k = 0 := by
    simp only [hh]
    rw [Finset.sum_sub_distrib, hrow q, hrow r, sub_self]
  obtain ⟨k0, hk0⟩ := hdiffer
  have hk0ne : h k0 ≠ 0 := by
    intro hzero
    apply hk0
    have hreal : ((G q k0 : ℤ) : ℝ) = ((G r k0 : ℤ) : ℝ) := by
      have := hzero
      simp only [hh] at this
      exact sub_eq_zero.mp this
    exact Int.cast_injective hreal
  have hval : ∀ k, h k = -1 ∨ h k = 0 ∨ h k = 1 := by
    intro k
    have hq := h01 q k
    have hr := h01 r k
    simp only [hh]
    rcases hq with hq | hq <;> rcases hr with hr | hr <;> simp [hq, hr]
  have hconv : ∀ k, h k = 1 → G q k = 1 ∧ G r k = 0 := by
    intro k hk
    rcases h01 q k with hq | hq <;> rcases h01 r k with hr | hr
    · simp only [hh, hq, hr] at hk
      norm_num at hk
    · simp only [hh, hq, hr] at hk
      norm_num at hk
    · exact ⟨hq, hr⟩
    · simp only [hh, hq, hr] at hk
      norm_num at hk
  rcases hval k0 with hk | hk | hk
  · have hpos : 0 < ∑ k ∈ (Finset.univ \ {k0}), h k := by
      have hsplit := (Finset.add_sum_erase (s := Finset.univ)
        (a := k0) (f := h) (by simp)).symm
      rw [Finset.erase_eq, hsum, hk] at hsplit
      linarith
    obtain ⟨k, hk_mem, hk_pos⟩ :=
      (Finset.exists_lt_of_sum_lt (s := Finset.univ \ {k0})
        (f := fun _ => (0 : ℝ)) (g := h) (by simpa using hpos))
    have hkone : h k = 1 := by
      rcases hval k with h1 | h0 | h1
      · linarith
      · rw [h0] at hk_pos; exact absurd hk_pos (lt_irrefl 0)
      · exact h1
    exact ⟨k, hconv k hkone⟩
  · exact absurd hk hk0ne
  · exact ⟨k0, hconv k0 hk⟩

/-- For a symmetric zero-one matrix with constant row sums, distinct rows `q` and `r` give a
diagonal-minus-off-diagonal second moment at least one [JanzingWocjan2006]. -/
theorem second_moment_ge_one {N : ℕ} (G : Matrix (Fin N) (Fin N) ℤ) (d : ℝ)
    (h01 : ∀ i j, G i j = 0 ∨ G i j = 1)
    (hsym : ∀ i j, G i j = G j i)
    (hrow : ∀ i, ∑ j, (G i j : ℝ) = d)
    (q r : Fin N) (hdiffer : ∃ k, G q k ≠ G r k) :
    1 ≤ ((Qatlib.Papers.BQPMixSparse06.MainResults.realCast G) ^ 2) q q -
        ((Qatlib.Papers.BQPMixSparse06.MainResults.realCast G) ^ 2) q r := by
  obtain ⟨k, hq, hr⟩ := exists_one_zero_of_differ G d h01 hrow q r hdiffer
  rw [second_moment_difference G d h01 hsym hrow q r]
  have hsingle : (1 : ℝ) ≤ ∑ k, (G q k : ℝ) * (1 - (G r k : ℝ)) := by
    have hterm : (1 : ℝ) ≤ (G q k : ℝ) * (1 - (G r k : ℝ)) := by
      rw [hq, hr]; norm_num
    refine le_trans hterm (Finset.single_le_sum
      (s := Finset.univ)
      (f := fun l : Fin N => (G q l : ℝ) * (1 - (G r l : ℝ)))
      (fun l _ => ?_) (Finset.mem_univ k))
    rcases h01 q l with hl | hl <;> rcases h01 r l with hr | hr <;> simp [hl, hr]
  exact hsingle

/-- A quantity cannot be both at least `a * e` and at most `b * e` when `b < a` and `e` is
positive. -/
theorem walkCount_thresholds_disjoint {Delta a b e : ℝ} (hba : b < a) (he : 0 < e) :
    ¬ (a * e ≤ Delta ∧ Delta ≤ b * e) := by
  rintro ⟨h1, h2⟩
  have hlt : b * e < a * e := mul_lt_mul_of_pos_right hba he
  linarith

end Qatlib.Papers.BQPMixSparse06.WalkCounts
