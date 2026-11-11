/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.BooleanEnergy.HadamardGram.Carrier

/-!
# Gram energy of Boolean sign matrices

This module forms the sign matrix and its column Gram matrix from Boolean data, then defines an
energy by summing squared off-diagonal Gram entries. The equivalence `energy_zero_iff`
identifies zero energy with a Gram matrix equal to the row count times the identity, as in the
Hadamard search setting of [SuksmonoMinato2019].

## Main statements

* `energy_zero_iff`: Characterize zero energy as an orthogonal frame.
* `gram_abs_le`: Bound each Gram entry by the row count.

## References

* [Suksmono and Minato, 2019][SuksmonoMinato2019]
-/

set_option autoImplicit false
open scoped BigOperators
namespace Qatlib.Foundations.BooleanEnergy.HadamardGram

/-- The real sign matrix obtained by replacing each Boolean entry with its spin. -/
def signMatrix {M N : ℕ} (q : Fin M → Fin N → Bool) : Matrix (Fin M) (Fin N) ℝ :=
  fun r c => spin (q r c)

/-- The column Gram matrix of `signMatrix q`. -/
def gram {M N : ℕ} (q : Fin M → Fin N → Bool) : Matrix (Fin N) (Fin N) ℝ :=
  (signMatrix q).transpose * signMatrix q

/-- The sign matrix has Gram matrix equal to `M` times the identity. -/
def IsOrthogonalFrame {M N : ℕ} (q : Fin M → Fin N → Bool) : Prop :=
  gram q = (M : ℝ) • (1 : Matrix (Fin N) (Fin N) ℝ)

/-- The sum of squared Gram entries over increasing pairs of distinct columns. -/
def energy {M N : ℕ} (q : Fin M → Fin N → Bool) : ℝ :=
  ∑ p : ColumnPair N, (gram q (left p) (right p))^2

/-- Each Gram entry is the sum of rowwise products of the corresponding spins; see
[SuksmonoMinato2019]. -/
theorem gram_apply {M N : ℕ} (q : Fin M → Fin N → Bool) (i j : Fin N) :
    gram q i j = ∑ r, spin (q r i)*spin (q r j) := rfl

/-- Every diagonal Gram entry equals the number of rows. -/
theorem gram_diagonal {M N : ℕ} (q : Fin M → Fin N → Bool) (i : Fin N) :
    gram q i i = (M : ℝ) := by
  rw [gram_apply]
  simp only [← sq,spin_sq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]

/-- The column Gram matrix is symmetric. -/
theorem gram_symmetric {M N : ℕ} (q : Fin M → Fin N → Bool) (i j : Fin N) :
    gram q i j = gram q j i := by
  simp only [gram_apply]
  exact Finset.sum_congr rfl (fun r _ => mul_comm _ _)

/-- The Gram energy is nonnegative. -/
theorem energy_nonneg {M N : ℕ} (q : Fin M → Fin N → Bool) : 0 ≤ energy q :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The Gram energy vanishes exactly when every increasing off-diagonal column-pair entry
vanishes. -/
theorem energy_zero_pairs {M N : ℕ} (q : Fin M → Fin N → Bool) :
    energy q = 0 ↔ ∀ p : ColumnPair N, gram q (left p) (right p) = 0 := by
  unfold energy
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp

/-- The Gram energy vanishes exactly when the sign matrix is an orthogonal frame; see
[SuksmonoMinato2019]. -/
theorem energy_zero_iff {M N : ℕ} (q : Fin M → Fin N → Bool) :
    energy q = 0 ↔ IsOrthogonalFrame q := by
  rw [energy_zero_pairs]
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    by_cases hij : i = j
    · subst j
      simp [gram_diagonal]
    · have hz : gram q i j = 0 := by
        rcases lt_or_gt_of_ne hij with hlt | hlt
        · exact h ⟨(i,j),hlt⟩
        · rw [gram_symmetric]
          exact h ⟨(j,i),hlt⟩
      simp [hz,hij]
  · intro h p
    have hp : left p ≠ right p := ne_of_lt p.property
    change gram q = _ at h
    rw [h]
    simp [hp]

/-- The absolute value of every spin is one. -/
theorem abs_spin (b : Bool) : |spin b| = 1 := by cases b <;> norm_num [spin,bit]

/-- The absolute value of every Gram entry is at most the number of rows. -/
theorem gram_abs_le {M N : ℕ} (q : Fin M → Fin N → Bool) (i j : Fin N) :
    |gram q i j| ≤ (M : ℝ) := by
  rw [gram_apply]
  calc
    _ ≤ ∑ r, |spin (q r i)*spin (q r j)| := Finset.abs_sum_le_sum_abs _ _
    _ = (M : ℝ) := by simp [abs_mul,abs_spin]

/-- The square of every Gram entry is at most the square of the number of rows. -/
theorem gram_sq_le {M N : ℕ} (q : Fin M → Fin N → Bool) (i j : Fin N) :
    (gram q i j)^2 ≤ (M : ℝ)^2 := by
  have h := abs_le.mp (gram_abs_le q i j)
  have hprod := mul_nonneg (sub_nonneg.mpr h.2)
    (show 0 ≤ (M : ℝ)+gram q i j by linarith [h.1])
  nlinarith

end Qatlib.Foundations.BooleanEnergy.HadamardGram
