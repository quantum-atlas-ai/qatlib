/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.GramGap

/-!
# Positive eigenvalue bounds for deletion Gram matrices

Uses the quadratic Gram gap to bound every positive eigenvalue possessing a nonzero eigenvector.
The general bound retains the natural-number fiber cardinality; `deletionGram_source_gap`
simplifies it to `Fintype.card L - 2 * Fintype.card I + 2` under the stated nonempty-coordinate
and cardinality hypotheses. See [MagniezZur2026] for related background.

## Main statements

* `deletionGram_positive_eigenvalue`: For a nonempty finite label type, a positive eigenvalue
  with a nonzero eigenvector of the deletion Gram action is at least `a - Fintype.card I + 1`,
  where `a = Fintype.card L - (Fintype.card I - 1)` is computed in the natural numbers.
* `deletionGram_source_gap`: If `0 < Fintype.card I ≤ Fintype.card L`, every positive eigenvalue
  with a nonzero eigenvector of the deletion Gram action is at least `(Fintype.card L : ℝ) - 2 *
  Fintype.card I + 2` [MagniezZur2026].

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

/-- For a nonempty finite label type, a positive eigenvalue with a nonzero eigenvector of the
deletion Gram action is at least `a - Fintype.card I + 1`, where `a = Fintype.card L -
(Fintype.card I - 1)` is computed in the natural numbers. -/
theorem deletionGram_positive_eigenvalue (v : EuclideanSpace ℂ (InjectiveTuple I L)) (hv : v ≠ 0)
    (hL : 0 < Fintype.card L) (ev : ℝ) (hev : 0 < ev)
    (he : deletionGramAction v=(ev : ℂ) • v) :
    (((Fintype.card L-(Fintype.card I-1) : ℕ) : ℝ)-(Fintype.card I : ℝ)+1) ≤ ev := by
  have h := deletionGram_quadratic_gap v hL
  have hq : (inner ℂ v (deletionGramAction v)).re=ev*‖v‖^2 := by
    rw [he,inner_smul_right,inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  have hn : ‖deletionGramAction v‖^2=ev^2*‖v‖^2 := by
    rw [he,norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hev,mul_pow]
  rw [hq,hn] at h
  have hp : 0 < ev*‖v‖^2 := mul_pos hev (sq_pos_of_pos (norm_pos_iff.mpr hv))
  apply (mul_le_mul_iff_right₀ hp).mp
  nlinarith [h]

/-- If `0 < Fintype.card I ≤ Fintype.card L`, every positive eigenvalue with a nonzero
eigenvector of the deletion Gram action is at least `(Fintype.card L : ℝ) - 2 * Fintype.card
I + 2` [MagniezZur2026]. -/
theorem deletionGram_source_gap (v : EuclideanSpace ℂ (InjectiveTuple I L)) (hv : v ≠ 0)
    (hI : 0 < Fintype.card I) (hIL : Fintype.card I ≤ Fintype.card L)
    (ev : ℝ) (hev : 0 < ev) (he : deletionGramAction v=(ev : ℂ) • v) :
    (Fintype.card L : ℝ)-2*(Fintype.card I : ℝ)+2 ≤ ev := by
  have hL : 0 < Fintype.card L := lt_of_lt_of_le hI hIL
  have h := deletionGram_positive_eigenvalue v hv hL ev hev he
  rw [Nat.cast_sub (le_trans (Nat.sub_le _ _) hIL),Nat.cast_sub (by omega : 1 ≤ Fintype.card I),Nat.cast_one] at h
  linarith
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
