/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.MatrixGeometry.TupleDeletion.CoordinatePair
import Qatlib.Foundations.MatrixGeometry.TupleDeletion.FiniteGap
import Qatlib.Foundations.MatrixGeometry.TupleDeletion.KernelExistence

/-!
# A quadratic gap for the deletion Gram operator

Defines `deletionGramAction` on the Euclidean space of injective tuples and identifies it with
the sum of the coordinate actions. The theorem `deletionGram_quadratic_gap` bounds its real
quadratic form by its squared output norm, with a coefficient that retains the natural-number
truncation in the fiber cardinality. See [MagniezZur2026] for related background.

## Main statements

* `deletionGramAction_sum`: The deletion Gram action is the sum of all coordinate Gram actions.
* `deletionGram_quadratic_gap`: For a nonempty finite label type, `(a - s + 1) * Re ⟨v, G v⟩ ≤
  ‖G v‖²` for the deletion Gram action `G`, where `s = Fintype.card I` and `a = Fintype.card L -
  (s - 1)` is computed in the natural numbers.

## References

* [Magniez and Zur, 2026][MagniezZur2026]
-/

set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
open Matrix
open scoped Classical BigOperators
namespace Qatlib.Foundations.MatrixGeometry.TupleDeletion
variable {I L : Type*} [Fintype I] [Fintype L]

/-- The linear operator on injective-tuple Euclidean space represented by the deletion Gram
matrix `deletionᴴ * deletion`. -/
def deletionGramAction : EuclideanSpace ℂ (InjectiveTuple I L) →ₗ[ℂ] EuclideanSpace ℂ (InjectiveTuple I L) :=
  Matrix.toEuclideanLin ((deletion (I := I) (L := L))ᴴ*deletion)

/-- The deletion Gram action is the sum of all coordinate Gram actions. -/
theorem deletionGramAction_sum (v : EuclideanSpace ℂ (InjectiveTuple I L)) :
    deletionGramAction v=∑ i : I,coordinateAction (L := L) i v := by
  ext y
  change (((deletion (I := I) (L := L))ᴴ*deletion)*ᵥ WithLp.ofLp v) y=_
  rw [deletion_gram_coordinates,Matrix.sum_mulVec]
  simp [coordinateAction,Matrix.toLpLin_apply]

/-- For a nonempty finite label type, `(a - s + 1) * Re ⟨v, G v⟩ ≤ ‖G v‖²` for the deletion Gram
action `G`, where `s = Fintype.card I` and `a = Fintype.card L - (s - 1)` is computed in the
natural numbers. -/
theorem deletionGram_quadratic_gap (v : EuclideanSpace ℂ (InjectiveTuple I L))
    (hL : 0 < Fintype.card L) :
    ((((Fintype.card L-(Fintype.card I-1) : ℕ) : ℝ)-(Fintype.card I : ℝ)+1))*
      (inner ℂ v (deletionGramAction v)).re ≤ ‖deletionGramAction v‖^2 := by
  let q : I → ℝ := fun i => (inner ℂ v (coordinateAction (L := L) i v)).re
  let B : I → I → ℝ :=
      fun i j => (inner ℂ (coordinateAction (L := L) i v) (coordinateAction (L := L) j v)).re
  have hd (i : I) : B i i=((Fintype.card L-(Fintype.card I-1) : ℕ) : ℝ)*q i := by
    dsimp [B,q]
    rw [← RCLike.re_eq_complex_re,← norm_sq_eq_re_inner (𝕜 := ℂ),coordinate_energy,off_card]
    rw [RCLike.re_eq_complex_re]
  have ho (i j : I) (hij : i ≠ j) : -q i-q j ≤ 2*B i j := coordinate_pair_bound v i j hij hL
  have h := finite_pair_sum_gap B q ((Fintype.card L-(Fintype.card I-1) : ℕ) : ℝ) hd ho
  have hq : ∑ i : I,q i=(inner ℂ v (deletionGramAction v)).re := by
    rw [deletionGramAction_sum,inner_sum]
    exact (map_sum Complex.reAddGroupHom _ _).symm
  have hB : (∑ i : I,∑ j : I,B i j)=‖deletionGramAction v‖^2 := by
    rw [deletionGramAction_sum,norm_sq_eq_re_inner (𝕜 := ℂ),sum_inner]
    simp_rw [inner_sum]
    simp only [map_sum,RCLike.re_eq_complex_re,B]
  rwa [hq,hB] at h
end Qatlib.Foundations.MatrixGeometry.TupleDeletion
