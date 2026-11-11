/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev

/-!
# A lower bound for the spectral overlap sum

`limitingDistribution` is the finite sum of products of squared real coordinates of two vectors
in an orthonormal basis. Equal coordinate magnitudes reduce it to a sum of fourth powers.

For a unit vector in a space with an orthonormal basis indexed by `Fin (2 * n + 1)`, this
fourth-power sum is at least `1 / (2 * n + 1)`. This gives the same lower bound for
`limitingDistribution` under the equal-magnitude hypothesis, the algebraic estimate used in the
paper's limiting-distribution calculation. The mathematical setting is described in
[ChildsFarhiGutmann2002].

## Main statements

* `limitingDistribution_of_parity`: reduce the overlap sum to fourth powers.
* `sum_fourth_pow_inner_lower_bound`: the unit-vector fourth-power bound.
* `limitingDistribution_rightRoot_lower_bound`: the overlap bound under equal coordinate
  magnitudes.

## References

* [Childs et al., 2002][ChildsFarhiGutmann2002]
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace RealInnerProductSpace

namespace Qatlib.Papers.QWalkDiff01.MainResults

/-- The sum over an orthonormal basis of the products of the squared real coordinates of `a` and
`c`. -/
def limitingDistribution {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (basis : OrthonormalBasis ι ℝ E) (a c : E) : ℝ :=
  ∑ r : ι, ⟪basis r, a⟫_ℝ ^ 2 * ⟪basis r, c⟫_ℝ ^ 2

/-- If `a` and `c` have equal absolute coordinates in the chosen basis, their spectral overlap
sum equals the sum of the fourth powers of the coordinates of `a`. -/
theorem limitingDistribution_of_parity {ι : Type*} [Fintype ι] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (basis : OrthonormalBasis ι ℝ E) (a c : E)
    (hparity : ∀ r : ι, |⟪basis r, a⟫_ℝ| = |⟪basis r, c⟫_ℝ|) :
    limitingDistribution basis a c = ∑ r : ι, ⟪basis r, a⟫_ℝ ^ 4 := by
  unfold limitingDistribution
  refine Finset.sum_congr rfl ?_
  intro r _
  have hsq : ⟪basis r, c⟫_ℝ ^ 2 = ⟪basis r, a⟫_ℝ ^ 2 := by
    have h := congrArg (fun z : ℝ => z ^ 2) (hparity r)
    simpa [sq_abs] using h.symm
  rw [hsq]
  ring

/-- For a unit vector and an orthonormal basis with `2 * n + 1` elements, the sum of the fourth
powers of its real coordinates is at least `1 / (2 * n + 1)`. See [ChildsFarhiGutmann2002]. -/
theorem sum_fourth_pow_inner_lower_bound (n : ℕ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (basis : OrthonormalBasis (Fin (2 * n + 1)) ℝ E) (a : E) (ha : ‖a‖ = 1) :
    1 / ((2 * n + 1 : ℕ) : ℝ) ≤ ∑ r : Fin (2 * n + 1), ⟪basis r, a⟫_ℝ ^ 4 := by
  set x : Fin (2 * n + 1) → ℝ := fun r => ⟪basis r, a⟫_ℝ ^ 2 with hx
  have hx_nonneg : ∀ r, 0 ≤ x r := fun r => sq_nonneg _
  have hsum : (∑ r, x r) = 1 := by
    simp only [hx]
    rw [basis.sum_sq_inner_right a, ha]
    norm_num
  have hcs : (∑ r ∈ Finset.univ, x r) ^ (1 + 1) / (Finset.univ.card : ℝ) ^ 1 ≤
      ∑ r ∈ Finset.univ, x r ^ (1 + 1) :=
    pow_sum_div_card_le_sum_pow (s := Finset.univ) (f := x) (fun r _ => hx_nonneg r) 1
  have hbound : 1 / ((2 * n + 1 : ℕ) : ℝ) ≤ ∑ r : Fin (2 * n + 1), x r ^ 2 := by
    simpa [hsum, Finset.card_univ, Fintype.card_fin] using hcs
  refine le_trans hbound (le_of_eq ?_)
  refine Finset.sum_congr rfl ?_
  intro r _
  simp only [hx]
  ring

/-- If `a` is a unit vector and `a` and `c` have equal absolute coordinates in a basis with `2 *
n + 1` elements, then `limitingDistribution basis a c` is at least `1 / (2 * n + 1)`. See
[ChildsFarhiGutmann2002]. -/
theorem limitingDistribution_rightRoot_lower_bound (n : ℕ) {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (basis : OrthonormalBasis (Fin (2 * n + 1)) ℝ E) (a c : E) (ha : ‖a‖ = 1)
    (hparity : ∀ r : Fin (2 * n + 1), |⟪basis r, a⟫_ℝ| = |⟪basis r, c⟫_ℝ|) :
    1 / ((2 * n + 1 : ℕ) : ℝ) ≤ limitingDistribution basis a c := by
  rw [limitingDistribution_of_parity basis a c hparity]
  exact sum_fourth_pow_inner_lower_bound n basis a ha

end Qatlib.Papers.QWalkDiff01.MainResults
