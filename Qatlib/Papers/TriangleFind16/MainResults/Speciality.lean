/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.TriangleFind16.MainResults.CostModel

set_option backward.isDefEq.respectTransparency false

/-!
# Extended learning graphs: speciality (Lemma 3.6)

Carette--Laurière--Magniez, fixed arXiv:1609.07786v2, Lemma 3.6 and its proof
(Section 3.2): a stage whose flow is uniform on the used transitions can be reweighted so that
the positive complexity becomes `1`, at the price of a factor `T = |F| / nused`, the speciality,
on the negative complexity.

* `SuperStage.edgeNegCost_rescale`, `SuperStage.edgePosCost_rescale`: edge complexities under a
  rescaling of the weights inside a super edge.
* `SuperStage.negCost_rescale`, `SuperStage.posCost_rescale`: staged complexities under the same
  rescaling.
* `SuperStage.speciality`: Lemma 3.6.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.TriangleFind16.MainResults

variable {E : Type} [Fintype E] {ι : E → Type} [∀ e, Fintype (ι e)]

namespace SuperStage

variable (S : SuperStage E ι)

/-- Rescaling the weights inside a super edge multiplies its negative edge complexity by the
factor. -/
@[simp]
theorem edgeNegCost_rescale (lam : E → ℝ) (e : E) :
    (S.rescale lam).edgeNegCost e = lam e * S.edgeNegCost e := by
  simp only [edgeNegCost, rescale, FlowData.negCost_rescale]

/-- Rescaling the weights inside a super edge divides its positive edge complexity by the factor. -/
theorem edgePosCost_rescale (lam : E → ℝ) (e : E) (h : lam e ≠ 0) :
    (S.rescale lam).edgePosCost e = S.edgePosCost e / lam e := by
  simp only [edgePosCost, rescale, FlowData.posCost_rescale _ _ h]

/-- The negative complexity of a stage after a rescaling of the super-edge weights. -/
theorem negCost_rescale (lam : E → ℝ) (F : Finset E) :
    (S.rescale lam).negCost F = ∑ e ∈ F, lam e * S.edgeNegCost e := by
  simp only [negCost, edgeNegCost_rescale]

/-- The positive complexity of a stage after a rescaling of the super-edge weights. -/
theorem posCost_rescale (lam : E → ℝ) (F : Finset E) (h : ∀ e ∈ F, lam e ≠ 0) :
    (S.rescale lam).posCost F = ∑ e ∈ F, S.p e ^ 2 * (S.edgePosCost e / lam e) := by
  simp only [posCost, rescale]
  refine Finset.sum_congr rfl fun e he => ?_
  show (S.rescale lam).p e ^ 2 * (S.rescale lam).edgePosCost e
      = S.p e ^ 2 * (S.edgePosCost e / lam e)
  rw [edgePosCost_rescale S lam e (h e he)]
  rfl

/-- Lemma 3.6 (Speciality, adapted from Belovs). Let `F` be a stage of super edges whose flow
uses `nused` transitions and is uniform on them, `p_y(e) = 1/nused`. Rescaling the weights inside
each super edge `e` by `c¹(e)/nused` keeps the flow and yields a stage with positive complexity
exactly `1` and negative complexity `T · Exp_{e∈F}[c⁰(e) c¹(e)]`, where `T = |F|/nused`. -/
theorem speciality (F : Finset E) (nused : ℕ) (hnused : 0 < nused) (hF : F.Nonempty)
    (hpos : ∀ e ∈ F, 0 < S.edgePosCost e)
    (hcard : (F.filter fun e => S.p e ≠ 0).card = nused)
    (huniform : ∀ e ∈ F, S.p e ≠ 0 → S.p e = 1 / (nused : ℝ)) :
    (S.rescale (fun e => S.edgePosCost e / (nused : ℝ))).negCost F
        = (F.card : ℝ) / nused * (𝔼 e ∈ F, S.edgeNegCost e * S.edgePosCost e) ∧
      (S.rescale (fun e => S.edgePosCost e / (nused : ℝ))).posCost F = 1 := by
  have hn : (nused : ℝ) ≠ 0 := by exact_mod_cast hnused.ne'
  have hFc : (F.card : ℝ) ≠ 0 := by exact_mod_cast F.card_ne_zero.mpr hF
  have hne : ∀ e ∈ F, S.edgePosCost e / (nused : ℝ) ≠ 0 := by
    intro e he
    exact div_ne_zero (hpos e he).ne' hn
  constructor
  · rw [negCost_rescale]
    have hterm : ∀ e ∈ F,
        S.edgePosCost e / (nused : ℝ) * S.edgeNegCost e
          = (1 / (nused : ℝ)) * (S.edgeNegCost e * S.edgePosCost e) := by
      intro e _
      field_simp
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.expect_eq_sum_div_card]
    field_simp
  · rw [posCost_rescale S (fun e => S.edgePosCost e / (nused : ℝ)) F hne]
    rw [← Finset.sum_filter_add_sum_filter_not (s := F) (p := fun e => S.p e ≠ 0)
      (f := fun e => S.p e ^ 2 * (S.edgePosCost e / (S.edgePosCost e / (nused : ℝ))))]
    have hzero : ∑ e ∈ F.filter (fun e => ¬ S.p e ≠ 0),
        S.p e ^ 2 * (S.edgePosCost e / (S.edgePosCost e / (nused : ℝ))) = 0 := by
      refine Finset.sum_eq_zero fun e he => ?_
      simp only [Finset.mem_filter, not_not] at he
      rw [he.2]
      ring
    have hused : ∑ e ∈ F.filter (fun e => S.p e ≠ 0),
        S.p e ^ 2 * (S.edgePosCost e / (S.edgePosCost e / (nused : ℝ))) = 1 := by
      have hterm : ∀ e ∈ F.filter (fun e => S.p e ≠ 0),
          S.p e ^ 2 * (S.edgePosCost e / (S.edgePosCost e / (nused : ℝ)))
            = 1 / (nused : ℝ) := by
        intro e he
        simp only [Finset.mem_filter] at he
        have hp := huniform e he.1 he.2
        have hq : S.edgePosCost e ≠ 0 := (hpos e he.1).ne'
        rw [hp]
        field_simp
      rw [Finset.sum_congr rfl hterm, Finset.sum_const, hcard, nsmul_eq_mul]
      field_simp
    rw [hused, hzero, add_zero]

end SuperStage

end Qatlib.Papers.TriangleFind16.MainResults
