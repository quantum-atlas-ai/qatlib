/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic
public import Qatlib.Papers.ConvexVolEst19.MainResults.LowerBound.SourceLowerBound

@[expose] public section


/-!
# Convexity of the volume lower-bound gadget

The coordinate model from arXiv:1908.03903v3, Section 6, is characterized
by pairwise absolute-value inequalities. This also covers dimensions zero
and one, where the old coordinate model is the whole space.
-/

set_option autoImplicit false

namespace Qatlib.Papers.ConvexVolEst19.MainResults.LowerBound

/-- Membership in the gadget is equivalent to all pairwise coordinate bounds. -/
theorem mem_gadget_iff {n : ℕ} (x : Fin n → ℝ) :
    x ∈ CnBody n ↔ ∀ i j, i ≠ j → |x i| + |x j| ≤ 1 := by
  constructor
  · rintro (hc | ⟨k, hk | hk⟩) i j hij
    · linarith [hc i, hc j]
    all_goals
      have hkabs : 1 / 2 ≤ |x k| := by
        first | exact hk.1.trans (le_abs_self _) | linarith [neg_le_abs (x k), hk.1]
      have hbound := hk.2
      by_cases hik : i = k
      · subst i
        linarith [hbound j (Ne.symm hij)]
      · by_cases hjk : j = k
        · subst j
          exact hbound i hik
        · linarith [hbound i hik, hbound j hjk]
  · intro h
    by_cases hc : Hn x
    · exact Or.inl hc
    · unfold Hn at hc
      push Not at hc
      obtain ⟨i, hi⟩ := hc
      right
      refine ⟨i, ?_⟩
      by_cases hsign : 0 ≤ x i
      · left
        refine ⟨?_, fun k hk => h k i hk⟩
        rw [abs_of_nonneg hsign] at hi
        exact hi.le
      · right
        refine ⟨?_, fun k hk => h k i hk⟩
        rw [abs_of_neg (lt_of_not_ge hsign)] at hi
        linarith

/-- The cube-and-pyramid gadget is convex, including its degenerate dimensions. -/
theorem source_lemma_6_1 (n : ℕ) : Convex ℝ (CnBody n) := by
  intro x hx y hy a b ha hb hab
  apply (mem_gadget_iff _).mpr
  intro i j hij
  have hxij := (mem_gadget_iff x).mp hx i j hij
  have hyij := (mem_gadget_iff y).mp hy i j hij
  have hi : |a * x i + b * y i| ≤ a * |x i| + b * |y i| := by
    simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
      abs_add_le (a * x i) (b * y i)
  have hj : |a * x j + b * y j| ≤ a * |x j| + b * |y j| := by
    simpa [abs_mul, abs_of_nonneg ha, abs_of_nonneg hb] using
      abs_add_le (a * x j) (b * y j)
  change |a * x i + b * y i| + |a * x j + b * y j| ≤ 1
  nlinarith [mul_nonneg ha (sub_nonneg.mpr hxij),
    mul_nonneg hb (sub_nonneg.mpr hyij)]

end Qatlib.Papers.ConvexVolEst19.MainResults.LowerBound
