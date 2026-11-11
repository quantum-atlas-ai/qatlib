/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SuperGrover22.MainResults.Model
import Mathlib.Analysis.Convex.Mul

set_option backward.isDefEq.respectTransparency false

/-!
# SuperGrover22 — Proposition 12 (convexity of a product)

Fixed arXiv:2212.01513v2, Proposition 12 (App. A.2, p. 40): if `f : (-∞,1] → [0,1]` is
monotonically non-decreasing and convex (twice differentiable wherever non-zero), then for
non-negative constants `c₁,…,cₘ` the product `h(x) = ∏_t f(c_t x)` is convex.

The paper uses this only with `0 < c_t < 1` (Definition 2), which is also what keeps every
`c_t x` inside the domain `(-∞,1]` for `x ≤ 1`; we therefore state it on that operative range.
The smoothness hypothesis of the paper is not needed for the convexity conclusion and is
omitted (a strengthening, not a weakening).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SuperGrover22.MainResults

/-- Proposition 12 (App. A.2, p. 40): a product of rescaled copies of a non-negative,
non-decreasing convex function is convex.  Each factor `x ↦ f(c_t · x)` is convex because
`f` is convex and `x ↦ c_t · x` is affine; the product of non-negative, non-decreasing convex
functions is convex by `ConvexOn.mul` (monotonicity gives `MonovaryOn`). -/
theorem proposition12_product_convex {m : ℕ} (c : Fin m → ℝ)
    (hc0 : ∀ t, 0 ≤ c t) (hc1 : ∀ t, c t ≤ 1)
    {f : ℝ → ℝ}
    (hf_conv : ConvexOn ℝ (Set.Iic (1 : ℝ)) f)
    (hf_mono : MonotoneOn f (Set.Iic (1 : ℝ)))
    (hf_nonneg : ∀ x ∈ Set.Iic (1 : ℝ), 0 ≤ f x) :
    ConvexOn ℝ (Set.Iic (1 : ℝ)) (fun x => ∏ t, f (c t * x)) := by
  -- `c t * x` stays in the domain whenever `x ≤ 1`, because `0 ≤ c t ≤ 1`.
  have hin : ∀ x ∈ Set.Iic (1 : ℝ), ∀ t, c t * x ∈ Set.Iic (1 : ℝ) := by
    intro x hx t
    simp only [Set.mem_Iic] at hx ⊢
    nlinarith [hc0 t, hc1 t, mul_le_mul_of_nonneg_left hx (hc0 t)]
  -- Each single factor is convex, monotone and non-negative on the domain.
  have hconv_t : ∀ t, ConvexOn ℝ (Set.Iic (1 : ℝ)) (fun x => f (c t * x)) := by
    intro t
    refine ⟨convex_Iic (1 : ℝ), ?_⟩
    intro x hx y hy a b ha hb hab
    have hxS : c t * x ∈ Set.Iic (1 : ℝ) := hin x hx t
    have hyS : c t * y ∈ Set.Iic (1 : ℝ) := hin y hy t
    have harg : a • (c t * x) + b • (c t * y) = c t * (a • x + b • y) := by
      simp only [smul_eq_mul]; ring
    change f (c t * (a • x + b • y)) ≤ a • f (c t * x) + b • f (c t * y)
    rw [← harg]
    exact hf_conv.2 hxS hyS ha hb hab
  have hmono_t : ∀ t, MonotoneOn (fun x => f (c t * x)) (Set.Iic (1 : ℝ)) := by
    intro t x hx y hy hxy
    exact hf_mono (hin x hx t) (hin y hy t) (mul_le_mul_of_nonneg_left hxy (hc0 t))
  have hnonneg_t : ∀ t, ∀ x ∈ Set.Iic (1 : ℝ), 0 ≤ f (c t * x) := by
    intro t x hx
    exact hf_nonneg _ (hin x hx t)
  -- Induct over the (finite) set of factors, maintaining convexity, monotonicity and non-negativity.
  have key : ∀ (T : Finset (Fin m)),
      ConvexOn ℝ (Set.Iic (1 : ℝ)) (fun x => ∏ t ∈ T, f (c t * x)) ∧
      MonotoneOn (fun x => ∏ t ∈ T, f (c t * x)) (Set.Iic (1 : ℝ)) ∧
      (∀ x ∈ Set.Iic (1 : ℝ), 0 ≤ ∏ t ∈ T, f (c t * x)) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        refine ⟨?_, ?_, ?_⟩
        · simpa using convexOn_const (1 : ℝ) (convex_Iic (1 : ℝ))
        · intro x _ y _ _
          simp
        · intro x _
          simp
    | insert a T ha ih =>
        obtain ⟨ihc, ihm, ihn⟩ := ih
        simp only [Finset.prod_insert ha]
        refine ⟨?_, ?_, ?_⟩
        · exact ConvexOn.mul (hconv_t a) ihc
            (fun x hx => hnonneg_t a x hx) (fun x hx => ihn x hx)
            (MonotoneOn.monovaryOn (hmono_t a) ihm)
        · exact MonotoneOn.mul (hmono_t a) ihm
            (fun x hx => hnonneg_t a x hx) (fun x hx => ihn x hx)
        · intro x hx
          exact mul_nonneg (hnonneg_t a x hx) (ihn x hx)
  exact (key Finset.univ).1

end Qatlib.Papers.SuperGrover22.MainResults
