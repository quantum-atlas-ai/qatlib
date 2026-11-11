/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.ConvexOpt18.MainResults.Model.SourceAnalyticModel

set_option backward.isDefEq.respectTransparency false

/-!
# ConvexOpt18 sharpness of the mollifier/smoothness tradeoff (Lemma A.3)

Fixed source: Chakrabarti--Childs--Li--Wu, arXiv:1809.01731v3, Appendix A, Lemma A.3
(p. 38).
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.ConvexOpt18.MainResults

/-- `β`-smoothness in one dimension, in the form of equation (2.3) with `n = 1`: there is a
derivative field `g'` with `|g(y) - g(x) - g'(x)(y-x)| ≤ (β/2)(y-x)²`. -/
def SmoothOn1 (g : ℝ → ℝ) (β : ℝ) : Prop :=
  ∃ g' : ℝ → ℝ, ∀ x y : ℝ, |g y - g x - g' x * (y - x)| ≤ β / 2 * (y - x) ^ 2

/-- Lemma A.3 (p. 38): there is a `1`-Lipschitz convex function `f` (namely `f(x) = |x|`)
such that every `β`-smooth `g` with `|f(x) - g(x)| ≤ δ` for all `x` satisfies `β δ ≥ c`
for an absolute constant `c`.  We prove the statement with `c = 1/4`; the paper only claims
the existence of a constant.

Proof (the paper's argument, made explicit): apply the smoothness inequality at `x = 0` to
the two points `y = ±4δ` and add; the closeness to `|·|` gives
`g(±4δ) ≥ 3δ`, while smoothness gives `g(4δ) + g(-4δ) ≤ 2g(0) + 16βδ² ≤ 2δ + 16βδ²`;
hence `4δ ≤ 16βδ²`, i.e. `βδ ≥ 1/4` for `δ > 0`. -/
theorem source_lemma_A_3 :
    ∃ c : ℝ, 0 < c ∧ ∀ (g : ℝ → ℝ) (β δ : ℝ), 0 < δ → SmoothOn1 g β →
      (∀ x : ℝ, abs (g x - abs x) ≤ δ) → c ≤ β * δ := by
  refine ⟨1 / 4, by norm_num, ?_⟩
  intro g β δ hδ hsmooth hclose
  obtain ⟨g', hg'⟩ := hsmooth
  have h4 : (0 : ℝ) < 4 * δ := by linarith
  have h1 := hg' 0 (4 * δ)
  have h2 := hg' 0 (-(4 * δ))
  have habs1 : abs (4 * δ) = 4 * δ := abs_of_pos h4
  have habs2 : abs (-(4 * δ)) = 4 * δ := by rw [abs_neg, abs_of_pos h4]
  have hc1 : abs (g (4 * δ) - 4 * δ) ≤ δ := by
    have h := hclose (4 * δ)
    rwa [habs1] at h
  have hc2 : abs (g (-(4 * δ)) - 4 * δ) ≤ δ := by
    have h := hclose (-(4 * δ))
    rwa [habs2] at h
  have hlow1 : 3 * δ ≤ g (4 * δ) := by
    have := (abs_le.mp hc1).1
    linarith
  have hlow2 : 3 * δ ≤ g (-(4 * δ)) := by
    have := (abs_le.mp hc2).1
    linarith
  have hsq1 : (4 * δ) ^ 2 = 16 * δ ^ 2 := by ring
  have hsq2 : (-(4 * δ)) ^ 2 = 16 * δ ^ 2 := by ring
  have hs1 : g (4 * δ) - g 0 - g' 0 * (4 * δ) ≤ 8 * β * δ ^ 2 := by
    have h := (abs_le.mp h1).2
    rw [sub_zero, hsq1] at h
    nlinarith
  have hs2 : g (-(4 * δ)) - g 0 - g' 0 * (-(4 * δ)) ≤ 8 * β * δ ^ 2 := by
    have h := (abs_le.mp h2).2
    rw [sub_zero, hsq2] at h
    nlinarith
  have hc0 : abs (g 0) ≤ δ := by
    simpa using hclose 0
  have hupper0 : g 0 ≤ δ := (abs_le.mp hc0).2
  have hmain : 4 * δ ≤ 16 * β * δ ^ 2 := by linarith
  have hfact : 4 * δ * (1 - 4 * β * δ) ≤ 0 := by nlinarith [hmain]
  have hle : 1 - 4 * β * δ ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_pos h4 hcon]
  nlinarith [hle]

end Qatlib.Papers.ConvexOpt18.MainResults
