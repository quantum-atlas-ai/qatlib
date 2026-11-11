/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GridWalk16.MainResults.SourceSpectralModel

set_option backward.isDefEq.respectTransparency false

/-!
# GridWalk16 — Lemma 6: sub-additivity of the escape time (claim c003)

Fixed paper: arXiv:1612.08958v1, Lemma 6, §2 p. 7 (proof same page).

Statement (paper): for any two disjoint subsets `S₁, S₂ ⊆ X`,
`E(P, S₁ ∪ S₂) ≤ E(P, S₁) + E(P, S₂)`.

Proof route formalised here (paper p. 7):
* the normalised projection onto the union is the convex combination
  `|S₁∪S₂⟩ = a|S₁⟩ + b|S₂⟩` with `a² + b² = 1`, where
  `a = √(ε_{S₁}/ε_{S₁∪S₂})`, `b = √(ε_{S₂}/ε_{S₁∪S₂})` (`proj_union`);
* Cauchy–Schwarz gives `⟨λ_k|S₁∪S₂⟩² ≤ ⟨λ_k|S₁⟩² + ⟨λ_k|S₂⟩²` per mode
  (`sq_convex_comb_le`);
* dividing each mode by the positive gap `1 − λ_k` and summing gives the claim
  (`escape_union_le`).

No `sorry` in this file.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset

namespace Qatlib.Papers.GridWalk16.MainResults

variable {X ι : Type*} [Fintype X] [DecidableEq X] [Fintype ι]

/-- Cauchy–Schwarz in the two-dimensional form used in Lemma 6: for `a²+b²=1`,
`(a·x + b·y)² ≤ x² + y²`.  This is the pointwise core of the proof of Lemma 6
(paper p. 7: "by the Cauchy–Schwarz inequality"). -/
lemma sq_convex_comb_le (a b x y : ℝ) (h : a^2 + b^2 = 1) :
    (a * x + b * y)^2 ≤ x^2 + y^2 := by
  nlinarith [sq_nonneg (a * y - b * x)]

namespace SpectralWalk

variable (W : SpectralWalk X ι)

/-- The spectral amplitude of the union of two disjoint nonempty subsets is the
convex combination `a·⟨λ_k|S₁⟩ + b·⟨λ_k|S₂⟩` with `a = √(ε₁/ε_{S₁∪S₂})`,
`b = √(ε₂/ε_{S₁∪S₂})` (paper p. 7). -/
lemma proj_union {S T : Finset X} (h : Disjoint S T)
    (hS : S.Nonempty) (hT : T.Nonempty) (k : ι) :
    W.proj (S ∪ T) k =
      (Real.sqrt (W.eps S) / Real.sqrt (W.eps (S ∪ T))) * W.proj S k +
      (Real.sqrt (W.eps T) / Real.sqrt (W.eps (S ∪ T))) * W.proj T k := by
  have hsS : Real.sqrt (W.eps S) ≠ 0 := by
    have := W.eps_pos hS; positivity
  have hsT : Real.sqrt (W.eps T) ≠ 0 := by
    have := W.eps_pos hT; positivity
  have hsU : Real.sqrt (W.eps (S ∪ T)) ≠ 0 := by
    have := W.eps_pos (hS.mono (Finset.subset_union_left (s₂ := T))); positivity
  simp only [SpectralWalk.proj, Finset.sum_union h]
  field_simp

/-- The coefficients `a = √(ε₁/ε_{S₁∪S₂})`, `b = √(ε₂/ε_{S₁∪S₂})` of the convex
combination in Lemma 6 satisfy `a² + b² = 1` (paper p. 7: "noting that a²+b²=1"). -/
lemma proj_union_coeff_sq {S T : Finset X} (h : Disjoint S T)
    (hS : S.Nonempty) :
    (Real.sqrt (W.eps S) / Real.sqrt (W.eps (S ∪ T)))^2 +
      (Real.sqrt (W.eps T) / Real.sqrt (W.eps (S ∪ T)))^2 = 1 := by
  have hUpos : 0 < W.eps (S ∪ T) :=
    W.eps_pos (hS.mono (Finset.subset_union_left (s₂ := T)))
  have hU : W.eps (S ∪ T) = W.eps S + W.eps T := W.eps_union h
  rw [div_pow, div_pow, Real.sq_sqrt (W.eps_nonneg S), Real.sq_sqrt (W.eps_nonneg T),
      Real.sq_sqrt (W.eps_nonneg (S ∪ T)), ← add_div, ← hU, div_self (ne_of_gt hUpos)]

/-- **Lemma 6 (c003).** For any two disjoint nonempty subsets `S₁, S₂`,
`E(P, S₁ ∪ S₂) ≤ E(P, S₁) + E(P, S₂)`.
Paper arXiv:1612.08958v1, Lemma 6, §2 p. 7 (proved p. 7). -/
theorem escape_union_le {S T : Finset X} (h : Disjoint S T)
    (hS : S.Nonempty) (hT : T.Nonempty) :
    W.escape (S ∪ T) ≤ W.escape S + W.escape T := by
  have hcoef := W.proj_union_coeff_sq (T := T) h hS
  unfold SpectralWalk.escape
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  have hpu := W.proj_union (T := T) h hS hT k
  have hcs : (W.proj (S ∪ T) k)^2 ≤ (W.proj S k)^2 + (W.proj T k)^2 := by
    rw [hpu]
    exact sq_convex_comb_le _ _ _ _ hcoef
  have hg : 0 ≤ W.gap k := (W.gap_pos k).le
  calc
    (W.proj (S ∪ T) k)^2 / W.gap k
        ≤ ((W.proj S k)^2 + (W.proj T k)^2) / W.gap k :=
          div_le_div_of_nonneg_right hcs hg
    _ = (W.proj S k)^2 / W.gap k + (W.proj T k)^2 / W.gap k := by ring

end SpectralWalk

end Qatlib.Papers.GridWalk16.MainResults
