/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.NLTSAnshu23.MainResults.Model.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SourceLemma8 — expansion implies clustering (Lemma 8, p.6)

Anshu–Breuckmann–Nirkhe, fixed arXiv:2206.13228v4.

Definition 6 (p.5): `A ∈ F₂^{m×n}` is `(α, β)`-expanding on `V` when every
`x ∈ V` with `|x| ≤ αn` satisfies `|Ax| ≥ β|x|`.

Definition 7 (p.5): `A` is `(δ, μ, ν)`-clustering on `V` when every `x ∈ V`
with `|Ax| ≤ δn` satisfies `|x| ≤ μn` or `|x| ≥ νn`.

Lemma 8: a matrix that is `(ν, δ/μ)`-expanding on `V` is `(δ, μ, ν`-clustering
on `V`.

The proof is the paper's two-line argument: if `|x| > μn` then
`|Ax| ≤ δn < (δ/μ)|x|`; if additionally `|x| ≤ νn`, expansion would give
`|Ax| ≥ (δ/μ)|x| > δn`, a contradiction, hence `|x| > νn`.  Positivity of `δ`
and `μ` is the nondegeneracy condition discussed right after the lemma
(`0 < δ < αβ`, `μ < ν`); the theorem below records it explicitly.

Boundary: pure combinatorial statement; no quantum ingredient is used.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open Qatlib.Papers.NLTSAnshu23.MainResults.Model
open Matrix

namespace Qatlib.Papers.NLTSAnshu23.MainResults.Lemma8

/-! ## Definitions of expansion and clustering -/

/-- Definition 6 (p.5): `(α, β)`-expansion of a binary matrix on `V`. -/
abbrev IsExpanding {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (V : Set (BitString n)) (α β : ℝ) : Prop :=
  ∀ x ∈ V, (hammingWeight x : ℝ) ≤ α * (n : ℝ) →
    β * (hammingWeight x : ℝ) ≤ (hammingWeight (A *ᵥ x) : ℝ)

/-- Definition 7 (p.5): `(δ, μ, ν)`-clustering of a binary matrix on `V`. -/
abbrev IsClustering {m n : ℕ} (A : Matrix (Fin m) (Fin n) (ZMod 2))
    (V : Set (BitString n)) (δ μ ν : ℝ) : Prop :=
  ∀ x ∈ V, (hammingWeight (A *ᵥ x) : ℝ) ≤ δ * (n : ℝ) →
    (hammingWeight x : ℝ) ≤ μ * (n : ℝ) ∨
    ν * (n : ℝ) ≤ (hammingWeight x : ℝ)

/-- Lemma 8 (p.6): if `A` is `(ν, δ/μ)`-expanding on `V`, then `A` is
`(δ, μ, ν)`-clustering on `V`.

Source proof: take `x ∈ V` with `|Ax| ≤ δn`.  If `|x| ≤ μn` there is nothing
to prove.  Otherwise `|x| > μn`, so `|Ax| ≤ δn < (δ/μ)|x|`; were `|x| ≤ νn`,
expansion would give `|Ax| ≥ (δ/μ)|x| > δn`, contradiction.  Hence `|x| > νn`.

The hypotheses `0 < δ` and `0 < μ` are exactly the nondegeneracy required for
the ratio `δ/μ` to be positive (see the paragraph after Lemma 8).
-/
theorem expansion_implies_clustering {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (V : Set (BitString n))
    {δ μ ν : ℝ} (hδ : 0 < δ) (hμ : 0 < μ)
    (hexp : IsExpanding A V ν (δ / μ)) :
    IsClustering A V δ μ ν := by
  intro x hxV hAx
  by_cases hnear : (hammingWeight x : ℝ) ≤ μ * (n : ℝ)
  · exact Or.inl hnear
  · right
    have hgreater : μ * (n : ℝ) < (hammingWeight x : ℝ) := lt_of_not_ge hnear
    by_contra hfar
    -- `hfar : ¬ ν * n ≤ |x|`, hence `|x| < ν * n` and expansion applies.
    have hxsmall : (hammingWeight x : ℝ) < ν * (n : ℝ) := not_le.mp hfar
    have hexp' : (δ / μ) * (hammingWeight x : ℝ) ≤
        (hammingWeight (A *ᵥ x) : ℝ) := hexp x hxV (le_of_lt hxsmall)
    have hβpos : 0 < δ / μ := div_pos hδ hμ
    have hkey : δ * (n : ℝ) < (δ / μ) * (hammingWeight x : ℝ) := by
      have hstep : (δ / μ) * (μ * (n : ℝ)) < (δ / μ) * (hammingWeight x : ℝ) :=
        mul_lt_mul_of_pos_left hgreater hβpos
      have hcancel : (δ / μ) * (μ * (n : ℝ)) = δ * (n : ℝ) := by
        field_simp
      rwa [hcancel] at hstep
    linarith

/-- Lemma 8 specialized to the Property-1 side discussed after the lemma
(p.6): on minimal representatives `x` of a code `C` (no codeword shift reduces
the weight), clustering of `A` transfers to the paper's distance-to-code
alternatives `|x|_C ≤ c₁δn` or `|x|_C ≥ c₂n`. -/
theorem expansion_implies_property1_on_minimal_representatives {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (ZMod 2)) (C : BinaryCode n)
    (V : Set (BitString n)) {δ c1 c2 : ℝ}
    (hδ : 0 < δ) (hμ : 0 < c1) (_hν : 0 < c2)
    (hexp : IsExpanding A V c2 (1 / c1))
    (hminimal : ∀ x ∈ V, ∀ s ∈ C, hammingWeight x ≤ hammingWeight (x + s))
    (hV : ∀ x ∈ V, (syndromeWeight A x : ℝ) ≤ δ * (n : ℝ)) :
    ∀ x ∈ V, IsCloseTo C x (c1 * δ * (n : ℝ)) ∨ IsFarFrom C x (c2 * (n : ℝ)) := by
  intro x hxV
  have hratio : δ / (c1 * δ) = 1 / c1 := by field_simp
  have hexp' : IsExpanding A V c2 (δ / (c1 * δ)) := by
    rw [hratio]
    exact hexp
  have hcluster : IsClustering A V δ (c1 * δ) c2 :=
    expansion_implies_clustering A V hδ (mul_pos hμ hδ) hexp'
  rcases hcluster x hxV (hV x hxV) with hnear | hfar
  · left
    refine ⟨0, C.zero_mem, ?_⟩
    simpa [mul_assoc] using hnear
  · right
    intro s hs
    have hm : (hammingWeight x : ℝ) ≤ (hammingWeight (x + s) : ℝ) := by
      exact_mod_cast hminimal x hxV s hs
    exact le_trans hfar hm

end Qatlib.Papers.NLTSAnshu23.MainResults.Lemma8
