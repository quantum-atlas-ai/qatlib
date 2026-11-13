/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PolyMethod01.SymDegree.SymmetricGamma
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Layer-change counts and counting-cost bounds

The set `layerChangeLayers` collects weight layers at which a Boolean function changes. For a
symmetric function, its cardinality bounds from below the degree of a polynomial approximating
the function within one third; elementary inequalities also bound the counting-cost expression
in the low- and high-weight regimes. These constructions support the symmetric-function analysis
of [BealsEtAl2001].

## Main statements

* `layerChange_card_le_totalDegree`: For a symmetric Boolean function approximated within one
  third by `p` on the Boolean cube, the number of changing layers is at most `p.totalDegree`.
* `counting_cost_sqrt_le`: Under the low-weight condition `2 * (t + 1) + Γ ≤ N` and `t ≤ N`, the
  square root of the counting-cost product is at most `sqrt (N * (N - Γ))`.

## References

* [Beals et al., 2001][BealsEtAl2001]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Qatlib.Papers.PolyMethod01.SymDegree

open Qatlib.Concepts.QueryComplexity.DegreeMethod
open scoped Classical BigOperators

variable {n : ℕ}

/-- The finite set of weights `k < n` at which `f` changes between layers `k` and `k + 1`. -/
noncomputable def layerChangeLayers (f : (Fin n → Bool) → Bool) : Finset ℕ := by
  classical
  exact (Finset.range n).filter (fun k => LayerChange f k)

/-- A weight belongs to `layerChangeLayers f` exactly when it is less than `n` and satisfies
`LayerChange f k`. -/
theorem mem_layerChangeLayers {f : (Fin n → Bool) → Bool} {k : ℕ} :
    k ∈ layerChangeLayers f ↔ k < n ∧ LayerChange f k := by
  classical
  simp [layerChangeLayers]

/-- For a symmetric Boolean function approximated within one third by `p` on the Boolean cube,
the number of changing layers is at most `p.totalDegree`. See [Beals et al.,
2001][BealsEtAl2001]. -/
theorem layerChange_card_le_totalDegree {f : (Fin n → Bool) → Bool} (hsym : Symmetric f)
    {p : MvPolynomial (Fin n) ℝ}
    (hyp : ∀ g : Fin n → Bool,
      |p.eval (boolPoint g) - (if f g then (1 : ℝ) else 0)| ≤ 1 / 3) :
    (layerChangeLayers f).card ≤ p.totalDegree := by
  classical
  by_cases hn : n = 0
  · subst hn
    have hempty : layerChangeLayers f = ∅ := by
      ext k
      rw [mem_layerChangeLayers]
      simp
    rw [hempty, Finset.card_empty]
    exact Nat.zero_le _
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn

  have key : ∀ k ∈ layerChangeLayers f,
      ∃ c : ℝ, c ∈ Set.Ioo (k : ℝ) ((k + 1 : ℕ) : ℝ) ∧
        (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).eval c = 0 := by
    intro k hk
    rw [mem_layerChangeLayers] at hk
    exact jump_root hsym hyp hk.1 hk.2
  choose c hc hroot using key

  have hQne : avgPoly p - Polynomial.C ((1 : ℝ) / 2) ≠ 0 := by
    intro hzero
    have hA := layerAverage_close_symmetric hsym hyp (k := 0) (Nat.zero_le n)
    rw [layerAverage_eq_avgPoly p 0 (by simp)] at hA
    have hval : (avgPoly p).eval (0 : ℝ) = 1 / 2 := by
      have h : Polynomial.eval (0 : ℝ) (avgPoly p - Polynomial.C ((1 : ℝ) / 2)) = 0 := by
        rw [hzero]
        simp
      simp only [Polynomial.eval_sub, Polynomial.eval_C] at h
      linarith
    rcases (show layerVal f 0 = true ∨ layerVal f 0 = false from Bool.eq_false_or_eq_true _)
      with hb | hb
    · rw [hb] at hA
      simp only [if_true] at hA
      have hA' : |(avgPoly p).eval (0 : ℝ) - 1| ≤ 1 / 3 := by simpa using! hA
      rw [hval] at hA'
      norm_num at hA'
    · rw [hb] at hA
      simp only [Bool.false_eq_true, if_false] at hA
      have hA' : |(avgPoly p).eval (0 : ℝ) - 0| ≤ 1 / 3 := by simpa using! hA
      rw [hval] at hA'
      norm_num at hA'

  have hinj : ∀ k₁ (h₁ : k₁ ∈ layerChangeLayers f) (k₂ : ℕ)
      (h₂ : k₂ ∈ layerChangeLayers f), c k₁ h₁ = c k₂ h₂ → k₁ = k₂ := by
    intro k₁ h₁ k₂ h₂ heq
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hstep : (k₁ + 1 : ℕ) ≤ k₂ := hlt
      have h1 : c k₁ h₁ < ((k₁ + 1 : ℕ) : ℝ) := (hc k₁ h₁).2
      have h2 : (k₂ : ℝ) < c k₂ h₂ := (hc k₂ h₂).1
      have hcast : ((k₁ + 1 : ℕ) : ℝ) ≤ (k₂ : ℝ) := by exact_mod_cast hstep
      rw [heq] at h1
      linarith
    · have hstep : (k₂ + 1 : ℕ) ≤ k₁ := hlt
      have h1 : c k₂ h₂ < ((k₂ + 1 : ℕ) : ℝ) := (hc k₂ h₂).2
      have h2 : (k₁ : ℝ) < c k₁ h₁ := (hc k₁ h₁).1
      have hcast : ((k₂ + 1 : ℕ) : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast hstep
      rw [heq] at h2
      linarith
  let Z : Finset ℝ := (layerChangeLayers f).attach.image (fun k => c k.1 k.2)
  have hZcard : Z.card = (layerChangeLayers f).card := by
    show ((layerChangeLayers f).attach.image (fun k => c k.1 k.2)).card = _
    have hinj' : Set.InjOn (fun k : {k // k ∈ layerChangeLayers f} => c k.1 k.2)
        ↑(layerChangeLayers f).attach := by
      intro k₁ _ k₂ _ heq
      exact Subtype.ext (hinj k₁.1 k₁.2 k₂.1 k₂.2 heq)
    rw [Finset.card_image_of_injOn hinj']
    exact Finset.card_attach
  have hZroots : Z.val ⊆ (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).roots := by
    intro x hx
    have hxZ : x ∈ Z := by simpa using! hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hxZ
    rw [Polynomial.mem_roots hQne]
    exact hroot k.1 k.2
  have hcard := Polynomial.card_le_degree_of_subset_roots hZroots
  rw [hZcard] at hcard
  refine hcard.trans ?_
  calc (avgPoly p - Polynomial.C ((1 : ℝ) / 2)).natDegree
      ≤ max (avgPoly p).natDegree (Polynomial.C ((1 : ℝ) / 2)).natDegree :=
        Polynomial.natDegree_sub_le _ _
    _ ≤ p.totalDegree := by
        refine max_le (avgPoly_natDegree_le p) ?_
        have hzero : (Polynomial.C ((1 : ℝ) / 2)).natDegree = 0 := Polynomial.natDegree_C _
        omega

/-- If `t ≤ N` and `2 * (t + 1) + Γ ≤ N`, the real counting-cost product `(t + 1) * (N - t + 1)`
is at most `N * (N - Γ)`. -/
theorem counting_cost_le {N Γ t : ℕ} (htN : t ≤ N) (h : 2 * (t + 1) + Γ ≤ N) :
    ((t + 1) * (N - t + 1) : ℝ) ≤ (N : ℝ) * ((N - Γ : ℕ) : ℝ) := by
  have hΓN : Γ ≤ N := by omega
  have hcast : ((N - Γ : ℕ) : ℝ) = (N : ℝ) - (Γ : ℝ) := by
    rw [Nat.cast_sub hΓN]
  have h2 : (2 : ℝ) * ((t : ℝ) + 1) ≤ (N : ℝ) - (Γ : ℝ) := by
    have hc : ((2 * (t + 1) + Γ : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast h
    push_cast at hc
    linarith
  have ht : (t : ℝ) ≤ (N : ℝ) := by exact_mod_cast htN
  have hNt : ((N - t + 1 : ℕ) : ℝ) = (N : ℝ) - (t : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub htN]
  have hGnon : (0 : ℝ) ≤ (N : ℝ) - (Γ : ℝ) := by linarith
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
  have hΓnon : (0 : ℝ) ≤ (Γ : ℝ) := Nat.cast_nonneg Γ
  have hNnon : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hN2 : (2 : ℝ) ≤ (N : ℝ) := by linarith
  rw [hcast]
  nlinarith [h2, ht, hGnon, ht0, hΓnon, hNnon, hN2]

/-- Under the low-weight condition `2 * (t + 1) + Γ ≤ N` and `t ≤ N`, the square root of the
counting-cost product is at most `sqrt (N * (N - Γ))`. See [Beals et al.,
2001][BealsEtAl2001]. -/
theorem counting_cost_sqrt_le {N Γ t : ℕ} (htN : t ≤ N) (h : 2 * (t + 1) + Γ ≤ N) :
    Real.sqrt ((t + 1) * (N - t + 1) : ℝ) ≤ Real.sqrt ((N : ℝ) * ((N - Γ : ℕ) : ℝ)) :=
  Real.sqrt_le_sqrt (counting_cost_le htN h)

/-- If `t ≤ N` and `2 * (N - t + 1) + Γ ≤ N`, the real counting-cost product `(t + 1) * (N - t +
1)` is at most `N * (N - Γ)`. -/
theorem counting_cost_le_of_high_weight {N Γ t : ℕ} (htN : t ≤ N)
    (h : 2 * (N - t + 1) + Γ ≤ N) :
    ((t + 1) * (N - t + 1) : ℝ) ≤ (N : ℝ) * ((N - Γ : ℕ) : ℝ) := by
  have hsub : ((N - t : ℕ) : ℝ) = (N : ℝ) - (t : ℝ) := Nat.cast_sub htN
  have hc := counting_cost_le (N := N) (Γ := Γ) (t := N - t) (Nat.sub_le N t) h
  rw [hsub] at hc
  nlinarith [hc]

/-- Under the high-weight condition `2 * (N - t + 1) + Γ ≤ N` and `t ≤ N`, the square root of
the counting-cost product is at most `sqrt (N * (N - Γ))`. -/
theorem counting_cost_sqrt_le_of_high_weight {N Γ t : ℕ} (htN : t ≤ N)
    (h : 2 * (N - t + 1) + Γ ≤ N) :
    Real.sqrt ((t + 1) * (N - t + 1) : ℝ) ≤ Real.sqrt ((N : ℝ) * ((N - Γ : ℕ) : ℝ)) :=
  Real.sqrt_le_sqrt (counting_cost_le_of_high_weight htN h)

end Qatlib.Papers.PolyMethod01.SymDegree
