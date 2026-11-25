/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.FiniteLocc.LOCCProgram.Entanglement

@[expose] public section


/-!
# Schmidt decomposition with strictly positive coefficients

Paper version: **arXiv:1106.1445v8**, [Wilde2017], Theorem 3.8.1, Eqs. (3.238)–(3.240), fixed
PDF p. 115.
<https://arxiv.org/abs/1106.1445>

The shared statement `Qatlib.Concepts.FiniteLocc.LOCCProgram.g1` records a Schmidt
expansion with nonnegative coefficients, orthonormal factors on both sides, the first
marginal and the count of nonzero coefficients.  Theorem 3.8.1 asks for the reduced form in
which zero singular values have been deleted: all coefficients are then strictly positive.
This file drops the zero coefficients from the expansion of
`Qatlib.Concepts.FiniteLocc.LOCCProgram.exists_schmidtData` by restricting to their finite
support and reindexing along `Finset.equivFin`, and bounds the resulting number of terms by
`min D E` through the Schmidt rank.

The expansion is only established for coefficient matrices indexed by `Fin D × Fin E`; the
two bases are the computational ones, not arbitrary orthonormal bases of an abstract Hilbert
space.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QShannonWilde11.MainResults.EntMeasures

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.FiniteLocc.LOCCProgram
open scoped BigOperators

noncomputable section

/-- **Theorem 3.8.1** — [Wilde2017], arXiv:1106.1445v8, Eqs. (3.238)–(3.240).  A normalized bipartite pure
state admits a Schmidt expansion whose coefficients are all strictly positive, whose factors are
orthonormal on each side, whose number of terms is at most `min D E`, and whose squared
coefficients sum to one.

The expansion is taken from `Qatlib.Concepts.FiniteLocc.LOCCProgram.exists_schmidtData`;
zero coefficients are removed by reindexing along the support, and the term count is bounded
by the Schmidt rank `schmidtRank ψ`. -/
theorem exists_schmidtData_pos {D E : ℕ} (ψ : QState (Fin D × Fin E)) (hψ : Normalized ψ) :
    ∃ (r : ℕ) (c : Fin r → ℝ) (u : Fin r → QState (Fin D)) (v : Fin r → QState (Fin E)),
      r ≤ min D E ∧ (∀ i, 0 < c i) ∧
      (∀ i j, Qatlib.Foundations.PureStateMath.Inner (u i) (u j) = if i = j then 1 else 0) ∧
      (∀ i j, Qatlib.Foundations.PureStateMath.Inner (v i) (v j) = if i = j then 1 else 0) ∧
      (ψ = ∑ i, (c i : ℂ) • TensorState (u i) (v i)) ∧
      (∑ i, c i * c i = 1) := by
  classical
  obtain ⟨r₀, c₀, u₀, v₀, hnonneg, horthU, horthV, hexp, hnorm, _, hrank⟩ := g1.1 D E ψ hψ
  set S : Finset (Fin r₀) := Finset.univ.filter (fun k => c₀ k ≠ 0) with hSdef
  let r := S.card
  let e : S ≃ Fin r := Finset.equivFin S
  let c : Fin r → ℝ := fun i => c₀ (e.symm i)
  let u : Fin r → QState (Fin D) := fun i => u₀ (e.symm i)
  let v : Fin r → QState (Fin E) := fun i => v₀ (e.symm i)
  have hmem : ∀ i : Fin r, c₀ (e.symm i) ≠ 0 := by
    intro i
    have h := (e.symm i).2
    simpa only [hSdef, Finset.mem_filter, Finset.mem_univ, true_and] using h
  have hzero : ∀ k : Fin r₀, k ∉ S → c₀ k = 0 := by
    intro k hk
    by_contra hne
    exact hk (by simp [hSdef, hne])
  have hreindexℂ :
      (∑ i : Fin r, (c₀ (e.symm i) : ℂ) • TensorState (u₀ (e.symm i)) (v₀ (e.symm i)))
        = ∑ k : Fin r₀, (c₀ k : ℂ) • TensorState (u₀ k) (v₀ k) := by
    calc (∑ i : Fin r, (c₀ (e.symm i) : ℂ) • TensorState (u₀ (e.symm i)) (v₀ (e.symm i)))
        = ∑ k : S, (c₀ ↑k : ℂ) • TensorState (u₀ ↑k) (v₀ ↑k) :=
          Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      _ = ∑ k ∈ S, (c₀ k : ℂ) • TensorState (u₀ k) (v₀ k) :=
          Finset.sum_coe_sort S (fun k : Fin r₀ => (c₀ k : ℂ) • TensorState (u₀ k) (v₀ k))
      _ = ∑ k : Fin r₀, (c₀ k : ℂ) • TensorState (u₀ k) (v₀ k) := by
          refine Finset.sum_subset (Finset.subset_univ S) (fun k _ hk => ?_)
          rw [hzero k hk]
          simp
  have hreindexℝ :
      (∑ i : Fin r, c₀ (e.symm i) * c₀ (e.symm i)) = ∑ k : Fin r₀, c₀ k * c₀ k := by
    calc (∑ i : Fin r, c₀ (e.symm i) * c₀ (e.symm i))
        = ∑ k : S, c₀ ↑k * c₀ ↑k := Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
      _ = ∑ k ∈ S, c₀ k * c₀ k :=
          Finset.sum_coe_sort S (fun k : Fin r₀ => c₀ k * c₀ k)
      _ = ∑ k : Fin r₀, c₀ k * c₀ k := by
          refine Finset.sum_subset (Finset.subset_univ S) (fun k _ hk => ?_)
          rw [hzero k hk]
          ring
  refine ⟨r, c, u, v, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hrank' : r = schmidtRank ψ := by
      rw [hrank]
      show S.card = ({i : Fin r₀ | c₀ i ≠ 0} : Set (Fin r₀)).ncard
      have hset : ({i : Fin r₀ | c₀ i ≠ 0} : Set (Fin r₀)) = (S : Set (Fin r₀)) := by
        ext k
        simp [hSdef]
      rw [hset, Set.ncard_coe_finset]
    rw [hrank']
    refine le_min ?_ ?_
    · simpa [schmidtRank] using Matrix.rank_le_card_height (bipartiteMatrix ψ)
    · simpa [schmidtRank] using Matrix.rank_le_card_width (bipartiteMatrix ψ)
  · intro i
    exact lt_of_le_of_ne (hnonneg (e.symm i)) (Ne.symm (hmem i))
  · intro i j
    have h := horthU (e.symm i) (e.symm j)
    by_cases hij : i = j
    · subst hij
      simpa using h
    · have hne : ¬ ((e.symm i : S) : Fin r₀) = ((e.symm j : S) : Fin r₀) := by
        intro hc
        exact hij (e.symm.injective (Subtype.coe_injective hc))
      rw [ite_eq_right hij]
      simpa [hne] using h
  · intro i j
    have h := horthV (e.symm i) (e.symm j)
    by_cases hij : i = j
    · subst hij
      simpa using h
    · have hne : ¬ ((e.symm i : S) : Fin r₀) = ((e.symm j : S) : Fin r₀) := by
        intro hc
        exact hij (e.symm.injective (Subtype.coe_injective hc))
      rw [ite_eq_right hij]
      simpa [hne] using h
  · dsimp only [c, u, v]
    rw [hreindexℂ]
    exact hexp
  · dsimp only [c]
    rw [hreindexℝ]
    exact hnorm

end

end Qatlib.Papers.QShannonWilde11.MainResults.EntMeasures
