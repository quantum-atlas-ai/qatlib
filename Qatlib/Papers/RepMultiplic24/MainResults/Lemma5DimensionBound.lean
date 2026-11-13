/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.RepMultiplic24.MainResults.SourceModel

/-!
# Hook-Length Dimension Bounds for Long-First-Row Partitions

This module proves Lemma 5 of Larocca and Havlicek: when $\mu = (n - k, \alpha_1, \alpha_2, \dots)$
is obtained by prepending a first row of length $n - k \ge \alpha_1$ to a partition $\alpha \vdash k$,
its symmetric-group irreducible dimension satisfies the sharp hook-length bound
$d_\mu \le n^k d_\alpha / k!$ and hence $d_\mu \le k! n^k / d_\alpha$.

## Main statements

* `hookDim_le_factorial`: For $\alpha \vdash k$, the hook-length dimension satisfies $d_\alpha \le k!$.
* `lemma5_dimension_bound_sharp`: Sharp hook-length dimension bound $d_\mu \le n^k d_\alpha / k!$.
* `lemma5_dimension_bound`: Corollary dimension bound $d_\mu \le k! n^k / d_\alpha$.

## References

* [Larocca and Havlicek, 2025][LaroccaHavlicek2025]
-/

set_option autoImplicit false

namespace Qatlib.Papers.RepMultiplic24.MainResults

open scoped BigOperators

/-! ## Elementary positivity of hook lengths -/

/-- Every hook length of a cell of `μ` is positive. -/
theorem hookLength_pos {μ : YoungDiagram} {c : ℕ × ℕ} (hc : c ∈ μ.cells) :
    0 < hookLength μ c.1 c.2 := by
  have hmem : c ∈ μ := (YoungDiagram.mem_cells c).mp hc
  have hrow : c.2 < μ.rowLen c.1 := YoungDiagram.mem_iff_lt_rowLen.mp hmem
  have hcol : c.1 < μ.colLen c.2 := YoungDiagram.mem_iff_lt_colLen.mp hmem
  have h2 : c.1 + c.2 + 2 ≤ μ.rowLen c.1 + μ.colLen c.2 := by omega
  unfold hookLength
  omega

/-- The hook product of a Young diagram is at least one. -/
theorem one_le_hookProduct (μ : YoungDiagram) : 1 ≤ hookProduct μ := by
  unfold hookProduct
  exact Finset.one_le_prod (fun _ hc => hookLength_pos hc)

/-- For a partition `α` of `k`, the hook-length dimension is at most `k!`. -/
theorem hookDim_le_factorial {k : ℕ} {α : YoungDiagram} (hcard : α.cells.card = k) :
    hookDim α ≤ (k.factorial : ℚ) := by
  have hprod : (1 : ℚ) ≤ (hookProduct α : ℚ) := by
    exact_mod_cast one_le_hookProduct α
  have hfac : (0 : ℚ) ≤ (k.factorial : ℚ) := by positivity
  unfold hookDim
  rw [hcard]
  rw [div_le_iff₀ (by linarith : (0 : ℚ) < (hookProduct α : ℚ))]
  have := mul_le_mul_of_nonneg_left hprod hfac
  simpa using this

/-! ## Lemma 5 -/

private lemma rowLens_getD (μ : YoungDiagram) (i : ℕ) :
    μ.rowLens.getD i 0 = μ.rowLen i := by
  by_cases hi : i < μ.rowLens.length
  · rw [← List.getElem_eq_getD 0 (h := hi), YoungDiagram.get_rowLens]
  · have hz : μ.rowLen i = 0 := by
      apply Nat.eq_zero_of_not_pos
      intro hp
      have hc := YoungDiagram.mem_iff_lt_colLen.mp
        (YoungDiagram.mem_iff_lt_rowLen.mpr hp)
      exact hi (by simpa only [YoungDiagram.length_rowLens] using hc)
    simp only [List.getD, List.getElem?_eq_none (Nat.le_of_not_gt hi), Option.getD_none, hz]

private lemma prepended_rowLens {m : ℕ} {α μ : YoungDiagram}
    (hμ : μ.rowLens = m :: α.rowLens) :
    μ.rowLen 0 = m ∧ ∀ i, μ.rowLen (i + 1) = α.rowLen i := by
  constructor
  · simpa only [hμ, List.getD_cons_zero] using (rowLens_getD μ 0).symm
  · intro i
    rw [← rowLens_getD μ (i + 1), hμ, List.getD_cons_succ, rowLens_getD]

private def firstRowEmbedding : ℕ ↪ ℕ × ℕ where
  toFun j := (0, j)
  inj' := by intro a b h; exact congrArg Prod.snd h

private def shiftRowEmbedding : (ℕ × ℕ) ↪ ℕ × ℕ where
  toFun c := (c.1 + 1, c.2)
  inj' := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have h₁ := congrArg Prod.fst h
    have h₂ := congrArg Prod.snd h
    dsimp at h₁ h₂
    exact Prod.ext (by omega) h₂

private lemma firstRowEmbedding_apply (j : ℕ) : firstRowEmbedding j = (0, j) := rfl

private lemma shiftRowEmbedding_apply (c : ℕ × ℕ) :
    shiftRowEmbedding c = (c.1 + 1, c.2) := rfl

private lemma prepended_cells {m : ℕ} {α μ : YoungDiagram}
    (hμ : μ.rowLens = m :: α.rowLens) :
    μ.cells = (Finset.range m).map firstRowEmbedding ∪ α.cells.map shiftRowEmbedding := by
  obtain ⟨hzero, hsucc⟩ := prepended_rowLens hμ
  ext ⟨i, j⟩
  cases i <;>
    simp [Finset.mem_map, firstRowEmbedding_apply, shiftRowEmbedding_apply, Prod.ext_iff,
      YoungDiagram.mem_iff_lt_rowLen, hzero, hsucc]

private lemma prepended_cells_disjoint (m : ℕ) (α : YoungDiagram) :
    Disjoint ((Finset.range m).map firstRowEmbedding) (α.cells.map shiftRowEmbedding) := by
  rw [Finset.disjoint_left]
  rintro c hc hd
  obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hc
  obtain ⟨⟨i, l⟩, _, h⟩ := Finset.mem_map.mp hd
  have := congrArg Prod.fst h
  simp [firstRowEmbedding, shiftRowEmbedding] at this

private lemma prepended_colLen {m : ℕ} {α μ : YoungDiagram}
    (hμ : μ.rowLens = m :: α.rowLens) (hα : α.rowLen 0 ≤ m)
    {i j : ℕ} (hc : (i, j) ∈ α.cells) : μ.colLen j = α.colLen j + 1 := by
  obtain ⟨hzero, hsucc⟩ := prepended_rowLens hμ
  have hj : j < m := lt_of_lt_of_le
    (YoungDiagram.mem_iff_lt_rowLen.mp hc)
    ((α.rowLen_anti 0 i (Nat.zero_le i)).trans hα)
  have htop : 0 < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp
    (YoungDiagram.mem_iff_lt_rowLen.mpr (by simpa [hzero] using hj))
  have hshift (r : ℕ) : r + 1 < μ.colLen j ↔ r < α.colLen j := by
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen, hsucc,
      ← YoungDiagram.mem_iff_lt_rowLen, YoungDiagram.mem_iff_lt_colLen]
  have hupper := (hshift (α.colLen j)).not.mpr (Nat.lt_irrefl _)
  by_cases hcol : α.colLen j = 0
  · omega
  · have hlower := (hshift (α.colLen j - 1)).mpr (by omega)
    omega

private lemma prod_range_sub (m : ℕ) :
    ∏ j ∈ Finset.range m, (m - j) = m.factorial := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.prod_range_succ']
    simp only [Nat.add_sub_add_right, Nat.sub_zero]
    rw [ih, Nat.factorial_succ]
    exact Nat.mul_comm _ _

private lemma prepended_hookProduct {m : ℕ} {α μ : YoungDiagram}
    (hμ : μ.rowLens = m :: α.rowLens) (hα : α.rowLen 0 ≤ m) :
    m.factorial * hookProduct α ≤ hookProduct μ := by
  obtain ⟨hzero, hsucc⟩ := prepended_rowLens hμ
  have htail : ∀ c ∈ α.cells,
      hookLength μ (c.1 + 1) c.2 = hookLength α c.1 c.2 := by
    intro c hc
    unfold hookLength
    rw [hsucc, prepended_colLen hμ hα hc]
    omega
  have hfirst : m.factorial ≤ ∏ j ∈ Finset.range m, hookLength μ 0 j := by
    rw [← prod_range_sub m]
    apply Finset.prod_le_prod
    intro j hj
    have hcol : 0 < μ.colLen j := YoungDiagram.mem_iff_lt_colLen.mp
      (YoungDiagram.mem_iff_lt_rowLen.mpr (by simpa [hzero] using hj))
    unfold hookLength
    rw [hzero]
    omega
  unfold hookProduct
  rw [prepended_cells hμ, Finset.prod_union (prepended_cells_disjoint m α)]
  simp only [Finset.prod_map, firstRowEmbedding_apply, shiftRowEmbedding_apply]
  rw [Finset.prod_congr rfl htail]
  exact Nat.mul_le_mul_right _ hfirst

/-- **Lemma 5 (sharp form)** [LaroccaHavlicek2025]: if `μ = (n - k, α₁, α₂, …)` with `α ⊢ k`
and `α.rowLen 0 ≤ n - k`, then `hookDim μ ≤ n ^ k * hookDim α / k!`. -/
theorem lemma5_dimension_bound_sharp (n k : ℕ) (α μ : YoungDiagram)
    (hcard : α.cells.card = k) (hμ : μ.rowLens = (n - k) :: α.rowLens)
    (hα1 : α.rowLen 0 ≤ n - k) :
    hookDim μ ≤ (n : ℚ) ^ k * hookDim α / (k.factorial : ℚ) := by
  have hpos : 0 < n - k := μ.pos_of_mem_rowLens _ (by rw [hμ]; exact List.mem_cons_self)
  have hkn : k ≤ n := by omega
  have hμcard : μ.cells.card = n := by
    rw [prepended_cells hμ, Finset.card_union_of_disjoint
      (prepended_cells_disjoint (n - k) α), Finset.card_map, Finset.card_map,
      Finset.card_range, hcard]
    omega
  have hprod : ((n - k).factorial : ℚ) * (hookProduct α : ℚ) ≤
      (hookProduct μ : ℚ) := by
    exact_mod_cast prepended_hookProduct hμ hα1
  have hden : (0 : ℚ) < ((n - k).factorial : ℚ) * (hookProduct α : ℚ) := by
    have := one_le_hookProduct α
    positivity
  have hfac : n.factorial ≤ n ^ k * (n - k).factorial := by
    calc
      n.factorial = (n - k).factorial * n.descFactorial k :=
        (Nat.factorial_mul_descFactorial hkn).symm
      _ ≤ (n - k).factorial * n ^ k :=
        Nat.mul_le_mul_left _ (Nat.descFactorial_le_pow n k)
      _ = _ := Nat.mul_comm _ _
  have hfacq : (n.factorial : ℚ) ≤ (n : ℚ) ^ k * ((n - k).factorial : ℚ) := by
    exact_mod_cast hfac
  calc
    hookDim μ = (n.factorial : ℚ) / (hookProduct μ : ℚ) := by rw [hookDim, hμcard]
    _ ≤ (n.factorial : ℚ) / (((n - k).factorial : ℚ) * (hookProduct α : ℚ)) :=
      div_le_div_of_nonneg_left (by positivity) hden hprod
    _ ≤ ((n : ℚ) ^ k * ((n - k).factorial : ℚ)) /
        (((n - k).factorial : ℚ) * (hookProduct α : ℚ)) :=
      div_le_div_of_nonneg_right hfacq hden.le
    _ = (n : ℚ) ^ k * hookDim α / (k.factorial : ℚ) := by
      rw [hookDim, hcard]
      have hf : ((n - k).factorial : ℚ) ≠ 0 := by positivity
      have hk : (k.factorial : ℚ) ≠ 0 := by positivity
      field_simp

/-- **Lemma 5** [LaroccaHavlicek2025]: if `μ = (n - k, α₁, α₂, …)` with `α ⊢ k` and
`α.rowLen 0 ≤ n - k`, then `hookDim μ ≤ k! * n ^ k / hookDim α`. -/
theorem lemma5_dimension_bound (n k : ℕ) (α μ : YoungDiagram)
    (hcard : α.cells.card = k) (hμ : μ.rowLens = (n - k) :: α.rowLens)
    (hα1 : α.rowLen 0 ≤ n - k) :
    hookDim μ ≤ (k.factorial : ℚ) * (n : ℚ) ^ k / hookDim α := by
  have hd : (0 : ℚ) < hookDim α := by
    unfold hookDim
    have := one_le_hookProduct α
    exact div_pos (by positivity) (by exact_mod_cast (by omega : 0 < hookProduct α))
  have hf : (0 : ℚ) < (k.factorial : ℚ) := by positivity
  have hle := hookDim_le_factorial hcard
  have hsq : hookDim α * hookDim α ≤ (k.factorial : ℚ) * (k.factorial : ℚ) :=
    mul_self_le_mul_self hd.le hle
  refine (lemma5_dimension_bound_sharp n k α μ hcard hμ hα1).trans ?_
  rw [le_div_iff₀ hd, div_mul_eq_mul_div, div_le_iff₀ hf]
  have hp := mul_le_mul_of_nonneg_left hsq (show (0 : ℚ) ≤ (n : ℚ) ^ k by positivity)
  nlinarith only [hp]

end Qatlib.Papers.RepMultiplic24.MainResults
