/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option backward.isDefEq.respectTransparency false

/-!
# Sparsity of `C_{m,k}` (DiagMatEig19)

Source: *Computing eigenvalues of diagonalizable matrices in a quantum computer*,
fixed arXiv:1912.08015, Lemma 12 (§2.4, p.12).

For an `s`-sparse `M`, the paper shows that every row of the block matrix
`C_{m,k}` of eq. (12) is the sum of three contributions:

* the identity block (`1` nonzero entry per row);
* the `2πiMΔt/q` chain block (at most `s` nonzero entries per row, because `M`
  is `s`-sparse);
* the `(p+1)(k+1)`-coupling block, involving the `k+1` columns `q' = 0,…,k`
  (only for rows with `q = 0`).

Hence each row has at most `1 + s + (k+1) = s + k + 2` nonzero entries.  For the
rows with `q = 0` the `k+1` coupling entries (coefficient `-1`) are disjoint
from the identity and chain entries, so those rows have at least `k+1` nonzero
entries.  This gives `Θ(s+k)` for the sparsity of `C_{m,k}`.

The file abstracts a row by three functions `diag`, `chain`, `endpoint` on a
finite index type and proves both bounds.  The instantiation to the actual
`C_{m,k}` is the paper's eq. (33)-(35) entry computation.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.DiagMatEig19.MainResults

open scoped BigOperators

/-- Support (nonzero set) of a finitely supported row. -/
def rowSupport {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (f : Ω → ℂ) : Finset Ω :=
  Finset.univ.filter (fun x => f x ≠ 0)

/-- arXiv:1912.08015, Lemma 12, §2.4, p.12: upper bound on the number of
nonzero entries of a row of `C_{m,k}`.  The row is the sum of the identity,
chain and coupling contributions; their supports have at most `1`, `s` and
`k+1` elements, so the row has at most `s + k + 2` nonzero entries. -/
theorem lemma12_row_sparsity_upper
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (diag chain endpoint row : Ω → ℂ) (s k : ℕ)
    (hrow : ∀ x, row x = diag x + chain x + endpoint x)
    (hdiag : (rowSupport diag).card ≤ 1)
    (hchain : (rowSupport chain).card ≤ s)
    (hend : (rowSupport endpoint).card ≤ k + 1) :
    (rowSupport row).card ≤ s + k + 2 := by
  have hsub : rowSupport row ⊆
      rowSupport diag ∪ rowSupport chain ∪ rowSupport endpoint := by
    intro x hx
    by_contra h
    have h1 : x ∉ rowSupport diag := by
      intro hx1; exact h (by simp [hx1])
    have h2 : x ∉ rowSupport chain := by
      intro hx2; exact h (by simp [hx2])
    have h3 : x ∉ rowSupport endpoint := by
      intro hx3; exact h (by simp [hx3])
    have hd : diag x = 0 := by
      by_contra hd
      exact h1 (by simp [rowSupport, hd])
    have hc : chain x = 0 := by
      by_contra hc
      exact h2 (by simp [rowSupport, hc])
    have he : endpoint x = 0 := by
      by_contra he
      exact h3 (by simp [rowSupport, he])
    have hz : row x = 0 := by rw [hrow x, hd, hc, he]; ring
    have hxne : row x ≠ 0 := by simpa [rowSupport] using hx
    exact hxne hz
  calc
    (rowSupport row).card
        ≤ (rowSupport diag ∪ rowSupport chain ∪ rowSupport endpoint).card :=
          Finset.card_le_card hsub
    _ ≤ (rowSupport diag ∪ rowSupport chain).card + (rowSupport endpoint).card :=
          Finset.card_union_le _ _
    _ ≤ ((rowSupport diag).card + (rowSupport chain).card) +
          (rowSupport endpoint).card := by
          have := Finset.card_union_le (rowSupport diag) (rowSupport chain)
          linarith
    _ ≤ 1 + s + (k + 1) := by linarith
    _ = s + k + 2 := by ring

/-- arXiv:1912.08015, Lemma 12, §2.4, p.12: lower bound on the number of
nonzero entries of a `q = 0` row of `C_{m,k}`.  The `k+1` coupling entries have
coefficient `-1` and their columns are disjoint from the identity and chain
columns, so all of them survive in the sum. -/
theorem lemma12_row_sparsity_lower
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (diag chain endpoint row : Ω → ℂ) (k : ℕ)
    (hrow : ∀ x, row x = diag x + chain x + endpoint x)
    (hend : (rowSupport endpoint).card = k + 1)
    (hdisj : Disjoint (rowSupport endpoint) (rowSupport diag ∪ rowSupport chain)) :
    k + 1 ≤ (rowSupport row).card := by
  have hsub : rowSupport endpoint ⊆ rowSupport row := by
    intro x hx
    have hnotdiag : x ∉ rowSupport diag ∪ rowSupport chain :=
      Finset.disjoint_left.1 hdisj hx
    have hd : diag x = 0 := by
      by_contra hd
      exact hnotdiag (Finset.mem_union_left _ (by simp [rowSupport, hd]))
    have hc : chain x = 0 := by
      by_contra hc
      exact hnotdiag (Finset.mem_union_right _ (by simp [rowSupport, hc]))
    have he : endpoint x ≠ 0 := by simpa [rowSupport] using hx
    have : row x ≠ 0 := by rw [hrow x, hd, hc, zero_add, zero_add]; exact he
    simpa [rowSupport] using this
  calc
    k + 1 = (rowSupport endpoint).card := hend.symm
    _ ≤ (rowSupport row).card := Finset.card_le_card hsub

/-- arXiv:1912.08015, Lemma 12, §2.4, p.12: the sparsity of `C_{m,k}` is
`Θ(s + k)`.  For a `q = 0` row (where the coupling term spans all `k+1`
columns) the number of nonzero entries is at least `k+1` and at most
`s + k + 2`, and for an arbitrary row it is at most `s + k + 2`; both bounds
are linear in `s + k`, which is the paper's `Θ(s+k)` claim. -/
theorem lemma12_cmk_sparsity
    {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (diag chain endpoint row : Ω → ℂ) (s k : ℕ)
    (hrow : ∀ x, row x = diag x + chain x + endpoint x)
    (hdiag : (rowSupport diag).card ≤ 1)
    (hchain : (rowSupport chain).card ≤ s)
    (hend : (rowSupport endpoint).card = k + 1)
    (hdisj : Disjoint (rowSupport endpoint) (rowSupport diag ∪ rowSupport chain)) :
    k + 1 ≤ (rowSupport row).card ∧ (rowSupport row).card ≤ s + k + 2 :=
  ⟨lemma12_row_sparsity_lower diag chain endpoint row k hrow hend hdisj,
   lemma12_row_sparsity_upper diag chain endpoint row s k hrow hdiag hchain hend.le⟩

end Qatlib.Papers.DiagMatEig19.MainResults
