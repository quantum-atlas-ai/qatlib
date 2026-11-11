/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.UnambigMeas25.MainResults.Definitions.UnambigMeasModel

set_option backward.isDefEq.respectTransparency false

/-!
# Coset leaders and combinatorial counts — Appendix A.2

Paper: Buzet–Chailloux, *Fine-Grained Unambiguous Measurements*,
arXiv:2510.07298v2 (4 Nov 2025).

This file states Lemma 3 (p. 31), Lemma 4 (p. 31–32) and Lemma 5 (p. 32).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.UnambigMeas25.MainResults.Combinatorics

open Matrix BigOperators
open scoped Classical MatrixOrder ComplexOrder BigOperators

/-- The row support of a matrix `H`, i.e. the set of coordinates on which some
row of `H` is `1`. -/
def rowSupport {n k : ℕ} (H : MatZ k n) (j : Fin n) : Prop := ∃ r : Fin k, H r j = 1

/-- The coset leader `r_H^min(s)` of Lemma 3 for `H = I_S` (encoded by
`f : Fin k → Fin n` with `S = range f`): `0` on `S` and `s` on `Sᶜ`. -/
def cosetLeader {n k : ℕ} (f : Fin k → Fin n)
    (s : complementIndex f → ZMod 2) : F2 n :=
  fun j => if h : j ∈ Set.range f then 0 else s ⟨j, h⟩

/-- The indicator vector of `Sᶜ = [n] \ range f`. -/
def eIs {n k : ℕ} (f : Fin k → Fin n) : F2 n :=
  fun j => if j ∈ Set.range f then 0 else 1

/-- The count `N(k, i, x)` of Lemma 5:
`|{H ∈ E_k^n : i ∈ D_H(1) and ∃ s, r_H^min(s) = x}|`.  For `H ∈ E_k^n` with row
set `S = range f`, the conditions read `x_j = 0` for `j ∈ S` and `i_j = 1` for
`j ∉ S`. -/
def Ncount (n k : ℕ) (i x : F2 n) : ℕ :=
  (Finset.univ.filter (fun H : MatZ k n =>
    H ∈ EknSet n k ∧
      (∀ j : Fin n, rowSupport H j → x j = 0) ∧
      (∀ j : Fin n, ¬ rowSupport H j → i j = 1))).card

/-- **Lemma 3** (arXiv:2510.07298v2, p. 31).  For `H = I_S ∈ E_k^n` with
canonical generator `G_C = I_{Sᶜ}`, the dual coset is
`D_H(s) = {x : x_{Sᶜ} = s}` and its coset leader is the vector which is `0` on
`S` and `s` on `Sᶜ`; this leader is the unique minimum-weight element and its
support is contained in `Sᶜ`.

Source: Lemma 3, p. 31.  Proof: decompose any `x ∈ D_H(s)` as `x = (u, s)`
with `u` on `S`; `|x|_H = |u|_H + |s|_H` is minimised exactly at `u = 0`. -/
theorem lemma3 {n k : ℕ} (f : Fin k → Fin n) (s : complementIndex f → ZMod 2) :
    (cosetLeader f s ∈ canonCoset f s) ∧
      (∀ j : Fin n, cosetLeader f s j ≠ 0 → j ∉ Set.range f) ∧
      (∀ x : F2 n, x ∈ canonCoset f s →
        hammingWeight (cosetLeader f s) ≤ hammingWeight x) := by
  refine ⟨?_, ?_, ?_⟩
  · -- (i) the leader lies in the coset `D_H(s)`
    intro j
    show (if h : j.1 ∈ Set.range f then (0 : ZMod 2) else s ⟨j.1, h⟩) = s j
    rw [dif_neg j.2]
    exact congrArg s (Subtype.ext rfl)
  · -- (ii) its support is contained in `Sᶜ`
    intro j hj hmem
    have h0 : cosetLeader f s j = 0 := by
      show (if h : j ∈ Set.range f then (0 : ZMod 2) else s ⟨j, h⟩) = 0
      rw [dif_pos hmem]
    exact hj h0
  · -- (iii) minimality: nonzero coordinates of the leader are nonzero in `x`
    intro x hx
    unfold hammingWeight
    apply Finset.card_le_card
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ⊢
    by_cases hmem : a ∈ Set.range f
    · have h0 : cosetLeader f s a = 0 := by
        show (if h : a ∈ Set.range f then (0 : ZMod 2) else s ⟨a, h⟩) = 0
        rw [dif_pos hmem]
      exact absurd h0 ha
    · have hval : cosetLeader f s a = s ⟨a, hmem⟩ := by
        show (if h : a ∈ Set.range f then (0 : ZMod 2) else s ⟨a, h⟩) = s ⟨a, hmem⟩
        rw [dif_neg hmem]
      have hx' : x a = s ⟨a, hmem⟩ := hx ⟨a, hmem⟩
      rw [hx']
      exact hval ▸ ha

/-- **Lemma 4** (arXiv:2510.07298v2, p. 31–32).  For every `x ∈ 𝔽₂ⁿ` there is a
unique pair `(k, H)` with `H ∈ E_k^n` such that the coset leader
`r_H^min(1)` equals `x` (equivalently, `x ∈ D_H(1)`).

Source: Lemma 4, p. 31–32.  Proof: take `S = {j : x_j = 0}`, `k = n − |x|_H`
and `H = I_S`; by Lemma 3 the leader of `D_H(1)` is `0` on `S` and `1` on `Sᶜ`,
i.e. exactly `x`.  Uniqueness follows because the row set and `k` are recovered
from `x`. -/
def lemma4 {n : ℕ} (x : F2 n) : Prop :=
  ∃! p : (k : ℕ) × {H : MatZ k n // H ∈ EknSet n k},
      ∀ (f : Fin p.1 → Fin n), StrictMono f →
        (∀ (r : Fin p.1) (j : Fin n), p.2.1 r j = if j = f r then 1 else 0) →
          eIs f = x
  -- Paper: arXiv:2510.07298v2, Lemma 4, p. 31–32.
  -- Key steps: existence with `S = {j : x j = 0}`, ordered as a strictly
  -- monotone `f : Fin k → Fin n` with `k = n - |x|_H`; uniqueness by recovering
  -- `S` and `k` from `x`.
  -- Gap: constructing the strictly monotone enumeration `f` of an arbitrary
  -- `Finset` (`Finset.orderIsoOfFin`), and the uniqueness of `H ∈ E_k^n` for a
  -- given row set.
  -- Suggested tactic: use `Finset.equivFin`/`Finset.orderIsoOfFin` to produce
  -- `f`; for uniqueness, `Subtype.ext`/`Sigma.ext` after showing the row sets
  -- agree.
  -- Candidate dependencies: `Finset.orderIsoOfFin`, `Finset.card_eq_iff_eq_univ`.

/-- **Lemma 5** (arXiv:2510.07298v2, p. 32).  `N(k,i,x)` equals
`C(|i|_H − |x|_H, k − (n − |i|_H))` when `supp(x) ⊆ supp(i)` and
`n − |i|_H ≤ k ≤ n − |x|_H`, and `0` otherwise.

Source: Lemma 5, p. 32.  Proof: count the row sets `S` of size `k` such that
`x = 0` on `S` and `i = 1` off `S`; the description reduces to choosing
`k − (n − |i|_H)` elements among the `|i|_H − |x|_H` coordinates where `x = 1`,
and the count is zero when the bounds fail. -/
def lemma5 (n k : ℕ) (i x : F2 n) : Prop :=
  Ncount n k i x =
      if (∀ j : Fin n, x j ≠ 0 → i j ≠ 0) ∧
          n - hammingWeight i ≤ k ∧ k ≤ n - hammingWeight x then
        Nat.choose (hammingWeight i - hammingWeight x) (k - (n - hammingWeight i))
      else 0
  -- Paper: arXiv:2510.07298v2, Lemma 5, p. 32.
  -- Key steps: a row set `S` of size `k` satisfies the two conditions iff
  -- `{j : x_j = 1} ⊆ S ⊆ {j : i_j = 1}`; counting such `S` is
  -- `C(|i|_H - |x|_H, k - (n - |i|_H))` because the complement of `S` has
  -- `n - k` elements inside the support of `i`.
  -- Gap: translating the `E_k^n` filter into a `Finset.card` over subsets, and
  -- the binomial counting identity.
  -- Suggested tactic: rewrite `Ncount` as a sum over `Finset.powersetCard`,
  -- then use `Finset.card_eq_choose`/`Nat.choose` identities and `split_ifs`.

end Qatlib.Papers.UnambigMeas25.MainResults.Combinatorics
