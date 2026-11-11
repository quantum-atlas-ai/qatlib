/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Order.Partition.Finpartition
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.Order.WellFounded

set_option backward.isDefEq.respectTransparency false

/-!
# PropTestGraph10 source model: the partition lattice and its chain coefficient

Fixed source: arXiv:1012.3174v3. This module transcribes the combinatorial core
of Sections 3--5 of the paper:

* `chainCoeff` is the paper's coefficient `c_{L',L}` (p. 6, used in
  Proposition 5 p. 6, Proposition 6 p. 7, and Proposition 19 p. 20). The paper
  defines it as the alternating count `∑_k (-1)^k · #{strict chains
  L' = L₀ < L₁ < … < L_k = L}` of the partition lattice, and in Appendix C.4
  derives the recurrence of eq. (12), p. 20.  We take the recurrence
  `c(P,Q) = -∑_{P < R ≤ Q} c(R,Q)` (together with `c(Q,Q) = 1`) as the
  definition: the alternating chain sum satisfies precisely this recurrence,
  and a recurrence on a finite poset has exactly one solution, so the two
  definitions agree.  The recurrence is well founded because the first argument
  strictly increases towards a fixed top element.
* `matchingFactor`, `fL` are the paper's `R_d(M,l)` (eq. (3), p. 6) and `f_L`
  (eq. (4), p. 6) built from the matching data `d_{i,j}`.
* `fL'` is the paper's `f'_L = ∑_{L' ≤ L} c_{L',L} f_{L'}` (p. 7).
* `Sα` is the paper's `S_α(L') = ∑_{S ∈ L'} ∑_{j=1}^c (∑_{i∈S} d_{i,j})^α`
  (p. 20), used in Proposition 19.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

-- The `≤` relation of an abstract finite poset (in particular the partition
-- lattice) is not decidable as a typeclass instance; the paper's sums range over
-- decidable predicates, and classically every proposition is decidable, so we
-- use classical decidability locally. The choice of `Decidable` instance does
-- not affect the value of a `filter`/`if` on a proposition.
attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.PropTestGraph10.MainResults.Model

/-- The number of elements strictly above a point of a finite poset. Used as the
well-founded measure for the recurrence defining `chainCoeff`. -/
noncomputable def rankUp {α : Type*} [PartialOrder α] [Fintype α] (P : α) : ℕ :=
  (by classical exact (Finset.univ.filter fun S : α => P < S).card)

/-- `rankUp` strictly decreases when the argument strictly increases. -/
theorem rankUp_lt_of_lt {α : Type*} [PartialOrder α] [Fintype α] {P R : α} (h : P < R) :
    rankUp R < rankUp P := by
  classical
  unfold rankUp
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
  · intro S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact fun hS => lt_trans h hS
  · intro hEq
    have hmem : R ∈ Finset.univ.filter (fun S : α => P < S) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact h
    rw [← hEq] at hmem
    simp at hmem

/-- The paper's chain coefficient `c_{L',L}` (p. 6), defined through the
recurrence of eq. (12), p. 20: `c(P,Q) = 1` when `P = Q` and
`c(P,Q) = -∑_{P < R ≤ Q} c(R,Q)` otherwise. The alternating strict-chain sum
that the paper uses satisfies this recurrence, and the recurrence determines a
unique function on a finite poset, so this is the paper's coefficient. -/
noncomputable def chainCoeff {α : Type*} [PartialOrder α] [Fintype α]
    (P : α) (Q : α) : ℤ :=
  (InvImage.wf (rankUp (α := α)) Nat.lt_wfRel.wf).fix (C := fun _ => ℤ)
    (fun P' ih =>
      if P' = Q then 1
      else -∑ R : {R : α // R ∈ Finset.univ.filter (fun R : α => P' < R ∧ R ≤ Q)},
             ih R.1 (rankUp_lt_of_lt (by
               have hR : P' < R.1 := (Finset.mem_filter.mp R.2).2.1
               exact hR))) P

/-- Unfolding lemma for `chainCoeff`: on the diagonal the coefficient is `1`
(the empty chain, p. 6). -/
theorem chainCoeff_self {α : Type*} [PartialOrder α] [Fintype α] (Q : α) :
    chainCoeff Q Q = 1 := by
  classical
  conv_lhs => unfold chainCoeff
  rw [WellFounded.fix_eq]
  simp

/-- Unfolding lemma for `chainCoeff`: the recurrence of eq. (12), p. 20. -/
theorem chainCoeff_of_lt {α : Type*} [PartialOrder α] [Fintype α] {P Q : α} (h : P < Q) :
    chainCoeff P Q =
      -∑ R ∈ Finset.univ.filter (fun R : α => P < R ∧ R ≤ Q), chainCoeff R Q := by
  classical
  conv_lhs => unfold chainCoeff
  rw [WellFounded.fix_eq]
  have hne : ¬ P = Q := h.ne
  simp only [hne, if_false]
  congr 1
  change ∑ x : {x : α // x ∈ Finset.univ.filter (fun R : α => P < R ∧ R ≤ Q)},
      chainCoeff x.1 Q =
    ∑ R ∈ Finset.univ.filter (fun R : α => P < R ∧ R ≤ Q), chainCoeff R Q
  rw [Finset.sum_coe_sort (Finset.univ.filter (fun R : α => P < R ∧ R ≤ Q))
    (fun R => chainCoeff R Q)]

/-- The Möbius identity behind Proposition 5 (p. 6): for `P < Q`, the
alternating chain coefficient sums to zero over the interval `[P, Q]`. More
generally, `∑_{P ≤ R ≤ Q} c_{R,Q} = 1` if `P = Q` and `0` otherwise. -/
theorem sum_chainCoeff_eq {α : Type*} [PartialOrder α] [Fintype α] (P Q : α) :
    ∑ R ∈ Finset.univ.filter (fun R : α => P ≤ R ∧ R ≤ Q), chainCoeff R Q =
      if P = Q then 1 else 0 := by
  classical
  by_cases hPQ : P = Q
  · subst hPQ
    -- diagonal case: the interval is the singleton `{P}`
    have hset : Finset.univ.filter (fun R : α => P ≤ R ∧ R ≤ P) = {P} := by
      ext R
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩
        exact le_antisymm h2 h1
      · intro hmem
        rw [hmem]
        exact ⟨le_refl P, le_refl P⟩
    rw [hset, Finset.sum_singleton, chainCoeff_self, if_pos rfl]
  · by_cases hle : P ≤ Q
    · -- strict case: split off the `P` term and use the recurrence
      have hlt : P < Q := lt_of_le_of_ne hle hPQ
      rw [if_neg hPQ]
      have hset : Finset.univ.filter (fun R : α => P ≤ R ∧ R ≤ Q) =
          insert P (Finset.univ.filter (fun R : α => P < R ∧ R ≤ Q)) := by
        ext R
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · rintro ⟨h1, h2⟩
          rcases eq_or_lt_of_le h1 with hEq | h1lt
          · exact Or.inl hEq.symm
          · exact Or.inr ⟨h1lt, h2⟩
        · rintro (hEq | ⟨h1, h2⟩)
          · rw [hEq]
            exact ⟨le_refl P, hlt.le⟩
          · exact ⟨le_of_lt h1, h2⟩
      have hnotmem : P ∉ Finset.univ.filter (fun R : α => P < R ∧ R ≤ Q) := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact fun hPP => (lt_irrefl P) hPP.1
      rw [hset, Finset.sum_insert hnotmem, chainCoeff_of_lt hlt]
      ring
    · -- `P ≰ Q`: the interval is empty and `P ≠ Q`
      rw [if_neg hPQ]
      have hempty : Finset.univ.filter (fun R : α => P ≤ R ∧ R ≤ Q) = ∅ := by
        rw [Finset.filter_eq_empty_iff]
        intro R _
        rintro ⟨h1, h2⟩
        exact hle (le_trans h1 h2)
      rw [hempty, Finset.sum_empty]

/-- Proposition 5 of the paper (p. 6), for an arbitrary finite poset: if
`L'' < L` then `∑_{L'' ≤ L' ≤ L} c_{L',L} = 0`. The partition lattice of
`{1,…,k}` is the paper's instance; the statement holds for any finite partial
order, so we prove it at that generality. -/
theorem proposition5_chain_identity {α : Type*} [PartialOrder α] [Fintype α]
    {L'' L : α} (h : L'' < L) :
    ∑ L' ∈ Finset.univ.filter (fun L' : α => L'' ≤ L' ∧ L' ≤ L), chainCoeff L' L = 0 := by
  rw [sum_chainCoeff_eq, if_neg h.ne]

/-- Proposition 5 of the paper (p. 6) specialised to the partition lattice of
`{1,…,k}`, which is the form used in Sections 3--5. -/
theorem proposition5_partition_identity {k : ℕ}
    {L'' L : Finpartition (Finset.univ : Finset (Fin k))} (h : L'' < L) :
    ∑ L' ∈ Finset.univ.filter
        (fun L' : Finpartition (Finset.univ : Finset (Fin k)) => L'' ≤ L' ∧ L' ≤ L),
        chainCoeff L' L = 0 :=
  proposition5_chain_identity h

/-- The factor `l / (M - (2j-1)l)` of the paper's product `R_d(M,l)`
(eq. (3), p. 6), indexed with `r = j - 1` so that `r ∈ range m` enumerates
`j = 1,…,m` and the odd numbers `2j-1 = 2r+1`. -/
def matchingFactor (M l : ℝ) (m : ℕ) : ℝ :=
  ∏ r ∈ Finset.range m, l / (M - (2 * (r : ℝ) + 1) * l)

/-- The paper's `f_L` (eq. (4), p. 6): the product over the blocks `S` of `L` and
over the `c` matchings of `R_{d_{S,j}}(M,l)`, where `d_{S,j} = ∑_{i∈S} d_{i,j}`. -/
def fL {k c : ℕ} (d : Fin k → Fin c → ℕ) (M l : ℝ)
    (L : Finpartition (Finset.univ : Finset (Fin k))) : ℝ :=
  ∏ S ∈ L.parts, ∏ j : Fin c, matchingFactor M l (∑ i ∈ S, d i j)

/-- The paper's `f'_L = ∑_{L' ≤ L} c_{L',L} f_{L'}` (p. 7). -/
noncomputable def fL' {k c : ℕ} (d : Fin k → Fin c → ℕ) (M l : ℝ)
    (L : Finpartition (Finset.univ : Finset (Fin k))) : ℝ :=
  ∑ L' ∈ Finset.univ.filter
      (fun L' : Finpartition (Finset.univ : Finset (Fin k)) => L' ≤ L),
    (chainCoeff L' L : ℝ) * fL d M l L'

/-- The paper's `S_α(L') = ∑_{S ∈ L'} ∑_{j=1}^c (∑_{i∈S} d_{i,j})^α` (p. 20). -/
noncomputable def Sα {k c : ℕ} (d : Fin k → Fin c → ℕ) (a : ℕ)
    (L : Finpartition (Finset.univ : Finset (Fin k))) : ℝ :=
  ∑ S ∈ L.parts, ∑ j : Fin c, (∑ i ∈ S, (d i j : ℝ)) ^ a

end Qatlib.Papers.PropTestGraph10.MainResults.Model
