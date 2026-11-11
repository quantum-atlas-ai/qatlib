/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Graph collision of Jeffery--Kothari--Magniez (arXiv:1112.5855v2, Section 3)

The paper solves the graph collision problem on a balanced bipartite graph that
is known up to at most `m` non-edges, and whose left vertices are sorted by
decreasing degree (so the non-neighbour counts `c i = n - d i` are sorted
increasingly).  The algorithm `AllGCG` splits on the non-neighbour count `c r`
of the highest-degree marked vertex `r`:

* Case 1 (`c r ≤ √m`): read all non-neighbours of `r`;
* Case 2 (`c r ≥ √m`): every remaining left vertex has at least `√m`
  non-neighbours, so there are at most `√m` of them.

This module formalizes the bipartite problem statement, the co-degree
bookkeeping, and the counting/cost cores of Theorem 3.1.  The quantum
subroutines (`FindMax`, `SearchAll`, `Search`) are the cited primitives; only
their paper-stated costs enter the ledger.
-/

namespace Qatlib.Papers.BoolMatMult11.MainResults.GraphCollision

open scoped BigOperators

set_option autoImplicit false

/-- Graph collision of the paper: `(i, j)` is an edge of the known bipartite
graph and both endpoint labels are `1`.  The known graph is recorded by its
non-edges, which is exactly the data the Boolean matrix product maintains. -/
def IsCollision {n : ℕ} (nonEdges : Finset (Fin n × Fin n)) (fA fB : Fin n → Bool)
    (i j : Fin n) : Prop :=
  fA i = true ∧ fB j = true ∧ (i, j) ∉ nonEdges

/-- All graph collisions of an instance. -/
noncomputable def collisionPairs {n : ℕ} (nonEdges : Finset (Fin n × Fin n))
    (fA fB : Fin n → Bool) : Finset (Fin n × Fin n) := by
  classical
  exact Finset.univ.filter fun p => IsCollision nonEdges fA fB p.1 p.2

/-- Number of graph collisions `λ`. -/
noncomputable def collisionCount {n : ℕ} (nonEdges : Finset (Fin n × Fin n))
    (fA fB : Fin n → Bool) : ℕ :=
  (collisionPairs nonEdges fA fB).card

/-- Number of non-neighbours of the left vertex `i`, the paper's
`c i = n - d i`. -/
def coDegree {n : ℕ} (nonEdges : Finset (Fin n × Fin n)) (i : Fin n) : ℕ :=
  (nonEdges.filter fun e => e.1 = i).card

/-- The co-degrees partition the non-edges: their total is exactly `m`. -/
theorem sum_coDegree {n : ℕ} (nonEdges : Finset (Fin n × Fin n)) :
    (∑ i : Fin n, coDegree nonEdges i) = nonEdges.card := by
  have h := Finset.card_eq_sum_card_fiberwise (s := nonEdges) (f := Prod.fst)
    (t := Finset.univ) (fun x _ => Finset.mem_univ x.1)
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  simp [coDegree]

/-- Along the paper's sorted co-degree sequence, a later vertex has at least as
many non-neighbours as an earlier one. -/
theorem coDegree_mono_le (c : ℕ → ℕ) (hmono : ∀ i, c i ≤ c (i + 1))
    {r i : ℕ} (hri : r ≤ i) : c r ≤ c i := by
  refine Nat.le_induction (m := r) (P := fun k _ => c r ≤ c k) le_rfl ?_ i hri
  intro k _ ih
  exact ih.trans (hmono k)

/-- Block lower bound: the tail `r, …, n-1` of the sorted co-degree sequence
contributes at least `c r * (n - r)` non-edges. -/
theorem block_cost_le {n r : ℕ} (c : ℕ → ℕ) (hmono : ∀ i, c i ≤ c (i + 1)) :
    c r * (n - r) ≤ ∑ i ∈ Finset.range n, c i := by
  have hsub : Finset.Ico r n ⊆ Finset.range n := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    rw [Finset.mem_range]
    omega
  have hblock : c r * (n - r) = ∑ _i ∈ Finset.Ico r n, c r := by
    rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul, mul_comm]
  calc
    c r * (n - r) = ∑ _i ∈ Finset.Ico r n, c r := hblock
    _ ≤ ∑ i ∈ Finset.Ico r n, c i := by
        apply Finset.sum_le_sum
        intro i hi
        rw [Finset.mem_Ico] at hi
        exact coDegree_mono_le c hmono hi.1
    _ ≤ ∑ i ∈ Finset.range n, c i :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro i _ _; exact Nat.zero_le _)

/-- **Case 2 of `AllGCG`.**  If the highest-degree marked vertex `r` has
`c r ≥ √m`, then the remaining left vertices number at most `√m`: each of them
has at least `c r ≥ √m` non-neighbours and there are only `m` non-edges in
total.  The inequality `c r ≥ √m` is stated in the division-free form
`m ≤ c r * c r`. -/
theorem case2_remaining_le_sqrt {n m r : ℕ} (c : ℕ → ℕ)
    (hmono : ∀ i, c i ≤ c (i + 1))
    (hsum : ∑ i ∈ Finset.range n, c i ≤ m)
    (hm : 0 < m) (hcr : m ≤ c r * c r) :
    ((n - r : ℕ) : ℝ) ≤ Real.sqrt (m : ℝ) := by
  have hblock : c r * (n - r) ≤ ∑ i ∈ Finset.range n, c i := block_cost_le c hmono
  have hblock' : c r * (n - r) ≤ m := hblock.trans hsum
  have hnat : (c r : ℝ) * ((n - r : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hblock'
  have hcr' : (m : ℝ) ≤ (c r : ℝ) * (c r : ℝ) := by exact_mod_cast hcr
  have hcr_ge : Real.sqrt (m : ℝ) ≤ (c r : ℝ) := by
    rw [Real.sqrt_le_iff]
    exact ⟨Nat.cast_nonneg _, by simpa [pow_two] using hcr'⟩
  have hmul : Real.sqrt (m : ℝ) * ((n - r : ℕ) : ℝ) ≤ (m : ℝ) := by
    calc
      Real.sqrt (m : ℝ) * ((n - r : ℕ) : ℝ) ≤
          (c r : ℝ) * ((n - r : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcr_ge (Nat.cast_nonneg _)
      _ ≤ (m : ℝ) := hnat
  have hsq : Real.sqrt (m : ℝ) * Real.sqrt (m : ℝ) = (m : ℝ) := by
    rw [← sq, Real.sq_sqrt (Nat.cast_nonneg m)]
  have hpos : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hm)
  exact le_of_mul_le_mul_left (by simpa [hsq] using hmul) hpos

/-- **Case 1 of `AllGCG`.**  If `c r ≤ √m` then reading all non-neighbours of
`r` costs at most `√m` queries. -/
theorem case1_read_cost_le {m c : ℕ} (hc : c * c ≤ m) :
    (c : ℝ) ≤ Real.sqrt (m : ℝ) := by
  rw [Real.le_sqrt (Nat.cast_nonneg c) (Nat.cast_nonneg m)]
  have hcast : (c : ℝ) * (c : ℝ) ≤ (m : ℝ) := by exact_mod_cast hc
  simpa [pow_two] using hcast

/-- **Theorem 3.1, `GC_all` cost core.**  `FindMax` costs `√n`, the two
`SearchAll` calls cost `2√(nλ)`, and the read step costs `√m`; for `λ ≥ 1`
this is at most `4(√(nλ) + √m)`. -/
theorem allGC_cost_bound {n m lam : ℕ} (hlam : 1 ≤ lam) :
    Real.sqrt (n : ℝ) + 2 * Real.sqrt ((n : ℝ) * lam) + Real.sqrt (m : ℝ) ≤
      4 * (Real.sqrt ((n : ℝ) * lam) + Real.sqrt (m : ℝ)) := by
  have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlam' : (1 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hlam
  have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * lam) := by
    apply Real.sqrt_le_sqrt
    nlinarith
  have h2 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * lam) := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  nlinarith

/-- **Theorem 3.1, decision version.**  Replacing the `SearchAll` calls by a
single `Search` costs `√n`, so deciding whether a collision exists costs at
most `2(√(nλ) + √m)`; with `λ ≥ 1` this is `O(√n + √m)` in the paper's `Õ`
ledger. -/
theorem gc_decision_cost_bound {n m lam : ℕ} (hlam : 1 ≤ lam) :
    Real.sqrt (n : ℝ) + Real.sqrt (m : ℝ) ≤
      2 * (Real.sqrt ((n : ℝ) * lam) + Real.sqrt (m : ℝ)) := by
  have h1 : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) * lam) := by
    apply Real.sqrt_le_sqrt
    have hlam' : (1 : ℝ) ≤ (lam : ℝ) := by exact_mod_cast hlam
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have h2 : (0 : ℝ) ≤ Real.sqrt ((n : ℝ) * lam) := Real.sqrt_nonneg _
  have h3 : (0 : ℝ) ≤ Real.sqrt (m : ℝ) := Real.sqrt_nonneg _
  linarith

end Qatlib.Papers.BoolMatMult11.MainResults.GraphCollision
