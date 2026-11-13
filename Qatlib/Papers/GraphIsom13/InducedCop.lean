/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphIsom13.GiCost
import Mathlib.Data.Fintype.Pi

/-!
# A cost function for induced subgraph isomorphism

This module extends the graph-isomorphism cost construction of [GaitanClark2014] to induced
subgraphs. The product penalty `sgiCost3` searches over vertex embeddings, and the total
`sgiCost` has a zero exactly when `ContainsInduced` holds.

## Main statements

* `sgi_cop_zero_iff`: zero cost characterizes an induced copy of the target graph.
* `sgi_cop_witness`: permutation and embedding data extracted from a zero-cost string.

## References

* [Gaitan and Clark, 2014][GaitanClark2014]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GraphIsom13.InducedCop

open Qatlib.Papers.GraphIsom13.GiCost

/-- An injective choice of `n` vertices from an `N`-vertex set. -/
abbrev Choice (N n : ℕ) := Fin n ↪ Fin N

/-- The submatrix selected by `α` from the adjacency matrix conjugated by `sigmaMat s`. -/
def subgraphMatrix {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (s : IntStr N) (α : Fin n ↪ Fin N) : Matrix (Fin n) (Fin n) ℤ :=
  (sigmaMat s * G.adjMatrix ℤ * (sigmaMat s)ᵀ).submatrix α α

/-- The selected subgraph matrix entry is the corresponding entry of the conjugated adjacency
matrix [GaitanClark2014]. -/
theorem subgraphMatrix_apply {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (s : IntStr N) (α : Fin n ↪ Fin N) (i j : Fin n) :
    subgraphMatrix G s α i j
      = (sigmaMat s * G.adjMatrix ℤ * (sigmaMat s)ᵀ) (α i) (α j) :=
  Matrix.submatrix_apply ..

/-- The product over vertex embeddings of the entrywise adjacency discrepancy sums for the
selected submatrices. -/
def sgiCost3 {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (s : IntStr N) : ℕ :=
  ∏ α : Fin n ↪ Fin N,
    ∑ i : Fin n, ∑ j : Fin n,
      Int.natAbs (subgraphMatrix G s α i j - H.adjMatrix ℤ i j)

/-- The sum of the out-of-range and collision penalties and the induced-subgraph discrepancy
product. -/
def sgiCost {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (s : IntStr N) : ℕ :=
  cost1 s + cost2 s + sgiCost3 G H s

/-- There is an injective vertex map from `H` into `G` preserving and reflecting adjacency. -/
def ContainsInduced {N n : ℕ} (G : SimpleGraph (Fin N))
    (H : SimpleGraph (Fin n)) : Prop :=
  ∃ β : Fin n ↪ Fin N, ∀ i j, G.Adj (β i) (β j) ↔ H.Adj i j

/-- An integer adjacency-matrix entry is zero if and only if its vertices are not adjacent. -/
theorem adjMatrix_eq_zero_iff {m : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (i j : Fin m) : G.adjMatrix ℤ i j = 0 ↔ ¬ G.Adj i j := by
  rw [SimpleGraph.adjMatrix_apply]
  split <;> simp_all

/-- Two integer adjacency-matrix entries are equal if and only if their adjacency propositions
are equivalent. -/
theorem adjMatrix_entry_eq_iff {m n : ℕ} (G : SimpleGraph (Fin m)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (i k : Fin m) (a b : Fin n) :
    G.adjMatrix ℤ i k = H.adjMatrix ℤ a b ↔ (G.Adj i k ↔ H.Adj a b) := by
  constructor
  · intro h
    rw [← adjMatrix_eq_one_iff G i k, ← adjMatrix_eq_one_iff H a b, h]
  · intro h
    by_cases hg : G.Adj i k
    · rw [(adjMatrix_eq_one_iff G i k).mpr hg, (adjMatrix_eq_one_iff H a b).mpr (h.mp hg)]
    · have hg' : ¬ H.Adj a b := fun hh => hg (h.mpr hh)
      rw [(adjMatrix_eq_zero_iff G i k).mpr hg, (adjMatrix_eq_zero_iff H a b).mpr hg']

/-- The induced-subgraph discrepancy product is zero exactly when some selected submatrix equals
the adjacency matrix of `H`. -/
theorem sgiCost3_eq_zero_iff {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (s : IntStr N) :
    sgiCost3 G H s = 0 ↔ ∃ α : Fin n ↪ Fin N,
      ∀ i j, subgraphMatrix G s α i j = H.adjMatrix ℤ i j := by
  unfold sgiCost3
  rw [Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨α, -, hα⟩
    refine ⟨α, ?_⟩
    intro i j
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)).mp hα
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le _)).mp
      (h1 i (Finset.mem_univ _))
    have h3 := h2 j (Finset.mem_univ _)
    rw [Int.natAbs_eq_zero, sub_eq_zero] at h3
    exact h3
  · rintro ⟨α, hα⟩
    refine ⟨α, Finset.mem_univ _, ?_⟩
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)]
    intro i _
    rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le _)]
    intro j _
    rw [show subgraphMatrix G s α i j - H.adjMatrix ℤ i j = 0 by rw [hα]; simp]
    simp

/-- A zero-cost string exists if and only if `G` contains an induced copy of `H`
[GaitanClark2014]. -/
theorem sgi_cop_zero_iff {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    (∃ s : IntStr N, sgiCost G H s = 0) ↔ ContainsInduced G H := by
  constructor
  · rintro ⟨s, hs⟩
    unfold sgiCost at hs
    have h1 : cost1 s = 0 := by omega
    have h2 : cost2 s = 0 := by omega
    have h3 : sgiCost3 G H s = 0 := by omega
    obtain ⟨α, hα⟩ := (sgiCost3_eq_zero_iff G H s).mp h3
    have h1' := (cost1_eq_zero_iff s).mp h1
    have h2' := (cost2_eq_zero_iff s).mp h2
    have hsig := sigmaMat_eq_transpose_permMatrix s h1' h2'
    have hM : ∀ i j, (sigmaMat s * G.adjMatrix ℤ * (sigmaMat s)ᵀ) i j
        = G.adjMatrix ℤ ((permOf s h1' h2').symm i) ((permOf s h1' h2').symm j) := by
      intro i j
      rw [hsig]
      exact transpose_permMatrix_conj_apply (permOf s h1' h2') _ i j
    let β : Fin n ↪ Fin N := ⟨fun i => (permOf s h1' h2').symm (α i),
      fun a b hab => α.injective ((permOf s h1' h2').symm.injective hab)⟩
    refine ⟨β, ?_⟩
    intro i j
    have hentry : G.adjMatrix ℤ (β i) (β j) = H.adjMatrix ℤ i j := by
      have h := hα i j
      rw [subgraphMatrix, Matrix.submatrix_apply, hM (α i) (α j)] at h
      exact h
    exact (adjMatrix_entry_eq_iff G H (β i) (β j) i j).mp hentry
  · rintro ⟨β, hβ⟩
    let s : IntStr N := fun i =>
      ⟨i.val, lt_of_lt_of_le i.isLt (Nat.le_pow_clog (by norm_num) N)⟩
    refine ⟨s, ?_⟩
    have hc1 : cost1 s = 0 := (cost1_eq_zero_iff s).mpr (fun i => i.isLt)
    have hc2 : cost2 s = 0 := (cost2_eq_zero_iff s).mpr
      (fun i j hij => Fin.ext (by simpa [s] using congrArg Fin.val hij))
    have hσ : sigmaMat s = 1 := by
      ext i j
      simp only [sigmaMat, Matrix.one_apply, s]
      by_cases h : i = j
      · subst h
        simp
      · have hne : (i.val : ℤ) ≠ (j.val : ℤ) :=
          fun hv => h (Fin.ext (by exact_mod_cast hv))
        rw [if_neg hne, if_neg h]
    have hfac : (∑ i : Fin n, ∑ j : Fin n,
        Int.natAbs (subgraphMatrix G s β i j - H.adjMatrix ℤ i j)) = 0 := by
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Nat.zero_le _)]
      intro i _
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun j _ => Nat.zero_le _)]
      intro j _
      have hentry : G.adjMatrix ℤ (β i) (β j) = H.adjMatrix ℤ i j :=
        (adjMatrix_entry_eq_iff G H (β i) (β j) i j).mpr (hβ i j)
      have hM : subgraphMatrix G s β i j = G.adjMatrix ℤ (β i) (β j) := by
        rw [subgraphMatrix, Matrix.submatrix_apply, hσ, Matrix.one_mul,
          Matrix.transpose_one, Matrix.mul_one]
      rw [hM, hentry]
      simp
    have hc3 : sgiCost3 G H s = 0 := by
      unfold sgiCost3
      exact Finset.prod_eq_zero (Finset.mem_univ β) hfac
    unfold sgiCost
    rw [hc1, hc2, hc3]

/-- A zero-cost string yields a permutation and a vertex embedding identifying a selected
conjugated submatrix with `H` and preserving and reflecting adjacency. -/
theorem sgi_cop_witness {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (s : IntStr N)
    (hs : sgiCost G H s = 0) :
    ∃ (π : Equiv.Perm (Fin N)) (α : Fin n ↪ Fin N),
      sigmaMat s = (π.permMatrix ℤ)ᵀ ∧
      (∀ i j, subgraphMatrix G s α i j = H.adjMatrix ℤ i j) ∧
      (∀ i j, G.Adj (π.symm (α i)) (π.symm (α j)) ↔ H.Adj i j) := by
  unfold sgiCost at hs
  have h1 : cost1 s = 0 := by omega
  have h2 : cost2 s = 0 := by omega
  have h3 : sgiCost3 G H s = 0 := by omega
  obtain ⟨α, hα⟩ := (sgiCost3_eq_zero_iff G H s).mp h3
  have h1' := (cost1_eq_zero_iff s).mp h1
  have h2' := (cost2_eq_zero_iff s).mp h2
  refine ⟨permOf s h1' h2', α, sigmaMat_eq_transpose_permMatrix s h1' h2', hα, ?_⟩
  intro i j
  have hsig := sigmaMat_eq_transpose_permMatrix s h1' h2'
  have h := hα i j
  rw [subgraphMatrix, Matrix.submatrix_apply, hsig,
    transpose_permMatrix_conj_apply] at h
  exact (adjMatrix_entry_eq_iff G H _ _ i j).mp h

/-- Every string has strictly positive induced-subgraph cost if and only if `G` contains no
induced copy of `H`. -/
theorem sgi_cop_positive_iff {N n : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (H : SimpleGraph (Fin n)) [DecidableRel H.Adj] :
    (∀ s : IntStr N, 0 < sgiCost G H s) ↔ ¬ ContainsInduced G H := by
  constructor
  · intro h hc
    obtain ⟨s, hs⟩ := (sgi_cop_zero_iff G H).mpr hc
    exact absurd hs (Nat.ne_of_gt (h s))
  · intro hc s
    exact Nat.pos_of_ne_zero fun hzero => hc ((sgi_cop_zero_iff G H).mp ⟨s, hzero⟩)

end Qatlib.Papers.GraphIsom13.InducedCop
