/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.FieldTheory.Finiteness
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Logic.Relation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Hamiltonian cycle as a 2inK-SAT occupation problem

Paper: arXiv:1512.00859v2 (29 Aug 2016), Sec. IV, pp. 13–15.

The Hamiltonian-cycle instance on a `K`-regular undirected graph with `n` nodes is
mapped to a `2inK-SAT` Occupation problem (source Eq. (8)):

* variables are the `M = K n / 2` edges, clauses are the `n` nodes, and each
  clause asks that exactly two incident edges be selected;
* the related incidence matrix `A` is `n × M`, with exactly `K` ones per row
  (nodes) and exactly two ones per column (edges);
* the source proves that all rows of `A` are linearly independent over `GF(2)`
  except for one (the modulo-2 sum of all rows vanishes, and connectivity removes
  the trivial dependencies), i.e. `n' = n - 1` (source p. 14, line 141);
* consequently the quantum search space has size `2^(M - n')` and the cost is
  `√(2^(M-n')) = 2^((M - (n-1))/2) = 2^((K-2)n/4 + 1/2) = O(2^((K-2)n/4))`
  (source p. 13, line 127), giving `O(2^(n/4))` for `K = 3` and for
  `(3,3)`-regular bipartite graphs.

The incidence-matrix model below indexes edges by `Fin m` and records the two
endpoints of every edge.  The linear-algebra content is proved over `ZMod 2`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.ExactSat15.MainResults.HamiltonianCycleReduction

local instance : Fact (Nat.Prime 2) := ⟨by decide⟩

open Matrix

/-- A finite graph presented by its edges: edge `e` joins the distinct nodes
`s e` and `t e`.  This is the incidence data of the `2inK-SAT` reduction
(source p. 13: every edge connects two nodes). -/
structure EdgeEndpoints (n m : ℕ) where
  s : Fin m → Fin n
  t : Fin m → Fin n
  ne : ∀ e, s e ≠ t e

/-- The `n × m` incidence matrix of `E` over `ZMod 2`: entry `(i,e)` is `1` iff
node `i` is an endpoint of edge `e` (source p. 14). -/
def incidenceMatrix {n m : ℕ} (E : EdgeEndpoints n m) : Matrix (Fin n) (Fin m) (ZMod 2) :=
  fun i e => if i = E.s e then 1 else if i = E.t e then 1 else 0

/-- The node-adjacency relation induced by the edges. -/
def Adj {n m : ℕ} (E : EdgeEndpoints n m) (i j : Fin n) : Prop :=
  i ≠ j ∧ ∃ e, (i = E.s e ∧ j = E.t e) ∨ (i = E.t e ∧ j = E.s e)

/-- `E` is connected in the combinatorial sense: every pair of nodes is joined
by a walk along the edges (source hypothesis "G has a single connected
component", p. 14). -/
def EdgeConnected {n m : ℕ} (E : EdgeEndpoints n m) : Prop :=
  ∀ i j : Fin n, Relation.ReflTransGen (Adj E) i j

/-- Pointwise decomposition of the incidence-matrix product: the entry at `i`
of column `e` is `1` exactly at the two endpoints of `e`. -/
lemma incidence_entry_mul {n m : ℕ} (E : EdgeEndpoints n m) (v : Fin n → ZMod 2)
    (e : Fin m) (i : Fin n) :
    incidenceMatrix E i e * v i =
      (if i = E.s e then v i else 0) + (if i = E.t e then v i else 0) := by
  unfold incidenceMatrix
  by_cases hs : i = E.s e
  · subst hs
    have hne : E.s e ≠ E.t e := E.ne e
    simp [hne]
  · by_cases ht : i = E.t e
    · subst ht
      simp [hs]
    · simp [hs, ht]

/-- Multiplying the transposed incidence matrix by `v` returns, at edge `e`,
the sum of `v` over the two endpoints of `e`. -/
lemma transpose_mulVec_apply {n m : ℕ} (E : EdgeEndpoints n m)
    (v : Fin n → ZMod 2) (e : Fin m) :
    (incidenceMatrix E)ᵀ.mulVec v e = v (E.s e) + v (E.t e) := by
  have hfun : (incidenceMatrix E)ᵀ.mulVec v e =
      ∑ j, incidenceMatrix E j e * v j := rfl
  rw [hfun]
  rw [Finset.sum_congr rfl (fun i _ => incidence_entry_mul E v e i)]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

/-- In the kernel of the transposed incidence matrix, `v` takes equal values at
the two endpoints of every edge. -/
lemma kernel_edges_eq {n m : ℕ} (E : EdgeEndpoints n m) (v : Fin n → ZMod 2)
    (hv : v ∈ LinearMap.ker (incidenceMatrix E)ᵀ.mulVecLin) (e : Fin m) :
    v (E.s e) = v (E.t e) := by
  have h : (incidenceMatrix E)ᵀ.mulVec v e = 0 := by
    have h0 : (incidenceMatrix E)ᵀ.mulVecLin v = 0 := LinearMap.mem_ker.mp hv
    simpa only [Matrix.mulVecLin_apply, Pi.zero_apply] using congrFun h0 e
  rw [transpose_mulVec_apply] at h
  have ht2 : v (E.t e) + v (E.t e) = 0 := by
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc v (E.t e) + v (E.t e) = (2 : ZMod 2) * v (E.t e) := by ring
      _ = 0 := by rw [h2, zero_mul]
  calc v (E.s e) = v (E.s e) + 0 := by rw [add_zero]
    _ = v (E.s e) + (v (E.t e) + v (E.t e)) := by rw [ht2]
    _ = (v (E.s e) + v (E.t e)) + v (E.t e) := by ring
    _ = 0 + v (E.t e) := by rw [h]
    _ = v (E.t e) := by rw [zero_add]

/-- Values equal on the endpoints of every edge are equal across one adjacency
step. -/
lemma adj_eq {n m : ℕ} (E : EdgeEndpoints n m) (v : Fin n → ZMod 2)
    (hv : ∀ e, v (E.s e) = v (E.t e)) {i j : Fin n} (h : Adj E i j) :
    v i = v j := by
  rcases h with ⟨_, e, hor⟩
  rcases hor with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hv e
  · exact (hv e).symm

/-- Connectivity propagates the endpoint equalities to all pairs of nodes:
a kernel vector is constant on a connected graph. -/
lemma eq_of_edgeConnected {n m : ℕ} (E : EdgeEndpoints n m) (v : Fin n → ZMod 2)
    (hv : ∀ e, v (E.s e) = v (E.t e)) (hconn : EdgeConnected E) (i j : Fin n) :
    v i = v j := by
  induction hconn i j with
  | refl => rfl
  | tail _ hbc ih => exact ih.trans (adj_eq E v hv hbc)

/-- **Kernel of the incidence matrix** (source p. 14): for a connected graph the
left kernel of the incidence matrix is exactly the one-dimensional space of
constant functions.  The modulo-2 sum of all rows therefore vanishes, and no
other dependency exists. -/
theorem kernel_eq_span_ones {n m : ℕ} (E : EdgeEndpoints n m) (hconn : EdgeConnected E)
    (hn : 0 < n) :
    LinearMap.ker (incidenceMatrix E)ᵀ.mulVecLin =
      Submodule.span (ZMod 2) ({fun _ : Fin n => (1 : ZMod 2)} :
        Set (Fin n → ZMod 2)) := by
  apply le_antisymm
  · intro v hv
    have hedge : ∀ e, v (E.s e) = v (E.t e) := fun e => kernel_edges_eq E v hv e
    have hveq : v = (v ⟨0, hn⟩) • (fun _ : Fin n => (1 : ZMod 2)) := by
      funext i
      rw [Pi.smul_apply, smul_eq_mul, mul_one, eq_of_edgeConnected E v hedge hconn i ⟨0, hn⟩]
    rw [hveq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · rw [Submodule.span_le]
    intro v hv
    simp only [Set.mem_singleton_iff] at hv
    rw [hv]
    show (incidenceMatrix E)ᵀ.mulVecLin (fun _ : Fin n => (1 : ZMod 2)) = 0
    funext e
    rw [Matrix.mulVecLin_apply, transpose_mulVec_apply]
    have h2 : (2 : ZMod 2) = 0 := by decide
    calc (1 : ZMod 2) + 1 = 2 := by norm_num
      _ = 0 := h2

/-- The kernel is one-dimensional, hence `k = 1`. -/
theorem finrank_kernel_eq_one {n m : ℕ} (E : EdgeEndpoints n m)
    (hconn : EdgeConnected E) (hn : 0 < n) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (incidenceMatrix E)ᵀ.mulVecLin) = 1 := by
  rw [kernel_eq_span_ones E hconn hn]
  exact finrank_span_singleton (v := fun _ : Fin n => (1 : ZMod 2)) (by
    intro hzero
    have := congrFun hzero ⟨0, hn⟩
    simp at this)

/-- **`n' = n - 1`** (source p. 14, line 141): the incidence matrix of a
connected graph has rank `n - 1` over `GF(2)`, so all rows but one are linearly
independent. -/
theorem rank_incidenceMatrix {n m : ℕ} (E : EdgeEndpoints n m) (hconn : EdgeConnected E)
    (hn : 0 < n) :
    Matrix.rank (incidenceMatrix E) = n - 1 := by
  have h := LinearMap.finrank_range_add_finrank_ker (incidenceMatrix E)ᵀ.mulVecLin
  have hker := finrank_kernel_eq_one E hconn hn
  have hsrc : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  rw [hker, hsrc] at h
  have hrankT : Matrix.rank (incidenceMatrix E)ᵀ = n - 1 := by
    have : Matrix.rank (incidenceMatrix E)ᵀ =
        Module.finrank (ZMod 2) (LinearMap.range (incidenceMatrix E)ᵀ.mulVecLin) := rfl
    omega
  rw [← Matrix.rank_transpose (A := incidenceMatrix E)]
  exact hrankT

/-! ## The resulting query complexity (source p. 13) -/

/-- Exponent of the quantum search on the `2inK-SAT` candidate space:
`(M - n') / 2` with `M = K n / 2` edge-variables and `n' = n - 1` independent
node-clauses. -/
def hcQueryExponent (K n : ℝ) : ℝ := (K * n / 2 - (n - 1)) / 2

/-- Exponent claimed by the paper, `(K-2)n/4`. -/
def hcClaimExponent (K n : ℝ) : ℝ := (K - 2) * n / 4

/-- The two exponents differ by exactly `1/2`. -/
theorem hcQueryExponent_eq (K n : ℝ) :
    hcQueryExponent K n = hcClaimExponent K n + 1 / 2 := by
  unfold hcQueryExponent hcClaimExponent
  ring

/-- The quantum search cost `2^((M-n')/2)` for the Hamiltonian-cycle reduction. -/
def hcQueryCost (K n : ℝ) : ℝ := Real.rpow 2 (hcQueryExponent K n)

/-- **Hamiltonian-cycle complexity** (source p. 13, line 127): for a
`K`-regular graph, `2^((M-n')/2) ≤ √2 · 2^((K-2)n/4)`, i.e. the algorithm runs in
`O(2^((K-2)n/4))`. -/
theorem hcQueryCost_le (K n : ℝ) (hK : 3 ≤ K) (hn : 1 ≤ n) :
    hcQueryCost K n ≤ Real.sqrt 2 * Real.rpow 2 (hcClaimExponent K n) := by
  unfold hcQueryCost
  rw [hcQueryExponent_eq]
  have hrw : Real.rpow 2 (hcClaimExponent K n + 1 / 2) =
      Real.rpow 2 (hcClaimExponent K n) * Real.rpow 2 (1 / 2 : ℝ) :=
    Real.rpow_add (by norm_num : (0 : ℝ) < 2) _ _
  rw [hrw]
  have hhalf : Real.rpow 2 (1 / 2 : ℝ) = Real.sqrt 2 :=
    (Real.sqrt_eq_rpow 2).symm
  rw [hhalf]
  rw [mul_comm]

/-- **The `K = 3` case** (source p. 13): `O(2^(n/4))`; the same bound holds for
`(3,3)`-regular bipartite graphs, whose maximum degree is `3`. -/
theorem hcQueryCost_three (n : ℝ) (hn : 1 ≤ n) :
    hcQueryCost 3 n ≤ Real.sqrt 2 * Real.rpow 2 (n / 4) := by
  have h := hcQueryCost_le 3 n (by norm_num) hn
  have he : hcClaimExponent 3 n = n / 4 := by
    unfold hcClaimExponent
    ring
  rwa [he] at h

end Qatlib.Papers.ExactSat15.MainResults.HamiltonianCycleReduction
