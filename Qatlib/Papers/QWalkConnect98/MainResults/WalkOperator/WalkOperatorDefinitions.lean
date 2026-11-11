/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Matrix.Mul
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Algebra.BigOperators.Field

/-!
# Operators for the regular graph connectivity walk

`walkF`, `walkX`, and `walkP` are the local neighborhood matrix, coordinate swap, and diagonal
projection on vertex pairs. Their product `walkQ` is paired with the vertex-space matrix
`walkM`, defined using the adjacency matrix and the coefficients `walkA` and `walkB`.

The module also defines component sets and their uniform vectors, coordinate basis vectors,
diagonal lifts, and a finite Euclidean norm, with basic reachability and norm identities. The
mathematical setting is described in [Watrous1998].

## Main statements

* `walkQ` and `walkM`: the pair-space projected operator and vertex-space walk matrix.
* `uniformOn`: the uniform vector on a connected component.
* `l2norm_diagLift`: diagonal lifting preserves Euclidean norm.

## References

* [Watrous, 1998][Watrous1998]
-/

namespace Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator

open Finset
open scoped BigOperators

set_option autoImplicit false
noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The finite closed neighborhood obtained by adjoining `u` to its neighbor set. -/
def closedNbhd (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V :=
  insert u (G.neighborFinset u)

/-- A vertex belongs to the closed neighborhood of `u` exactly when it equals `u` or is adjacent
to `u`. -/
@[simp]
theorem mem_closedNbhd {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ closedNbhd G u ↔ v = u ∨ G.Adj u v := by
  simp [closedNbhd]

/-- Every vertex belongs to its own closed neighborhood. -/
@[simp]
theorem self_mem_closedNbhd (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    u ∈ closedNbhd G u := mem_closedNbhd.mpr (Or.inl rfl)

/-- Membership in each other's closed neighborhoods is symmetric. -/
theorem closedNbhd_comm {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ closedNbhd G u ↔ u ∈ closedNbhd G v := by
  rw [mem_closedNbhd, mem_closedNbhd]
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h.symm
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr h.symm

/-- The vector on vertex pairs equal to `x u` at `(u, u)` and zero on off-diagonal pairs. -/
def diagLift (x : V → ℝ) : V × V → ℝ :=
  fun p => if p.1 = p.2 then x p.1 else 0

/-- The diagonal lift at `p` is `x p.1` when the pair is diagonal and zero otherwise. -/
@[simp]
theorem diagLift_apply (x : V → ℝ) (p : V × V) :
    diagLift x p = if p.1 = p.2 then x p.1 else 0 := rfl

/-- The block matrix that, for each fixed first vertex, subtracts `2 / (d + 1)` times the
closed-neighborhood sum on that neighborhood and acts as the identity outside it. -/
def walkF (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) : Matrix (V × V) (V × V) ℝ :=
  Matrix.of fun p q =>
    if q.1 = p.1 then
      (if p.2 ∈ closedNbhd G p.1 then
        ((if q.2 = p.2 then 1 else 0) -
          (if q.2 ∈ closedNbhd G p.1 then 2 / (d + 1) else 0))
      else (if q.2 = p.2 then 1 else 0))
    else 0

/-- The permutation matrix exchanging the two vertices of a pair. -/
def walkX : Matrix (V × V) (V × V) ℝ :=
  Matrix.of fun p q => if q.1 = p.2 ∧ q.2 = p.1 then 1 else 0

/-- The coordinate projection onto the subspace supported on diagonal vertex pairs. -/
def walkP : Matrix (V × V) (V × V) ℝ :=
  Matrix.of fun p q => if p = q ∧ p.1 = p.2 then 1 else 0

/-- The projected pair-space operator `walkP * walkF G d * walkX * walkF G d * walkP`. -/
def walkQ (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) : Matrix (V × V) (V × V) ℝ :=
  walkP * walkF G d * walkX * walkF G d * walkP

/-- The real adjacency matrix of `G`, with entries one on adjacent pairs and zero elsewhere. -/
def adjMatrix (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  Matrix.of fun u v => if G.Adj u v then 1 else 0

/-- The coefficient `(1 - 2 / (d + 1)) ^ 2` for the identity part of the vertex walk. -/
def walkA (d : ℝ) : ℝ := (1 - 2 / (d + 1)) ^ 2

/-- The coefficient `(2 / (d + 1)) ^ 2` for the adjacency part of the vertex walk. -/
def walkB (d : ℝ) : ℝ := (2 / (d + 1)) ^ 2

/-- The vertex-space matrix `walkA d • 1 + walkB d • adjMatrix G`. -/
def walkM (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) : Matrix V V ℝ :=
  walkA d • (1 : Matrix V V ℝ) + walkB d • adjMatrix G

/-- The finite set of vertices reachable from `u`. -/
def compSet (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : Finset V := by
  classical
  exact Finset.univ.filter fun v => G.Reachable u v

/-- The cardinality of the connected component containing `u`. -/
def compSize (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : ℕ := (compSet G u).card

/-- Membership in `compSet G u` is equivalent to reachability from `u`. -/
@[simp]
theorem mem_compSet {G : SimpleGraph V} [DecidableRel G.Adj] {u v : V} :
    v ∈ compSet G u ↔ G.Reachable u v := by
  simp [compSet]

/-- Every vertex belongs to its own component set. -/
theorem self_mem_compSet (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    u ∈ compSet G u := by
  simp

/-- The natural-number cardinality of the component containing `u` is positive. -/
theorem compSet_pos (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : 0 < compSize G u := by
  unfold compSize
  exact Finset.card_pos.mpr ⟨u, self_mem_compSet G u⟩

/-- The real-valued cardinality of the component containing `u` is positive. -/
theorem compSize_pos (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) :
    (0 : ℝ) < (compSize G u : ℝ) := by
  exact_mod_cast compSet_pos G u

/-- The vector equal to the reciprocal component size on vertices reachable from `u` and zero
elsewhere. -/
def uniformOn (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) : V → ℝ := by
  classical
  exact fun v => if G.Reachable u v then 1 / (compSize G u : ℝ) else 0

/-- The Euclidean norm of a finite real vector, defined as the square root of the sum of
coordinate squares. -/
def l2norm {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ :=
  Real.sqrt (∑ i, x i ^ 2)

/-- The Euclidean norm `l2norm` is nonnegative. -/
theorem l2norm_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ l2norm x :=
  Real.sqrt_nonneg _

/-- The square of `l2norm x` is the sum of the squares of the coordinates of `x`. -/
theorem l2norm_sq_eq {ι : Type*} [Fintype ι] (x : ι → ℝ) :
    l2norm x ^ 2 = ∑ i, x i ^ 2 := by
  unfold l2norm
  exact Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

/-- Diagonal lifting preserves the Euclidean norm. -/
theorem l2norm_diagLift (x : V → ℝ) : l2norm (diagLift x) = l2norm x := by
  unfold l2norm
  congr 1
  rw [Fintype.sum_prod_type]
  have : ∀ a : V, (∑ b : V, diagLift x (a, b) ^ 2) = x a ^ 2 := by
    intro a
    simp [diagLift_apply]
  simp only [this]

/-- A vertex adjacent to a vertex reachable from `u` is itself reachable from `u`. -/
theorem reachable_of_adj {G : SimpleGraph V} {u v w : V}
    (huv : G.Reachable u v) (hvw : G.Adj v w) : G.Reachable u w := by
  exact huv.trans hvw.reachable

/-- If `v` is not reachable from `u`, then any vertex adjacent to `v` is also not reachable from
`u`. -/
theorem not_reachable_adj {G : SimpleGraph V} {u v w : V}
    (hv : ¬ G.Reachable u v) (hvw : G.Adj v w) : ¬ G.Reachable u w := by
  intro hw
  exact hv (hw.trans hvw.symm.reachable)

/-- The coordinate vector equal to one at `u` and zero at every other vertex. -/
def basisVec (u : V) : V → ℝ := fun v => if v = u then 1 else 0

/-- The coordinate vector `basisVec u` has value one at `u`. -/
@[simp]
theorem basisVec_apply_self (u : V) : basisVec u u = 1 := by
  simp [basisVec]

/-- The coordinate vector `basisVec u` vanishes at a vertex different from `u`. -/
theorem basisVec_apply_of_ne {u v : V} (h : v ≠ u) : basisVec u v = 0 := by
  simp [basisVec, h]

/-- The diagonal lift of `basisVec u` is the coordinate vector supported at the pair `(u, u)`. -/
theorem diagLift_basisVec (u : V) :
    diagLift (basisVec u) = fun p : V × V => if p = (u, u) then 1 else 0 := by
  funext p
  by_cases hp : p = (u, u)
  · subst hp
    simp [diagLift_apply, basisVec]
  · have hzero : (if p = (u, u) then (1 : ℝ) else 0) = 0 := by simp [hp]
    rw [hzero]
    by_cases h1 : p.1 = p.2
    · by_cases h2 : p.1 = u
      · exfalso
        apply hp
        ext
        · exact h2
        · rw [← h1]; exact h2
      · have h2' : ¬ p.2 = u := by rw [← h1]; exact h2
        simp [diagLift_apply, basisVec, h1, h2, h2']
    · simp [diagLift_apply, h1]

end

end Qatlib.Papers.QWalkConnect98.MainResults.WalkOperator
