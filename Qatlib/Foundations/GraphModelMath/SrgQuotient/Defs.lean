/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Combinatorics.SimpleGraph.StronglyRegular
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# Three-cell quotients for strongly regular graph search

This module partitions a graph around a marked vertex into the marked, neighboring, and
remaining cells. For a strongly regular graph, explicit adjacency actions on these indicators
define the three-dimensional `quotient` and the embedding `embed`.

The graph search `hamiltonian` intertwines with the reduced matrix `reduced` through this
embedding. This is the three-cell reduction underlying the search analysis in
[JanmarkMeyerWong2014].

## Main statements

* `adjacency_intertwines`: For a strongly regular graph, the cell embedding intertwines the
  quotient matrix with the full adjacency matrix, giving the three-cell adjacency reduction in
  [JanmarkMeyerWong2014].
* `hamiltonian_intertwines`: For a strongly regular graph, the cell embedding intertwines the
  reduced search matrix with the full graph search Hamiltonian.
* `parameter_identity`: For a strongly regular graph with positive vertex count, the parameters
  satisfy `k * (k-l-1) = (n-k-1) * m` in natural-number arithmetic.

## References

* [Janmark et al., 2014][JanmarkMeyerWong2014]
-/

set_option autoImplicit false
namespace Qatlib.Foundations.GraphModelMath.SrgQuotient
open Matrix
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (w : V)

/-- The complex indicator function of the marked vertex `w`. -/
def marked : V → ℂ := Pi.single w 1

/-- The complex indicator function of the neighbors of `w`. -/
def near : V → ℂ := fun v => G.adjMatrix ℂ v w

/-- The complex indicator function of vertices distinct from and nonadjacent to `w`. -/
def far : V → ℂ := fun v => if v ≠ w ∧ ¬ G.Adj v w then 1 else 0

omit [Fintype V] in

/-- The marked, neighbor, and nonneighbor indicators sum to the constant-one vector. -/
theorem partition : marked w + near G w + far G w = fun _ => 1 := by
  funext v
  by_cases hv : v = w
  · subst v; simp [marked, near, far]
  · by_cases ha : G.Adj v w <;> simp [marked, near, far, hv, ha]

/-- The adjacency matrix sends the marked indicator to the neighbor indicator. -/
theorem adjacency_marked : G.adjMatrix ℂ *ᵥ marked w = near G w := by
  simp only [marked, Matrix.mulVec_single_one]
  rfl

/-- The complement graph's adjacency matrix sends the marked indicator to the nonneighbor
indicator. -/
theorem complement_marked : Gᶜ.adjMatrix ℂ *ᵥ marked w = far G w := by
  funext v
  simp [marked, far,
    SimpleGraph.compl_adj]

/-- In a strongly regular graph, adjacency sends the neighbor indicator to the combination with
coefficients `k`, `l`, and `m` on the three cells. -/
theorem adjacency_near {n k l m : ℕ} (h : G.IsSRGWith n k l m) :
    G.adjMatrix ℂ *ᵥ near G w =
      (k : ℂ) • marked w + (l : ℂ) • near G w + (m : ℂ) • far G w := by
  rw [← adjacency_marked, Matrix.mulVec_mulVec, ← pow_two, h.matrix_eq,
    Matrix.add_mulVec, Matrix.add_mulVec]
  simp only [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [complement_marked, adjacency_marked]
  simp only [Nat.cast_smul_eq_nsmul]

/-- In a strongly regular graph, adjacency sends the nonneighbor indicator to `(k-l-1)` times
the neighbor indicator plus `(k-m)` times the nonneighbor indicator, with subtraction in the
complex coefficients. -/
theorem adjacency_far {n k l m : ℕ} (h : G.IsSRGWith n k l m) :
    G.adjMatrix ℂ *ᵥ far G w =
      ((k : ℂ) - l - 1) • near G w + ((k : ℂ) - m) • far G w := by
  have hp := partition G w
  have hf : far G w = (fun _ : V => (1 : ℂ)) - marked w - near G w := by
    rw [← hp]; abel
  have hu : G.adjMatrix ℂ *ᵥ (fun _ : V => (1 : ℂ)) = (k : ℂ) • (fun _ => 1) := by
    funext v
    exact G.adjMatrix_mulVec_const_apply_of_regular h.regular
  rw [hf, Matrix.mulVec_sub, Matrix.mulVec_sub, hu, adjacency_marked,
    adjacency_near G w h, ← partition G w]
  module

/-- The vertex vector constant on the three cells with respective values `z 0`, `z 1`, and `z
2`. -/
def embed (z : Fin 3 → ℂ) : V → ℂ :=
  z 0 • marked w + z 1 • near G w + z 2 • far G w

/-- The three-cell adjacency quotient matrix with rows `(0,k,0)`, `(1,l,k-l-1)`, and
`(0,m,k-m)`, with complex coefficients. -/
def quotient (k l m : ℕ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, (k : ℂ), 0;
     1, (l : ℂ), (k : ℂ) - l - 1;
     0, (m : ℂ), (k : ℂ) - m]

/-- For a strongly regular graph, the cell embedding intertwines the quotient matrix with the
full adjacency matrix, giving the three-cell adjacency reduction in [JanmarkMeyerWong2014]. -/
theorem adjacency_intertwines {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (z : Fin 3 → ℂ) :
    G.adjMatrix ℂ *ᵥ embed G w z = embed G w (quotient k l m *ᵥ z) := by
  simp only [embed, Matrix.mulVec_add, Matrix.mulVec_smul,
    adjacency_marked, adjacency_near G w h, adjacency_far G w h]
  funext v
  simp [quotient, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  ring

/-- The coordinate projector onto the marked vertex. -/
def markProjector : Matrix V V ℂ := fun v u => if v = w ∧ u = w then 1 else 0

/-- The marked projector sends a vector to its marked coordinate times the marked indicator. -/
theorem marked_projection (x : V → ℂ) :
    markProjector w *ᵥ x = x w • marked w := by
  funext v
  by_cases hv : v = w
  · subst v; simp [markProjector, Matrix.mulVec, dotProduct, marked]
  · simp [markProjector, Matrix.mulVec, dotProduct, marked, hv]

omit [Fintype V] in

/-- The value of the embedded vector at the marked vertex is its first coordinate. -/
theorem embed_at_marked (z : Fin 3 → ℂ) : embed G w z w = z 0 := by
  simp [embed, marked, near, far]

/-- The graph search matrix `-gamma • adjacency - markProjector`. -/
def hamiltonian (gamma : ℝ) : Matrix V V ℂ :=
  - (gamma : ℂ) • G.adjMatrix ℂ - markProjector w

/-- The three-dimensional search matrix formed from the adjacency quotient and the projector
onto coordinate zero. -/
def reduced (k l m : ℕ) (gamma : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  - (gamma : ℂ) • quotient k l m - markProjector (0 : Fin 3)

/-- For a strongly regular graph, the cell embedding intertwines the reduced search matrix with
the full graph search Hamiltonian. -/
theorem hamiltonian_intertwines {n k l m : ℕ} (h : G.IsSRGWith n k l m)
    (gamma : ℝ) (z : Fin 3 → ℂ) :
    hamiltonian G w gamma *ᵥ embed G w z =
      embed G w (reduced k l m gamma *ᵥ z) := by
  rw [hamiltonian, Matrix.sub_mulVec, Matrix.smul_mulVec, adjacency_intertwines G w h,
    marked_projection, embed_at_marked]
  funext v
  simp only [reduced, Matrix.sub_mulVec, Matrix.smul_mulVec,
    marked_projection, embed, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul]
  simp only [marked, Pi.single_apply, near, far, SimpleGraph.adjMatrix_apply]
  split_ifs <;> simp_all

omit [Fintype V] in

/-- Embedding equal cell coefficients produces the constant vertex vector with that value. -/
theorem uniform_embedding (a : ℂ) : embed G w (fun _ => a) = fun _ => a := by
  have hp := partition G w
  funext v
  have hh := congrFun hp v
  simp only [Pi.add_apply] at hh
  simp only [embed, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  linear_combination a * hh
omit [DecidableEq V] in

/-- For a strongly regular graph with positive vertex count, the parameters satisfy `k * (k-l-1)
= (n-k-1) * m` in natural-number arithmetic. -/
theorem parameter_identity {n k l m : ℕ} (h : G.IsSRGWith n k l m) (hn : 0 < n) :
    k * (k-l-1) = (n-k-1)*m := h.param_eq G hn
end Qatlib.Foundations.GraphModelMath.SrgQuotient
