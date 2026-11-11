/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GraphCollis12.MainResults.SourceDefinitions

set_option backward.isDefEq.respectTransparency false

/-!
# GraphCollis12 — elementary consequences of the §2 vocabulary

Fixed source: arXiv:1204.1527v1, §2 (pp.3-4) and §4 correctness argument (p.6).

This file records the elementary (fully proved) consequences of the definitions:

* `graphCollision (adjOf G) x = false ↔ IsIndep G (markedSet x)`: the graph
  collision answer is "no" exactly when the marked set is an independent set —
  Definition 1 / the remark following it (p.3).
* monotonicity of `degSum`, `degSum ∅ = 0`;
* `α*(G)` dominates `deg(S)` for every independent `S`, hence in particular the
  degree of any single vertex and the whole degree sum;
* if the collision answer is "no" then `deg(marked) ≤ α*(G)`, which is exactly the
  first line of the case-(c) correctness argument of §4 (p.6, "t ≤ α*(G) ≤ s").
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators
open Qatlib.Concepts.GraphQuery.EdgeQuery

namespace Qatlib.Papers.GraphCollis12.MainResults

variable {n : ℕ}

/-- The shared Frozen predicate, unfolded on a `SimpleGraph`: a collision exists iff
there is an edge with both endpoints marked (Definition 1, p.3). -/
theorem graphCollision_adjOf_eq_true_iff (G : SimpleGraph (Fin n)) (x : Fin n → Bool) :
    graphCollision (adjOf G) x = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphCollision, adjOf]

/-- Definition 1, p.3: the graph-collision answer is "no" iff the marked vertices
form an independent set of `G`. -/
theorem graphCollision_adjOf_eq_false_iff_indep (G : SimpleGraph (Fin n))
    (x : Fin n → Bool) :
    graphCollision (adjOf G) x = false ↔ IsIndep G (markedSet x) := by
  rw [Bool.eq_false_iff, ne_eq, graphCollision_adjOf_eq_true_iff]
  constructor
  · rintro h u hu v hv hadj
    exact h ⟨u, v, hadj, (mem_markedSet x u).1 hu, (mem_markedSet x v).1 hv⟩
  · rintro h ⟨u, v, hadj, hu, hv⟩
    exact h u ((mem_markedSet x u).2 hu) v ((mem_markedSet x v).2 hv) hadj

/-- `degSum` is monotone in the vertex set. -/
theorem degSum_mono (G : SimpleGraph (Fin n)) {S T : Finset (Fin n)} (hST : S ⊆ T) :
    degSum G S ≤ degSum G T := by
  unfold degSum
  exact Finset.sum_le_sum_of_subset_of_nonneg hST (fun _ _ _ => Nat.zero_le _)

/-- The total degree of the empty set is zero. -/
@[simp] theorem degSum_empty (G : SimpleGraph (Fin n)) : degSum G ∅ = 0 := by
  simp [degSum]

/-- The empty set is independent. -/
@[simp] theorem isIndep_empty (G : SimpleGraph (Fin n)) : IsIndep G ∅ := by
  intro u hu
  simp at hu

/-- `deg(S) ≤ α*(G)` for every independent set `S` (definition of `α*`, p.3). -/
theorem degSum_le_alphaStar_of_indep (G : SimpleGraph (Fin n)) {S : Finset (Fin n)}
    (hS : IsIndep G S) : degSum G S ≤ alphaStar G := by
  unfold alphaStar
  exact Finset.le_sup (f := degSum G)
    (Finset.mem_filter.2 ⟨Finset.mem_univ S, hS⟩)

/-- A single vertex is always an independent set in a simple graph, so `α*(G)`
dominates every vertex degree. -/
theorem deg_le_alphaStar (G : SimpleGraph (Fin n)) (v : Fin n) : deg G v ≤ alphaStar G := by
  have hsingle : IsIndep G {v} := by
    intro u hu w hw
    rw [Finset.mem_singleton] at hu hw
    subst hu; subst hw
    exact G.irrefl
  have hdeg : deg G v = degSum G {v} := by simp [degSum]
  rw [hdeg]
  exact degSum_le_alphaStar_of_indep G hsingle

/-- `α*(G)` is at most the sum of all vertex degrees. -/
theorem alphaStar_le_total (G : SimpleGraph (Fin n)) :
    alphaStar G ≤ ∑ v : Fin n, deg G v := by
  unfold alphaStar
  refine Finset.sup_le ?_
  intro S _
  unfold degSum
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
    (fun _ _ _ => Nat.zero_le _)

/-- §4 correctness, case (c) (p.6): if the collision answer is "no" (the marked
vertices are independent) then `deg(marked) = t ≤ α*(G) ≤ s`, so the preprocessing
promise `deg(marked) ≤ s` holds. -/
theorem degSum_marked_le_alphaStar_of_no_collision (G : SimpleGraph (Fin n))
    (x : Fin n → Bool) (h : graphCollision (adjOf G) x = false) :
    degSum G (markedSet x) ≤ alphaStar G :=
  degSum_le_alphaStar_of_indep G
    ((graphCollision_adjOf_eq_false_iff_indep G x).1 h)

/-- §4 correctness, case (c) (p.6): when the answer is "no" and `s ≥ α*(G)`, the
marked set satisfies the `deg(S) ≤ s` promise that step 3 (Lemma 7(ii)) requires. -/
theorem promise_of_no_collision (G : SimpleGraph (Fin n)) (x : Fin n → Bool) {s : ℕ}
    (h : graphCollision (adjOf G) x = false) (hs : alphaStar G ≤ s) :
    PromiseDegLe G s x := by
  unfold PromiseDegLe
  exact le_trans (degSum_marked_le_alphaStar_of_no_collision G x h) hs

/-- The number of possible edges `C(n,2)` is nonnegative (used by the §5 model). -/
theorem numPairs_nonneg (n : ℕ) : 0 ≤ numPairs n := Nat.zero_le _

end Qatlib.Papers.GraphCollis12.MainResults
