/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.PropTestGraph10.MainResults.Model.QueryTester
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Option
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option backward.isDefEq.respectTransparency false

/-!
# PropTestGraph10 source model: the random graph distribution `P_{M,l}`

Fixed source: arXiv:1012.3174v3. This module transcribes the sampling
procedure `P_{M,l}` of Section 4 (p. 17, used by Lemmas 14 and 16) and Section 3
(p. 7, used by Lemma 3 and Proposition 6):

1. partition the `M` vertices into `l` blocks `V_1,…,V_l`, each of size `M/l`;
2. choose `c` uniformly random perfect matchings on the `M` vertices;
3. choose `N` vertices `v_1,…,v_N` one at a time: at step `a`, pick a block
   uniformly at random among the `l` blocks, then a uniformly random vertex of
   that block that has not been chosen before (the procedure fails if the block
   is exhausted).
4. output the subgraph induced on `v_1,…,v_N`, where the `j`-th neighbour of
   `v_a` is the partner of `v_a` in the `j`-th matching, if that partner was
   chosen, and `*` (`none`) otherwise.

`PMlSample` records the partition, the matchings and the chosen ordered
vertices.  `PMlSample.weight` is the probability of that execution:
`∏_a (1/l) · 1/(m - k_a)`, where `m = M/l` and `k_a` is the number of earlier
chosen vertices in the block of `v_a`.  `PMlSample.toGraph` is the induced
adjacency-list graph.  `pmWeightSum` is the probability that the procedure
succeeds; `pmFailureMass = 1 - pmWeightSum` is the failure probability studied
in Lemma 14 (p. 17).  `pmProb` and `pmAccept` are the success-conditioned
probabilities/expectations used by Lemmas 3 and 16.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

-- The sampling law's events are arbitrary graph predicates; classically every
-- proposition is decidable, and the choice of `Decidable` instance does not
-- change the value of a `filter`/`if` on a proposition.
attribute [local instance] Classical.propDecidable

namespace Qatlib.Papers.PropTestGraph10.MainResults.Model

/-- One successful execution of the paper's sampling procedure `P_{M,l}`
(p. 17): an equipartition of `Fin M` into `l` blocks, `c` perfect matchings,
and the ordered list of `N` chosen vertices. -/
abbrev PMlSample (N M l c : ℕ) : Type :=
  { p : (Fin M → Fin l) × ((Fin c → Fin M → Fin M) × (Fin N → Fin M)) //
      (∀ j : Fin l, (Finset.univ.filter (fun v : Fin M => p.1 v = j)).card = M / l) ∧
      (∀ (j : Fin c) (x : Fin M), p.2.1 j (p.2.1 j x) = x) ∧
      (∀ (j : Fin c) (x : Fin M), p.2.1 j x ≠ x) ∧
      Function.Injective p.2.2 }

/-- The block assignment `V ∋ v ↦` block index of the sample. -/
def PMlSample.blockOf {N M l c : ℕ} (S : PMlSample N M l c) : Fin M → Fin l :=
  S.val.1

/-- The `c` perfect matchings (as fixed-point-free involutions). -/
def PMlSample.matchings {N M l c : ℕ} (S : PMlSample N M l c) : Fin c → Fin M → Fin M :=
  S.val.2.1

/-- The ordered list `v_1,…,v_N` of chosen vertices. -/
def PMlSample.order {N M l c : ℕ} (S : PMlSample N M l c) : Fin N → Fin M :=
  S.val.2.2

/-- Equipartition condition of a sample: every block has `M / l` vertices. -/
theorem PMlSample.block_card {N M l c : ℕ} (S : PMlSample N M l c) (j : Fin l) :
    (Finset.univ.filter (fun v : Fin M => S.blockOf v = j)).card = M / l :=
  S.property.1 j

/-- Each matching is an involution. -/
theorem PMlSample.matching_invol {N M l c : ℕ} (S : PMlSample N M l c)
    (j : Fin c) (x : Fin M) : S.matchings j (S.matchings j x) = x :=
  S.property.2.1 j x

/-- Each matching has no fixed point (so the `c` matchings are perfect
matchings read off as involutions). -/
theorem PMlSample.matching_fixedFree {N M l c : ℕ} (S : PMlSample N M l c)
    (j : Fin c) (x : Fin M) : S.matchings j x ≠ x :=
  S.property.2.2.1 j x

/-- The chosen vertices `v_1,…,v_N` are pairwise distinct. -/
theorem PMlSample.order_injective {N M l c : ℕ} (S : PMlSample N M l c) :
    Function.Injective S.order :=
  S.property.2.2.2

/-- Probability weight of a successful execution: at each of the `N` steps the
procedure picks one of the `l` blocks uniformly and one of the still unchosen
vertices of that block uniformly. -/
def PMlSample.weight {N M l c : ℕ} (S : PMlSample N M l c) : ℝ :=
  ∏ a : Fin N,
    (1 / (l : ℝ)) *
      (1 / (((M / l : ℕ) : ℝ) -
        ((Finset.univ.filter
          (fun b : Fin N => b < a ∧ S.blockOf (S.order b) = S.blockOf (S.order a))).card : ℝ)))

/-- The graph induced by a sample on the chosen vertices: the `j`-th neighbour
of `v_a` is the partner of `v_a` in the `j`-th matching, if the partner is among
the chosen vertices, and `none` (the paper's `*`) otherwise. -/
def PMlSample.toGraph {N M l c : ℕ} (S : PMlSample N M l c) : BoundedDegreeGraph N c where
  adj a j :=
    let w := S.matchings j (S.order a)
    if h : ∃ b : Fin N, S.order b = w then some (Classical.choose h) else none

/-- Total success probability of the sampling procedure: the sum of the weights
of all successful executions. -/
def pmWeightSum (N M l c : ℕ) : ℝ :=
  ∑ S : PMlSample N M l c, S.weight

/-- Failure probability of the sampling procedure (Lemma 14, p. 17): the
probability that some block is chosen after it has been exhausted. -/
def pmFailureMass (N M l c : ℕ) : ℝ :=
  1 - pmWeightSum N M l c

/-- Probability of a graph event under `P_{M,l}`, conditioned on the sampling
procedure succeeding. -/
def pmProb {N c : ℕ} (M l : ℕ) (E : BoundedDegreeGraph N c → Prop) : ℝ :=
  (∑ S : PMlSample N M l c, if E S.toGraph then S.weight else 0) / pmWeightSum N M l c

/-- Acceptance probability of a quantum tester on a graph drawn from `P_{M,l}`,
conditioned on the sampling procedure succeeding. -/
def pmAccept {N c : ℕ} (T : QuantumTester N c) (M l : ℕ) : ℝ :=
  (∑ S : PMlSample N M l c, S.weight * T.acceptProb S.toGraph) / pmWeightSum N M l c

end Qatlib.Papers.PropTestGraph10.MainResults.Model
