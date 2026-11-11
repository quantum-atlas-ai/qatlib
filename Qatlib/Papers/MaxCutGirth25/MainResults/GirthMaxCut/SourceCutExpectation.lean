/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Combinatorics.SimpleGraph.Girth
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

set_option backward.isDefEq.respectTransparency false

/-!
# MaxCut of high-girth 3-regular graphs: the expectation principle

Fixed version: arXiv:2503.12789v2 (2026-01-27), Farhi--Gutmann--Ranard--Villalonga,
"Lower bounding the MaxCut of high girth 3-regular graphs using the QAOA".

This module formalizes the finite combinatorial heart of the paper's leading
comparison Eq. (9), p. 4:

* a cut of a finite graph is given by a vertex subset `S`, and `cutNum G S` counts
  the edges crossing `S` (the paper's cost `C(b)`, Eq. (4));
* `maxCutNum G` is the largest crossing count over all subsets;
* for **any** probability distribution on cuts, the expected cut size is at most
  the maximum cut size.  The QAOA only supplies such a distribution (the Born
  law of its measured state), so this single order-theoretic fact converts the
  quantum expectation `F_p(γ,β) = |E(G)| c_edge(γ,β)` of Eq. (7) into the
  lower bound `M_g ≥ c_edge(γ,β)` of Eq. (9)/(11), without asserting anything
  about the quantum computation itself.

Everything here is graph theory over `SimpleGraph`; no numerical QAOA input is
used, and no axiom beyond the standard three is introduced.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset

namespace Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of edges of a finite graph, the paper's `|E(G)|`. -/
def edgeCount (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ := G.edgeFinset.card

/-- The crossing predicate for an edge `e` and a cut `S`: neither endpoint set is
contained in `S` nor in its complement, which for a genuine edge means exactly one
endpoint lies in `S`.  Source Eq. (4), p. 3. -/
def isCutEdge (S : Finset V) (e : Sym2 V) : Prop :=
  ¬ e.toFinset ⊆ S ∧ ¬ e.toFinset ⊆ Sᶜ

instance instDecidableIsCutEdge (S : Finset V) : DecidablePred (isCutEdge S) := by
  intro e
  unfold isCutEdge
  infer_instance

/-- The edges crossing the cut `S`, i.e. the MaxCut cost `C(b)` of the bit string
`b` that labels `S`.  Source Eq. (4), p. 3. -/
def cutEdges (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset.filter (isCutEdge S)

/-- The cut size: the number of edges with one endpoint in `S` and one outside.
This is the paper's `C(b)` in Eq. (4) and `C(b)` in Eq. (17). -/
def cutNum (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : ℕ :=
  (cutEdges G S).card

/-- The maximum cut size over all vertex bipartitions, `MaxCut(G)`. -/
def maxCutNum (G : SimpleGraph V) [DecidableRel G.Adj] : ℕ :=
  Finset.univ.sup (fun S : Finset V => cutNum G S)

/-- The cut fraction `MaxCut(G)/|E(G)|`, the quantity whose infimum is `M_g`
in Eq. (1), p. 2. -/
noncomputable def maxCutFraction (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  (maxCutNum G : ℝ) / (edgeCount G : ℝ)

/-- Every cut has at most the maximum cut size. -/
theorem cutNum_le_maxCutNum (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) :
    cutNum G S ≤ maxCutNum G :=
  Finset.le_sup (f := fun S : Finset V => cutNum G S) (Finset.mem_univ S)

/-- An every-cut value: a real number is at most the maximum cut size when it is
at most the crossing count of every cut. -/
theorem le_maxCutNum_of_forall (G : SimpleGraph V) [DecidableRel G.Adj] {c : ℝ}
    (h : ∀ S : Finset V, c ≤ (cutNum G S : ℝ)) : c ≤ (maxCutNum G : ℝ) :=
  (h ∅).trans (by exact_mod_cast cutNum_le_maxCutNum G ∅)

/-- A probability mass function on the finitely many cuts of a finite graph:
nonnegative weights summing to one.  This is the discrete Born law of a measured
QAOA state. -/
def IsProbCutLaw (μ : Finset V → ℝ) : Prop :=
  (∀ S, 0 ≤ μ S) ∧ ∑ S, μ S = 1

/-- The expected cut size of a probability law over cuts. -/
noncomputable def expectedCutNum (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : Finset V → ℝ) : ℝ :=
  ∑ S, μ S * (cutNum G S : ℝ)

/-- The expected cut fraction `E[C]/|E(G)|` of a probability law over cuts. -/
noncomputable def expectedCutFraction (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : Finset V → ℝ) : ℝ :=
  ∑ S, μ S * ((cutNum G S : ℝ) / (edgeCount G : ℝ))

/-- **Paper Eq. (9), expectation form.** For any probability law on cuts, the
expected cut size is at most the maximum cut size.  In the paper the law is the
measured distribution of the QAOA state and the expectation is `F_p(γ,β)`; the
only invocation of that physics is the existence of this law. -/
theorem expectedCutNum_le_maxCutNum (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : Finset V → ℝ) (hμ : IsProbCutLaw μ) :
    expectedCutNum G μ ≤ (maxCutNum G : ℝ) := by
  obtain ⟨h0, h1⟩ := hμ
  unfold expectedCutNum
  calc
    ∑ S, μ S * (cutNum G S : ℝ)
        ≤ ∑ S, μ S * (maxCutNum G : ℝ) := by
          refine Finset.sum_le_sum fun S _ => ?_
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast cutNum_le_maxCutNum G S) (h0 S)
    _ = (∑ S, μ S) * (maxCutNum G : ℝ) := by rw [Finset.sum_mul]
    _ = (maxCutNum G : ℝ) := by rw [h1, one_mul]

/-- **Paper Eq. (9), fraction form.** With at least one edge, the expected cut
fraction of any probability law is at most the maximum cut fraction. -/
theorem expectedCutFraction_le_maxCutFraction (G : SimpleGraph V) [DecidableRel G.Adj]
    (μ : Finset V → ℝ) (hμ : IsProbCutLaw μ) (hE : 0 < edgeCount G) :
    expectedCutFraction G μ ≤ maxCutFraction G := by
  have hEpos : (0 : ℝ) < (edgeCount G : ℝ) := by exact_mod_cast hE
  have h := expectedCutNum_le_maxCutNum G μ hμ
  have hsum : expectedCutFraction G μ =
      expectedCutNum G μ / (edgeCount G : ℝ) := by
    unfold expectedCutFraction expectedCutNum
    rw [div_eq_mul_inv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [div_eq_mul_inv, mul_assoc]
  rw [hsum]
  unfold maxCutFraction
  exact div_le_div_of_nonneg_right h hEpos.le

/-- A graph *has expected cut fraction* `c` when some probability law on its cuts
has expected cut fraction `c`.  For the QAOA at optimal parameters the paper's
Eq. (7), `F_p(γ,β) = |E(G)| c_edge(γ,β)`, says exactly that the measured cut law
has this expected fraction `c = c_edge(γ,β)`. -/
def HasExpectedCutFraction (G : SimpleGraph V) [DecidableRel G.Adj] (c : ℝ) : Prop :=
  ∃ μ : Finset V → ℝ, IsProbCutLaw μ ∧ expectedCutFraction G μ = c

/-- **Paper Eq. (9), graph form.** If a graph admits a cut law with expected cut
fraction `c`, then its maximum cut fraction is at least `c`. -/
theorem expectedCutFraction_le_maxCut_of_has (G : SimpleGraph V) [DecidableRel G.Adj]
    {c : ℝ} (hE : 0 < edgeCount G) (h : HasExpectedCutFraction G c) :
    c ≤ maxCutFraction G := by
  obtain ⟨μ, hμ, hc⟩ := h
  rw [← hc]
  exact expectedCutFraction_le_maxCutFraction G μ hμ hE

/-- Three-regular graphs have `2 |E| = 3 |V|` (the handshaking identity of
`SimpleGraph.sum_degrees_eq_twice_card_edges`, p. 9/11 of the paper). -/
theorem two_mul_edgeCount_eq_three_mul_card
    (G : SimpleGraph V) [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree 3) :
    2 * edgeCount G = 3 * Fintype.card V := by
  have hsum := SimpleGraph.sum_degrees_eq_twice_card_edges (G := G)
  have hdeg : ∑ v : V, G.degree v = 3 * Fintype.card V := by
    simp_rw [hreg.degree_eq]
    simp [Finset.sum_const, Nat.mul_comm]
  rw [hdeg] at hsum
  unfold edgeCount
  exact hsum.symm

end Qatlib.Papers.MaxCutGirth25.MainResults.GirthMaxCut
