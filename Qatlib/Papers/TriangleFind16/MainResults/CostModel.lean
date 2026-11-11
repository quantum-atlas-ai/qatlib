/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Extended learning graphs: complexity calculus

Carette--Laurière--Magniez, *Extended Learning Graphs for Triangle Finding*,
fixed arXiv:1609.07786v2 (PDF SHA-256
`a4f815fbd1cd55fb05613cf7ceac1401017378ba627a0f84d914e193876e3ae9`).

This module records the *cost* content of the model of Section 3: the negative and
positive complexities of Definition 3.2, the edge complexities of Definition 3.4, and the
complexity identities of Lemma 3.5 for the expansion of a learning graph with super edges.
The graph-theoretic well-formedness conditions of Definition 3.1 (vertex labelling, DAG,
certificates, flow conservation) are not asserted here: only the numerical quantities that
the paper's later complexity estimates are computed from are formalised.

Main results:

* `FlowData.negCost`, `FlowData.posCost`, `FlowData.cost`: Definition 3.2 on a finite edge set.
* `SuperStage`: a stage of super edges carrying an inner learning graph per edge (Definition 3.4),
  with `SuperStage.expand` the learning graph obtained by expanding every super edge.
* `SuperStage.negCost_expand`, `SuperStage.posCost_expand`, `SuperStage.cost_expand`:
  Lemma 3.5, the expansion has exactly the summed complexities.
-/

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace Qatlib.Papers.TriangleFind16.MainResults

/-- Definition 3.2 data for a finite edge set `ι`: the negative weights `w⁰`, the positive
weights `w¹` and the flow `p` of one positive instance. -/
structure FlowData (ι : Type) [Fintype ι] where
  /-- Negative weight `w⁰(e)` on the current negative instance. -/
  w0 : ι → ℝ
  /-- Positive weight `w¹(e)` on the current positive instance. -/
  w1 : ι → ℝ
  /-- Flow `p_y(e)` of the current positive instance. -/
  p : ι → ℝ

namespace FlowData

variable {ι : Type} [Fintype ι]

/-- Definition 3.2: the negative complexity `C⁰(F, x) = ∑_{e ∈ F} w⁰_x(e)`. -/
def negCost (F : FlowData ι) : ℝ := ∑ e, F.w0 e

/-- Definition 3.2: the positive complexity `C¹(F, y) = ∑_{e ∈ F} p_y(e)² / w¹_y(e)`. -/
def posCost (F : FlowData ι) : ℝ := ∑ e, F.p e ^ 2 / F.w1 e

/-- Definition 3.2: the complexity `C(F) = sqrt (C⁰(F) · C¹(F))`. -/
def cost (F : FlowData ι) : ℝ := Real.sqrt (F.negCost * F.posCost)

/-- Lemma 3.6 scaffolding: multiplying both weights of every edge by `lam` multiplies the
negative complexity by `lam`. -/
def rescale (F : FlowData ι) (lam : ℝ) : FlowData ι where
  w0 e := lam * F.w0 e
  w1 e := lam * F.w1 e
  p := F.p

/-- Rescaling the weights scales the negative complexity linearly. -/
theorem negCost_rescale (F : FlowData ι) (lam : ℝ) :
    (F.rescale lam).negCost = lam * F.negCost := by
  simp only [negCost, rescale, Finset.mul_sum]

/-- Rescaling the weights divides the positive complexity by the same factor. -/
theorem posCost_rescale (F : FlowData ι) (lam : ℝ) (h : lam ≠ 0) :
    (F.rescale lam).posCost = F.posCost / lam := by
  simp only [posCost, rescale]
  have hpt : ∀ x : ι, F.p x ^ 2 / (lam * F.w1 x) = (F.p x ^ 2 / F.w1 x) / lam := by
    intro x
    field_simp
  simp only [hpt, Finset.sum_div]

end FlowData

variable {E : Type} [Fintype E] {ι : E → Type} [∀ e, Fintype (ι e)]

/-- Definition 3.4 data: a stage of super edges. Each super edge `e` carries an inner learning
graph, whose complexities are the edge complexities `c⁰(e) = C⁰(G_e)` and `c¹(e) = C¹(G_e)`;
`p` is the outer flow of one positive instance. -/
structure SuperStage (E : Type) [Fintype E] (ι : E → Type) [∀ e, Fintype (ι e)] where
  /-- The inner learning graph of every super edge. -/
  inner : ∀ e, FlowData (ι e)
  /-- The outer flow `p_y(e)` on the super edges. -/
  p : E → ℝ

namespace SuperStage

variable (S : SuperStage E ι)

/-- Definition 3.4: the negative edge complexity `c⁰(e, x) = C⁰(G_e, x)` of a super edge. -/
def edgeNegCost (e : E) : ℝ := (S.inner e).negCost

/-- Definition 3.4: the positive edge complexity `c¹(e, y) = C¹(G_e, y)` of a super edge. -/
def edgePosCost (e : E) : ℝ := (S.inner e).posCost

/-- Definition 3.2 for a stage of super edges: `C⁰(F, x) = ∑_{e ∈ F} c⁰(e, x)`. -/
def negCost (F : Finset E) : ℝ := ∑ e ∈ F, S.edgeNegCost e

/-- Definition 3.2 for a stage of super edges: `C¹(F, y) = ∑_{e ∈ F} p_y(e)² c¹(e, y)`. -/
def posCost (F : Finset E) : ℝ := ∑ e ∈ F, S.p e ^ 2 * S.edgePosCost e

/-- Definition 3.2: the complexity of a stage is `sqrt (C⁰ · C¹)`. -/
def cost (F : Finset E) : ℝ := Real.sqrt (S.negCost F * S.posCost F)

/-- Lemma 3.6: rescaling the weights inside every super edge by a factor `lam e`. -/
def rescale (S : SuperStage E ι) (lam : E → ℝ) : SuperStage E ι where
  inner e := (S.inner e).rescale (lam e)
  p := S.p

/-- The expansion of a learning graph with super edges (Lemma 3.5): every super edge is replaced
by its inner learning graph, the outer flow being distributed along the inner flow. -/
def expand (S : SuperStage E ι) : FlowData (Σ e, ι e) where
  w0 x := (S.inner x.1).w0 x.2
  w1 x := (S.inner x.1).w1 x.2
  p x := S.p x.1 * (S.inner x.1).p x.2

/-- Lemma 3.5, negative part: `C⁰(exp(F), x) = ∑_{e ∈ F} c⁰(e, x)`. -/
theorem negCost_expand : S.expand.negCost = ∑ e, S.edgeNegCost e := by
  rw [show S.expand.negCost = ∑ x : Sigma ι, (S.inner x.1).w0 x.2 from rfl]
  rw [Fintype.sum_sigma' (f := fun e i => (S.inner e).w0 i)]
  rfl

/-- Lemma 3.5, positive part: `C¹(exp(F), y) = ∑_{e ∈ F} p_y(e)² c¹(e, y)`. -/
theorem posCost_expand (h : ∀ e i, (S.inner e).w1 i ≠ 0) :
    S.expand.posCost = ∑ e, S.p e ^ 2 * S.edgePosCost e := by
  simp only [FlowData.posCost, expand]
  rw [Fintype.sum_sigma' (f := fun e i => (S.p e * (S.inner e).p i) ^ 2 / (S.inner e).w1 i)]
  simp only [edgePosCost, FlowData.posCost]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hw := h e i
  rw [mul_pow]
  field_simp

/-- Lemma 3.5: the expansion has the same complexity as the learning graph with super edges,
`C(exp(F)) = sqrt (C⁰(F) · C¹(F))`, where the two factors are the summed edge complexities. -/
theorem cost_expand (h : ∀ e i, (S.inner e).w1 i ≠ 0) :
    S.expand.cost = Real.sqrt ((∑ e, S.edgeNegCost e) * ∑ e, S.p e ^ 2 * S.edgePosCost e) := by
  simp only [FlowData.cost, negCost_expand, posCost_expand S h]

end SuperStage

end Qatlib.Papers.TriangleFind16.MainResults
