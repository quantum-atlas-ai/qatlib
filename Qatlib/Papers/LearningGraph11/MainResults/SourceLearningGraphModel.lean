/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Sym.Sym2

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 source model (learning-graph complexity)

Fixed source: "A learning graph based quantum query algorithm for finding constant-size
subgraphs", arXiv:1109.5135v1 (2011).

This file records the paper's Definitions 1, 3, 4 and 5 (pp. 3-5) and the elementary
complexity API used by Lemmas 3-5 (pp. 5-7). A learning graph is kept as its finite
edge/vertex/flow data: the rooted acyclic structure only matters through the `level`
map and through the stage edge sets, which the lemmas take as explicit arguments.

Boundary: no quantum-mechanical semantics and no algorithm construction live here; the
model only carries the weighted-flow complexity of Definition 4. `p_y` is a unit flow
over the whole graph (`stage_flow`), and a *stage* is an arbitrary finite edge set on
which the same complexity formula is evaluated.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

/-- Source Definition 1 (arXiv:1109.5135v1, p. 3): a learning graph is a rooted,
weighted, directed acyclic graph with a length function and, for every positive input
`y ∈ Y`, a unit flow `p_y` from the root. Finiteness of the vertex/edge/input sets is
carried by `Fintype`; the level map records the distance-from-root grading used for
stages (p. 4). -/
structure LearningGraph (V E Y : Type*) [Fintype V] [Fintype E] [Fintype Y] where
  src : E → V
  tgt : E → V
  level : V → ℕ
  weight : E → ℝ
  len : E → ℕ
  flow : Y → E → ℝ
  weight_pos : ∀ e, 0 < weight e
  flow_nonneg : ∀ y e, 0 ≤ flow y e
  stage_flow : ∀ y, ∑ e, flow y e = 1

section Defs

variable {V E Y : Type*} [Fintype V] [Fintype E] [Fintype Y] [Nonempty Y]

/-- The flow mass `p_y(S)` of a finite edge set `S` (p. 5, `p_y(E) = ∑_{e ∈ E} p_y(e)`). -/
def edgeSum (G : LearningGraph V E Y) (S : Finset E) (y : Y) : ℝ :=
  ∑ e ∈ S, G.flow y e

/-- Source Definition 4 (p. 4): negative complexity `C_0(E) = ∑_{e∈E} ℓ(e) w(e)`. -/
def negComplexityW (len : E → ℕ) (w : E → ℝ) (S : Finset E) : ℝ :=
  ∑ e ∈ S, (len e : ℝ) * w e

/-- Source Definition 4 (p. 4): positive complexity of `E` under a single flow,
`C_{1,y}(E) = ∑_{e∈E} (ℓ(e)/w(e)) (p_y(e)/p_y(E))²`, and `0` when `p_y(E) = 0`. -/
def posComplexityAtW (len : E → ℕ) (w : E → ℝ) (p : E → ℝ) (S : Finset E) : ℝ :=
  if ∑ e ∈ S, p e = 0 then 0
  else ∑ e ∈ S, (len e : ℝ) / w e * (p e / (∑ e ∈ S, p e)) ^ 2

/-- Source Definition 4 (p. 4): positive complexity `C_1(E) = max_{y∈Y} C_{1,y}(E)`. -/
def posComplexityW (len : E → ℕ) (w : E → ℝ) (p : Y → E → ℝ) (S : Finset E) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun y => posComplexityAtW len w (p y) S)

/-- Source Definition 4 (p. 4): complexity `C(E) = sqrt(C_0(E) C_1(E))`. -/
def complexityW (len : E → ℕ) (w : E → ℝ) (p : Y → E → ℝ) (S : Finset E) : ℝ :=
  Real.sqrt (negComplexityW len w S * posComplexityW len w p S)

/-- Complexity of a stage with respect to the graph's own weight and flow. -/
def complexity (G : LearningGraph V E Y) (S : Finset E) : ℝ :=
  complexityW G.len G.weight G.flow S

end Defs

section Basics

variable {V E Y ι : Type*} [Fintype V] [Fintype E] [Fintype Y] [Fintype ι]
  [DecidableEq ι] [Nonempty Y]

/-- The `i`-th piece of a partition of the edge set, `E_i = {e : part e = i}`. -/
def piece (part : E → ι) (i : ι) : Finset E :=
  Finset.univ.filter (fun e => part e = i)

/-- Source Definition 5 (p. 5): the flows `{p_y}` are consistent with `{E_i}` when
`p_y(E_i)` is independent of `y` for every `i`. -/
def ConsistentWith (G : LearningGraph V E Y) (part : E → ι) : Prop :=
  ∀ y y' i, edgeSum G (piece part i) y = edgeSum G (piece part i) y'

/-- The `negComplexityW_nonneg` result for the LearningGraph11 paper model. -/
theorem negComplexityW_nonneg (len : E → ℕ) {w : E → ℝ} (hw : ∀ e, 0 ≤ w e)
    (S : Finset E) : 0 ≤ negComplexityW len w S := by
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (Nat.cast_nonneg _) (hw e)

/-- The `posComplexityAtW_nonneg` result for the LearningGraph11 paper model. -/
theorem posComplexityAtW_nonneg (len : E → ℕ) {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (p : E → ℝ) (S : Finset E) : 0 ≤ posComplexityAtW len w p S := by
  unfold posComplexityAtW
  split_ifs
  · exact le_rfl
  · apply Finset.sum_nonneg
    intro e _
    have hw' : 0 < w e := hw e
    have h1 : 0 ≤ (len e : ℝ) / w e := div_nonneg (Nat.cast_nonneg _) hw'.le
    exact mul_nonneg h1 (sq_nonneg _)

/-- The `posComplexityW_nonneg` result for the LearningGraph11 paper model. -/
theorem posComplexityW_nonneg (len : E → ℕ) {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (p : Y → E → ℝ) (S : Finset E) : 0 ≤ posComplexityW len w p S := by
  obtain ⟨y0⟩ := (inferInstance : Nonempty Y)
  unfold posComplexityW
  have h1 : 0 ≤ posComplexityAtW len w (p y0) S := posComplexityAtW_nonneg len hw (p y0) S
  have h2 : posComplexityAtW len w (p y0) S ≤
      Finset.univ.sup' Finset.univ_nonempty (fun y => posComplexityAtW len w (p y) S) :=
    Finset.le_sup' (fun y => posComplexityAtW len w (p y) S) (Finset.mem_univ y0)
  exact h1.trans h2

/-- The `complexityW_nonneg` result for the LearningGraph11 paper model. -/
theorem complexityW_nonneg (len : E → ℕ) {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (p : Y → E → ℝ) (S : Finset E) : 0 ≤ complexityW len w p S :=
  Real.sqrt_nonneg _

/-- The `negComplexityW_nonneg_of_pos` result for the LearningGraph11 paper model. -/
theorem negComplexityW_nonneg_of_pos (len : E → ℕ) {w : E → ℝ} (hw : ∀ e, 0 < w e)
    (S : Finset E) : 0 ≤ negComplexityW len w S :=
  negComplexityW_nonneg len (fun e => (hw e).le) S

/-- Regrouping a sum over the whole edge set along the partition `part`
(Definition 5's partition bookkeeping). -/
theorem sum_piece (part : E → ι) (f : E → ℝ) :
    ∑ i, ∑ e ∈ piece part i, f e = ∑ e, f e := by
  simpa [piece] using (Finset.sum_fiberwise (Finset.univ : Finset E) part f)

/-- `p_y` of the whole edge set is the sum of the piece masses. -/
theorem edgeSum_univ_eq_sum_piece (G : LearningGraph V E Y) (part : E → ι) (y : Y) :
    ∑ i, edgeSum G (piece part i) y = edgeSum G (Finset.univ : Finset E) y := by
  simpa [edgeSum] using sum_piece part (fun e => G.flow y e)

end Basics

end Qatlib.Papers.LearningGraph11.MainResults
