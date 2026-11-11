/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# `MainResults/LearningGraphStage` — learning-graph stage complexity (source Lemma 3)

Lee--Magniez--Santha, *Improved Quantum Query Algorithms for Triangle Finding and
Associativity Testing*, fixed arXiv:1210.1014v1 (21 pages of the `arxiv` PDF).

Source locations:

* Definition 5, page 4: the negative complexity `C0(E) = sum_e len(e) w(e)`, the
  positive complexity `C1,y(E) = sum_e (len(e)/w(e)) p_y(e)^2`, and the stage
  complexity `C(E) = sqrt (C0(E) * C1(E))`.
* Lemma 3, page 5: a stage between consecutive levels, uniform out-degree `d`,
  unit L-edge weights, L-edge lengths at most `L`, incoming flow uniform over
  `W ⊆ V` and directed from every `v ∈ W` to `g` of its `d` successors, has stage
  complexity at most `L * sqrt ((d |V|) / (g |W|))`.

The source proves Lemma 3 by two counts: the total weight of the stage is
`d |V|`, hence `C0(E) ≤ L d |V|`; and each of the `g |W|` flow-carrying L-edges
carries flow `(g |W|)^{-1}`, hence `C1 ≤ L / (g |W|)`; taking the geometric mean
gives the stated bound.

What is *not* in this module: the reweighting step of source Lemma 2, the
partition into stages, and the appeal to Belovs' theorem `Q(f) = O(LG(f))`
(source Theorem 1), which are separate statements.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.TriangleFind12.MainResults

/-- Source Definition 5 (negative complexity of a set `E` of stage L-edges):
`C0(E) = sum_{e in E} len(e) * w(e)`. -/
def negativeComplexity {E : Type*} [DecidableEq E] (len : E → ℕ) (weight : E → ℝ)
    (stage : Finset E) : ℝ :=
  ∑ e ∈ stage, (len e : ℝ) * weight e

/-- Source Definition 5 (positive complexity of a set `E` of stage L-edges under
the flow `p`): `C1(E) = sum_{e in E} (len(e)/w(e)) * p(e)^2`. -/
def positiveComplexity {E : Type*} [DecidableEq E] (len : E → ℕ) (weight : E → ℝ)
    (flow : E → ℝ) (stage : Finset E) : ℝ :=
  ∑ e ∈ stage, ((len e : ℝ) / weight e) * flow e ^ 2

/-- Source Definition 5 (complexity of a stage): the geometric mean
`C(E) = sqrt (C0(E) * C1(E))` of the negative and positive complexity. -/
def stageComplexity {E : Type*} [DecidableEq E] (len : E → ℕ) (weight : E → ℝ)
    (flow : E → ℝ) (stage : Finset E) : ℝ :=
  Real.sqrt (negativeComplexity len weight stage * positiveComplexity len weight flow stage)

/-- The negative complexity is nonnegative when every L-edge of the stage has
unit weight. -/
theorem negativeComplexity_nonneg {E : Type*} [DecidableEq E] (len : E → ℕ)
    (weight : E → ℝ) (stage : Finset E) (hweight : ∀ e ∈ stage, weight e = 1) :
    0 ≤ negativeComplexity len weight stage := by
  refine Finset.sum_nonneg ?_
  intro e he
  rw [hweight e he, mul_one]
  positivity

/-- The positive complexity is nonnegative when every L-edge of the stage has
unit weight. -/
theorem positiveComplexity_nonneg {E : Type*} [DecidableEq E] (len : E → ℕ)
    (weight : E → ℝ) (flow : E → ℝ) (stage : Finset E)
    (hweight : ∀ e ∈ stage, weight e = 1) :
    0 ≤ positiveComplexity len weight flow stage := by
  refine Finset.sum_nonneg ?_
  intro e he
  rw [hweight e he, div_one]
  positivity

/-- Source Definition 5 arithmetic: a stage with unit L-edge weights, L-edge
lengths at most `L`, `M` L-edges in total, and `G` flow-carrying L-edges each
carrying flow `G^{-1}`, has stage complexity at most `L * sqrt (M / G)`.

This is Lemma 3 stripped of the learning-graph bookkeeping: `M = d |V|` and
`G = g |W|` in the source notation. -/
theorem stageComplexity_le_of_uniform_flow {E : Type*} [DecidableEq E]
    (len : E → ℕ) (weight flow : E → ℝ) (stage carried : Finset E)
    (M G L : ℕ) (hM : stage.card = M) (hcarried : carried ⊆ stage)
    (hG : carried.card = G) (hweight : ∀ e ∈ stage, weight e = 1)
    (hlen : ∀ e ∈ stage, len e ≤ L)
    (hflow : ∀ e ∈ stage, flow e = if e ∈ carried then 1 / (G : ℝ) else 0) :
    stageComplexity len weight flow stage ≤ (L : ℝ) * Real.sqrt ((M : ℝ) / (G : ℝ)) := by
  classical
  have hC0_nonneg : 0 ≤ negativeComplexity len weight stage :=
    negativeComplexity_nonneg len weight stage hweight
  have hC1_nonneg : 0 ≤ positiveComplexity len weight flow stage :=
    positiveComplexity_nonneg len weight flow stage hweight
  -- `C0 ≤ L * M`
  have hC0 : negativeComplexity len weight stage ≤ (L : ℝ) * M := by
    have hrewrite : negativeComplexity len weight stage = ∑ e ∈ stage, (len e : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro e he
      rw [hweight e he, mul_one]
    rw [hrewrite]
    calc ∑ e ∈ stage, (len e : ℝ) ≤ ∑ _e ∈ stage, (L : ℝ) := by
          refine Finset.sum_le_sum ?_
          intro e he
          exact_mod_cast hlen e he
      _ = (stage.card : ℝ) * L := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = (L : ℝ) * M := by
          rw [hM]
          ring
  -- `C1 ≤ L / G`
  have hC1 : positiveComplexity len weight flow stage ≤ (L : ℝ) / (G : ℝ) := by
    have hterm : ∀ e ∈ stage, (len e : ℝ) / weight e * flow e ^ 2
        = if e ∈ carried then (len e : ℝ) * (1 / (G : ℝ)) ^ 2 else 0 := by
      intro e he
      rw [hweight e he, div_one, hflow e he]
      by_cases h : e ∈ carried <;> simp [h]
    rw [positiveComplexity]
    calc ∑ e ∈ stage, ((len e : ℝ) / weight e * flow e ^ 2)
        = ∑ e ∈ stage, (if e ∈ carried then (len e : ℝ) * (1 / (G : ℝ)) ^ 2 else 0) :=
          Finset.sum_congr rfl hterm
      _ = ∑ e ∈ carried, (len e : ℝ) * (1 / (G : ℝ)) ^ 2 := by
          rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hcarried]
      _ ≤ ∑ _e ∈ carried, (L : ℝ) * (1 / (G : ℝ)) ^ 2 := by
          refine Finset.sum_le_sum ?_
          intro e he
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen e (hcarried he))
            (sq_nonneg _)
      _ = (G : ℝ) * ((L : ℝ) * (1 / (G : ℝ)) ^ 2) := by
          rw [Finset.sum_const, nsmul_eq_mul, hG]
      _ = (L : ℝ) / (G : ℝ) := by
          rcases Nat.eq_zero_or_pos G with hG0 | hGpos
          · simp [hG0]
          · have hGne : (G : ℝ) ≠ 0 := by
              exact_mod_cast Nat.pos_iff_ne_zero.mp hGpos
            field_simp
  -- combine
  have hprod : negativeComplexity len weight stage * positiveComplexity len weight flow stage
      ≤ ((L : ℝ) * M) * ((L : ℝ) / (G : ℝ)) :=
    mul_le_mul hC0 hC1 hC1_nonneg (by positivity)
  rcases Nat.eq_zero_or_pos G with hG0 | hGpos
  · -- `G = 0`: the carried set is empty, so the flow vanishes and so does `C1`
    have hC1zero : positiveComplexity len weight flow stage = 0 :=
      le_antisymm (by simpa [hG0] using hC1) hC1_nonneg
    rw [stageComplexity, hC1zero, mul_zero, Real.sqrt_zero, hG0, Nat.cast_zero, div_zero,
      Real.sqrt_zero]
    exact mul_nonneg (by positivity) le_rfl
  · have hGne : (G : ℝ) ≠ 0 := by
      exact_mod_cast Nat.pos_iff_ne_zero.mp hGpos
    have hstep : ((L : ℝ) * M) * ((L : ℝ) / (G : ℝ))
        = (L : ℝ) * (L : ℝ) * ((M : ℝ) / (G : ℝ)) := by
      field_simp
    have hsqrt : Real.sqrt ((L : ℝ) * (L : ℝ) * ((M : ℝ) / (G : ℝ)))
        = (L : ℝ) * Real.sqrt ((M : ℝ) / (G : ℝ)) := by
      have hnonneg : (0 : ℝ) ≤ (L : ℝ) * (L : ℝ) := by positivity
      rw [Real.sqrt_mul hnonneg, Real.sqrt_mul_self (by positivity)]
    rw [stageComplexity]
    calc Real.sqrt (negativeComplexity len weight stage * positiveComplexity len weight flow stage)
        ≤ Real.sqrt (((L : ℝ) * M) * ((L : ℝ) / (G : ℝ))) := Real.sqrt_le_sqrt hprod
      _ = (L : ℝ) * Real.sqrt ((M : ℝ) / (G : ℝ)) := by rw [hstep, hsqrt]

/-- **Source Lemma 3** (page 5). Consider a stage of a learning graph between
consecutive levels. `level` is the set `V` of L-vertices at the beginning of the
stage; every `v ∈ V` has outgoing degree `d` via `out`, all outgoing L-edges
have weight one and length at most `L`; the incoming flow is uniform over the
L-vertices `W ⊆ V` and is directed from each `v ∈ W` to the `g` successors in
`succ v ⊆ out v`, each of those L-edges carrying flow `(g |W|)^{-1}`. Then the
complexity of this stage is at most `L * sqrt ((d |V|) / (g |W|))`.

The flow hypothesis is stated on the whole stage as in the paper's proof: the
flow-carrying L-edges are exactly `W.biUnion succ` and carry the constant flow
`(g |W|)^{-1}`. -/
theorem stageComplexity_le {V E : Type*} [DecidableEq V] [DecidableEq E]
    (len : E → ℕ) (weight flow : E → ℝ) (stage : Finset E)
    (level : Finset V) (out succ : V → Finset E) (W : Finset V) (d g L : ℕ)
    (hstage : stage = level.biUnion out)
    (hdisj : (level : Set V).PairwiseDisjoint out)
    (hdegree : ∀ v ∈ level, (out v).card = d)
    (hweight : ∀ e ∈ stage, weight e = 1)
    (hlen : ∀ e ∈ stage, len e ≤ L)
    (hW : W ⊆ level)
    (hsuccsub : ∀ v ∈ W, succ v ⊆ out v)
    (hsucccard : ∀ v ∈ W, (succ v).card = g)
    (hflow : ∀ e ∈ stage,
      flow e = if e ∈ W.biUnion succ then 1 / (((g * W.card : ℕ)) : ℝ) else 0) :
    stageComplexity len weight flow stage
      ≤ (L : ℝ) * Real.sqrt (((d * level.card : ℕ) : ℝ) / (((g * W.card : ℕ)) : ℝ)) := by
  classical
  have hWdisj : (W : Set V).PairwiseDisjoint succ := by
    intro v hv v' hv' hne
    exact (hdisj (hW hv) (hW hv') hne).mono (hsuccsub v hv) (hsuccsub v' hv')
  have hcard_stage : stage.card = d * level.card := by
    have hsum : ∑ v ∈ level, (out v).card = ∑ _v ∈ level, d :=
      Finset.sum_congr rfl hdegree
    rw [hstage, Finset.card_biUnion hdisj, hsum, Finset.sum_const_nat (fun _ _ => rfl),
      Nat.mul_comm]
  have hcard_carried : (W.biUnion succ).card = g * W.card := by
    have hsum : ∑ v ∈ W, (succ v).card = ∑ _v ∈ W, g :=
      Finset.sum_congr rfl hsucccard
    rw [Finset.card_biUnion hWdisj, hsum, Finset.sum_const_nat (fun _ _ => rfl), Nat.mul_comm]
  have hcarried_sub : W.biUnion succ ⊆ stage := by
    intro e he
    rw [Finset.mem_biUnion] at he
    obtain ⟨v, hv, hev⟩ := he
    rw [hstage, Finset.mem_biUnion]
    exact ⟨v, hW hv, hsuccsub v hv hev⟩
  exact stageComplexity_le_of_uniform_flow len weight flow stage (W.biUnion succ)
    (d * level.card) (g * W.card) L hcard_stage hcarried_sub hcard_carried hweight hlen hflow

end Qatlib.Papers.TriangleFind12.MainResults
