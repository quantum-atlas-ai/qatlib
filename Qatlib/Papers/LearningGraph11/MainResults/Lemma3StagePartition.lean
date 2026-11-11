/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LearningGraph11.MainResults.SourceLearningGraphModel

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 Lemma 3: partition of a stage

Fixed source: arXiv:1109.5135v1, Lemma 3 and its proof (p. 5).

If a stage `E` is split into pieces `E_i` on which the flow mass `p_y(E_i) = α_i` is
independent of the input `y` (Definition 5 consistency), then the reweighting
`w'(e) = α_{i(e)} C_1(E_i) w(e)` makes the stage complexity at most `max_i C(E_i)`.

The paper's proof deletes pieces with `α_i = 0` ("these edges can be deleted from the
graph without affecting anything"); the statement below is the reduced stage on which
every `α_i > 0`, and also assumes the pieces have positive positive-complexity, which
holds for every nonempty flow-carrying piece. The three displayed conclusions are the
paper's three displayed estimates: `C_1^{w'}(E) ≤ 1`, `C_0^{w'}(E) ≤ max_i C(E_i)²`,
and `C^{w'}(E) ≤ max_i C(E_i)`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

variable {V E Y ι : Type*} [Fintype V] [Fintype E] [Fintype Y] [Fintype ι]
  [DecidableEq ι] [Nonempty ι] [Nonempty Y]

/-- The reweighting of Lemma 3: `w'(e) = α_{i(e)} C_1(E_i) w(e)`. -/
def lemma3Reweight (G : LearningGraph V E Y) (part : E → ι) (α : ι → ℝ) : E → ℝ :=
  fun e => α (part e) * posComplexityW G.len G.weight G.flow (piece part (part e)) *
    G.weight e

/-- Fixed source arXiv:1109.5135v1, Lemma 3 (p. 5): consistency of the flows with a
partition `{E_i}` of the stage edge set gives a reweighting whose stage complexity is at
most `max_i C(E_i)`. -/
theorem source_lemma_3
    (G : LearningGraph V E Y)
    (part : E → ι) (α : ι → ℝ)
    (hα_pos : ∀ i, 0 < α i)
    (hconsistent : ∀ y i, edgeSum G (piece part i) y = α i)
    (hC1_pos : ∀ i, 0 < posComplexityW G.len G.weight G.flow (piece part i)) :
    (∀ y, posComplexityAtW G.len (lemma3Reweight G part α) (G.flow y)
        (Finset.univ : Finset E) ≤ 1) ∧
    (negComplexityW G.len (lemma3Reweight G part α) (Finset.univ : Finset E) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => negComplexityW G.len G.weight (piece part i) *
          posComplexityW G.len G.weight G.flow (piece part i))) ∧
    (complexityW G.len (lemma3Reweight G part α) G.flow (Finset.univ : Finset E) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => complexityW G.len G.weight G.flow (piece part i))) := by
  classical
  obtain ⟨y0⟩ := (inferInstance : Nonempty Y)
  set w' : E → ℝ := lemma3Reweight G part α with hw'
  set C0 : ι → ℝ := fun i => negComplexityW G.len G.weight (piece part i) with hC0
  set C1 : ι → ℝ := fun i => posComplexityW G.len G.weight G.flow (piece part i) with hC1
  have hC0_nonneg : ∀ i, 0 ≤ C0 i := fun i =>
    negComplexityW_nonneg_of_pos G.len G.weight_pos (piece part i)
  have hC1_pos' : ∀ i, 0 < C1 i := hC1_pos
  have hC1_nonneg : ∀ i, 0 ≤ C1 i := fun i => (hC1_pos' i).le
  have hw'_pos : ∀ e, 0 < w' e := by
    intro e
    have h1 : 0 < α (part e) * C1 (part e) := mul_pos (hα_pos _) (hC1_pos' _)
    exact mul_pos h1 (G.weight_pos e)
  have hw'_apply : ∀ e, w' e = α (part e) * C1 (part e) * G.weight e := by
    intro e
    simp only [hw', lemma3Reweight, C1]
  -- The pieces carry total mass one.
  have hsumα : ∑ i, α i = 1 := by
    have hstage : edgeSum G (Finset.univ : Finset E) y0 = 1 := by
      simpa [edgeSum] using G.stage_flow y0
    calc ∑ i, α i = ∑ i, edgeSum G (piece part i) y0 :=
          Finset.sum_congr rfl (fun i _ => (hconsistent y0 i).symm)
      _ = 1 := by rw [edgeSum_univ_eq_sum_piece]; exact hstage
  -- Per-piece identity behind the positive-complexity estimate.
  have hpiece_eq : ∀ (y : Y) (i : ι),
      (∑ e ∈ piece part i, (G.len e : ℝ) / w' e * (G.flow y e) ^ 2)
        = (α i / C1 i) * posComplexityAtW G.len G.weight (G.flow y) (piece part i) := by
    intro y i
    have hden : (∑ e ∈ piece part i, G.flow y e) = α i := hconsistent y i
    rw [posComplexityAtW, if_neg (by rw [hden]; exact ne_of_gt (hα_pos i)), hden,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro e he
    have hpart : part e = i := by
      simpa [piece] using (Finset.mem_filter.mp he).2
    have hαne : α i ≠ 0 := ne_of_gt (hα_pos i)
    have hC1ne : C1 i ≠ 0 := ne_of_gt (hC1_pos' i)
    have hwne : G.weight e ≠ 0 := ne_of_gt (G.weight_pos e)
    rw [hw'_apply e, hpart]
    field_simp
  -- Positive complexity of the reweighted stage is at most one.
  have hpos_bound : ∀ y, posComplexityAtW G.len w' (G.flow y) (Finset.univ : Finset E) ≤ 1 := by
    intro y
    have hstage : (∑ e ∈ (Finset.univ : Finset E), G.flow y e) = 1 := by
      simpa [edgeSum] using G.stage_flow y
    rw [posComplexityAtW, if_neg (by rw [hstage]; norm_num)]
    simp only [hstage, div_one]
    have hsplit : (∑ e ∈ (Finset.univ : Finset E),
          (G.len e : ℝ) / w' e * (G.flow y e) ^ 2)
        = ∑ i, ∑ e ∈ piece part i, (G.len e : ℝ) / w' e * (G.flow y e) ^ 2 := by
      rw [← sum_piece part (fun e => (G.len e : ℝ) / w' e * (G.flow y e) ^ 2)]
    rw [hsplit]
    simp_rw [hpiece_eq y]
    calc ∑ i, (α i / C1 i) * posComplexityAtW G.len G.weight (G.flow y) (piece part i)
        ≤ ∑ i, (α i / C1 i) * C1 i := by
          apply Finset.sum_le_sum
          intro i _
          have hle : posComplexityAtW G.len G.weight (G.flow y) (piece part i) ≤ C1 i :=
            Finset.le_sup'
              (fun y' => posComplexityAtW G.len G.weight (G.flow y') (piece part i))
              (Finset.mem_univ y)
          exact mul_le_mul_of_nonneg_left hle (div_nonneg (hα_pos i).le (hC1_nonneg i))
      _ = ∑ i, α i := by
          apply Finset.sum_congr rfl
          intro i _
          field_simp [ne_of_gt (hC1_pos' i)]
      _ = 1 := hsumα
  -- Negative complexity of the reweighted stage.
  have hneg_bound : negComplexityW G.len w' (Finset.univ : Finset E) ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i => C0 i * C1 i) := by
    have hsplit : negComplexityW G.len w' (Finset.univ : Finset E)
        = ∑ i, α i * (C0 i * C1 i) := by
      rw [negComplexityW]
      rw [← sum_piece part (fun e => (G.len e : ℝ) * w' e)]
      apply Finset.sum_congr rfl
      intro i _
      have hterm : ∀ e ∈ piece part i,
          (G.len e : ℝ) * w' e = (α i * C1 i) * ((G.len e : ℝ) * G.weight e) := by
        intro e he
        have hpart : part e = i := by
          simpa [piece] using (Finset.mem_filter.mp he).2
        rw [hw'_apply e, hpart]
        ring
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
      have hC0i : C0 i = ∑ e ∈ piece part i, (G.len e : ℝ) * G.weight e := rfl
      rw [hC0i]
      ring
    rw [hsplit]
    calc ∑ i, α i * (C0 i * C1 i)
        ≤ ∑ i, α i * Finset.univ.sup' Finset.univ_nonempty (fun j => C0 j * C1 j) := by
          apply Finset.sum_le_sum
          intro i _
          exact mul_le_mul_of_nonneg_left
            (Finset.le_sup' (fun j => C0 j * C1 j) (Finset.mem_univ i)) (hα_pos i).le
      _ = (∑ i, α i) * Finset.univ.sup' Finset.univ_nonempty (fun j => C0 j * C1 j) := by
          rw [Finset.sum_mul]
      _ = Finset.univ.sup' Finset.univ_nonempty (fun j => C0 j * C1 j) := by
          rw [hsumα, one_mul]
  refine ⟨hpos_bound, hneg_bound, ?_⟩
  -- The stage complexity follows from the two bounds above.
  have hC1'_le : posComplexityW G.len w' G.flow (Finset.univ : Finset E) ≤ 1 := by
    apply Finset.sup'_le Finset.univ_nonempty (fun y => posComplexityAtW G.len w' (G.flow y)
      (Finset.univ : Finset E))
    intro y _
    exact hpos_bound y
  set M : ℝ := Finset.univ.sup' Finset.univ_nonempty
    (fun i => complexityW G.len G.weight G.flow (piece part i)) with hM
  have hM_nonneg : 0 ≤ M := by
    obtain ⟨i0⟩ := (inferInstance : Nonempty ι)
    exact (complexityW_nonneg G.len G.weight_pos G.flow (piece part i0)).trans
      (Finset.le_sup' (fun i => complexityW G.len G.weight G.flow (piece part i))
        (Finset.mem_univ i0))
  have hC0'_le : negComplexityW G.len w' (Finset.univ : Finset E) ≤ M ^ 2 := by
    refine hneg_bound.trans ?_
    apply Finset.sup'_le Finset.univ_nonempty
    intro i _
    have hsq : C0 i * C1 i = (complexityW G.len G.weight G.flow (piece part i)) ^ 2 := by
      rw [complexityW, Real.sq_sqrt (mul_nonneg (hC0_nonneg i) (hC1_nonneg i))]
    rw [hsq]
    have hle : complexityW G.len G.weight G.flow (piece part i) ≤ M :=
      Finset.le_sup' (fun j => complexityW G.len G.weight G.flow (piece part j))
        (Finset.mem_univ i)
    have hnonneg := complexityW_nonneg G.len G.weight_pos G.flow (piece part i)
    nlinarith
  have hC1'_nonneg : 0 ≤ posComplexityW G.len w' G.flow (Finset.univ : Finset E) :=
    posComplexityW_nonneg G.len hw'_pos G.flow (Finset.univ : Finset E)
  calc complexityW G.len w' G.flow (Finset.univ : Finset E)
      = Real.sqrt (negComplexityW G.len w' (Finset.univ : Finset E) *
          posComplexityW G.len w' G.flow (Finset.univ : Finset E)) := rfl
    _ ≤ Real.sqrt (M ^ 2 * 1) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul hC0'_le hC1'_le hC1'_nonneg (sq_nonneg M)
    _ = M := by
        rw [mul_one, Real.sqrt_sq hM_nonneg]

end Qatlib.Papers.LearningGraph11.MainResults
