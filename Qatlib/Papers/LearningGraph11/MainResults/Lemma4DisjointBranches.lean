/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LearningGraph11.MainResults.SourceLearningGraphModel

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 Lemma 4: disjoint branch sets

Fixed source: arXiv:1109.5135v1, Lemma 4 and its proof (p. 6).

Let a stage `E` (the edge slice `S`) be split into the outgoing edge sets `E_v^→` of the
vertices `v` in a vertex set `Vset` at the beginning of the stage (`part : E → ι` is the
branch map). If for every input `y`

1. the branch edge sets are disjoint (automatic for `pieceIn S part`),
2. the number `|W_y|` of branches receiving positive flow is independent of `y` (common
   value `c > 0`), and
3. for `v ∈ W_y` the flow is split uniformly, `p_y(E_v^→) = p_y(E_V^→)/|W_y|`,
   while branches outside `W_y` carry no flow,

then `C(E_V^→) ≤ sqrt(max_v C_0(E_v^→) · max_v C_1(E_v^→) · |V|/|W_y|)`.

The theorem is stated for an arbitrary edge slice `S` and an arbitrary beginning-vertex set
`Vset`, because Lemma 5 applies it inside each piece of a coarser partition of the stage.
`hVne` is needed only so that the two maxima over `V` exist; the paper always has a
nonempty set of active branches when `c > 0`.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

variable {V E Y ι : Type*} [Fintype V] [Fintype E] [Fintype Y] [Fintype ι]
  [DecidableEq ι] [Nonempty ι] [Nonempty Y]

/-- The `i`-th piece of the branch partition restricted to an edge slice `S`. -/
def pieceIn (S : Finset E) (part : E → ι) (i : ι) : Finset E :=
  S.filter (fun e => part e = i)

/-- Regrouping a sum over a slice along the branch partition. -/
theorem sum_pieceIn (S : Finset E) (part : E → ι) (f : E → ℝ) :
    ∑ i, ∑ e ∈ pieceIn S part i, f e = ∑ e ∈ S, f e := by
  simpa [pieceIn] using (Finset.sum_fiberwise S part f)

/-- Fixed source arXiv:1109.5135v1, Lemma 4 (p. 6), for an arbitrary edge slice and
beginning-vertex set: the complexity of a stage that splits into disjoint uniformly
flow-distributed branch sets is at most `sqrt(max C_0 · max C_1 · |V| / |W_y|)`. -/
theorem source_lemma_4_slice
    (len : E → ℕ) (w : E → ℝ) (p : Y → E → ℝ) (S : Finset E) (part : E → ι)
    (Vset : Finset ι) (W : Y → Finset ι) (c : ℕ)
    (hVne : Vset.Nonempty)
    (hw : ∀ e, 0 < w e)
    (hc : 0 < c)
    (hcover : ∀ e ∈ S, part e ∈ Vset)
    (hWsub : ∀ y, W y ⊆ Vset)
    (hWcard : ∀ y, (W y).card = c)
    (huniform : ∀ y v, v ∈ W y →
      (∑ e ∈ pieceIn S part v, p y e) = (∑ e ∈ S, p y e) / (c : ℝ))
    (houtside : ∀ y v, v ∈ Vset → v ∉ W y → ∀ e ∈ pieceIn S part v, p y e = 0) :
    complexityW len w p S ≤
      Real.sqrt ((Vset.sup' hVne (fun v => negComplexityW len w (pieceIn S part v))) *
        (Vset.sup' hVne (fun v => posComplexityW len w p (pieceIn S part v))) *
        ((Vset.card : ℝ) / (c : ℝ))) := by
  classical
  have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  set M0 : ℝ := Vset.sup' hVne (fun v => negComplexityW len w (pieceIn S part v)) with hM0
  set M1 : ℝ := Vset.sup' hVne (fun v => posComplexityW len w p (pieceIn S part v)) with hM1
  have hC0_nonneg : ∀ v, 0 ≤ negComplexityW len w (pieceIn S part v) := fun v =>
    negComplexityW_nonneg len (fun e => (hw e).le) (pieceIn S part v)
  have hM0_nonneg : 0 ≤ M0 := by
    obtain ⟨v0, hv0⟩ := hVne
    exact (hC0_nonneg v0).trans
      (Finset.le_sup' (fun v => negComplexityW len w (pieceIn S part v)) hv0)
  have hM1_nonneg : 0 ≤ M1 := by
    obtain ⟨v0, hv0⟩ := hVne
    have h1 : 0 ≤ posComplexityW len w p (pieceIn S part v0) :=
      posComplexityW_nonneg len hw p _
    exact h1.trans
      (Finset.le_sup' (fun v => posComplexityW len w p (pieceIn S part v)) hv0)
  -- Pieces outside the beginning-vertex set are empty, since `S` is covered by `Vset`.
  have hpieceIn_empty : ∀ v, v ∉ Vset → pieceIn S part v = ∅ := by
    intro v hv
    rw [pieceIn, Finset.filter_eq_empty_iff]
    intro e he hve
    exact hv (hve ▸ hcover e he)
  -- Negative complexity: split the edge sum along the branches.
  have hC0_split : negComplexityW len w S =
      ∑ v ∈ Vset, negComplexityW len w (pieceIn S part v) := by
    rw [negComplexityW, ← sum_pieceIn S part (fun e => (len e : ℝ) * w e)]
    symm
    apply Finset.sum_subset (Finset.subset_univ Vset)
    intro v _ hv
    rw [hpieceIn_empty v hv, negComplexityW]
    simp
  have hC0_le : negComplexityW len w S ≤ (Vset.card : ℝ) * M0 := by
    rw [hC0_split]
    calc ∑ v ∈ Vset, negComplexityW len w (pieceIn S part v)
        ≤ ∑ _v ∈ Vset, M0 := by
          apply Finset.sum_le_sum
          intro v hv
          exact Finset.le_sup' (fun v => negComplexityW len w (pieceIn S part v)) hv
      _ = (Vset.card : ℝ) * M0 := by
          rw [Finset.sum_const, nsmul_eq_mul]
  -- Positive complexity, one input at a time.
  have hC1_y : ∀ y, posComplexityAtW len w (p y) S ≤ M1 / (c : ℝ) := by
    intro y
    set T : ℝ := ∑ e ∈ S, p y e with hT
    by_cases hT0 : T = 0
    · rw [posComplexityAtW, if_pos (by simpa [hT] using hT0)]
      exact div_nonneg hM1_nonneg (Nat.cast_nonneg c)
    · rw [posComplexityAtW, if_neg (by simpa [hT] using hT0)]
      rw [← sum_pieceIn S part (fun e => (len e : ℝ) / w e * (p y e / T) ^ 2)]
      have hzeroV : ∀ v, v ∉ Vset →
          ∑ e ∈ pieceIn S part v, (len e : ℝ) / w e * (p y e / T) ^ 2 = 0 := by
        intro v hv
        rw [hpieceIn_empty v hv]
        simp
      have hzero : ∀ v, v ∈ Vset → v ∉ W y →
          ∑ e ∈ pieceIn S part v, (len e : ℝ) / w e * (p y e / T) ^ 2 = 0 := by
        intro v hvV hv
        apply Finset.sum_eq_zero
        intro e he
        rw [houtside y v hvV hv e he]
        simp
      have hpiece : ∀ v ∈ W y,
          ∑ e ∈ pieceIn S part v, (len e : ℝ) / w e * (p y e / T) ^ 2
            = (1 / (c : ℝ) ^ 2) * posComplexityAtW len w (p y) (pieceIn S part v) := by
        intro v hv
        have hσ : (∑ e ∈ pieceIn S part v, p y e) = T / (c : ℝ) := by
          rw [huniform y v hv, ← hT]
        have hσne : (∑ e ∈ pieceIn S part v, p y e) ≠ 0 := by
          rw [hσ]
          exact div_ne_zero hT0 hcR
        have hσc : (c : ℝ) * (∑ e ∈ pieceIn S part v, p y e) = T := by
          rw [hσ]
          field_simp
        rw [posComplexityAtW, if_neg hσne, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro e he
        have hwne : w e ≠ 0 := ne_of_gt (hw e)
        rw [← hσc]
        field_simp
      calc ∑ v, ∑ e ∈ pieceIn S part v, (len e : ℝ) / w e * (p y e / T) ^ 2
          = ∑ v ∈ Vset, ∑ e ∈ pieceIn S part v, (len e : ℝ) / w e * (p y e / T) ^ 2 :=
            (Finset.sum_subset (Finset.subset_univ Vset)
              (fun v _ hv => hzeroV v hv)).symm
        _ = ∑ v ∈ W y, ∑ e ∈ pieceIn S part v, (len e : ℝ) / w e * (p y e / T) ^ 2 := by
            symm
            apply Finset.sum_subset (hWsub y)
            intro v hvV hv
            exact hzero v hvV hv
        _ = ∑ v ∈ W y, (1 / (c : ℝ) ^ 2) *
              posComplexityAtW len w (p y) (pieceIn S part v) :=
            Finset.sum_congr rfl (fun v hv => hpiece v hv)
        _ ≤ ∑ _v ∈ W y, (1 / (c : ℝ) ^ 2) * M1 := by
            apply Finset.sum_le_sum
            intro v hvW
            have hle1 : posComplexityAtW len w (p y) (pieceIn S part v) ≤
                posComplexityW len w p (pieceIn S part v) :=
              Finset.le_sup' (fun y' => posComplexityAtW len w (p y') (pieceIn S part v))
                (Finset.mem_univ y)
            have hle2 : posComplexityW len w p (pieceIn S part v) ≤ M1 := by
              rw [hM1]
              exact Finset.le_sup' (fun v => posComplexityW len w p (pieceIn S part v))
                (hWsub y hvW)
            exact mul_le_mul_of_nonneg_left (hle1.trans hle2) (by positivity)
        _ = (1 / (c : ℝ) ^ 2) * ((W y).card : ℝ) * M1 := by
            rw [← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
            ring
        _ = M1 / (c : ℝ) := by
            rw [hWcard y]
            field_simp
  have hC1_le : posComplexityW len w p S ≤ M1 / (c : ℝ) := by
    apply Finset.sup'_le Finset.univ_nonempty
      (fun y => posComplexityAtW len w (p y) S)
    intro y _
    exact hC1_y y
  have hC1_nonneg : 0 ≤ posComplexityW len w p S := posComplexityW_nonneg len hw p _
  calc complexityW len w p S
      = Real.sqrt (negComplexityW len w S * posComplexityW len w p S) := rfl
    _ ≤ Real.sqrt (((Vset.card : ℝ) * M0) * (M1 / (c : ℝ))) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul hC0_le hC1_le hC1_nonneg
          (mul_nonneg (Nat.cast_nonneg _) hM0_nonneg)
    _ = Real.sqrt (M0 * M1 * ((Vset.card : ℝ) / (c : ℝ))) := by
        congr 1
        ring

/-- Fixed source arXiv:1109.5135v1, Lemma 4 (p. 6): the whole-stage version of
`source_lemma_4_slice` (beginning-vertex set all of `ι`). -/
theorem source_lemma_4
    (len : E → ℕ) (w : E → ℝ) (p : Y → E → ℝ) (part : E → ι)
    (W : Y → Finset ι) (c : ℕ)
    (hw : ∀ e, 0 < w e)
    (hc : 0 < c)
    (hWcard : ∀ y, (W y).card = c)
    (huniform : ∀ y v, v ∈ W y →
      (∑ e ∈ piece part v, p y e) = (∑ e ∈ (Finset.univ : Finset E), p y e) / (c : ℝ))
    (houtside : ∀ y v, v ∉ W y → ∀ e ∈ piece part v, p y e = 0) :
    complexityW len w p (Finset.univ : Finset E) ≤
      Real.sqrt ((Finset.univ.sup' Finset.univ_nonempty
          (fun v => negComplexityW len w (piece part v))) *
        (Finset.univ.sup' Finset.univ_nonempty
          (fun v => posComplexityW len w p (piece part v))) *
        ((Fintype.card ι : ℝ) / (c : ℝ))) := by
  simpa [pieceIn, piece] using
    (source_lemma_4_slice len w p (Finset.univ : Finset E) part (Finset.univ : Finset ι)
      W c Finset.univ_nonempty hw hc (fun e _ => Finset.mem_univ _) (fun y => Finset.subset_univ _)
      hWcard huniform (fun y v _ hv => houtside y v hv))

end Qatlib.Papers.LearningGraph11.MainResults
