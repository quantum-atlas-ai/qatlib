/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LearningGraph11.MainResults.Lemma3StagePartition
import Qatlib.Papers.LearningGraph11.MainResults.Lemma4DisjointBranches

set_option backward.isDefEq.respectTransparency false

/-!
# LearningGraph11 Lemma 5: consecutive-level stages (Equation (2))

Fixed source: arXiv:1109.5135v1, Lemma 5 and its proof (pp. 6-7), including Eq. (2).

A stage `E` between two consecutive levels has each of its beginning vertices `v` of
outdegree `d`, all of its edges of weight `1` and length at most `ℓ`. The beginning
vertices are partitioned into classes `V_i`. Assume that (1) the flows are consistent with
the class edge sets `V_i^+` (Definition 5), (2) `|W_{y,i}| = c_i` is independent of `y` and
the flow into `v ∈ W_{y,i}` is uniform inside the class, and (3) for `v ∈ W_{y,i}` the flow
leaves `v` uniformly along `g` of its `d` outgoing edges. Then some weighting `w'` satisfies
`C^{w'}(E) ≤ max_i ℓ sqrt((d/g)(|V_i|/|W_{y,i}|))`.

The proof chains Lemma 3 (group reweighting) and Lemma 4 (complexity inside each class),
plus the per-vertex evaluations `C_0(v^+) ≤ ℓ d` and `C_1(v^+) ≤ ℓ/g` from hypotheses 1-3.
`hC1pos` is the non-degeneracy condition under which Lemma 3 is applied; it holds whenever
the class edge sets carry positive flow and all edge lengths are positive, and the paper's
deletion of zero-mass classes (proof of Lemma 3) covers the remaining cases.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.LearningGraph11.MainResults

open Finset
open scoped BigOperators

/-- The group index of an edge, induced by the group of its source vertex. -/
def groupPart {E ι κ : Type*} (grpV : ι → κ) (part : E → ι) : E → κ :=
  fun e => grpV (part e)

/-- The vertex class `V_i = {v : grpV v = i}`. -/
def vertexGroup {ι κ : Type*} [Fintype ι] [DecidableEq κ] (grpV : ι → κ) (i : κ) : Finset ι :=
  Finset.univ.filter (fun v => grpV v = i)

/-- Inside class `i`, the vertex piece of the class edge slice is the full vertex piece. -/
theorem pieceIn_groupPiece_eq {E ι κ : Type*} [Fintype E] [Fintype ι] [DecidableEq ι]
    [DecidableEq κ] (grpV : ι → κ) (part : E → ι) {v : ι} {i : κ} (hv : grpV v = i) :
    pieceIn (piece (groupPart grpV part) i) part v = piece part v := by
  ext e
  simp only [pieceIn, piece, groupPart, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨-, hpart⟩
    exact hpart
  · intro hpart
    exact ⟨by rw [hpart]; exact hv, hpart⟩

section Lemma5

variable {E Y ι κ : Type*} [Fintype E] [Fintype Y] [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ] [Nonempty ι] [Nonempty κ] [Nonempty Y]

/-- Fixed source arXiv:1109.5135v1, Lemma 5 and Eq. (2) (pp. 6-7): a consecutive-level
stage with outdegree `d`, unit weights, edge lengths at most `ℓ`, consistent class flows
and uniform `g`-to-`d` routing admits a reweighting of complexity at most
`max_i ℓ sqrt((d/g)(|V_i|/|W_{y,i}|))`. -/
theorem source_lemma_5
    (len : E → ℕ) (p : Y → E → ℝ) (part : E → ι) (grpV : ι → κ)
    (W : Y → κ → Finset ι) (c : κ → ℕ)
    (d g ℓ : ℕ)
    (hp_nonneg : ∀ y e, 0 ≤ p y e)
    (hstage : ∀ y, ∑ e ∈ (Finset.univ : Finset E), p y e = 1)
    (hd : 0 < d) (hg : 0 < g)
    (hdeg : ∀ v, (piece part v).card = d)
    (hlen : ∀ e, len e ≤ ℓ)
    (hc : ∀ i, 0 < c i)
    (hWsub : ∀ y i, W y i ⊆ vertexGroup grpV i)
    (hWcard : ∀ y i, (W y i).card = c i)
    (hWpos : ∀ y i v, v ∈ W y i → 0 < ∑ e ∈ piece part v, p y e)
    (huniformV : ∀ y i v, v ∈ W y i →
      (∑ e ∈ piece part v, p y e) =
        (∑ e ∈ piece (groupPart grpV part) i, p y e) / (c i : ℝ))
    (hconsistent : ∀ y y' i,
      (∑ e ∈ piece (groupPart grpV part) i, p y e) =
        (∑ e ∈ piece (groupPart grpV part) i, p y' e))
    (houtsideV : ∀ y i v, grpV v = i → v ∉ W y i → ∀ e ∈ piece part v, p y e = 0)
    (hC1pos : ∀ i, 0 < posComplexityW len (fun _ => 1) p
      (piece (groupPart grpV part) i))
    (hsupp : ∀ y i v, v ∈ W y i → ∃ supp : Finset E, supp ⊆ piece part v ∧
      supp.card = g ∧
      (∀ e ∈ supp, p y e = (∑ e ∈ piece part v, p y e) / (g : ℝ)) ∧
      (∀ e ∈ piece part v, e ∉ supp → p y e = 0)) :
    ∃ w' : E → ℝ, complexityW len w' p (Finset.univ : Finset E) ≤
      Finset.univ.sup' Finset.univ_nonempty (fun i =>
        (ℓ : ℝ) * Real.sqrt ((d : ℝ) / (g : ℝ) *
          (((vertexGroup grpV i).card : ℝ) / (c i : ℝ)))) := by
  classical
  obtain ⟨y0⟩ := (inferInstance : Nonempty Y)
  -- The unit-weight learning graph carrying the same flow.
  let G : LearningGraph Unit E Y :=
    { src := fun _ => Unit.unit
      tgt := fun _ => Unit.unit
      level := fun _ => 0
      weight := fun _ => 1
      len := len
      flow := p
      weight_pos := by intro e; norm_num
      flow_nonneg := hp_nonneg
      stage_flow := hstage }
  -- Every class carries positive flow mass.
  have hWne : ∀ i, (W y0 i).Nonempty := fun i =>
    Finset.card_pos.mp (by rw [hWcard y0 i]; exact hc i)
  -- The class flow masses `α_i`.
  let α : κ → ℝ := fun i => ∑ e ∈ piece (groupPart grpV part) i, p y0 e
  have hα_pos : ∀ i, 0 < α i := by
    intro i
    obtain ⟨v, hv⟩ := hWne i
    have hσ : 0 < ∑ e ∈ piece part v, p y0 e := hWpos y0 i v hv
    have hcR : (0 : ℝ) < (c i : ℝ) := by exact_mod_cast hc i
    have hcne : (c i : ℝ) ≠ 0 := ne_of_gt hcR
    have hαeq : α i = (c i : ℝ) * (∑ e ∈ piece part v, p y0 e) := by
      have huni := huniformV y0 i v hv
      have h2 : (c i : ℝ) * (∑ e ∈ piece part v, p y0 e) = α i := by
        rw [huni]
        field_simp
        rfl
      exact h2.symm
    rw [hαeq]
    exact mul_pos hcR hσ
  have hconsistent' : ∀ y i, edgeSum G (piece (groupPart grpV part) i) y = α i := by
    intro y i
    change (∑ e ∈ piece (groupPart grpV part) i, p y e) = α i
    exact hconsistent y y0 i
  have hLem3 := source_lemma_3 (V := Unit) G (groupPart grpV part) α hα_pos hconsistent' hC1pos
  set w' : E → ℝ := lemma3Reweight (V := Unit) G (groupPart grpV part) α with hw'
  have hbound : complexityW G.len w' G.flow (Finset.univ : Finset E) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => complexityW G.len G.weight G.flow (piece (groupPart grpV part) i)) := by
    simpa [hw'] using hLem3.2.2
  -- Per-class complexity bound (Lemma 4 plus the two per-vertex evaluations).
  have hgroup_bound : ∀ i, complexityW len (fun _ => 1) p
      (piece (groupPart grpV part) i) ≤
      (ℓ : ℝ) * Real.sqrt ((d : ℝ) / (g : ℝ) *
        (((vertexGroup grpV i).card : ℝ) / (c i : ℝ))) := by
    intro i
    have hVne : (vertexGroup grpV i).Nonempty := by
      obtain ⟨v, hv⟩ := hWne i
      exact ⟨v, hWsub y0 i hv⟩
    have hcover : ∀ e ∈ piece (groupPart grpV part) i, part e ∈ vertexGroup grpV i := by
      intro e he
      have hg : grpV (part e) = i := by
        simpa [piece, groupPart] using (Finset.mem_filter.mp he).2
      simp only [vertexGroup, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hg
    have hgrp_of_mem : ∀ v ∈ vertexGroup grpV i, grpV v = i := by
      intro v hvV
      simpa only [vertexGroup, Finset.mem_filter, Finset.mem_univ, true_and] using hvV
    have huniform' : ∀ y v, v ∈ W y i →
        (∑ e ∈ pieceIn (piece (groupPart grpV part) i) part v, p y e) =
          (∑ e ∈ piece (groupPart grpV part) i, p y e) / (c i : ℝ) := by
      intro y v hv
      have hgv : grpV v = i := hgrp_of_mem v (hWsub y i hv)
      rw [pieceIn_groupPiece_eq grpV part hgv]
      exact huniformV y i v hv
    have houtside' : ∀ y v, v ∈ vertexGroup grpV i → v ∉ W y i →
        ∀ e ∈ pieceIn (piece (groupPart grpV part) i) part v, p y e = 0 := by
      intro y v hvV hvW e he
      have hgv : grpV v = i := hgrp_of_mem v hvV
      rw [pieceIn_groupPiece_eq grpV part hgv] at he
      exact houtsideV y i v hgv hvW e he
    have h4 := source_lemma_4_slice len (fun _ => 1) p (piece (groupPart grpV part) i)
      part (vertexGroup grpV i) (fun y => W y i) (c i) hVne
      (by intro e; norm_num) (hc i) hcover (fun y => hWsub y i) (fun y => hWcard y i)
      huniform' houtside'
    -- Replace the restricted pieces by the full vertex pieces in the two maxima.
    have hM0eq : (vertexGroup grpV i).sup' hVne
        (fun v => negComplexityW len (fun _ => 1)
          (pieceIn (piece (groupPart grpV part) i) part v)) =
        (vertexGroup grpV i).sup' hVne
          (fun v => negComplexityW len (fun _ => 1) (piece part v)) := by
      apply Finset.sup'_congr hVne rfl
      intro v hvV
      rw [pieceIn_groupPiece_eq grpV part (hgrp_of_mem v hvV)]
    have hM1eq : (vertexGroup grpV i).sup' hVne
        (fun v => posComplexityW len (fun _ => 1) p
          (pieceIn (piece (groupPart grpV part) i) part v)) =
        (vertexGroup grpV i).sup' hVne
          (fun v => posComplexityW len (fun _ => 1) p (piece part v)) := by
      apply Finset.sup'_congr hVne rfl
      intro v hvV
      rw [pieceIn_groupPiece_eq grpV part (hgrp_of_mem v hvV)]
    -- `C_0(v^+) ≤ ℓ d` for every beginning vertex.
    have hM0le : (vertexGroup grpV i).sup' hVne
        (fun v => negComplexityW len (fun _ => 1) (piece part v)) ≤ (d : ℝ) * (ℓ : ℝ) := by
      apply Finset.sup'_le hVne
      intro v _
      have h1 : negComplexityW len (fun _ => 1) (piece part v) =
          ∑ e ∈ piece part v, (len e : ℝ) := by
        simp [negComplexityW]
      rw [h1]
      calc ∑ e ∈ piece part v, (len e : ℝ)
          ≤ ∑ _e ∈ piece part v, (ℓ : ℝ) := by
            apply Finset.sum_le_sum
            intro e _
            exact_mod_cast hlen e
        _ = ((piece part v).card : ℝ) * (ℓ : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (d : ℝ) * (ℓ : ℝ) := by rw [hdeg v]
    -- `C_1(v^+) ≤ ℓ/g` for every beginning vertex.
    have hM1le : (vertexGroup grpV i).sup' hVne
        (fun v => posComplexityW len (fun _ => 1) p (piece part v)) ≤ (ℓ : ℝ) / (g : ℝ) := by
      apply Finset.sup'_le hVne
      intro v hvV
      have hgv : grpV v = i := hgrp_of_mem v hvV
      apply Finset.sup'_le Finset.univ_nonempty
      intro y _
      by_cases hvW : v ∈ W y i
      · obtain ⟨supp, hsub, hcard, hval, hzero2⟩ := hsupp y i v hvW
        have hσpos : 0 < ∑ e ∈ piece part v, p y e := hWpos y i v hvW
        have hσne : (∑ e ∈ piece part v, p y e) ≠ 0 := ne_of_gt hσpos
        have hgne : (g : ℝ) ≠ 0 := by exact_mod_cast hg.ne'
        rw [posComplexityAtW, if_neg hσne]
        have hsum_supp :
            ∑ e ∈ piece part v, (len e : ℝ) / (1 : ℝ) *
                (p y e / (∑ e ∈ piece part v, p y e)) ^ 2
              = ∑ e ∈ supp, (len e : ℝ) * (1 / (g : ℝ)) ^ 2 := by
          have hzero3 : ∀ e ∈ piece part v, e ∉ supp →
              (len e : ℝ) / (1 : ℝ) *
                (p y e / (∑ e ∈ piece part v, p y e)) ^ 2 = 0 := by
            intro e he hes
            rw [hzero2 e he hes]
            simp
          rw [← Finset.sum_subset hsub hzero3]
          apply Finset.sum_congr rfl
          intro e he
          rw [hval e he]
          field_simp
        rw [hsum_supp]
        calc ∑ e ∈ supp, (len e : ℝ) * (1 / (g : ℝ)) ^ 2
            ≤ ∑ _e ∈ supp, (ℓ : ℝ) * (1 / (g : ℝ)) ^ 2 := by
              apply Finset.sum_le_sum
              intro e _
              exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen e) (sq_nonneg _)
          _ = (supp.card : ℝ) * ((ℓ : ℝ) * (1 / (g : ℝ)) ^ 2) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = (ℓ : ℝ) / (g : ℝ) := by
              rw [hcard]
              field_simp
      · have hzeroflow : ∀ e ∈ piece part v, p y e = 0 :=
          fun e he => houtsideV y i v hgv hvW e he
        have hzero : posComplexityAtW len (fun _ => 1) (p y) (piece part v) = 0 := by
          rw [posComplexityAtW]
          split_ifs with h
          · rfl
          · apply Finset.sum_eq_zero
            intro e he
            rw [hzeroflow e he]
            simp
        rw [hzero]
        exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    -- Combine the two maxima with the Lemma 4 estimate.
    have hsqrt : Real.sqrt (((d : ℝ) * (ℓ : ℝ)) * ((ℓ : ℝ) / (g : ℝ)) *
        (((vertexGroup grpV i).card : ℝ) / (c i : ℝ))) =
        (ℓ : ℝ) * Real.sqrt ((d : ℝ) / (g : ℝ) *
          (((vertexGroup grpV i).card : ℝ) / (c i : ℝ))) := by
      have hℓ0 : (0 : ℝ) ≤ (ℓ : ℝ) := Nat.cast_nonneg _
      have hcR : (0 : ℝ) < (c i : ℝ) := by exact_mod_cast hc i
      have hX0 : 0 ≤ ((d : ℝ) / (g : ℝ)) *
          (((vertexGroup grpV i).card : ℝ) / (c i : ℝ)) := by positivity
      rw [show (((d : ℝ) * (ℓ : ℝ)) * ((ℓ : ℝ) / (g : ℝ)) *
            (((vertexGroup grpV i).card : ℝ) / (c i : ℝ))) =
          (ℓ : ℝ) ^ 2 * (((d : ℝ) / (g : ℝ)) *
            (((vertexGroup grpV i).card : ℝ) / (c i : ℝ))) by ring]
      rw [Real.sqrt_mul (sq_nonneg (ℓ : ℝ)), Real.sqrt_sq hℓ0]
    have hcard_nonneg : (0 : ℝ) ≤ ((vertexGroup grpV i).card : ℝ) := Nat.cast_nonneg _
    have hM0nonneg : 0 ≤ (vertexGroup grpV i).sup' hVne
        (fun v => negComplexityW len (fun _ => 1) (piece part v)) :=
      (negComplexityW_nonneg len (fun _ => zero_le_one) _).trans
        (Finset.le_sup' (fun v => negComplexityW len (fun _ => 1) (piece part v))
          hVne.choose_spec)
    have hM1nonneg : 0 ≤ (vertexGroup grpV i).sup' hVne
        (fun v => posComplexityW len (fun _ => 1) p (piece part v)) :=
      (posComplexityW_nonneg len (fun _ => zero_lt_one) p _).trans
        (Finset.le_sup' (fun v => posComplexityW len (fun _ => 1) p (piece part v))
          hVne.choose_spec)
    calc complexityW len (fun _ => 1) p (piece (groupPart grpV part) i)
        ≤ Real.sqrt ((vertexGroup grpV i).sup' hVne
              (fun v => negComplexityW len (fun _ => 1)
                (pieceIn (piece (groupPart grpV part) i) part v)) *
            (vertexGroup grpV i).sup' hVne
              (fun v => posComplexityW len (fun _ => 1) p
                (pieceIn (piece (groupPart grpV part) i) part v)) *
            (((vertexGroup grpV i).card : ℝ) / (c i : ℝ))) := h4
      _ = Real.sqrt ((vertexGroup grpV i).sup' hVne
              (fun v => negComplexityW len (fun _ => 1) (piece part v)) *
            (vertexGroup grpV i).sup' hVne
              (fun v => posComplexityW len (fun _ => 1) p (piece part v)) *
            (((vertexGroup grpV i).card : ℝ) / (c i : ℝ))) := by rw [hM0eq, hM1eq]
      _ ≤ Real.sqrt (((d : ℝ) * (ℓ : ℝ)) * ((ℓ : ℝ) / (g : ℝ)) *
            (((vertexGroup grpV i).card : ℝ) / (c i : ℝ))) := by
          apply Real.sqrt_le_sqrt
          have hcn : 0 ≤ ((vertexGroup grpV i).card : ℝ) / (c i : ℝ) :=
            div_nonneg hcard_nonneg (Nat.cast_nonneg _)
          exact mul_le_mul
            (mul_le_mul hM0le hM1le hM1nonneg
              (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg ℓ)))
            le_rfl hcn
            (mul_nonneg (mul_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg ℓ))
              (div_nonneg (Nat.cast_nonneg ℓ) (Nat.cast_nonneg g)))
      _ = (ℓ : ℝ) * Real.sqrt ((d : ℝ) / (g : ℝ) *
            (((vertexGroup grpV i).card : ℝ) / (c i : ℝ))) := hsqrt
  have hb : complexityW len w' p (Finset.univ : Finset E) ≤
      Finset.univ.sup' Finset.univ_nonempty
        (fun i => complexityW len (fun _ => 1) p (piece (groupPart grpV part) i)) := by
    simpa [G] using hbound
  refine ⟨w', hb.trans ?_⟩
  apply Finset.sup'_le Finset.univ_nonempty
  intro i _
  exact (hgroup_bound i).trans
    (Finset.le_sup' (fun i => (ℓ : ℝ) * Real.sqrt ((d : ℝ) / (g : ℝ) *
      (((vertexGroup grpV i).card : ℝ) / (c i : ℝ)))) (Finset.mem_univ i))

end Lemma5

end Qatlib.Papers.LearningGraph11.MainResults
