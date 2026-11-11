/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.LatentPQCTran26.MainResults.Definitions

/-!
# Finite atomic catalogs on compact metric spaces

The sets `cell` assign each covered point to the first catalog center within a chosen radius,
giving measurable disjoint cells. Using compactness, `lemma2_finite_catalog` constructs a
nonempty finite weighted atomic approximation to a probability measure with arbitrarily small
`wasserstein1` cost. See [TranEtAl2026] for the paper context.

## Main statements

* `measurable_cell`: Each first-center cell is measurable when open sets in the metric space are
  measurable.
* `cell_disjoint`: Cells belonging to distinct catalog indices are disjoint.
* `lemma2_finite_catalog`: Every probability measure on a compact metric space with measurable
  open sets has, for each positive `ε`, a nonempty finite atomic approximation with weights
  summing to one and `wasserstein1` cost at most `ε`.

## References

* [Tran et al., 2026][TranEtAl2026]
-/

set_option warningAsError false

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped Classical

namespace Qatlib.Papers.LatentPQCTran26.MainResults.FiniteCatalog

open Qatlib.Papers.LatentPQCTran26.MainResults

/-- The points within distance `ε` of center `ρ i` that are outside all such balls with smaller
indices. -/
private def cell {D : Type*} [MetricSpace D] {N : ℕ} (ρ : Fin N → D) (ε : ℝ)
    (i : Fin N) : Set D :=
  {x | dist x (ρ i) < ε ∧ ∀ j : Fin N, (j : ℕ) < (i : ℕ) → ε ≤ dist x (ρ j)}

/-- Each first-center cell is measurable when open sets in the metric space are measurable. -/
private theorem measurable_cell {D : Type*} [MeasurableSpace D] [MetricSpace D]
    [OpensMeasurableSpace D] {N : ℕ} (ρ : Fin N → D) (ε : ℝ) (i : Fin N) :
    MeasurableSet (cell ρ ε i) := by
  have hdist : ∀ j : Fin N, Measurable fun x : D => dist x (ρ j) :=
    fun j =>
      (Continuous.dist (continuous_id : Continuous fun x : D => x)
        (continuous_const : Continuous fun _ : D => ρ j)).measurable
  have h1 : MeasurableSet {x : D | dist x (ρ i) < ε} :=
    measurableSet_lt (hdist i) measurable_const
  have hjmeas : ∀ j : Fin N, MeasurableSet {x : D | (j : ℕ) < (i : ℕ) → ε ≤ dist x (ρ j)} := by
    intro j
    by_cases h : (j : ℕ) < (i : ℕ)
    · have heq : {x : D | (j : ℕ) < (i : ℕ) → ε ≤ dist x (ρ j)}
          = {x : D | ε ≤ dist x (ρ j)} := by ext x; simp [h]
      rw [heq]
      exact measurableSet_le measurable_const (hdist j)
    · have heq : {x : D | (j : ℕ) < (i : ℕ) → ε ≤ dist x (ρ j)} = Set.univ := by
        ext x; simp [h]
      rw [heq]
      exact MeasurableSet.univ
  have h2 : MeasurableSet {x : D | ∀ j : Fin N, (j : ℕ) < (i : ℕ) → ε ≤ dist x (ρ j)} := by
    have heq : {x : D | ∀ j : Fin N, (j : ℕ) < (i : ℕ) → ε ≤ dist x (ρ j)}
        = ⋂ j : Fin N, {x : D | (j : ℕ) < (i : ℕ) → ε ≤ dist x (ρ j)} := by
      ext x
      simp only [mem_setOf_eq, mem_iInter]
    rw [heq]
    exact MeasurableSet.iInter hjmeas
  have hcellEq : cell ρ ε i
      = {x : D | dist x (ρ i) < ε} ∩ {x : D | ∀ j : Fin N, (j : ℕ) < (i : ℕ) → ε ≤ dist x (ρ j)} := by
    ext x
    simp only [cell, Set.mem_setOf_eq, Set.mem_inter_iff]
  rw [hcellEq]
  exact MeasurableSet.inter h1 h2

/-- Cells belonging to distinct catalog indices are disjoint. -/
private theorem cell_disjoint {D : Type*} [MetricSpace D] {N : ℕ} (ρ : Fin N → D)
    (ε : ℝ) {i j : Fin N} (hij : i ≠ j) :
    Disjoint (cell ρ ε i) (cell ρ ε j) := by
  rw [Set.disjoint_right]
  intro x hx
  simp only [cell, Set.mem_setOf_eq] at hx
  obtain ⟨hxj, hxjmin⟩ := hx
  rcases lt_trichotomy (i : ℕ) (j : ℕ) with h | h | h
  · intro hmem
    exact absurd (hxjmin i h) (not_le.2 (Set.mem_setOf_eq.mp hmem).1)
  · exact absurd (Fin.ext h) hij
  · intro hmem
    exact absurd ((Set.mem_setOf_eq.mp hmem).2 j h) (not_le.2 hxj)

/-- Every probability measure on a compact metric space with measurable open sets has, for each
positive `ε`, a nonempty finite atomic approximation with weights summing to one and
`wasserstein1` cost at most `ε` [TranEtAl2026]. -/
theorem lemma2_finite_catalog
    {D : Type*} [MeasurableSpace D] [MetricSpace D] [OpensMeasurableSpace D] [CompactSpace D]
    (Q : Measure D) [IsProbabilityMeasure Q] :
    ∀ ε > 0, ∃ (N : ℕ) (_ : NeZero N) (q : Fin N → NNReal) (ρ : Fin N → D),
      (∑ i, (q i : ℝ)) = 1 ∧
        wasserstein1 Q (atomicMeasure q ρ) ≤ ε := by
  intro ε hε

  have hne : (Set.univ : Set D).Nonempty := by
    by_contra h
    have hempty : (Set.univ : Set D) = ∅ :=
      Set.eq_empty_iff_forall_notMem.2 fun x hx => h ⟨x, hx⟩
    have h0 : Q Set.univ = 0 := by rw [hempty]; exact measure_empty
    rw [measure_univ] at h0
    exact absurd h0 (by simp)
  obtain ⟨x₀, -⟩ := hne
  haveI : DecidableEq D := Classical.decEq D

  obtain ⟨t, hsub⟩ := isCompact_univ.elim_finite_subcover (fun y : D => Metric.ball y (ε / 2))
    (fun y => Metric.isOpen_ball)
    (fun x _ => Set.mem_iUnion.2 ⟨x, Metric.mem_ball_self (by positivity)⟩)
  set tf : Finset D := insert x₀ t with htfdef
  have htfmem : x₀ ∈ tf := Finset.mem_insert_self _ _
  have hcover : ∀ x : D, ∃ y ∈ tf, dist x y < ε := by
    intro x
    have h := hsub (mem_univ x)
    simp only [mem_iUnion, exists_prop, Metric.mem_ball] at h
    obtain ⟨y, hyt, hdy⟩ := h
    exact ⟨y, Finset.mem_insert_of_mem hyt, by linarith⟩

  obtain ⟨N, ⟨e⟩⟩ := Finite.exists_equiv_fin (α := {x // x ∈ tf})
  have hcardeq : Fintype.card {x // x ∈ tf} = N :=
    (Fintype.card_eq.2 ⟨e⟩).trans (Fintype.card_fin N)
  have hNpos : 0 < N := hcardeq ▸ Fintype.card_pos_iff.2 ⟨⟨x₀, htfmem⟩⟩
  set ρ : Fin N → D := fun i => ((e.symm i : {x // x ∈ tf}) : D) with hρdef
  have hρcover : ∀ x : D, ∃ i : Fin N, dist x (ρ i) < ε := by
    intro x
    obtain ⟨y, hyt, hdy⟩ := hcover x
    have hy : y ∈ (tf : Set D) := Finset.mem_coe.2 hyt
    refine ⟨e ⟨y, hy⟩, ?_⟩
    have hrw : ρ (e ⟨y, hy⟩) = y := by simp [hρdef, Equiv.symm_apply_apply]
    rw [hrw]; linarith

  have hnonempty : ∀ x : D, (Finset.univ.filter (fun i => dist x (ρ i) < ε)).Nonempty := by
    intro x
    obtain ⟨i, hi⟩ := hρcover x
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ i, hi⟩⟩
  set idx : D → Fin N := fun x =>
    (Finset.univ.filter (fun i => dist x (ρ i) < ε)).min' (hnonempty x) with hidxdef
  have hball : ∀ x, dist x (ρ (idx x)) < ε := by
    intro x
    have hmem : idx x ∈ Finset.univ.filter (fun i => dist x (ρ i) < ε) := by
      simp only [hidxdef]
      exact Finset.min'_mem _ _
    exact (Finset.mem_filter.1 hmem).2
  have hleast : ∀ (x : D) (j : Fin N), (j : ℕ) < (idx x : ℕ) → ε ≤ dist x (ρ j) := by
    intro x j hj
    by_contra hcon
    rw [not_le] at hcon
    have hmemj : j ∈ Finset.univ.filter (fun i => dist x (ρ i) < ε) :=
      Finset.mem_filter.2 ⟨Finset.mem_univ j, hcon⟩
    have hle : idx x ≤ j :=
      Finset.min'_le (Finset.univ.filter (fun i => dist x (ρ i) < ε)) j hmemj
    rw [Fin.le_def] at hle
    omega
  have hcellmem : ∀ x, x ∈ cell ρ ε (idx x) := fun x => ⟨hball x, hleast x⟩

  set q : Fin N → NNReal := fun i => ENNReal.toNNReal (Q (cell ρ ε i)) with hqdef
  have htinf : ∀ i, Q (cell ρ ε i) ≠ ⊤ := fun i => ne_of_lt (measure_lt_top Q (cell ρ ε i))
  have hdj : Pairwise (Function.onFun Disjoint (fun i => cell ρ ε i)) :=
    fun i j hij => cell_disjoint ρ ε hij
  have hcells : ∀ i, MeasurableSet (cell ρ ε i) := fun i => measurable_cell ρ ε i
  have huni : (⋃ i : Fin N, cell ρ ε i) = Set.univ :=
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.2 ⟨idx x, hcellmem x⟩
  have hsumENN : ∑ i, Q (cell ρ ε i) = 1 := by
    have h1 : Q (⋃ i : Fin N, cell ρ ε i) = ∑' i : Fin N, Q (cell ρ ε i) :=
      measure_iUnion hdj hcells
    rw [huni, measure_univ] at h1
    calc ∑ i, Q (cell ρ ε i) = ∑' i : Fin N, Q (cell ρ ε i) := (tsum_fintype _).symm
      _ = 1 := h1.symm

  have hg2 : Measurable fun x : D => ρ (idx x) := by
    intro S hS
    set F : Finset (Fin N) := Finset.univ.filter (fun i => ρ i ∈ S) with hFdef
    have hpre : (fun x : D => ρ (idx x)) ⁻¹' S
        = ⋃ i : ↥(F : Set (Fin N)), cell ρ ε (i : Fin N) := by
      ext x
      simp only [mem_preimage, Set.mem_iUnion]
      constructor
      · intro hx
        refine ⟨⟨idx x, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩)⟩, ?_⟩
        exact hcellmem x
      · rintro ⟨i, hxcell⟩
        have hidxeq : idx x = (i : Fin N) := by
          by_contra hne2
          exact (Set.disjoint_right.1 (cell_disjoint ρ ε hne2) hxcell (hcellmem x)).elim
        simp only [hidxeq]
        exact (Finset.mem_filter.1 (Finset.mem_coe.1 i.property)).2
    rw [hpre]
    haveI : Fintype ↥(F : Set (Fin N)) := FinsetCoe.fintype F
    exact MeasurableSet.iUnion fun i => hcells i

  set g : D → D × D := fun x => (x, ρ (idx x)) with hgdef
  have hmg : Measurable g := measurable_id.prodMk hg2
  set γ : Measure (D × D) := Q.map g with hγdef
  have hγ1 : γ.map Prod.fst = Q := by
    have hcomp : Prod.fst ∘ g = id := funext fun _ => rfl
    rw [hγdef, Measure.map_map measurable_fst hmg, hcomp, Measure.map_id]
  have hγ2 : γ.map Prod.snd = atomicMeasure q ρ := by
    have hcomp : Prod.snd ∘ g = fun x : D => ρ (idx x) := funext fun _ => rfl
    rw [hγdef, Measure.map_map measurable_snd hmg, hcomp]
    refine Measure.ext fun S hS => ?_
    set F : Finset (Fin N) := Finset.univ.filter (fun i => ρ i ∈ S) with hFdef2
    have hpre : (fun x : D => ρ (idx x)) ⁻¹' S
        = ⋃ i : ↥(F : Set (Fin N)), cell ρ ε (i : Fin N) := by
      ext x
      simp only [mem_preimage, Set.mem_iUnion]
      constructor
      · intro hx
        refine ⟨⟨idx x, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hx⟩)⟩, ?_⟩
        exact hcellmem x
      · rintro ⟨i, hxcell⟩
        have hidxeq : idx x = (i : Fin N) := by
          by_contra hne2
          exact (Set.disjoint_right.1 (cell_disjoint ρ ε hne2) hxcell (hcellmem x)).elim
        simp only [hidxeq]
        exact (Finset.mem_filter.1 (Finset.mem_coe.1 i.property)).2
    haveI : Fintype ↥(F : Set (Fin N)) := FinsetCoe.fintype F
    have hpair : Pairwise (Function.onFun Disjoint (fun i : ↥(F : Set (Fin N)) => cell ρ ε (i : Fin N))) :=
      fun i j hij => cell_disjoint ρ ε (fun h => hij (Subtype.ext h))
    calc (Q.map (fun x : D => ρ (idx x))) S
        = Q ((fun x : D => ρ (idx x)) ⁻¹' S) := Measure.map_apply hg2 hS
      _ = Q (⋃ i : ↥(F : Set (Fin N)), cell ρ ε (i : Fin N)) := by rw [hpre]
      _ = ∑' i : ↥(F : Set (Fin N)), Q (cell ρ ε (i : Fin N)) :=
          measure_iUnion hpair fun i => hcells i
      _ = ∑ i ∈ F, Q (cell ρ ε i) := by
          rw [tsum_fintype]
          exact (Finset.sum_subtype F (fun _ => Finset.mem_coe)
            (fun i => Q (cell ρ ε i))).symm
      _ = (atomicMeasure q ρ) S := by
          rw [atomicMeasure, Measure.finsetSum_apply Finset.univ
            (fun i => q i • Measure.dirac (ρ i)) S]
          rw [← Finset.sum_subset F.subset_univ ?off]
          · refine Finset.sum_congr rfl fun i hi => ?_
            by_cases hmem : ρ i ∈ S
            · have hdir : (Measure.dirac (ρ i)) S = 1 := by
                rw [Measure.dirac_apply, Set.indicator_of_mem hmem, Pi.one_apply]
              rw [Measure.smul_apply, hdir, ENNReal.smul_one]
              exact (ENNReal.coe_toNNReal (htinf i)).symm
            · exact absurd (Finset.mem_filter.1 hi).2 hmem
          · intro i _ hi
            have hni : ¬ (ρ i ∈ S) := fun h =>
              hi (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)
            rw [Measure.smul_apply, Measure.dirac_apply, Set.indicator_of_notMem hni, smul_zero]

  have hweights : (∑ i, (q i : ℝ)) = 1 := by
    have hcoe : ∀ i, ((q i : NNReal) : ℝ) = (Q (cell ρ ε i)).toReal := by
      intro i
      have h2 : (((Q (cell ρ ε i)).toNNReal : NNReal) : ENNReal) = Q (cell ρ ε i) :=
        ENNReal.coe_toNNReal (htinf i)
      calc ((q i : NNReal) : ℝ)
          = (((((Q (cell ρ ε i)).toNNReal : NNReal) : ENNReal))).toReal := by
            rw [ENNReal.coe_toReal]
        _ = (Q (cell ρ ε i)).toReal := by rw [h2]
    rw [Finset.sum_congr rfl fun i _ => hcoe i]
    rw [← ENNReal.toReal_sum (fun a _ => htinf a), hsumENN]
    simp

  have hcost : (∫ p, dist p.1 p.2 ∂γ) ≤ ε := by
    have hFmeas : Measurable fun x : D => dist x (ρ (idx x)) :=
      ((Continuous.dist continuous_fst continuous_snd).measurable).comp hmg
    have hint : Integrable (fun x : D => dist x (ρ (idx x))) Q :=
      (integrable_const ε).mono hFmeas.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simp only [Real.norm_eq_abs, abs_of_pos hε, abs_of_nonneg dist_nonneg]
          exact le_of_lt (hball x))
    have hmono : ∫ x : D, dist x (ρ (idx x)) ∂Q ≤ ∫ _ : D, ε ∂Q :=
      integral_mono hint (integrable_const ε) (fun _ => le_of_lt (hball _))
    rw [integral_const, probReal_univ, one_smul] at hmono
    calc (∫ p, dist p.1 p.2 ∂γ)
        = ∫ x : D, dist (g x).1 (g x).2 ∂Q := by
          rw [hγdef]
          exact integral_map hmg.aemeasurable
            ((Continuous.dist continuous_fst continuous_snd).aestronglyMeasurable)
      _ = ∫ x : D, dist x (ρ (idx x)) ∂Q := rfl
      _ ≤ ε := hmono
  have hbdd : BddBelow {c : ℝ | ∃ γ : Measure (D × D), γ ∈ coupling Q (atomicMeasure q ρ) ∧
      (∫ p, dist p.1 p.2 ∂γ) ≤ c} :=
    ⟨0, fun c ⟨γ, _, hle⟩ =>
      le_trans (integral_nonneg (fun _ => dist_nonneg)) hle⟩
  have hmem : ε ∈ {c : ℝ | ∃ γ : Measure (D × D), γ ∈ coupling Q (atomicMeasure q ρ) ∧
      (∫ p, dist p.1 p.2 ∂γ) ≤ c} := ⟨γ, ⟨hγ1, hγ2⟩, hcost⟩
  exact ⟨N, NeZero.of_pos hNpos, q, ρ, hweights, csInf_le hbdd hmem⟩

end Qatlib.Papers.LatentPQCTran26.MainResults.FiniteCatalog
