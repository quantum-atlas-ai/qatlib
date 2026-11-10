/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Order.Interval.Set.Defs
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Curve.Distance
import Mathlib.Algebra.Order.Field.Pi
import Mathlib.Data.List.Sort
import Mathlib.Order.Interval.Set.UnorderedInterval
import Mathlib.Topology.MetricSpace.Infsep
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti.Contour

open Set

private theorem min_pairwise_distance_pos {crossings : Finset ℝ} (h_card : 2 ≤ crossings.card) :
    ∃ d > 0, ∀ t₁ ∈ crossings, ∀ t₂ ∈ crossings, t₁ ≠ t₂ → d ≤ |t₁ - t₂| := by
  have h_nt : (↑crossings : Set ℝ).Nontrivial := by
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp h_card
    exact ⟨p, hp, q, hq, hpq⟩
  refine ⟨(↑crossings : Set ℝ).infsep,
    Set.infsep_pos.mpr ⟨crossings.finite_toSet.einfsep_pos, h_nt.einfsep_lt_top⟩,
    fun t₁ ht₁ t₂ ht₂ ht_ne => ?_⟩
  have h := Set.infsep_le_dist_of_mem (s := (↑crossings : Set ℝ))
    (Finset.mem_coe.mpr ht₁) (Finset.mem_coe.mpr ht₂) ht_ne
  rwa [Real.dist_eq] at h

private theorem crossings_bounded_from_endpoints {a b : ℝ} {crossings : Finset ℝ}
    (h_nonempty : crossings.Nonempty) (h_Ioo : ∀ t ∈ crossings, t ∈ Ioo a b) :
    ∃ c > 0, ∀ t ∈ crossings, a + c ≤ t ∧ t ≤ b - c := by
  obtain ⟨t_min, ht_min_mem, ht_min⟩ :=
    Finset.exists_min_image crossings (fun t => min (t - a) (b - t)) h_nonempty
  have h0 := h_Ioo t_min ht_min_mem
  refine ⟨min (t_min - a) (b - t_min),
    lt_min (by linarith [h0.1]) (by linarith [h0.2]), fun t ht => ?_⟩
  have h_ge := ht_min t ht
  exact ⟨by linarith [h_ge.trans (min_le_left (t - a) (b - t))],
    by linarith [h_ge.trans (min_le_right (t - a) (b - t))]⟩

private theorem crossings_bounded_from_exceptional {crossings P : Finset ℝ}
    (h_nonempty : crossings.Nonempty) (h_off : ∀ t ∈ crossings, t ∉ P) :
    ∃ c > 0, ∀ t ∈ crossings, ∀ p ∈ P, c ≤ |t - p| := by
  by_cases hP : P = ∅
  · exact ⟨1, one_pos, fun _ _ p hp => absurd (hP ▸ hp) (Finset.notMem_empty p)⟩
  · obtain ⟨p₀, hp₀⟩ := Finset.nonempty_iff_ne_empty.mpr hP
    obtain ⟨t₀, ht₀⟩ := h_nonempty
    obtain ⟨m, hm_mem, hm⟩ :=
      Finset.exists_min_image (crossings ×ˢ P) (fun q => |q.1 - q.2|)
        ⟨(t₀, p₀), Finset.mem_product.mpr ⟨ht₀, hp₀⟩⟩
    rw [Finset.mem_product] at hm_mem
    refine ⟨|m.1 - m.2|, abs_pos.mpr fun h_eq =>
      h_off m.1 hm_mem.1 (sub_eq_zero.mp h_eq ▸ hm_mem.2), ?_⟩
    exact fun t ht p hp => hm (t, p) (Finset.mem_product.mpr ⟨ht, hp⟩)

theorem exists_common_window_radius {a b : ℝ} {crossings P : Finset ℝ}
    (h_nonempty : crossings.Nonempty) (h_Ioo : ∀ t ∈ crossings, t ∈ Ioo a b)
    (h_off : ∀ t ∈ crossings, t ∉ P) :
    ∃ r > 0,
      (∀ t ∈ crossings, a + r ≤ t ∧ t ≤ b - r) ∧
      (∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|) ∧
      (∀ t ∈ crossings, ∀ p ∈ P, r < |t - p|) := by
  obtain ⟨c, hc_pos, h_endpts⟩ := crossings_bounded_from_endpoints h_nonempty h_Ioo
  obtain ⟨e, he_pos, h_exc⟩ := crossings_bounded_from_exceptional h_nonempty h_off
  by_cases h_card_one : crossings.card = 1
  · refine ⟨min c (e / 2), lt_min hc_pos (by linarith), fun t ht => ?_, ?_, fun t ht p hp => ?_⟩
    · obtain ⟨h1, h2⟩ := h_endpts t ht
      exact ⟨by linarith [min_le_left c (e / 2)], by linarith [min_le_left c (e / 2)]⟩
    · intro t ht t' ht' ht_ne
      obtain ⟨u, hu⟩ := Finset.card_eq_one.mp h_card_one
      rw [hu, Finset.mem_singleton] at ht ht'
      exact absurd (ht'.trans ht.symm) ht_ne
    · linarith [h_exc t ht p hp, min_le_right c (e / 2)]
  · have h_card : 2 ≤ crossings.card := by
      have := Finset.card_pos.mpr h_nonempty
      omega
    obtain ⟨d, hd_pos, h_dist⟩ := min_pairwise_distance_pos h_card
    refine ⟨min c (min (e / 2) (d / 4)),
      lt_min hc_pos (lt_min (by linarith) (by linarith)),
      fun t ht => ?_, fun t ht t' ht' ht_ne => ?_, fun t ht p hp => ?_⟩
    · obtain ⟨h1, h2⟩ := h_endpts t ht
      exact ⟨by linarith [min_le_left c (min (e / 2) (d / 4))],
        by linarith [min_le_left c (min (e / 2) (d / 4))]⟩
    · have h_d := h_dist t' ht' t ht ht_ne
      rw [abs_sub_comm] at h_d
      linarith [(min_le_right c (min (e / 2) (d / 4))).trans (min_le_right (e / 2) (d / 4))]
    · linarith [h_exc t ht p hp,
        (min_le_right c (min (e / 2) (d / 4))).trans (min_le_left (e / 2) (d / 4))]

theorem exists_common_window_radius_le {a b : ℝ} {crossings : Finset ℝ}
    (h_Ioo : ∀ t ∈ crossings, t ∈ Ioo a b) (R : ℝ → ℝ) (hR_pos : ∀ t ∈ crossings, 0 < R t) :
    ∃ r > 0,
      (∀ t ∈ crossings, a + r < t ∧ t < b - r) ∧
      (∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → 2 * r < |t - t'|) ∧
      (∀ t ∈ crossings, r ≤ R t) := by
  classical
  rcases crossings.eq_empty_or_nonempty with rfl | h_nonempty
  · exact ⟨1, one_pos, by simp, by simp, by simp⟩
  obtain ⟨r₀, hr₀_pos, h_endpts, h_pair, -⟩ :=
    exists_common_window_radius (P := ∅) h_nonempty h_Ioo fun t _ => Finset.notMem_empty t

  obtain ⟨r, hr_pos, hr_all⟩ := Pi.exists_forall_pos_add_lt
    (ι := Option {t // t ∈ crossings}) (x := fun _ => (0 : ℝ))
    (y := fun i => i.elim r₀ fun t => R t.1)
    (fun i => by
      cases i with
      | none => simpa using hr₀_pos
      | some t => simpa using hR_pos t.1 t.2)
  have hr_lt : r < r₀ := by simpa using hr_all none
  exact ⟨r, hr_pos, fun t ht => ⟨by linarith [(h_endpts t ht).1], by
    linarith [(h_endpts t ht).2]⟩,
    fun t ht t' ht' hne => by linarith [h_pair t ht t' ht' hne],
    fun t ht => le_of_lt (by simpa using hr_all (some ⟨t, ht⟩))⟩

theorem eq_of_mem_window_of_eq_of_le_of_lt {α : Type*} {γ : ℝ → α} {s : α} {a b : ℝ}
    {crossings : Finset ℝ} {r t_i : ℝ} (h_endpts : a + r ≤ t_i ∧ t_i ≤ b - r)
    (h_pairwise : ∀ t' ∈ crossings, t' ≠ t_i → r < |t_i - t'|)
    (h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ crossings)
    {t : ℝ} (ht : t ∈ Icc (t_i - r) (t_i + r)) (h_eq : γ t = s) :
    t = t_i := by
  obtain ⟨h_ge, h_le⟩ := h_endpts
  have h_t_cross : t ∈ crossings :=
    h_complete t ⟨by linarith [ht.1], by linarith [ht.2]⟩ h_eq
  by_contra h_ne
  have h_dist := h_pairwise t h_t_cross h_ne
  have : |t_i - t| ≤ r := by
    rw [abs_sub_comm, abs_le]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  linarith [abs_nonneg (t_i - t)]

theorem eq_of_mem_window_of_eq {α : Type*} {γ : ℝ → α} {s : α} {a b : ℝ}
    {crossings : Finset ℝ} {r : ℝ} (h_endpts : ∀ t ∈ crossings, a + r ≤ t ∧ t ≤ b - r)
    (h_pairwise : ∀ t ∈ crossings, ∀ t' ∈ crossings, t' ≠ t → r < |t - t'|)
    (h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ crossings) {t_i : ℝ} (ht_i : t_i ∈ crossings)
    {t : ℝ} (ht : t ∈ Icc (t_i - r) (t_i + r)) (h_eq : γ t = s) :
    t = t_i :=
  eq_of_mem_window_of_eq_of_le_of_lt (h_endpts t_i ht_i) (h_pairwise t_i ht_i) h_complete ht h_eq

theorem eq_of_mem_window_of_eq_of_lt_of_two_mul_lt {α : Type*} {γ : ℝ → α} {s : α} {a b : ℝ}
    {crossings : Finset ℝ} {r t_i : ℝ} (h_endpts : a + r < t_i ∧ t_i < b - r)
    (h_pairwise : ∀ t' ∈ crossings, t' ≠ t_i → 2 * r < |t_i - t'|)
    (h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ crossings)
    {t : ℝ} (ht : t ∈ Icc (t_i - r) (t_i + r)) (h_eq : γ t = s) :
    t = t_i := by
  have hr : 0 ≤ r := by linarith [ht.1, ht.2]
  exact eq_of_mem_window_of_eq_of_le_of_lt ⟨h_endpts.1.le, h_endpts.2.le⟩
    (fun t' ht' hne => by linarith [h_pairwise t' ht' hne]) h_complete ht h_eq

theorem exists_window_dist_lower_bound {γ : ℝ → ℂ} {s : ℂ} {t_i r : ℝ}
    (hγ_cont : ContinuousOn γ (Icc (t_i - r) (t_i + r)))
    (h_unique : ∀ t ∈ Icc (t_i - r) (t_i + r), γ t = s → t = t_i)
    {r' : ℝ} (hr'_pos : 0 < r') (hr'_le : r' ≤ r) :
    ∃ m > 0,
      (∀ t ∈ Icc (t_i - r) (t_i - r'), m ≤ ‖γ t - s‖) ∧
      (∀ t ∈ Icc (t_i + r') (t_i + r), m ≤ ‖γ t - s‖) := by
  have h_sub_l : uIcc (t_i - r) (t_i - r') ⊆ Icc (t_i - r) (t_i + r) := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_subset_Icc le_rfl (by linarith)
  have h_sub_r : uIcc (t_i + r') (t_i + r) ⊆ Icc (t_i - r) (t_i + r) := by
    rw [uIcc_of_le (by linarith)]
    exact Icc_subset_Icc (by linarith) le_rfl
  obtain ⟨ml, hml_pos, hml⟩ := exists_curve_dist_lower_bound (hγ_cont.mono h_sub_l)
    fun t ht h_eq => by
      have h_t := h_unique t (h_sub_l ht) h_eq
      rw [uIcc_of_le (by linarith)] at ht
      linarith [ht.2]
  obtain ⟨mr, hmr_pos, hmr⟩ := exists_curve_dist_lower_bound (hγ_cont.mono h_sub_r)
    fun t ht h_eq => by
      have h_t := h_unique t (h_sub_r ht) h_eq
      rw [uIcc_of_le (by linarith)] at ht
      linarith [ht.1]
  refine ⟨min ml mr, lt_min hml_pos hmr_pos, fun t ht => ?_, fun t ht => ?_⟩
  · exact (min_le_left _ _).trans (hml t (by rwa [uIcc_of_le (by linarith)]))
  · exact (min_le_right _ _).trans (hmr t (by rwa [uIcc_of_le (by linarith)]))

theorem exists_complement_windows_dist_lower_bound {γ : ℝ → ℂ} {s : ℂ} {a b : ℝ}
    {crossings : Finset ℝ} (hγ_cont : ContinuousOn γ (Icc a b))
    (h_complete : ∀ t ∈ Icc a b, γ t = s → t ∈ crossings)
    (r_at : ℝ → ℝ) (hr_pos : ∀ t ∈ crossings, 0 < r_at t) :
    ∃ m > 0, ∀ t ∈ Icc a b,
      (∀ t_i ∈ crossings, t ∉ Ioo (t_i - r_at t_i) (t_i + r_at t_i)) →
      m ≤ ‖γ t - s‖ := by
  classical
  set C : Set ℝ := {t ∈ Icc a b |
    ∀ t_i ∈ crossings, t ∉ Ioo (t_i - r_at t_i) (t_i + r_at t_i)} with hC_def
  have hC_subset : C ⊆ Icc a b := fun t ht => ht.1
  have hC_closed : IsClosed C := by
    have h_eq : C = Icc a b ∩ ⋂ t_i ∈ crossings, (Ioo (t_i - r_at t_i) (t_i + r_at t_i))ᶜ := by
      ext t
      simp only [hC_def, mem_setOf_eq, mem_inter_iff, mem_iInter, mem_compl_iff]
    rw [h_eq]
    exact isClosed_Icc.inter (isClosed_biInter fun _ _ => isOpen_Ioo.isClosed_compl)
  have hC_compact : IsCompact C := isCompact_Icc.of_isClosed_subset hC_closed hC_subset
  rcases C.eq_empty_or_nonempty with hC_empty | hC_ne
  · refine ⟨1, one_pos, fun t ht h_avoid => absurd ?_ (notMem_empty t)⟩
    have h_mem : t ∈ C := ⟨ht, h_avoid⟩
    rwa [hC_empty] at h_mem
  · obtain ⟨t_min, ht_min_mem, ht_min⟩ := hC_compact.exists_isMinOn hC_ne
      (((hγ_cont.mono hC_subset).sub continuousOn_const).norm)
    refine ⟨‖γ t_min - s‖, ?_, fun t ht h_avoid => ht_min ⟨ht, h_avoid⟩⟩
    refine norm_pos_iff.mpr (sub_ne_zero.mpr fun h_eq => ?_)
    have h_cross : t_min ∈ crossings := h_complete t_min (hC_subset ht_min_mem) h_eq
    exact ht_min_mem.2 t_min h_cross
      ⟨by linarith [hr_pos t_min h_cross], by linarith [hr_pos t_min h_cross]⟩

theorem sorted_crossing_gluing_induction {E : Type*} [NormedAddCommGroup E] {γ : ℝ → E} {s : E}
    {Q : ℝ → ℝ → Prop} {A b r m : ℝ}
    (h_piece : ∀ l u : ℝ, A ≤ l → l ≤ u → u ≤ b → (∀ t ∈ Icc l u, m ≤ ‖γ t - s‖) → Q l u)
    (hglue : ∀ l u₀ u : ℝ, l ≤ u₀ → u₀ ≤ u → Q l u₀ → Q u₀ u → Q l u) :
    ∀ (sorted : List ℝ), sorted.SortedLT → (sorted ≠ [] → 0 ≤ r) →
    ∀ a : ℝ, A ≤ a → a ≤ b → (∀ t ∈ sorted, a ≤ t - r) → (∀ t ∈ sorted, t + r ≤ b) →
      (∀ t ∈ sorted, ∀ t' ∈ sorted, t' ≠ t → 2 * r ≤ |t - t'|) →
      (∀ t ∈ sorted, Q (t - r) (t + r)) →
      (∀ u ∈ Icc a b, (∀ t ∈ sorted, u ∉ Ioo (t - r) (t + r)) → m ≤ ‖γ u - s‖) →
      Q a b := by
  intro sorted
  induction sorted with
  | nil =>
    intro _ _ a hA hab _ _ _ _ h_far
    exact h_piece a b hA hab le_rfl
      fun u hu => h_far u hu fun t ht => absurd ht (List.not_mem_nil)
  | cons t rest IH =>
    intro h_sorted hr a hA _ h_lo h_hi h_pair h_win h_far
    have hr_nonneg : 0 ≤ r := hr (List.cons_ne_nil t rest)
    have h_head_lo : a ≤ t - r := h_lo t List.mem_cons_self
    have h_head_hi : t + r ≤ b := h_hi t List.mem_cons_self
    have h_rest_above : ∀ t' ∈ rest, t + r ≤ t' - r := fun t' ht' => by
      have h_lt : t < t' := (List.pairwise_cons.mp h_sorted.pairwise).1 t' ht'
      have h_sep := h_pair t List.mem_cons_self t' (List.mem_cons_of_mem t ht') (ne_of_gt h_lt)
      rw [abs_sub_comm, abs_of_pos (by linarith)] at h_sep
      linarith
    have h_left : Q a (t - r) := by
      refine h_piece a (t - r) hA h_head_lo (by linarith) fun u hu => ?_
      refine h_far u ⟨hu.1, by linarith [hu.2]⟩ fun t' ht' h_in => ?_
      rcases List.mem_cons.mp ht' with rfl | h_rest
      · linarith [hu.2, h_in.1]
      · linarith [hu.2, h_in.1, h_rest_above t' h_rest]
    have h_rest : Q (t + r) b := IH
      ((List.pairwise_cons.mp h_sorted.pairwise).2).sortedLT (fun _ => hr_nonneg) (t + r)
      (by linarith) h_head_hi (fun t' ht' => h_rest_above t' ht')
      (fun t' ht' => h_hi t' (List.mem_cons_of_mem t ht'))
      (fun t' ht' t'' ht'' hne => h_pair t' (List.mem_cons_of_mem t ht')
        t'' (List.mem_cons_of_mem t ht'') hne)
      (fun t' ht' => h_win t' (List.mem_cons_of_mem t ht'))
      (fun u hu h_avoid => h_far u ⟨by linarith [hu.1], hu.2⟩ fun t' ht' => by
        rcases List.mem_cons.mp ht' with rfl | h_rest
        · exact fun h_in => absurd hu.1 (not_le.mpr h_in.2)
        · exact h_avoid t' h_rest)
    exact hglue a (t + r) b (h_head_lo.trans (by linarith)) h_head_hi
      (hglue a (t - r) (t + r) h_head_lo (by linarith) h_left (h_win t List.mem_cons_self)) h_rest

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
