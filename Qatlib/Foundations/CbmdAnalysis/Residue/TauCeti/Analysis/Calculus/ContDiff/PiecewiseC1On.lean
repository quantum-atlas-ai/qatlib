/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Calculus.ContDiff.ClosedInterval
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.MeasureTheory.Integral.IntervalIntegral.DerivIntegrable
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Order.Interval.Finite
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Topology.Order.Interval

/-!
# Piecewise C¹ functions on intervals

This module defines `IsPiecewiseC1On` using finite interior breakpoints and C¹ regularity on the
resulting pieces. It proves closure, restriction, and gluing properties, together with
derivative integrability and boundedness needed for the contour analysis supporting
[WangEtAl2026].

## Main statements

* `IsPiecewiseC1On.if_le`: gluing at a shared endpoint.
* `IsPiecewiseC1On.intervalIntegrable_deriv`: integrability of the derivative.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

namespace TauCeti

open Filter MeasureTheory Set Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → E} {a b : ℝ}

/-- Piecewise C¹ regularity on an unordered closed interval, expressed by continuity and a
finite set of interior breakpoints. -/
def IsPiecewiseC1On (γ : ℝ → E) (a b : ℝ) : Prop :=
  ContinuousOn γ (uIcc a b) ∧
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d)

/-- Unfolds piecewise C¹ regularity into continuity and C¹ regularity on subintervals whose
interiors avoid a finite breakpoint set. -/
theorem isPiecewiseC1On_iff :
    IsPiecewiseC1On γ a b ↔
      ContinuousOn γ (uIcc a b) ∧
        ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
          ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
            ContDiffOn ℝ 1 γ (Icc c d) :=
  Iff.rfl

/-- A piecewise C¹ function is continuous on its parameter interval. -/
theorem IsPiecewiseC1On.continuousOn (h : IsPiecewiseC1On γ a b) :
    ContinuousOn γ (uIcc a b) :=
  h.1

/-- A C¹ function on an unordered closed interval is piecewise C¹ there. -/
theorem IsPiecewiseC1On.of_contDiffOn (h : ContDiffOn ℝ 1 γ (uIcc a b)) :
    IsPiecewiseC1On γ a b :=
  ⟨h.continuousOn, ∅, by simp, fun c d hcd _ => h.mono hcd⟩

/-- Constructs piecewise C¹ regularity from continuity and C¹ pieces separated by a finite set
of interior breakpoints. -/
theorem IsPiecewiseC1On.of_breakpoints (hcont : ContinuousOn γ (uIcc a b)) (p : Finset ℝ)
    (hp : ↑p ⊆ Ioo (min a b) (max a b))
    (hC1 : ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
      ContDiffOn ℝ 1 γ (Icc c d)) :
    IsPiecewiseC1On γ a b :=
  ⟨hcont, p, hp, hC1⟩

/-- A piecewise C¹ function possesses finitely many interior breakpoints outside which every
closed subinterval is C¹. -/
theorem IsPiecewiseC1On.exists_breakpoints (h : IsPiecewiseC1On γ a b) :
    ∃ p : Finset ℝ, ↑p ⊆ Ioo (min a b) (max a b) ∧
      ∀ c d : ℝ, Icc c d ⊆ uIcc a b → Disjoint (↑p : Set ℝ) (Ioo c d) →
        ContDiffOn ℝ 1 γ (Icc c d) :=
  h.2

/-- Piecewise C¹ regularity restricts to any contained unordered closed interval. -/
theorem IsPiecewiseC1On.mono (h : IsPiecewiseC1On γ a b) {c d : ℝ}
    (hsub : uIcc c d ⊆ uIcc a b) : IsPiecewiseC1On γ c d := by
  obtain ⟨p, _, hC1⟩ := h.exists_breakpoints
  refine ⟨h.continuousOn.mono hsub, p.filter (· ∈ Ioo (min c d) (max c d)),
    fun x hx => (Finset.mem_filter.mp hx).2, fun u v huv hdis => hC1 u v (huv.trans hsub) ?_⟩
  refine Set.disjoint_left.mpr fun x hxp hxuv => Set.disjoint_left.mp hdis ?_ hxuv
  rw [← Icc_min_max] at huv
  obtain ⟨hlu, hvu⟩ := (Icc_subset_Icc_iff (hxuv.1.trans hxuv.2).le).1 huv
  exact Finset.mem_filter.mpr ⟨hxp, hlu.trans_lt hxuv.1, hxuv.2.trans_le hvu⟩

/-- Piecewise C¹ regularity is unchanged when the interval endpoints are exchanged. -/
theorem isPiecewiseC1On_comm : IsPiecewiseC1On γ a b ↔ IsPiecewiseC1On γ b a := by
  simp only [isPiecewiseC1On_iff, Set.uIcc_comm a b, min_comm a b, max_comm a b]

/-- Reverses the endpoints in a piecewise C¹ regularity statement. -/
theorem IsPiecewiseC1On.symm (h : IsPiecewiseC1On γ a b) : IsPiecewiseC1On γ b a :=
  isPiecewiseC1On_comm.mp h

/-- The pointwise sum of two piecewise C¹ functions is piecewise C¹. -/
theorem IsPiecewiseC1On.add {γ₁ γ₂ : ℝ → E} (h₁ : IsPiecewiseC1On γ₁ a b)
    (h₂ : IsPiecewiseC1On γ₂ a b) : IsPiecewiseC1On (fun t => γ₁ t + γ₂ t) a b := by
  obtain ⟨p₁, hp₁, hC₁⟩ := h₁.exists_breakpoints
  obtain ⟨p₂, hp₂, hC₂⟩ := h₂.exists_breakpoints
  refine ⟨h₁.continuousOn.add h₂.continuousOn, p₁ ∪ p₂, by simpa using union_subset hp₁ hp₂,
    fun c d hcd hdisj => ?_⟩
  rw [Finset.coe_union, disjoint_union_left] at hdisj
  exact (hC₁ c d hcd hdisj.1).add (hC₂ c d hcd hdisj.2)

/-- The pointwise difference of two piecewise C¹ functions is piecewise C¹. -/
theorem IsPiecewiseC1On.sub {γ₁ γ₂ : ℝ → E} (h₁ : IsPiecewiseC1On γ₁ a b)
    (h₂ : IsPiecewiseC1On γ₂ a b) : IsPiecewiseC1On (fun t => γ₁ t - γ₂ t) a b := by
  obtain ⟨p₁, hp₁, hC₁⟩ := h₁.exists_breakpoints
  obtain ⟨p₂, hp₂, hC₂⟩ := h₂.exists_breakpoints
  refine ⟨h₁.continuousOn.sub h₂.continuousOn, p₁ ∪ p₂, by simpa using union_subset hp₁ hp₂,
    fun c d hcd hdisj => ?_⟩
  rw [Finset.coe_union, disjoint_union_left] at hdisj
  exact (hC₁ c d hcd hdisj.1).sub (hC₂ c d hcd hdisj.2)

/-- Multiplication by a constant scalar preserves piecewise C¹ regularity. -/
theorem IsPiecewiseC1On.const_smul {R : Type*} [Semiring R] [Module R E] [SMulCommClass ℝ R E]
    [ContinuousConstSMul R E] (c : R) (h : IsPiecewiseC1On γ a b) :
    IsPiecewiseC1On (fun t => c • γ t) a b := by
  obtain ⟨p, hp, hC1⟩ := h.exists_breakpoints
  exact ⟨h.continuousOn.const_smul c, p, hp,
    fun u v huv hdisj => (hC1 u v huv hdisj).const_smul c⟩

/-- Reflection of the parameter by `t ↦ c - t` preserves piecewise C¹ regularity on the
reflected interval. -/
theorem IsPiecewiseC1On.comp_const_sub (h : IsPiecewiseC1On γ a b) (c : ℝ) :
    IsPiecewiseC1On (fun t => γ (c - t)) (c - a) (c - b) := by
  obtain ⟨p, hp, hC1⟩ := h.exists_breakpoints
  have hmem : ∀ {t : ℝ}, t ∈ uIcc (c - a) (c - b) → c - t ∈ uIcc a b := fun ht => by
    rwa [← preimage_const_sub_uIcc] at ht
  refine IsPiecewiseC1On.of_breakpoints
    (h.continuousOn.comp (continuous_sub_left c).continuousOn fun _ ht => hmem ht)
    (p.image (c - ·)) ?_ fun d e hde hdisj => ?_
  · intro x hx
    simp only [Finset.coe_image, mem_image, Finset.mem_coe] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' := hp hy
    rw [min_sub_sub_left, max_sub_sub_left]
    exact ⟨by linarith [hy'.2], by linarith [hy'.1]⟩
  · have hsub : Icc (c - e) (c - d) ⊆ uIcc a b := fun s hs => by
      have hs' : c - s ∈ Icc d e := ⟨by linarith [hs.2], by linarith [hs.1]⟩
      simpa using hmem (hde hs')
    have hdisj' : Disjoint (↑p : Set ℝ) (Ioo (c - e) (c - d)) := by
      rw [Set.disjoint_left] at hdisj ⊢
      intro x hxp hx
      exact hdisj (Finset.mem_coe.2 (Finset.mem_image_of_mem _ hxp))
        ⟨by linarith [hx.2], by linarith [hx.1]⟩
    exact (hC1 _ _ hsub hdisj').comp (contDiff_const.sub contDiff_id).contDiffOn
      fun t ht => ⟨by linarith [ht.2], by linarith [ht.1]⟩

/-- Two piecewise C¹ functions agreeing at a common endpoint glue to a piecewise C¹ function on
the combined interval. -/
theorem IsPiecewiseC1On.if_le {δ : ℝ → E} {c : ℝ} (h₁ : IsPiecewiseC1On γ a b)
    (h₂ : IsPiecewiseC1On δ b c) (hab : a ≤ b) (hbc : b ≤ c) (hb : γ b = δ b) :
    IsPiecewiseC1On (fun t => if t ≤ b then γ t else δ t) a c := by
  classical
  obtain ⟨p₁, -, hC₁⟩ := h₁.exists_breakpoints
  obtain ⟨p₂, -, hC₂⟩ := h₂.exists_breakpoints
  have hac : a ≤ c := hab.trans hbc
  have hη₁ : EqOn (fun t => if t ≤ b then γ t else δ t) γ (Icc a b) := fun t ht =>
    if_pos ht.2
  have hη₂ : EqOn (fun t => if t ≤ b then γ t else δ t) δ (Icc b c) := fun t ht => by
    rcases ht.1.eq_or_lt with rfl | hlt
    · simp [hb]
    · exact if_neg (not_le.2 hlt)
  refine IsPiecewiseC1On.of_breakpoints ?_ ((p₁ ∪ p₂ ∪ {b}).filter (· ∈ Ioo a c)) ?_
    fun d e hde hdisj => ?_
  · rw [uIcc_of_le hac, ← Icc_union_Icc_eq_Icc hab hbc]
    refine ContinuousOn.union_of_isClosed ?_ ?_ isClosed_Icc isClosed_Icc
    · exact (uIcc_of_le hab ▸ h₁.continuousOn).congr hη₁
    · exact (uIcc_of_le hbc ▸ h₂.continuousOn).congr hη₂
  · intro x hx
    rw [min_eq_left hac, max_eq_right hac]
    exact (Finset.mem_filter.1 (Finset.mem_coe.1 hx)).2
  · rw [uIcc_of_le hac] at hde
    have hIoo : Ioo d e ⊆ Ioo a c := fun x hx =>
      ⟨(hde ⟨le_rfl, (hx.1.trans hx.2).le⟩).1.trans_lt hx.1,
        hx.2.trans_le (hde ⟨(hx.1.trans hx.2).le, le_rfl⟩).2⟩
    have hnot : ∀ x ∈ p₁ ∪ p₂ ∪ {b}, x ∉ Ioo d e := fun x hx hxde =>
      Set.disjoint_left.1 hdisj (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hx, hIoo hxde⟩)) hxde
    have hside : e ≤ b ∨ b ≤ d := by
      by_contra hcon
      push Not at hcon
      exact hnot b (by simp) ⟨hcon.2, hcon.1⟩
    rcases hside with heb | hbd
    · have hsub : Icc d e ⊆ Icc a b := fun t ht => ⟨(hde ht).1, ht.2.trans heb⟩
      refine (hC₁ d e (uIcc_of_le hab ▸ hsub) (Set.disjoint_left.2 fun x hx hxde =>
        hnot x (by simp [Finset.mem_coe.1 hx]) hxde)).congr fun t ht => hη₁ (hsub ht)
    · have hsub : Icc d e ⊆ Icc b c := fun t ht => ⟨hbd.trans ht.1, (hde ht).2⟩
      refine (hC₂ d e (uIcc_of_le hbc ▸ hsub) (Set.disjoint_left.2 fun x hx hxde =>
        hnot x (by simp [Finset.mem_coe.1 hx]) hxde)).congr fun t ht => hη₂ (hsub ht)

/-- A piecewise C¹ function is differentiable at every interior point outside a finite set. -/
theorem IsPiecewiseC1On.exists_finset_differentiableAt (h : IsPiecewiseC1On γ a b) :
    ∃ p : Finset ℝ,
      ∀ t ∈ Ioo (min a b) (max a b) \ (↑p : Set ℝ), DifferentiableAt ℝ γ t := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints
  refine ⟨p, fun t ht => ?_⟩
  obtain ⟨c, d, htcd, hsub, hdisj⟩ :=
    exists_Icc_subset_uIcc_disjoint p.finite_toSet.isClosed ht.1 ht.2
  exact ((hC1 c d hsub hdisj).differentiableOn one_ne_zero).differentiableAt
    (Icc_mem_nhds htcd.1 htcd.2)

/-- A piecewise C¹ function is differentiable at every interior point outside a countable set. -/
theorem IsPiecewiseC1On.exists_countable_differentiableAt (h : IsPiecewiseC1On γ a b) :
    ∃ P : Set ℝ, P.Countable ∧
      ∀ t ∈ Ioo (min a b) (max a b) \ P, DifferentiableAt ℝ γ t :=
  let ⟨p, hp⟩ := h.exists_finset_differentiableAt
  ⟨↑p, p.countable_toSet, hp⟩

/-- Near an interior point, a piecewise C¹ function is eventually differentiable within any set
excluding that point. -/
theorem IsPiecewiseC1On.eventually_differentiableAt (h : IsPiecewiseC1On γ a b) {t₀ : ℝ}
    (ht₀ : t₀ ∈ Ioo (min a b) (max a b)) {u : Set ℝ} (hu : t₀ ∉ u) :
    ∀ᶠ t in 𝓝[u] t₀, DifferentiableAt ℝ γ t := by
  obtain ⟨p, hp⟩ := h.exists_finset_differentiableAt
  have hcl : IsClosed ((↑p \ {t₀} : Set ℝ)) := (p.finite_toSet.subset (fun _ hx => hx.1)).isClosed
  filter_upwards [nhdsWithin_le_nhds (hcl.isOpen_compl.mem_nhds (by simp)),
    nhdsWithin_le_nhds (isOpen_Ioo.mem_nhds ht₀), self_mem_nhdsWithin] with t htc htIoo htu
  exact hp t ⟨htIoo, fun htp => htc ⟨htp, fun h_eq => hu (h_eq ▸ htu)⟩⟩

/-- The derivative of a piecewise C¹ function is interval integrable. -/
theorem IsPiecewiseC1On.intervalIntegrable_deriv (h : IsPiecewiseC1On γ a b) :
    IntervalIntegrable (fun t ↦ deriv γ t) volume a b := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints

  refine (Icc_induction_of_disjoint_Ioo (p := p)
    (Q := fun c d => IntervalIntegrable (fun t ↦ deriv γ t) volume c d)
    (fun c d hcd hsub hdisj =>
      ContDiffOn.intervalIntegrable_deriv ((hC1 c d hsub hdisj).mono (uIcc_of_le hcd).le) le_rfl)
    (fun _ _ _ _ _ h₁ h₂ => h₁.trans h₂) min_le_max Icc_min_max.subset).mono_set ?_
  rw [uIcc_of_le min_le_max, Icc_min_max]

/-- The derivative of a piecewise C¹ function has bounded image on its unordered closed
interval. -/
theorem IsPiecewiseC1On.isBounded_image_deriv (h : IsPiecewiseC1On γ a b) :
    Bornology.IsBounded (deriv γ '' uIcc a b) := by
  obtain ⟨p, -, hC1⟩ := h.exists_breakpoints

  rw [← Icc_min_max]
  refine Icc_induction_of_disjoint_Ioo (p := p)
    (Q := fun c d => Bornology.IsBounded (deriv γ '' Icc c d))
    (fun c d _ hsub hdisj => ContDiffOn.isBounded_image_deriv (hC1 c d hsub hdisj) le_rfl)
    (fun c m d hcm hmd h₁ h₂ => ?_) min_le_max Icc_min_max.subset
  change Bornology.IsBounded (deriv γ '' Icc c d)
  rw [← Icc_union_Icc_eq_Icc hcm hmd, image_union]
  exact h₁.union h₂

end TauCeti

end
end
end Qatlib.Foundations.CbmdAnalysis.Residue
