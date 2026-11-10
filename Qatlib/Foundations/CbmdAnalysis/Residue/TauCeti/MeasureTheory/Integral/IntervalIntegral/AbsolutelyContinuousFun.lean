/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

open MeasureTheory Set

namespace AbsolutelyContinuousOnInterval

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {γ V : ℝ → F} {a b : ℝ}

theorem integral_fderiv_apply_eq_sub (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) {φ : F → ℝ} (hφ : ContDiff ℝ 1 φ) :
    ∫ t in a..b, fderiv ℝ φ (γ t) (V t) = φ (γ b) - φ (γ a) := by
  refine Eq.trans (intervalIntegral.integral_congr_ae ?_)
    ((AbsolutelyContinuousOnInterval.comp_of_contDiffAt hγ) fun _ _ ↦ hφ.contDiffAt).integral_deriv_eq_sub
  filter_upwards [hV] with t ht hmem
  exact (HasFDerivAt.comp_hasDerivAt t (hφ.differentiable one_ne_zero (γ t)).hasFDerivAt
    (ht hmem)).deriv.symm

theorem intervalIntegrable_of_ae_hasDerivAt [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) :
    IntervalIntegrable V volume a b := by
  let e := (Module.finBasis ℝ F).equivFun.toContinuousLinearEquiv
  rw [intervalIntegrable_iff, IntegrableOn, ← e.integrable_comp_iff,
    integrable_pi_iff]
  intro i
  let L : F →L[ℝ] ℝ := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ ↦ ℝ) i).comp (e : F →L[ℝ] _)
  refine (intervalIntegrable_iff.1
    (LipschitzWith.comp_absolutelyContinuousOnInterval L.lipschitz hγ).intervalIntegrable_deriv).congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_uIoc]
  filter_upwards [hV] with t ht hmem
  exact (L.hasFDerivAt.comp_hasDerivAt t (ht hmem)).deriv

theorem intervalIntegrable_deriv_of_finiteDimensional [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntervalIntegrable (deriv γ) volume a b := by
  apply (AbsolutelyContinuousOnInterval.intervalIntegrable_of_ae_hasDerivAt hγ)
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt

theorem integral_eq_sub_of_ae_hasDerivAt [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt γ (V t) t) :
    ∫ t in a..b, V t = γ b - γ a := by
  refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun g ↦ ?_
  rw [← g.intervalIntegral_comp_comm ((AbsolutelyContinuousOnInterval.intervalIntegrable_of_ae_hasDerivAt hγ) hV), map_sub]
  simpa [g.fderiv] using
      (AbsolutelyContinuousOnInterval.integral_fderiv_apply_eq_sub hγ) hV g.contDiff

theorem integral_deriv_eq_sub_of_finiteDimensional [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    ∫ t in a..b, deriv γ t = γ b - γ a := by
  apply (AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt hγ)
  filter_upwards [hγ.boundedVariationOn.ae_differentiableAt_of_mem_uIcc] with t ht hmem
  exact (ht (uIoc_subset_uIcc hmem)).hasDerivAt

theorem norm_sub_le_integral_norm_deriv_sub [FiniteDimensional ℝ F] {p : ℝ → F}
    (hp : AbsolutelyContinuousOnInterval p a b) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (ha : p a = γ a) {t : ℝ} (ht : t ∈ Icc a b) :
    ‖p t - γ t‖ ≤ ∫ v in a..b, ‖deriv p v - deriv γ v‖ := by
  have hpI := (AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_of_finiteDimensional hp)
  have hγI := (AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_of_finiteDimensional hγ)
  have hsub : uIcc a t ⊆ uIcc a b := uIcc_subset_uIcc left_mem_uIcc
    ((uIcc_of_le (ht.1.trans ht.2)).symm ▸ ht)
  have heq : ∫ v in a..t, deriv p v - deriv γ v = p t - γ t := by
    rw [intervalIntegral.integral_sub (hpI.mono_set hsub) (hγI.mono_set hsub),
      AbsolutelyContinuousOnInterval.integral_deriv_eq_sub_of_finiteDimensional (hp.mono hsub),
      AbsolutelyContinuousOnInterval.integral_deriv_eq_sub_of_finiteDimensional (hγ.mono hsub), ha]
    abel
  rw [← heq]
  exact (intervalIntegral.norm_integral_le_integral_norm ht.1).trans
    (intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (Filter.Eventually.of_forall fun _ ↦ norm_nonneg _) (hpI.sub hγI).norm)

theorem integrableOn_deriv_Ioc [FiniteDimensional ℝ F]
    (hγ : AbsolutelyContinuousOnInterval γ a b) :
    IntegrableOn (deriv γ) (Ioc a b) :=
  (AbsolutelyContinuousOnInterval.intervalIntegrable_deriv_of_finiteDimensional hγ).1

end AbsolutelyContinuousOnInterval

namespace AbsolutelyContinuousOnInterval

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [FiniteDimensional ℝ A]
  {f f' g g' : ℝ → A} {a b : ℝ}

theorem integral_mul_deriv_eq_deriv_mul_of_ae_hasDerivAt
    (hf : AbsolutelyContinuousOnInterval f a b)
    (hg : AbsolutelyContinuousOnInterval g a b)
    (hff' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (f' t) t)
    (hgg' : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt g (g' t) t) :
    ∫ t in a..b, f t * g' t = f b * g b - f a * g a - ∫ t in a..b, f' t * g t := by
  have hprod : AbsolutelyContinuousOnInterval (fun t ↦ f t * g t) a b := by
    have hmul : ContDiff ℝ 1 (fun p : A × A ↦ p.1 * p.2) := contDiff_mul
    exact AbsolutelyContinuousOnInterval.comp_of_contDiffAt (F := A × A) (G := A)
      (γ := fun t ↦ (f t, g t)) (φ := fun p : A × A ↦ p.1 * p.2)
      (AbsolutelyContinuousOnInterval.prodMk (γ := f) (δ := g) hf hg)
      (fun _ _ ↦ hmul.contDiffAt)
  have hder : ∀ᵐ t, t ∈ uIoc a b →
      HasDerivAt (fun t ↦ f t * g t) (f' t * g t + f t * g' t) t := by
    filter_upwards [hff', hgg'] with t ht hu hmem
    exact (ht hmem).mul (hu hmem)
  have h := (AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt hprod) hder
  rw [intervalIntegral.integral_add
    (((AbsolutelyContinuousOnInterval.intervalIntegrable_of_ae_hasDerivAt hf) hff').mul_continuousOn hg.continuousOn)
    (((AbsolutelyContinuousOnInterval.intervalIntegrable_of_ae_hasDerivAt hg) hgg').continuousOn_mul hf.continuousOn)] at h
  exact eq_sub_of_add_eq' h

end AbsolutelyContinuousOnInterval

namespace AbsolutelyContinuousOnInterval

variable {f V : ℝ → ℝ} {a b : ℝ}

private theorem ae_hasDerivAt_log (h0 : ∀ t ∈ uIcc a b, f t ≠ 0)
    (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (V t) t) :
    ∀ᵐ t, t ∈ uIoc a b → HasDerivAt (fun t ↦ Real.log (f t)) (V t / f t) t := by
  filter_upwards [hV] with t ht hmem
  exact (ht hmem).log (h0 t (uIoc_subset_uIcc hmem))

theorem intervalIntegrable_div_of_ae_hasDerivAt (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (V t) t) :
    IntervalIntegrable (fun t ↦ V t / f t) volume a b :=
  AbsolutelyContinuousOnInterval.intervalIntegrable_of_ae_hasDerivAt (AbsolutelyContinuousOnInterval.log hf h0) (ae_hasDerivAt_log h0 hV)

theorem integral_div_eq_log_sub_log (hf : AbsolutelyContinuousOnInterval f a b)
    (h0 : ∀ t ∈ uIcc a b, f t ≠ 0) (hV : ∀ᵐ t, t ∈ uIoc a b → HasDerivAt f (V t) t) :
    ∫ t in a..b, V t / f t = Real.log (f b) - Real.log (f a) :=
  AbsolutelyContinuousOnInterval.integral_eq_sub_of_ae_hasDerivAt (AbsolutelyContinuousOnInterval.log hf h0) (ae_hasDerivAt_log h0 hV)

end AbsolutelyContinuousOnInterval

namespace TauCeti.Probability

variable {f : ℝ → ℝ} {a x : ℝ}

theorem survival_eq_exp_integral_hazard {S : ℝ → ℝ}
    (hS : AbsolutelyContinuousOnInterval S a x) (hpos : ∀ t ∈ uIcc a x, 0 < S t)
    (hderiv : ∀ᵐ t, t ∈ uIoc a x → HasDerivAt S (-f t) t) :
    IntervalIntegrable (fun t => f t / S t) volume a x ∧
      S x = S a * Real.exp (-∫ t in a..x, f t / S t) := by
  have hne : ∀ t ∈ uIcc a x, S t ≠ 0 := fun t ht => (hpos t ht).ne'
  have hint : IntervalIntegrable (fun t => f t / S t) volume a x := by
    have h : (fun t => f t / S t) = -fun t => -f t / S t := by
      ext t
      simp [neg_div]
    rw [h]
    exact ((AbsolutelyContinuousOnInterval.intervalIntegrable_div_of_ae_hasDerivAt hS) hne hderiv).neg
  refine ⟨hint, ?_⟩
  have h := (AbsolutelyContinuousOnInterval.integral_div_eq_log_sub_log hS) hne hderiv
  simp only [neg_div, intervalIntegral.integral_neg] at h
  have ha : 0 < S a := hpos a left_mem_uIcc
  have hx : 0 < S x := hpos x right_mem_uIcc
  rw [h, Real.exp_sub, Real.exp_log hx, Real.exp_log ha]
  field_simp

end TauCeti.Probability

theorem IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral'
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : ℝ → F} {a b c : ℝ} (hf : IntervalIntegrable f volume a b) (hc : c ∈ uIcc a b) :
    AbsolutelyContinuousOnInterval (fun t ↦ ∫ v in c..t, f v) a b := by
  have hn := hf.norm.absolutelyContinuousOnInterval_intervalIntegral hc
  refine squeeze_zero' (Filter.Eventually.of_forall fun _ ↦
    Finset.sum_nonneg fun _ _ ↦ dist_nonneg) ?_ hn
  have he : ∀ᶠ E in AbsolutelyContinuousOnInterval.totalLengthFilter ⊓
      Filter.principal (AbsolutelyContinuousOnInterval.disjWithin a b),
      E ∈ AbsolutelyContinuousOnInterval.disjWithin a b :=
    Filter.eventually_inf_principal.mpr (by simp)
  filter_upwards [he] with E hE
  apply Finset.sum_le_sum
  intro i hi
  have hx := hf.mono_set (uIcc_subset_uIcc hc (hE.1 i hi).1)
  have hy := hf.mono_set (uIcc_subset_uIcc hc (hE.1 i hi).2)
  rw [dist_eq_norm, intervalIntegral.integral_interval_sub_left hx hy,
    Real.dist_eq, intervalIntegral.integral_interval_sub_left hx.norm hy.norm]
  exact intervalIntegral.norm_integral_le_abs_integral_norm

theorem ContinuousOn.absolutelyContinuousOnInterval_of_hasDerivAt_off_countable
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {f f' : ℝ → F} {a b : ℝ} {s : Set ℝ} (hf : ContinuousOn f (uIcc a b))
    (hs : s.Countable)
    (hd : ∀ t ∈ Ioo (min a b) (max a b) \ s, HasDerivAt f (f' t) t)
    (hi : IntervalIntegrable f' volume a b) : AbsolutelyContinuousOnInterval f a b := by
  have hbase : min a b ∈ uIcc a b := ⟨le_rfl, min_le_max⟩
  have hI := IntervalIntegrable.absolutelyContinuousOnInterval_intervalIntegral' hi hbase
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ ↦ f (min a b)) a b :=
    (LipschitzWith.const (f (min a b))).lipschitzOnWith.absolutelyContinuousOnInterval
  apply AbsolutelyContinuousOnInterval.congr (hc.add hI)
  intro t ht
  have hsub : uIcc (min a b) t ⊆ uIcc a b := uIcc_subset_uIcc hbase ht
  have hFTC := integral_eq_of_hasDerivAt_off_countable f f' hs (hf.mono hsub)
    (fun u hu ↦ hd u ⟨⟨by simpa only [min_eq_left ht.1] using hu.1.1,
      (by simpa only [max_eq_right ht.1] using hu.1.2 : u < t).trans_le ht.2⟩, hu.2⟩)
    (hi.mono_set hsub)
  change f (min a b) + (∫ u in min a b..t, f' u) = f t
  rw [hFTC]
  abel

end
end Qatlib.Foundations.CbmdAnalysis.Residue
