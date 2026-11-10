/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Order.Compact
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

def HasCauchyPVAt (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) (L : ℂ) : Prop :=
  (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b) ∧
    Tendsto (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 L)

theorem hasCauchyPVAt_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ} :
    HasCauchyPVAt γ a b f z₀ L ↔
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
          (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b) ∧
        Tendsto (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
          (𝓝[>] 0) (𝓝 L) :=
  Iff.rfl

theorem HasCauchyPVAt.of_tendsto {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ L : ℂ} {F : ℝ → ℂ}
    (hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 L))
    (h : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
        (fun t ↦ if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b ∧
      ∫ t in a..b, (if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) = F ε) :
    HasCauchyPVAt γ a b f z₀ L :=
  hasCauchyPVAt_iff.mpr ⟨h.mono fun _ hε ↦ hε.1, hF.congr' (h.mono fun _ hε ↦ hε.2.symm)⟩

def cauchyPVAt (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) : ℂ :=
  limUnder (𝓝[>] (0 : ℝ)) fun ε ↦
    ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0

def CauchyPVExistsAt (γ : ℝ → ℂ) (a b : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ L : ℂ, HasCauchyPVAt γ a b f z₀ L

theorem cauchyPVExistsAt_iff {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} :
    CauchyPVExistsAt γ a b f z₀ ↔ ∃ L, HasCauchyPVAt γ a b f z₀ L :=
  Iff.rfl

theorem CauchyPVExistsAt.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) : CauchyPVExistsAt γ a b f z₀ :=
  ⟨L, h⟩

theorem aestronglyMeasurable_truncated {α E : Type*} [MeasurableSpace α] [TopologicalSpace E]
    [Zero E] {μ : MeasureTheory.Measure α} {γ : α → ℂ} {F : α → E} {z₀ : ℂ} {ε : ℝ}
    (hγ : AEMeasurable γ μ) (hF : MeasureTheory.AEStronglyMeasurable F μ) :
    MeasureTheory.AEStronglyMeasurable (fun t => if ‖γ t - z₀‖ > ε then F t else 0) μ := by
  have h : (fun t => if ‖γ t - z₀‖ > ε then F t else 0)
      = {t | ε < ‖γ t - z₀‖}.indicator F := by
    funext t
    simp [Set.indicator_apply]
  rw [h]
  exact hF.indicator₀ (nullMeasurableSet_lt aemeasurable_const ((hγ.sub_const z₀).norm))

theorem intervalIntegrable_truncated_mul_deriv {γ : ℝ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {a b M ε : ℝ}
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume a b)
    (h_aesm : MeasureTheory.AEStronglyMeasurable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (h_bd : ∀ t : ℝ, ε < ‖γ t - z₀‖ → ‖f (γ t)‖ ≤ M) :
    IntervalIntegrable (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      MeasureTheory.volume a b := by
  refine (hderiv_int.norm.const_mul M).mono_fun h_aesm (.of_forall fun t => ?_)
  (try dsimp only)
  split_ifs with h_far
  · rw [norm_mul, Real.norm_eq_abs]
    exact (mul_le_mul_of_nonneg_right (h_bd t h_far) (norm_nonneg _)).trans (le_abs_self _)
  · rw [norm_zero]
    positivity

theorem intervalIntegrable_pow_inv_mul_deriv_truncated {γ : ℝ → ℂ} {z₀ : ℂ} {a b : ℝ}
    (c : ℂ) (k : ℕ) (hγ_cont : ContinuousOn γ (Set.uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume a b)
    {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then c / (γ t - z₀) ^ k * deriv γ t else 0)
      MeasureTheory.volume a b := by
  have hγ_aem : AEMeasurable γ (MeasureTheory.volume.restrict (Set.uIoc a b)) :=
    (hγ_cont.mono Set.uIoc_subset_uIcc).aemeasurable measurableSet_uIoc
  refine intervalIntegrable_truncated_mul_deriv (f := fun z => c / (z - z₀) ^ k)
    (M := ‖c‖ / ε ^ k) hderiv_int
    (aestronglyMeasurable_truncated hγ_aem
      ((((hγ_aem.sub_const z₀).pow_const k).const_div c).aestronglyMeasurable.mul
        hderiv_int.def'.aestronglyMeasurable)) fun t h_far => ?_
  rw [norm_div, norm_pow]
  gcongr

theorem intervalIntegrable_inv_sub_truncated {γ : ℝ → ℂ} {z₀ : ℂ} {a b : ℝ}
    (hγ_cont : ContinuousOn γ (Set.uIcc a b))
    (hderiv_int : IntervalIntegrable (fun t => deriv γ t) MeasureTheory.volume a b)
    {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (fun t => if ‖γ t - z₀‖ > ε then (γ t - z₀)⁻¹ * deriv γ t else 0)
      MeasureTheory.volume a b := by
  simpa using
    intervalIntegrable_pow_inv_mul_deriv_truncated (z₀ := z₀) 1 1 hγ_cont hderiv_int hε

theorem ae_logDeriv_sub_eq_truncated {γ : ℝ → ℂ} {z₀ : ℂ} {a b ε : ℝ} (hab : a ≤ b)
    (hfar : ∀ s ∈ Set.Ioo a b, ε < ‖γ s - z₀‖) :
    ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc a b →
      deriv (fun r ↦ γ r - z₀) s / (γ s - z₀) =
        (if ε < ‖γ s - z₀‖ then (γ s - z₀)⁻¹ * deriv γ s else 0) := by
  filter_upwards [MeasureTheory.volume.ae_ne b] with s hs_ne hmem
  rw [Set.uIoc_of_le hab] at hmem
  rw [if_pos (hfar s ⟨hmem.1, hmem.2.lt_of_ne hs_ne⟩), deriv_sub_const, inv_mul_eq_div]

theorem intervalIntegrable_truncated_and_integral_truncated_eq_zero_of_norm_le {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {γ : ℝ → ℂ} {g : ℝ → E} {z₀ : ℂ} {a b ε : ℝ}
    (hnear : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc a b → ‖γ s - z₀‖ ≤ ε) :
    IntervalIntegrable (fun s => if ε < ‖γ s - z₀‖ then g s else 0)
        MeasureTheory.volume a b ∧
      ∫ s in a..b, (if ε < ‖γ s - z₀‖ then g s else 0) = 0 := by
  have hae : ∀ᵐ s ∂MeasureTheory.volume, s ∈ Set.uIoc a b →
      (if ε < ‖γ s - z₀‖ then g s else 0) = 0 := by
    filter_upwards [hnear] with s hs hmem using if_neg (not_lt.mpr (hs hmem))
  exact ⟨(intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : E)) MeasureTheory.volume a b).congr_ae
      (((MeasureTheory.ae_restrict_iff' measurableSet_uIoc).mpr hae).mono fun _ hs => hs.symm),
    intervalIntegral.integral_zero_ae hae⟩

theorem HasCauchyPVAt.intro {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (hint : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b)
    (htendsto : Tendsto
      (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) (𝓝[>] 0) (𝓝 L)) :
    HasCauchyPVAt γ a b f z₀ L :=
  ⟨hint, htendsto⟩

theorem HasCauchyPVAt.of_dist_lower_bound {γ : ℝ → ℂ} {z₀ : ℂ} {f : ℂ → ℂ}
    {a b m : ℝ} (hm_pos : 0 < m) (h_far : ∀ t ∈ Set.uIcc a b, m ≤ ‖γ t - z₀‖)
    (h_int_tr : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b) :
    HasCauchyPVAt γ a b f z₀ (∫ t in a..b, f (γ t) * deriv γ t) := by
  have h_ev : (fun ε : ℝ => ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      =ᶠ[𝓝[>] (0 : ℝ)] fun _ => ∫ t in a..b, f (γ t) * deriv γ t := by
    filter_upwards [Ioo_mem_nhdsGT hm_pos] with ε hε
    refine intervalIntegral.integral_congr fun t ht => ?_
    rw [if_pos (lt_of_lt_of_le hε.2 (h_far t ht))]
  exact HasCauchyPVAt.intro h_int_tr (Tendsto.congr' h_ev.symm tendsto_const_nhds)

theorem HasCauchyPVAt.tendsto {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) :
    Tendsto (fun ε ↦ ∫ t in a..b, if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0)
      (𝓝[>] 0) (𝓝 L) :=
  h.2

theorem HasCauchyPVAt.eventually_intervalIntegrable {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    {L : ℂ} (h : HasCauchyPVAt γ a b f z₀ L) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b :=
  h.1

theorem HasCauchyPVAt.cauchyPVAt_eq {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) : cauchyPVAt γ a b f z₀ = L :=
  h.2.limUnder_eq

theorem HasCauchyPVAt.unique {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L₁ L₂ : ℂ}
    (h₁ : HasCauchyPVAt γ a b f z₀ L₁) (h₂ : HasCauchyPVAt γ a b f z₀ L₂) : L₁ = L₂ :=
  tendsto_nhds_unique h₁.2 h₂.2

theorem CauchyPVExistsAt.hasCauchyPVAt_cauchyPVAt {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) :
    HasCauchyPVAt γ a b f z₀ (cauchyPVAt γ a b f z₀) := by
  obtain ⟨_, hL⟩ := h
  rwa [hL.cauchyPVAt_eq]

theorem HasCauchyPVAt.congr_along_curve {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) (h_eq : ∀ t ∈ Set.uIoo a b, f (γ t) = g (γ t)) :
    HasCauchyPVAt γ a b g z₀ L := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with ε hε
    refine (intervalIntegrable_congr_uIoo fun t ht => ?_).mp hε
    simp only [h_eq t ht]
  · refine Filter.Tendsto.congr (fun ε => intervalIntegral.integral_congr_uIoo fun t ht => ?_) h.2
    simp only [h_eq t ht]

theorem cauchyPVAt_congr_along_curve {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ}
    (h_eq : ∀ t ∈ Set.uIoo a b, f (γ t) = g (γ t)) :
    cauchyPVAt γ a b f z₀ = cauchyPVAt γ a b g z₀ := by
  unfold cauchyPVAt
  congr 1
  ext ε
  refine intervalIntegral.integral_congr_uIoo fun t ht => ?_
  simp only [h_eq t ht]

private theorem truncated_integrand_congr_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_eq : γ₁ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t)
    {ε : ℝ} (hε : 0 < ε) :
    (fun t => if ‖γ₁ t - z₀‖ > ε then f (γ₁ t) * deriv γ₁ t else 0)
      =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)]
    (fun t => if ‖γ₂ t - z₀‖ > ε then f (γ₂ t) * deriv γ₂ t else 0) := by
  filter_upwards [h_eq, h_deriv] with t ht htd
  by_cases hz : γ₁ t = z₀
  · rw [if_neg, if_neg] <;> simp [hz, ← ht, hε.not_gt]
  · simp only [ht, htd hz]

theorem HasCauchyPVAt.congr_curve_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ₁ a b f z₀ L)
    (h_eq : γ₁ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t) :
    HasCauchyPVAt γ₂ a b f z₀ L := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1, self_mem_nhdsWithin] with ε hε hpos
    exact (intervalIntegrable_congr_ae
      (truncated_integrand_congr_ae h_eq h_deriv (Set.mem_Ioi.mp hpos))).mp hε
  · refine Filter.Tendsto.congr' ?_ h.2
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact intervalIntegral.integral_congr_ae_restrict
      (truncated_integrand_congr_ae h_eq h_deriv (Set.mem_Ioi.mp hε))

private theorem truncated_integrand_eqOn_uIoo {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) (ε : ℝ) :
    Set.EqOn (fun t => if ‖γ₁ t - z₀‖ > ε then f (γ₁ t) * deriv γ₁ t else 0)
      (fun t => if ‖γ₂ t - z₀‖ > ε then f (γ₂ t) * deriv γ₂ t else 0) (Set.uIoo a b) :=
  fun _ ht => by simp only [h_eq ht, h_eq.deriv isOpen_Ioo ht]

theorem HasCauchyPVAt.congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ₁ a b f z₀ L) (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    HasCauchyPVAt γ₂ a b f z₀ L :=
  ⟨h.1.mono fun ε hε => IntervalIntegrable.congr_uIoo hε (truncated_integrand_eqOn_uIoo h_eq ε),
    h.2.congr fun ε => intervalIntegral.integral_congr_uIoo (truncated_integrand_eqOn_uIoo h_eq ε)⟩

theorem CauchyPVExistsAt.congr_curve_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ₁ a b f z₀)
    (h_eq : γ₁ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t) :
    CauchyPVExistsAt γ₂ a b f z₀ :=
  let ⟨_, hL⟩ := h
  CauchyPVExistsAt.intro (hL.congr_curve_ae h_eq h_deriv)

theorem CauchyPVExistsAt.congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ₁ a b f z₀) (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    CauchyPVExistsAt γ₂ a b f z₀ :=
  let ⟨_, hL⟩ := h
  CauchyPVExistsAt.intro (hL.congr_curve h_eq)

theorem cauchyPVAt_congr_curve_ae {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_eq : γ₁ =ᵐ[MeasureTheory.volume.restrict (Set.uIoc a b)] γ₂)
    (h_deriv : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc a b),
      γ₁ t ≠ z₀ → deriv γ₁ t = deriv γ₂ t) :
    cauchyPVAt γ₁ a b f z₀ = cauchyPVAt γ₂ a b f z₀ := by
  have hev : (fun ε => ∫ t in a..b, if ‖γ₁ t - z₀‖ > ε then f (γ₁ t) * deriv γ₁ t else 0)
      =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun ε => ∫ t in a..b, if ‖γ₂ t - z₀‖ > ε then f (γ₂ t) * deriv γ₂ t else 0) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact intervalIntegral.integral_congr_ae_restrict
      (truncated_integrand_congr_ae h_eq h_deriv (Set.mem_Ioi.mp hε))
  unfold cauchyPVAt Filter.limUnder
  rw [Filter.map_congr hev]

theorem cauchyPVAt_congr_curve {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_eq : Set.EqOn γ₁ γ₂ (Set.uIoo a b)) :
    cauchyPVAt γ₁ a b f z₀ = cauchyPVAt γ₂ a b f z₀ := by
  unfold cauchyPVAt
  congr 1
  ext ε
  exact intervalIntegral.integral_congr_uIoo (truncated_integrand_eqOn_uIoo h_eq ε)

theorem HasCauchyPVAt.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) (c : ℂ) :
    HasCauchyPVAt γ a b (fun z => c * f z) z₀ (c * L) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h.1] with ε hε
    simpa only [mul_ite, mul_zero, mul_assoc] using hε.const_mul c
  · simpa only [← intervalIntegral.integral_const_mul, mul_ite, mul_zero, mul_assoc] using
      h.2.const_mul c

theorem HasCauchyPVAt.add {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ} {L₁ L₂ : ℂ}
    (hf : HasCauchyPVAt γ a b f z₀ L₁) (hg : HasCauchyPVAt γ a b g z₀ L₂) :
    HasCauchyPVAt γ a b (fun z => f z + g z) z₀ (L₁ + L₂) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [hf.1, hg.1] with ε hfi hgi
    simpa only [ite_add_ite, add_zero, add_mul] using hfi.add hgi
  · refine (hf.2.add hg.2).congr' ?_
    filter_upwards [hf.1, hg.1] with ε hfi hgi
    simp only [← intervalIntegral.integral_add hfi hgi, ite_add_ite, add_zero, add_mul]

theorem HasCauchyPVAt.zero {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    HasCauchyPVAt γ a b (fun _ => 0) z₀ 0 := by
  refine ⟨?_, ?_⟩
  · filter_upwards with ε
    simpa only [zero_mul, ite_self] using intervalIntegrable_const
  · simpa only [zero_mul, ite_self, intervalIntegral.integral_zero] using tendsto_const_nhds

@[simp]
theorem cauchyPVAt_zero {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    cauchyPVAt γ a b (fun _ => 0) z₀ = 0 :=
  HasCauchyPVAt.zero.cauchyPVAt_eq

theorem HasCauchyPVAt.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    HasCauchyPVAt γ a a f z₀ 0 := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards with ε
    exact IntervalIntegrable.refl
  · simpa only [intervalIntegral.integral_same] using tendsto_const_nhds (x := (0 : ℂ))

theorem CauchyPVExistsAt.refl (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    CauchyPVExistsAt γ a a f z₀ :=
  CauchyPVExistsAt.intro (HasCauchyPVAt.refl γ a f z₀)

@[simp]
theorem cauchyPVAt_same (γ : ℝ → ℂ) (a : ℝ) (f : ℂ → ℂ) (z₀ : ℂ) :
    cauchyPVAt γ a a f z₀ = 0 :=
  (HasCauchyPVAt.refl γ a f z₀).cauchyPVAt_eq

theorem HasCauchyPVAt.sum {ι : Type*} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {f : ι → ℂ → ℂ} {L : ι → ℂ}
    {s : Finset ι} (h : ∀ i ∈ s, HasCauchyPVAt γ a b (f i) z₀ (L i)) :
    HasCauchyPVAt γ a b (fun z => ∑ i ∈ s, f i z) z₀ (∑ i ∈ s, L i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using HasCauchyPVAt.zero
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    exact (h j (Finset.mem_insert_self j s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem HasCauchyPVAt.of_avoidance {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Set.uIcc a b)) (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ z₀)
    (hf_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b) :
    HasCauchyPVAt γ a b f z₀ (∫ t in a..b, f (γ t) * deriv γ t) := by
  obtain ⟨t₀, ht₀, ht₀_min⟩ := isCompact_uIcc.exists_isMinOn
    Set.nonempty_uIcc (h_cont.sub continuousOn_const).norm
  have hpos : 0 < ‖γ t₀ - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (h_avoid t₀ ht₀))
  refine .of_dist_lower_bound hpos (fun t ht => ht₀_min ht) ?_
  filter_upwards [Ioo_mem_nhdsGT hpos] with ε hε
  refine (intervalIntegrable_congr fun t ht => ?_).mpr hf_int
  exact if_pos (hε.2.trans_le (ht₀_min (Set.uIoc_subset_uIcc ht)))

theorem HasCauchyPVAt.concat {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} {L₁ L₂ : ℂ}
    (h_ab : HasCauchyPVAt γ a b f z₀ L₁) (h_bc : HasCauchyPVAt γ b c f z₀ L₂) :
    HasCauchyPVAt γ a c f z₀ (L₁ + L₂) := by
  refine ⟨?_, ?_⟩
  · filter_upwards [h_ab.1, h_bc.1] with ε hab_int hbc_int
    exact hab_int.trans hbc_int
  · refine Filter.Tendsto.congr' ?_ (h_ab.2.add h_bc.2)
    filter_upwards [h_ab.1, h_bc.1] with ε hab_int hbc_int
    exact intervalIntegral.integral_add_adjacent_intervals hab_int hbc_int

theorem HasCauchyPVAt.concat_range {γ : ℝ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {n : ℕ} {t : ℕ → ℝ} {L : ℕ → ℂ}
    (h : ∀ k < n, HasCauchyPVAt γ (t k) (t (k + 1)) f z₀ (L k)) :
    HasCauchyPVAt γ (t 0) (t n) f z₀ (∑ k ∈ Finset.range n, L k) := by
  induction n with
  | zero => simpa using HasCauchyPVAt.refl γ (t 0) f z₀
  | succ n ih =>
      have hprefix : HasCauchyPVAt γ (t 0) (t n) f z₀
          (∑ k ∈ Finset.range n, L k) :=
        ih fun k hk => h k (hk.trans n.lt_succ_self)
      simpa only [Finset.sum_range_succ] using hprefix.concat (h n n.lt_succ_self)

theorem cauchyPVExistsAt_of_dist_lower_bound {γ : ℝ → ℂ} {z₀ : ℂ} {f : ℂ → ℂ} {a b m : ℝ}
    (hm_pos : 0 < m) (h_far : ∀ t ∈ Set.uIcc a b, m ≤ ‖γ t - z₀‖)
    (h_int_tr : ∀ᶠ ε in 𝓝[>] (0 : ℝ), IntervalIntegrable
      (fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) MeasureTheory.volume a b) :
    CauchyPVExistsAt γ a b f z₀ :=
  ⟨_, HasCauchyPVAt.of_dist_lower_bound hm_pos h_far h_int_tr⟩

theorem cauchyPVExistsAt_of_avoidance {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_cont : ContinuousOn γ (Set.uIcc a b)) (h_avoid : ∀ t ∈ Set.uIcc a b, γ t ≠ z₀)
    (hf_int : IntervalIntegrable (fun t => f (γ t) * deriv γ t) MeasureTheory.volume a b) :
    CauchyPVExistsAt γ a b f z₀ :=
  ⟨_, HasCauchyPVAt.of_avoidance h_cont h_avoid hf_int⟩

theorem CauchyPVExistsAt.const_mul {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) (c : ℂ) :
    CauchyPVExistsAt γ a b (fun z => c * f z) z₀ :=
  let ⟨_, hL⟩ := h
  ⟨_, hL.const_mul c⟩

theorem CauchyPVExistsAt.add {γ : ℝ → ℂ} {a b : ℝ} {f g : ℂ → ℂ} {z₀ : ℂ}
    (hf : CauchyPVExistsAt γ a b f z₀) (hg : CauchyPVExistsAt γ a b g z₀) :
    CauchyPVExistsAt γ a b (fun z => f z + g z) z₀ :=
  let ⟨_, hLf⟩ := hf
  let ⟨_, hLg⟩ := hg
  ⟨_, hLf.add hLg⟩

theorem CauchyPVExistsAt.zero {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} :
    CauchyPVExistsAt γ a b (fun _ => 0) z₀ :=
  ⟨0, HasCauchyPVAt.zero⟩

theorem CauchyPVExistsAt.sum {ι : Type*} {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {f : ι → ℂ → ℂ}
    {s : Finset ι} (h : ∀ i ∈ s, CauchyPVExistsAt γ a b (f i) z₀) :
    CauchyPVExistsAt γ a b (fun z => ∑ i ∈ s, f i z) z₀ :=
  ⟨_, HasCauchyPVAt.sum fun i hi => (h i hi).hasCauchyPVAt_cauchyPVAt⟩

theorem HasCauchyPVAt.translate {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) (c : ℂ) :
    HasCauchyPVAt (fun t => γ t + c) a b (fun z => f (z - c)) (z₀ + c) L := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [h.eventually_intervalIntegrable] with ε hε
    simpa using hε
  · simpa using h.tendsto

theorem CauchyPVExistsAt.translate {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) (c : ℂ) :
    CauchyPVExistsAt (fun t => γ t + c) a b (fun z => f (z - c)) (z₀ + c) :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  CauchyPVExistsAt.intro (hL.translate c)

theorem cauchyPVAt_translate {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ} (c : ℂ) :
    cauchyPVAt (fun t => γ t + c) a b (fun z => f (z - c)) (z₀ + c)
      = cauchyPVAt γ a b f z₀ := by
  simp [cauchyPVAt]

private theorem truncated_const_mul_curve_eq {γ : ℝ → ℂ} {f : ℂ → ℂ} {z₀ c : ℂ} (hc : c ≠ 0)
    (ε t : ℝ) : (if ‖c * γ t - c * z₀‖ > ε then
        (fun z => c⁻¹ * f (c⁻¹ * z)) (c * γ t) * deriv (fun t => c * γ t) t else 0)
      = if ‖γ t - z₀‖ > ε / ‖c‖ then f (γ t) * deriv γ t else 0 := by
  have hiff : ‖c * γ t - c * z₀‖ > ε ↔ ‖γ t - z₀‖ > ε / ‖c‖ := by
    rw [← mul_sub, norm_mul, gt_iff_lt, gt_iff_lt, div_lt_iff₀' (norm_pos_iff.mpr hc)]
  simp only [hiff, deriv_const_mul_field', inv_mul_cancel_left₀ hc]
  split_ifs <;> field_simp

theorem HasCauchyPVAt.const_mul_curve {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) {c : ℂ} (hc : c ≠ 0) :
    HasCauchyPVAt (fun t => c * γ t) a b (fun z => c⁻¹ * f (c⁻¹ * z)) (c * z₀) L := by
  have hscale : Tendsto (fun ε : ℝ => ε / ‖c‖) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    simpa [div_eq_mul_inv] using
      Filter.TendstoNhdsWithinIoi.mul_const (b := ‖c‖⁻¹) (c := 0)
        (inv_pos.mpr (norm_pos_iff.mpr hc)) (tendsto_id (x := 𝓝[>] (0 : ℝ)))
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [hscale.eventually h.eventually_intervalIntegrable] with ε hε
    exact (intervalIntegrable_congr fun t _ => truncated_const_mul_curve_eq hc ε t).mpr hε
  · refine h.tendsto.comp hscale |>.congr' ?_
    filter_upwards with ε
    exact intervalIntegral.integral_congr fun t _ => (truncated_const_mul_curve_eq hc ε t).symm

theorem CauchyPVExistsAt.const_mul_curve {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) {c : ℂ} (hc : c ≠ 0) :
    CauchyPVExistsAt (fun t => c * γ t) a b (fun z => c⁻¹ * f (c⁻¹ * z)) (c * z₀) :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  CauchyPVExistsAt.intro (hL.const_mul_curve hc)

theorem cauchyPVAt_const_mul_curve {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ c : ℂ} (hc : c ≠ 0) :
    cauchyPVAt (fun t => c * γ t) a b (fun z => c⁻¹ * f (c⁻¹ * z)) (c * z₀)
      = cauchyPVAt γ a b f z₀ := by
  have hpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hmap : map (fun ε : ℝ => ε / ‖c‖) (𝓝[>] 0) = 𝓝[>] 0 := by
    simpa [div_eq_inv_mul, Set.image_mul_left_Ioi (inv_pos.2 hpos)] using
      (Homeomorph.mulLeft₀ _ (inv_ne_zero hpos.ne')).isEmbedding.map_nhdsWithin_eq (Set.Ioi 0) 0
  unfold cauchyPVAt limUnder
  conv_rhs => rw [← hmap, map_map]
  congr 3 with ε
  exact intervalIntegral.integral_congr fun t _ => truncated_const_mul_curve_eq hc ε t

theorem HasCauchyPVAt.symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ L : ℂ}
    (h : HasCauchyPVAt γ a b f z₀ L) :
    HasCauchyPVAt γ b a f z₀ (-L) := by
  refine HasCauchyPVAt.intro ?_ ?_
  · filter_upwards [h.eventually_intervalIntegrable] with ε hε
    exact hε.symm
  · refine Filter.Tendsto.congr (fun ε => ?_) h.tendsto.neg
    exact (intervalIntegral.integral_symm (f :=
      fun t => if ‖γ t - z₀‖ > ε then f (γ t) * deriv γ t else 0) a b).symm

theorem CauchyPVExistsAt.symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) :
    CauchyPVExistsAt γ b a f z₀ :=
  let ⟨_, hL⟩ := cauchyPVExistsAt_iff.mp h
  cauchyPVExistsAt_iff.mpr ⟨_, hL.symm⟩

theorem cauchyPVAt_symm {γ : ℝ → ℂ} {a b : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h : CauchyPVExistsAt γ a b f z₀) :
    cauchyPVAt γ b a f z₀ = -cauchyPVAt γ a b f z₀ :=
  h.hasCauchyPVAt_cauchyPVAt.symm.cauchyPVAt_eq

theorem CauchyPVExistsAt.concat {γ : ℝ → ℂ} {a b c : ℝ} {f : ℂ → ℂ} {z₀ : ℂ}
    (h_ab : CauchyPVExistsAt γ a b f z₀) (h_bc : CauchyPVExistsAt γ b c f z₀) :
    CauchyPVExistsAt γ a c f z₀ :=
  let ⟨_, hL₁⟩ := h_ab
  let ⟨_, hL₂⟩ := h_bc
  ⟨_, hL₁.concat hL₂⟩

theorem CauchyPVExistsAt.concat_range {γ : ℝ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {n : ℕ}
    {t : ℕ → ℝ} (h : ∀ k < n, CauchyPVExistsAt γ (t k) (t (k + 1)) f z₀) :
    CauchyPVExistsAt γ (t 0) (t n) f z₀ := by
  refine CauchyPVExistsAt.intro (HasCauchyPVAt.concat_range (L := fun k =>
    cauchyPVAt γ (t k) (t (k + 1)) f z₀) ?_)
  exact fun k hk => (h k hk).hasCauchyPVAt_cauchyPVAt

theorem cauchyPVAt_concat_range {γ : ℝ → ℂ} {f : ℂ → ℂ} {z₀ : ℂ} {n : ℕ}
    {t : ℕ → ℝ} (h : ∀ k < n, CauchyPVExistsAt γ (t k) (t (k + 1)) f z₀) :
    cauchyPVAt γ (t 0) (t n) f z₀ =
      ∑ k ∈ Finset.range n, cauchyPVAt γ (t k) (t (k + 1)) f z₀ :=
  (HasCauchyPVAt.concat_range fun k hk => (h k hk).hasCauchyPVAt_cauchyPVAt).cauchyPVAt_eq

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
