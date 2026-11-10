/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.NullHomologous
set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {Ω : Set ℂ}

local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

theorem windingNumber_symm (h : CauchyPVExistsAt γ a b κ[z₀] z₀) :
    windingNumber γ b a z₀ = -windingNumber γ a b z₀ := by
  rw [windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt.symm,
    windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt]
  ring

theorem windingNumber_eq_zero_symm (hzero : windingNumber γ a b z₀ = 0)
    (hpv : CauchyPVExistsAt γ a b κ[z₀] z₀) :
    windingNumber γ b a z₀ = 0 := by
  rw [windingNumber_symm hpv, hzero, neg_zero]

theorem IsNullHomologous.symm (h : IsNullHomologous γ a b Ω)
    (hpv : ∀ z ∉ Ω, CauchyPVExistsAt γ a b κ[z] z) :
    IsNullHomologous γ b a Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  exact windingNumber_eq_zero_symm (h z hz) (hpv z hz)

theorem IsNullHomologous.symm_of_avoidance (h : IsNullHomologous γ a b Ω)
    (hγ : ∀ t ∈ Set.uIcc a b, γ t ∈ Ω) (hcont : ContinuousOn γ (Set.uIcc a b)) (hint : ∀ z ∉ Ω,
      IntervalIntegrable (fun t => (γ t - z)⁻¹ * deriv γ t) MeasureTheory.volume a b) :
    IsNullHomologous γ b a Ω := by
  refine h.symm ?_
  intro z hz
  refine cauchyPVExistsAt_of_avoidance hcont ?_ (hint z hz)
  intro t ht htz
  exact hz (htz ▸ hγ t ht)

end TauCeti.Contour

end

end
end Qatlib.Foundations.CbmdAnalysis.Residue
