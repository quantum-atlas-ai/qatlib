/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck, Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.CBMDCompat

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.NullHomologous

/-!
# Reversing winding numbers and null homology

Shows that exchanging the integration endpoints negates `windingNumber` when the relevant
principal value exists. The corresponding `IsNullHomologous.symm` lemmas preserve null homology
under explicit existence or avoidance hypotheses.

These orientation rules support the contour framework associated with [WangEtAl2026].

## Main statements

* `windingNumber_symm`: Exchanging the interval endpoints negates the winding number when the
  defining Cauchy principal value exists.
* `IsNullHomologous.symm_of_avoidance`: Null homology is preserved under exchanging endpoints
  for a continuous curve contained in the set whose logarithmic derivatives are interval
  integrable outside it.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

section

noncomputable section

open Filter Topology

namespace TauCeti.Contour

variable {γ : ℝ → ℂ} {a b : ℝ} {z₀ : ℂ} {Ω : Set ℂ}

local notation "κ[" z "]" => (fun w : ℂ => (w - z)⁻¹)

/-- Exchanging the interval endpoints negates the winding number when the defining Cauchy
principal value exists. -/
theorem windingNumber_symm (h : CauchyPVExistsAt γ a b κ[z₀] z₀) :
    windingNumber γ b a z₀ = -windingNumber γ a b z₀ := by
  rw [windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt.symm,
    windingNumber_eq_of_hasCauchyPVAt h.hasCauchyPVAt_cauchyPVAt]
  ring

/-- A zero winding number remains zero after exchanging endpoints when the defining Cauchy
principal value exists. -/
theorem windingNumber_eq_zero_symm (hzero : windingNumber γ a b z₀ = 0)
    (hpv : CauchyPVExistsAt γ a b κ[z₀] z₀) :
    windingNumber γ b a z₀ = 0 := by
  rw [windingNumber_symm hpv, hzero, neg_zero]

/-- Null homology is preserved under exchanging endpoints when the requisite Cauchy principal
values exist outside the set. -/
theorem IsNullHomologous.symm (h : IsNullHomologous γ a b Ω)
    (hpv : ∀ z ∉ Ω, CauchyPVExistsAt γ a b κ[z] z) :
    IsNullHomologous γ b a Ω := by
  rw [isNullHomologous_iff] at h ⊢
  intro z hz
  exact windingNumber_eq_zero_symm (h z hz) (hpv z hz)

/-- Null homology is preserved under exchanging endpoints for a continuous curve contained in
the set whose logarithmic derivatives are interval integrable outside it. -/
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
