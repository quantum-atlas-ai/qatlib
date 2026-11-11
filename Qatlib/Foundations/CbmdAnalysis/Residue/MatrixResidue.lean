/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Residue.Cycle
import Qatlib.Foundations.CbmdAnalysis.Residue.TauCeti.Analysis.Contour.Winding.UnboundedComponent
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# Residues on positive Jordan contours

This module packages positively oriented piecewise C¹ Jordan contours in `PositiveJordanContour`
and defines their trace and interior. Scalar residue formulas are lifted entrywise to finite
matrices through `matrixResidue`, supplying contour identities for the matrix decomposition
framework of [WangEtAl2026].

## Main statements

* `scalar_residue`: the scalar residue formula on a positive Jordan contour.
* `matrix_residue`: the corresponding entrywise matrix formula.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Residue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace CBMDResidue

open _root_.Set Complex MeasureTheory TauCeti TauCeti.Contour
open scoped Topology Matrix.Norms.Elementwise

/-- A closed, simple, piecewise C¹ complex contour with increasing parameter endpoints and
winding number one throughout its filled interior. -/
structure PositiveJordanContour where
  curve : ℝ → ℂ
  start : ℝ
  finish : ℝ
  increasing : start < finish
  piecewiseC1 : IsPiecewiseC1On curve start finish
  closed : curve start = curve finish
  simple : Set.InjOn curve (Set.Ico start finish)
  positive : ∀ z ∈ filledHull (curve '' uIcc start finish) \ (curve '' uIcc start finish),
    windingNumber curve start finish z = 1

namespace PositiveJordanContour

/-- The trace of a positive Jordan contour over its parameter interval. -/
def trace (Γ : PositiveJordanContour) : Set ℂ := Γ.curve '' uIcc Γ.start Γ.finish

/-- The filled hull of the contour trace with the trace removed. -/
def inside (Γ : PositiveJordanContour) : Set ℂ := filledHull Γ.trace \ Γ.trace

/-- The trace of a positive Jordan contour is compact. -/
theorem trace_isCompact (Γ : PositiveJordanContour) : IsCompact Γ.trace :=
  isCompact_uIcc.image_of_continuousOn Γ.piecewiseC1.continuousOn

/-- The interior of a positive Jordan contour is open. -/
theorem inside_isOpen (Γ : PositiveJordanContour) : IsOpen Γ.inside :=
  IsClosed.isOpen_filledHull_sdiff Γ.trace_isCompact.isClosed

/-- The winding number of a positive Jordan contour vanishes outside the filled hull of its
trace. -/
theorem winding_eq_zero_outside (Γ : PositiveJordanContour) {z : ℂ}
    (hz : z ∉ filledHull Γ.trace) : windingNumber Γ.curve Γ.start Γ.finish z = 0 := by
  exact Γ.piecewiseC1.windingNumber_eq_zero_of_unbounded_component Γ.closed hz

/-- A positive Jordan contour is null-homologous in any set containing the filled hull of its
trace. -/
theorem nullHomologous_of_filledHull_subset (Γ : PositiveJordanContour) {U : Set ℂ}
    (hU : filledHull Γ.trace ⊆ U) : IsNullHomologous Γ.curve Γ.start Γ.finish U := by
  rw [isNullHomologous_iff]
  intro z hz
  exact Γ.winding_eq_zero_outside (fun h => hz (hU h))

/-- The contour integral equals `2πi` times the sum of residues at the specified interior
points, assuming analyticity elsewhere and meromorphicity at those points. -/
theorem scalar_residue (Γ : PositiveJordanContour) (f : ℂ → ℂ) (S : Finset ℂ)
    (hS : ∀ s ∈ S, s ∈ Γ.inside)
    (hboundary : ∀ z ∈ Γ.trace, AnalyticAt ℂ f z)
    (hoff : ∀ z ∈ Γ.inside \ (↑S : Set ℂ), AnalyticAt ℂ f z)
    (hmero : ∀ s ∈ S, MeromorphicAt f s) :
    (∫ t in Γ.start..Γ.finish, deriv Γ.curve t • f (Γ.curve t)) =
      2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue f s := by
  classical
  let U : Set ℂ := Γ.inside ∪ {z | AnalyticAt ℂ f z}
  have hU : IsOpen U := Γ.inside_isOpen.union (isOpen_analyticAt ℂ f)
  have hfill : filledHull Γ.trace ⊆ U := by
    intro z hz
    by_cases hzt : z ∈ Γ.trace
    · exact Or.inr (hboundary z hzt)
    · exact Or.inl ⟨hz, hzt⟩
  have hf : DifferentiableOn ℂ f (U \ (↑S : Set ℂ)) := by
    intro z hz
    rcases hz.1 with hi | ha
    · exact (hoff z ⟨hi, hz.2⟩).differentiableAt.differentiableWithinAt
    · exact ha.differentiableAt.differentiableWithinAt
  have hcurve : ∀ t ∈ uIcc Γ.start Γ.finish, Γ.curve t ∈ U := by
    intro t ht
    exact hfill (subset_filledHull ⟨t, ht, rfl⟩)
  have hav : ∀ t ∈ uIcc Γ.start Γ.finish, Γ.curve t ∉ (↑S : Set ℂ) := by
    intro t ht hs
    exact (hS _ hs).2 ⟨t, ht, rfl⟩
  have h := classicalResidueTheorem_nullHomologous hU hf
    (fun s hs _ => hmero s hs) Γ.piecewiseC1 hcurve Γ.closed hav
    (Γ.nullHomologous_of_filledHull_subset hfill)
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro s hs
  rw [Γ.positive s (hS s hs), one_mul]

/-- The scalar residue formula holds for a function meromorphic on an open set containing the
filled contour, with all interior nonanalytic points in `S`. -/
theorem scalar_residue_on_open (Γ : PositiveJordanContour) (f : ℂ → ℂ)
    (U : Set ℂ) (_hU : IsOpen U) (hfill : filledHull Γ.trace ⊆ U)
    (hf : MeromorphicOn f U) (S : Finset ℂ)
    (hS : ∀ s ∈ S, s ∈ Γ.inside)
    (hboundary : ∀ z ∈ Γ.trace, AnalyticAt ℂ f z)
    (hall : ∀ z ∈ Γ.inside, ¬ AnalyticAt ℂ f z → z ∈ S) :
    (∫ t in Γ.start..Γ.finish, deriv Γ.curve t • f (Γ.curve t)) =
      2 * (Real.pi : ℂ) * Complex.I * ∑ s ∈ S, residue f s := by
  apply Γ.scalar_residue f S hS hboundary
  · intro z hz
    by_contra hn
    exact hz.2 (hall z hz.1 hn)
  · intro s hs
    exact hf s (hfill (hS s hs).1)

/-- The matrix formed by taking the scalar residue of each matrix entry at `z`. -/
def matrixResidue {n m : Type*} (F : ℂ → Matrix n m ℂ) (z : ℂ) : Matrix n m ℂ :=
  fun i j => residue (fun w => F w i j) z

/-- Entrywise analyticity on the contour trace ensures interval integrability of the matrix
contour integrand. -/
theorem matrix_contour_integrable {n m : Type*} [Fintype n] [Fintype m]
    (Γ : PositiveJordanContour) (F : ℂ → Matrix n m ℂ)
    (hboundary : ∀ i j z, z ∈ Γ.trace → AnalyticAt ℂ (fun w => F w i j) z) :
    IntervalIntegrable (fun t => deriv Γ.curve t • F (Γ.curve t)) volume
      Γ.start Γ.finish := by
  apply Γ.piecewiseC1.intervalIntegrable_deriv.smul_continuousOn
  apply continuousOn_pi.2
  intro i
  apply continuousOn_pi.2
  intro j t ht
  exact (hboundary i j _ ⟨t, ht, rfl⟩).continuousAt.comp_continuousWithinAt
    (Γ.piecewiseC1.continuousOn t ht)

/-- The matrix contour integral equals `2πi` times the sum of entrywise residues under entrywise
analyticity and meromorphicity hypotheses. -/
theorem matrix_residue {n m : Type*} [Fintype n] [Fintype m]
    (Γ : PositiveJordanContour) (F : ℂ → Matrix n m ℂ) (S : Finset ℂ)
    (hS : ∀ s ∈ S, s ∈ Γ.inside)
    (hboundary : ∀ i j z, z ∈ Γ.trace → AnalyticAt ℂ (fun w => F w i j) z)
    (hoff : ∀ i j z, z ∈ Γ.inside \ (↑S : Set ℂ) → AnalyticAt ℂ (fun w => F w i j) z)
    (hmero : ∀ i j s, s ∈ S → MeromorphicAt (fun w => F w i j) s) :
    (∫ t in Γ.start..Γ.finish, deriv Γ.curve t • F (Γ.curve t)) =
      (2 * (Real.pi : ℂ) * Complex.I) • ∑ s ∈ S, matrixResidue F s := by
  classical
  have hint := Γ.matrix_contour_integrable F hboundary
  ext i j
  let ev : Matrix n m ℂ →L[ℂ] ℂ :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : m => ℂ) j).comp
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => m → ℂ) i)
  have hcomm := ev.intervalIntegral_comp_comm hint
  change (∫ t in Γ.start..Γ.finish, deriv Γ.curve t • F (Γ.curve t) i j) =
    (∫ t in Γ.start..Γ.finish, deriv Γ.curve t • F (Γ.curve t)) i j at hcomm
  rw [← hcomm]
  simpa only [Matrix.smul_apply, Matrix.sum_apply, matrixResidue, smul_eq_mul]
    using Γ.scalar_residue (fun z => F z i j) S hS (hboundary i j) (hoff i j) (hmero i j)

/-- The matrix residue formula holds for entries meromorphic on an open set containing the
filled contour, with all interior nonanalytic points in `S`. -/
theorem matrix_residue_on_open {n m : Type*} [Fintype n] [Fintype m]
    (Γ : PositiveJordanContour) (F : ℂ → Matrix n m ℂ)
    (U : Set ℂ) (_hU : IsOpen U) (hfill : filledHull Γ.trace ⊆ U)
    (hf : ∀ i j, MeromorphicOn (fun w => F w i j) U) (S : Finset ℂ)
    (hS : ∀ s ∈ S, s ∈ Γ.inside)
    (hboundary : ∀ i j z, z ∈ Γ.trace → AnalyticAt ℂ (fun w => F w i j) z)
    (hall : ∀ i j z, z ∈ Γ.inside → ¬ AnalyticAt ℂ (fun w => F w i j) z → z ∈ S) :
    (∫ t in Γ.start..Γ.finish, deriv Γ.curve t • F (Γ.curve t)) =
      (2 * (Real.pi : ℂ) * Complex.I) • ∑ s ∈ S, matrixResidue F s := by
  apply Γ.matrix_residue F S hS hboundary
  · intro i j z hz
    by_contra hn
    exact hz.2 (hall i j z hz.1 hn)
  · intro i j s hs
    exact hf i j s (hfill (hS s hs).1)

end PositiveJordanContour
end CBMDResidue

end
end Qatlib.Foundations.CbmdAnalysis.Residue
