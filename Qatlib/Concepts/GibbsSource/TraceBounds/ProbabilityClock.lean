/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.TraceBounds.CenteredTrial
public import Mathlib.MeasureTheory.Measure.Basic

@[expose] public section


/-! # Trace conservation for arbitrary probability clocks

Every positive finite source operator supplies a uniform integrable bound on
the whole unitary orbit of a test matrix. Finite sums commute with the
probability integral, preserving the full matrix-unit trace exactly.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Qatlib.Concepts.GibbsSource.SourceForms
open Qatlib.Concepts.GibbsSource.SpectralGeom
open Matrix MeasureTheory
open scoped BigOperators MatrixOrder ComplexOrder

namespace Qatlib.Concepts.GibbsSource.TraceBounds

noncomputable section
variable {D : ℕ}

/-- Positive source energies along a unitary probability clock are integrable without a moment bound. -/
theorem unitary_energy_probability_integrable
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0 ≤ (hsInner X (L X)).re)
    (U : ℝ → Operator D) (hU : ∀ t, (U t)ᴴ * U t = 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Operator D)
    (hcont : Continuous (fun t => (hsInner (fullUnitaryConj (U t) X)
      (L (fullUnitaryConj (U t) X))).re)) :
    Integrable (fun t => (hsInner (fullUnitaryConj (U t) X)
      (L (fullUnitaryConj (U t) X))).re) μ := by
  apply Integrable.of_bound (C := sourceTrace L * (hsInner X X).re)
  · exact hcont.aestronglyMeasurable
  · apply Filter.Eventually.of_forall
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (hpos _)]
    have hb := sourceTrace_positive_cap L hL hpos (fullUnitaryConj (U t) X)
    simpa only [fullUnitaryConj_hsInner _ _ _ (hU t)] using hb

/-- The complete averaged matrix-unit energy equals the actual source trace. -/
theorem sum_probabilityClockEnergy_matrixUnits
    (L : Operator D →ₗ[ℂ] Operator D) (hL : SourceSelfAdjoint L)
    (hpos : ∀ X, 0 ≤ (hsInner X (L X)).re)
    (U : ℝ → Operator D) (hU : ∀ t, (U t)ᴴ * U t = 1)
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hcont : ∀ X, Continuous (fun t => (hsInner (fullUnitaryConj (U t) X)
      (L (fullUnitaryConj (U t) X))).re)) :
    (∑ i, ∑ j, ∫ t, (hsInner (fullUnitaryConj (U t) (matUnit i j 1))
      (L (fullUnitaryConj (U t) (matUnit i j 1)))).re ∂μ) = sourceTrace L := by
  have hi (i j : Fin D) :=
    unitary_energy_probability_integrable L hL hpos U hU μ (matUnit i j 1) (hcont _)
  calc
    _ = ∫ t, ∑ i, ∑ j, (hsInner (fullUnitaryConj (U t) (matUnit i j 1))
        (L (fullUnitaryConj (U t) (matUnit i j 1)))).re ∂μ := by
      rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
      apply Finset.sum_congr rfl
      intro i _
      exact (integral_finsetSum _ (fun j _ => hi i j)).symm
    _ = _ := by
      simp_rw [sum_unitary_energy L _ (hU _)]
      simp

end
end Qatlib.Concepts.GibbsSource.TraceBounds
