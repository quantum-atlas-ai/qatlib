/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPopulationRayleigh
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section


/-!
# Attainment of the actual probability-clock Rayleigh infimum

The actual energy is continuous in the complete complex operator input.
A locally constant integrable dominator follows from the time-invariant
mass upper bound, so no clock support or moment bound is required.
Compactness then gives an attained clock Rayleigh infimum. No averaged
parent matrix or spectral identification is introduced.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix MeasureTheory Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockRayleighAttainment
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelClockRayleighGap

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

noncomputable section

/-- Time Conjugation input continuous for the stated finite source data. -/
theorem timeConjugation_input_continuous (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ) :
    Continuous (timeConjugation σ E t) := by
  unfold timeConjugation
  fun_prop

/-- Continuity needs only a finite clock measure and the actual upper source
certificate; no strict lower constant or nonzero-beta condition is needed. -/
theorem clockEnergy_continuous (σ : Perm) (β S s m B : ℝ)
    (hcert : ScaledStackBounds σ S s m B)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    Continuous (clockEnergy σ β S s μ) := by
  let : FirstCountableTopology (Operator 4) := by
    change FirstCountableTopology (Fin 4 → Fin 4 → ℂ)
    infer_instance
  apply continuous_iff_continuousAt.mpr
  intro X₀
  let E := physicalEnergies β S s
  let C : ℝ := (B/12) * invariantMass σ S s X₀ + 1
  have hc : Continuous (fun X : Operator 4 => (B/12) * invariantMass σ S s X) :=
    continuous_const.mul (ThreeLevelPopulationRayleigh.invariantMass_continuous σ S s)
  have hnear : ∀ᶠ X in 𝓝 X₀, (B/12) * invariantMass σ S s X < C :=
    hc.continuousAt.eventually_lt continuousAt_const (by dsimp [C]; linarith)
  have hbound : ∀ᶠ X in 𝓝 X₀, ∀ᵐ t ∂μ,
      ‖plainEnergy σ S s (timeConjugation σ E t X)‖ ≤ C := by
    filter_upwards [hnear] with X hX
    exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (plainEnergy_nonneg σ S s _)]
      have hu := (plainEnergy_bounds σ S s m B hcert (timeConjugation σ E t X)).2
      rw [invariantMass_timeConjugation] at hu
      exact hu.trans hX.le
  change ContinuousAt (fun X : Operator 4 =>
    ∫ t : ℝ, plainEnergy σ S s (timeConjugation σ E t X) ∂μ) X₀
  exact continuousAt_of_dominated
    (Filter.Eventually.of_forall fun X =>
      (continuous_time_plainEnergy σ S s E X).aestronglyMeasurable)
    hbound (integrable_const C)
    (Filter.Eventually.of_forall fun t =>
      ((plainEnergy_continuous σ S s).comp
        (timeConjugation_input_continuous σ E t)).continuousAt)

/-- The exact clock infimum is attained on the entire complex HS unit sphere
orthogonal to the actual spectral Gibbs line. -/
theorem clockGap_attained (σ : Perm) (β S s m B : ℝ)
    (hcert : ScaledStackBounds σ S s m B)
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∃ X ∈ unitInputs σ S s,
      clockGap σ β S s μ = clockEnergy σ β S s μ X ∧
        ∀ Y ∈ unitInputs σ S s, clockEnergy σ β S s μ X ≤ clockEnergy σ β S s μ Y :=
  (unitInputs_isCompact σ S s).exists_sInf_image_eq_and_le
    (unitInputs_nonempty σ S s) (clockEnergy_continuous σ β S s m B hcert μ).continuousOn

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockRayleighAttainment
