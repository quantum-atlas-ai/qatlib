/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCoordinateMetric
public import Mathlib.MeasureTheory.Measure.Basic
public import Mathlib.MeasureTheory.Measure.CompleteLattice
public import Mathlib.MeasureTheory.Measure.Continuity
public import Mathlib.MeasureTheory.Measure.Filter
public import Mathlib.MeasureTheory.Measure.Interval
public import Mathlib.MeasureTheory.Measure.Module
public import Mathlib.MeasureTheory.Measure.OuterMeasure
public import Mathlib.MeasureTheory.Measure.Sum

@[expose] public section


/-!
# Actual source-square transport at the scalar corner

The row-major finite source stack is transported to the existing
Hilbert--Schmidt source energy, preserving every complex input and
the full original six-source family. Together with the exact coordinate
metric and two kernel-checked residuals, this discharges the scalar-corner
ScaledStackBounds premise, including its original physical mass downstream.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCornerForm

open ThreeLevelCluster ThreeLevelInvariant ThreeLevelWordDual
open ThreeLevelGramCertificateCorner ThreeLevelCornerFastChart ThreeLevelBernstein
open ThreeLevelCoordinateMetric

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def stackIndex (k : Fin 6) (i j : Fin 4) : Fin 96 :=
  ⟨16*k.val + 4*i.val + j.val, by omega⟩

/-- Source Index stack Index for the stated finite source data. -/
theorem sourceIndex_stackIndex (k : Fin 6) (i j : Fin 4) :
    sourceIndex (stackIndex k i j) = k := by
  apply Fin.ext
  dsimp [sourceIndex, stackIndex]
  omega

/-- Row Index stack Index for the stated finite source data. -/
theorem rowIndex_stackIndex (k : Fin 6) (i j : Fin 4) :
    rowIndex (stackIndex k i j) = i := by
  apply Fin.ext
  dsimp [rowIndex, stackIndex]
  omega

/-- Column Index stack Index for the stated finite source data. -/
theorem columnIndex_stackIndex (k : Fin 6) (i j : Fin 4) :
    columnIndex (stackIndex k i j) = j := by
  apply Fin.ext
  dsimp [columnIndex, stackIndex]
  omega

/-- Stack Index source row column for the stated finite source data. -/
theorem stackIndex_source_row_column (a : Fin 96) :
    stackIndex (sourceIndex a) (rowIndex a) (columnIndex a) = a := by
  apply Fin.ext
  dsimp [stackIndex, sourceIndex, rowIndex, columnIndex]
  omega

def sourceRows : Fin 96 ≃ Fin 6 × (Fin 4 × Fin 4) where
  toFun a := (sourceIndex a, rowIndex a, columnIndex a)
  invFun a := stackIndex a.1 a.2.1 a.2.2
  left_inv := stackIndex_source_row_column
  right_inv a := by
    rcases a with ⟨k,i,j⟩
    simp only [sourceIndex_stackIndex, rowIndex_stackIndex, columnIndex_stackIndex]

/-- Sum flat source for the stated finite source data. -/
theorem sum_flat_source {M : Type*} [AddCommMonoid M]
    (f : Fin 6 → Fin 4 → Fin 4 → M) :
    (∑ a : Fin 96, f (sourceIndex a) (rowIndex a) (columnIndex a)) =
      ∑ k, ∑ i, ∑ j, f k i j := by
  simpa only [sourceRows, Fintype.sum_prod_type] using!
    Equiv.sum_comp sourceRows (fun a => f a.1 a.2.1 a.2.2)

/-- Sum norm Sq flat source for the stated finite source data. -/
theorem sum_normSq_flat_source (C : Fin 6 → Operator 4) :
    (∑ a : Fin 96, Complex.normSq
      (C (sourceIndex a) (rowIndex a) (columnIndex a))) =
      ∑ k : Fin 6, hsSquare (C k) := by
  simpa only [hsSquare_eq_sum_normSq] using
    sum_flat_source (fun k i j => Complex.normSq (C k i j))

/-- Corner Stack sum norm Sq for the stated finite source data. -/
theorem cornerStack_sum_normSq (σ : Perm) (z : Fin 15 → ℂ) :
    (∑ a : Fin 96, Complex.normSq ((cornerStack *ᵥ z) a)) =
      ∑ k : Fin 6, hsSquare
        (actualGradient σ (fun _ => 0) k (literalCombination z)) := by
  simp_rw [cornerStack_mulVec_eq_actualGradient σ]
  exact sum_normSq_flat_source (fun k => actualGradient σ (fun _ => 0) k (literalCombination z))

/-- Scalar seed One for the stated finite source data. -/
theorem scalar_seedOne :
    seedOne (Equiv.refl (Fin 3)) 0 = pOne+pTwo := by
  simp [seedOne, halfAmplitude, cexp, spectralProjectors, projectors]

/-- Scalar seed Two for the stated finite source data. -/
theorem scalar_seedTwo :
    seedTwo (Equiv.refl (Fin 3)) = pTwo := by
  rfl

/-- Scaled Source zero spacings for the stated finite source data. -/
theorem scaledSource_zero_spacings (c d : ℂ) (Y : Operator 4) (k : Fin 6) :
    scaledSource (Equiv.refl (Fin 3)) 0 0 c d Y k =
      actualGradient (Equiv.refl (Fin 3)) (fun _ => 0) k
        (c • (pOne+pTwo) + d • pTwo + Y) := by
  have hz : smallAmplitude 0 = 1 := by simp [smallAmplitude, cexp]
  simp only [scaledSource, columnOne, columnTwo, zero_spacings_profile,
    hz, inv_one, one_smul, scalar_seedOne, scalar_seedTwo,
    actualGradient_add, actualGradient_smul]


/-- Corner Gram quadratic eq actual source for the stated finite source data. -/
theorem cornerGram_quadratic_eq_actual_source (σ : Perm) (z : Fin 15 → ℂ) :
    quadratic cornerGram z =
      ∑ k : Fin 6, hsSquare
        (actualGradient σ (fun _ => 0) k (literalCombination z)) := by
  rw [cornerGram, quadratic_gram_eq_sum_normSq]
  exact cornerStack_sum_normSq σ z

/-- Corner Gram full Coordinates quadratic for the stated finite source data. -/
theorem cornerGram_fullCoordinates_quadratic (c d : ℂ) (Y : Operator 4)
    (hY : IsFast (Equiv.refl (Fin 3)) Y) :
    quadratic cornerGram (fullCoordinates c d Y) =
      stackSquare (Equiv.refl (Fin 3)) 0 0 c d Y := by
  rw [cornerGram_quadratic_eq_actual_source (Equiv.refl (Fin 3)),
    literalCombination_fullCoordinates (Equiv.refl (Fin 3)) c d Y hY]
  simp only [stackSquare, scaledSource_zero_spacings]

/-- The first actual source-stack certificate, with every coordinate and
metric premise discharged in the Lean kernel. This endpoint is order012. -/
theorem scalar_scaledStackBounds :
    ScaledStackBounds (Equiv.refl (Fin 3)) 0 0 1 34 := by
  intro c d Y hY
  have hb := quadratic_bounds cornerMetric cornerGram 1 34
    (by simpa only [one_smul] using cornerGram_lower_posSemidef)
    cornerGram_upper_posSemidef (fullCoordinates c d Y)
  rw [cornerMetric_fullCoordinates_quadratic (Equiv.refl (Fin 3)) c d Y hY,
    cornerGram_fullCoordinates_quadratic c d Y hY] at hb
  exact hb

/-- The original physical one-twelfth mass is restored downstream. -/
theorem scalar_plainEnergy_bounds (X : Operator 4) :
    (1/12 : ℝ) * invariantMass (Equiv.refl (Fin 3)) 0 0 X ≤
        plainEnergy (Equiv.refl (Fin 3)) 0 0 X ∧
      plainEnergy (Equiv.refl (Fin 3)) 0 0 X ≤
        (17/6 : ℝ) * invariantMass (Equiv.refl (Fin 3)) 0 0 X := by
  convert plainEnergy_bounds (Equiv.refl (Fin 3)) 0 0 1 34 scalar_scaledStackBounds X
    using 1
  norm_num

/-- Scalar clock Energy bounds for the stated finite source data. -/
theorem scalar_clockEnergy_bounds (β : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (X : Operator 4) :
    (1/12 : ℝ) * invariantMass (Equiv.refl (Fin 3)) 0 0 X ≤
        clockEnergy (Equiv.refl (Fin 3)) β 0 0 μ X ∧
      clockEnergy (Equiv.refl (Fin 3)) β 0 0 μ X ≤
        (17/6 : ℝ) * invariantMass (Equiv.refl (Fin 3)) 0 0 X := by
  rw [clockEnergy_zero_spacings]
  exact scalar_plainEnergy_bounds X

/-- Scalar clock Energy comparison for the stated finite source data. -/
theorem scalar_clockEnergy_comparison (β : ℝ)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy (Equiv.refl (Fin 3)) β 0 0 ν X ≤
      34 * clockEnergy (Equiv.refl (Fin 3)) β 0 0 μ X :=
  clockEnergy_comparison_34 (Equiv.refl (Fin 3)) β 0 0 scalar_scaledStackBounds μ ν X

/-- Scalar clock Energy kernel for the stated finite source data. -/
theorem scalar_clockEnergy_kernel (β : ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (X : Operator 4) :
    clockEnergy (Equiv.refl (Fin 3)) β 0 0 μ X = 0 ↔
      ∃ c : ℂ, X = c • (1 : Operator 4) := by
  have h := clockEnergy_eq_zero_iff (Equiv.refl (Fin 3)) β 0 0 1 34
    (by norm_num) scalar_scaledStackBounds μ X
  simpa only [zero_spacings_profile, gibbsRoot, mul_zero, neg_zero,
    zero_div, cexp_zero, population_one] using h


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCornerForm
