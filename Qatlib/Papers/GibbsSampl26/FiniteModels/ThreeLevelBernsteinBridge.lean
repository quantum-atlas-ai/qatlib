/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockInvariantForm
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCompactDomain
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.LinearAlgebra.Matrix.PosDef
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
# Tensor Bernstein certificates for the actual three-level source

Finite coefficient positivity is transported through the actual physical
five-coordinate cube. Reconstruction and coordinate-mass identities remain
explicit algebraic proof obligations; no source bound is assumed as an axiom.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCluster
open Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelInvariant
open Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCompactDomain
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder unitInterval

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernstein

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

abbrev CoefficientIndex (degree : Fin 5 → ℕ) := (i : Fin 5) → Fin (degree i + 1)

def univariateWeight (degree index : ℕ) (x : ℝ) : ℝ :=
  (degree.choose index : ℝ) * x ^ index * (1-x) ^ (degree-index)

def weight (degree : Fin 5 → ℕ) (index : CoefficientIndex degree)
    (x : Fin 5 → ℝ) : ℝ :=
  ∏ i, univariateWeight (degree i) (index i) (x i)

/-- Univariate Weight nonneg for the stated finite source data. -/
theorem univariateWeight_nonneg (degree index : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ univariateWeight degree index x := by
  simpa only [bernstein_apply, univariateWeight] using
    (bernstein_nonneg (n := degree) (ν := index) (x := ⟨x, hx⟩))

/-- Univariate Weight sum for the stated finite source data. -/
theorem univariateWeight_sum (degree : ℕ) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    (∑ index : Fin (degree+1), univariateWeight degree index x) = 1 := by
  simpa only [bernstein_apply, univariateWeight] using
    bernstein.probability degree ⟨x, hx⟩

/-- Weight nonneg for the stated finite source data. -/
theorem weight_nonneg (degree : Fin 5 → ℕ) (index : CoefficientIndex degree)
    {x : Fin 5 → ℝ} (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    0 ≤ weight degree index x := by
  exact Finset.prod_nonneg fun i _ => univariateWeight_nonneg _ _ (hx i)

/-- Weight sum for the stated finite source data. -/
theorem weight_sum (degree : Fin 5 → ℕ) {x : Fin 5 → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    (∑ index : CoefficientIndex degree, weight degree index x) = 1 := by
  unfold weight
  calc
    _ = ∏ i, ∑ j : Fin (degree i + 1), univariateWeight (degree i) j (x i) :=
      (Fintype.prod_sum (fun (i : Fin 5) (j : Fin (degree i + 1)) =>
        univariateWeight (degree i) j (x i))).symm
    _ = 1 := by simp only [univariateWeight_sum _ (hx _), Finset.prod_const_one]

variable {n : Type*}

def matrixValue (degree : Fin 5 → ℕ)
    (coeff : CoefficientIndex degree → Matrix n n ℂ)
    (x : Fin 5 → ℝ) : Matrix n n ℂ :=
  ∑ index, weight degree index x • coeff index

/-- Matrix Value pos Semidef for the stated finite source data. -/
theorem matrixValue_posSemidef (degree : Fin 5 → ℕ)
    (coeff : CoefficientIndex degree → Matrix n n ℂ)
    {x : Fin 5 → ℝ} (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hcoeff : ∀ index, (coeff index).PosSemidef) :
    (matrixValue degree coeff x).PosSemidef := by
  exact Matrix.posSemidef_sum _ fun index _ =>
    (hcoeff index).smul (weight_nonneg degree index hx)

/-- Matrix Value const for the stated finite source data. -/
theorem matrixValue_const (degree : Fin 5 → ℕ) (M : Matrix n n ℂ)
    {x : Fin 5 → ℝ} (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1) :
    matrixValue degree (fun _ => M) x = M := by
  simp only [matrixValue, ← Finset.sum_smul, weight_sum degree hx, one_smul]

/-- Matrix Value sub for the stated finite source data. -/
theorem matrixValue_sub (degree : Fin 5 → ℕ)
    (C D : CoefficientIndex degree → Matrix n n ℂ) (x : Fin 5 → ℝ) :
    matrixValue degree (fun index => C index - D index) x =
      matrixValue degree C x - matrixValue degree D x := by
  simp only [matrixValue, smul_sub, Finset.sum_sub_distrib]

/-- Matrix Value bounds for the stated finite source data. -/
theorem matrixValue_bounds (degree : Fin 5 → ℕ)
    (coeff : CoefficientIndex degree → Matrix n n ℂ)
    (M : Matrix n n ℂ) (m B : ℝ) {x : Fin 5 → ℝ}
    (hx : ∀ i, x i ∈ Set.Icc (0 : ℝ) 1)
    (hlower : ∀ index, (coeff index - m • M).PosSemidef)
    (hupper : ∀ index, (B • M - coeff index).PosSemidef) :
    (matrixValue degree coeff x - m • M).PosSemidef ∧
      (B • M - matrixValue degree coeff x).PosSemidef := by
  constructor
  · have h := matrixValue_posSemidef degree (fun index => coeff index - m • M) hx hlower
    simpa only [matrixValue_sub, matrixValue_const degree (m • M) hx] using h
  · have h := matrixValue_posSemidef degree (fun index => B • M - coeff index) hx hupper
    simpa only [matrixValue_sub, matrixValue_const degree (B • M) hx] using h

variable [Fintype n]

def quadratic (M : Matrix n n ℂ) (v : n → ℂ) : ℝ :=
  (star v ⬝ᵥ (M *ᵥ v)).re

/-- Quadratic sub for the stated finite source data. -/
theorem quadratic_sub (M N : Matrix n n ℂ) (v : n → ℂ) :
    quadratic (M-N) v = quadratic M v - quadratic N v := by
  simp [quadratic, Matrix.sub_mulVec, dotProduct_sub]

/-- Quadratic smul for the stated finite source data. -/
theorem quadratic_smul (a : ℝ) (M : Matrix n n ℂ) (v : n → ℂ) :
    quadratic (a • M) v = a * quadratic M v := by
  simp [quadratic, Matrix.smul_mulVec, dotProduct_smul]

/-- Quadratic nonneg for the stated finite source data. -/
theorem quadratic_nonneg (M : Matrix n n ℂ) (hM : M.PosSemidef) (v : n → ℂ) :
    0 ≤ quadratic M v := by
  exact (Complex.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg v)).1

/-- Quadratic bounds for the stated finite source data. -/
theorem quadratic_bounds (M G : Matrix n n ℂ) (m B : ℝ)
    (hlower : (G-m • M).PosSemidef) (hupper : (B • M-G).PosSemidef)
    (v : n → ℂ) :
    m * quadratic M v ≤ quadratic G v ∧ quadratic G v ≤ B * quadratic M v := by
  have hlo := quadratic_nonneg _ hlower v
  have hhi := quadratic_nonneg _ hupper v
  rw [quadratic_sub, quadratic_smul] at hlo hhi
  constructor <;> linarith

omit [Fintype n] in
/-- Physical matrix Value bounds for the stated finite source data. -/
theorem physical_matrixValue_bounds (degree : Fin 5 → ℕ)
    (coeff : CoefficientIndex degree → Matrix n n ℂ)
    (M : Matrix n n ℂ) (m B S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s)
    (hlower : ∀ index, (coeff index - m • M).PosSemidef)
    (hupper : ∀ index, (B • M - coeff index).PosSemidef) :
    (matrixValue degree coeff (cubePoint S s) - m • M).PosSemidef ∧
      (B • M - matrixValue degree coeff (cubePoint S s)).PosSemidef :=
  matrixValue_bounds degree coeff M m B (cubePoint_mem_Icc hS hs) hlower hupper

/-- Algebraic reconstruction, mass identification, and finite PSD checks imply
the actual source-stack bound. No arbitrary external energy appears. -/
theorem scaledStackBounds_of_coefficients (order : Perm) (degree : Fin 5 → ℕ)
    (coeff : CoefficientIndex degree → Matrix n n ℂ)
    (M : Matrix n n ℂ) (coordinates : ℂ → ℂ → Operator 4 → n → ℂ)
    (m B S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s)
    (hmass : ∀ c d Y, IsFast order Y →
      coordinateMass c d Y = quadratic M (coordinates c d Y))
    (hreconstruct : ∀ c d Y, IsFast order Y →
      stackSquare order S s c d Y =
        quadratic (matrixValue degree coeff (cubePoint S s)) (coordinates c d Y))
    (hlower : ∀ index, (coeff index - m • M).PosSemidef)
    (hupper : ∀ index, (B • M - coeff index).PosSemidef) :
    ScaledStackBounds order S s m B := by
  intro c d Y hY
  have hb := physical_matrixValue_bounds degree coeff M m B S s hS hs hlower hupper
  rw [hmass c d Y hY, hreconstruct c d Y hY]
  exact quadratic_bounds M _ m B hb.1 hb.2 (coordinates c d Y)


/-- The lower and upper certificates may use different rectangular degrees,
as the exact producer's selectively elevated lower certificate does. -/
theorem scaledStackBounds_of_residual_coefficients (order : Perm)
    (lowerDegree upperDegree : Fin 5 → ℕ)
    (lowerCoeff : CoefficientIndex lowerDegree → Matrix n n ℂ)
    (upperCoeff : CoefficientIndex upperDegree → Matrix n n ℂ)
    (coordinates : ℂ → ℂ → Operator 4 → n → ℂ)
    (m B S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s)
    (hlowerIdentity : ∀ c d Y, IsFast order Y →
      stackSquare order S s c d Y - m * coordinateMass c d Y =
        quadratic (matrixValue lowerDegree lowerCoeff (cubePoint S s)) (coordinates c d Y))
    (hupperIdentity : ∀ c d Y, IsFast order Y →
      B * coordinateMass c d Y - stackSquare order S s c d Y =
        quadratic (matrixValue upperDegree upperCoeff (cubePoint S s)) (coordinates c d Y))
    (hlower : ∀ index, (lowerCoeff index).PosSemidef)
    (hupper : ∀ index, (upperCoeff index).PosSemidef) :
    ScaledStackBounds order S s m B := by
  intro c d Y hY
  have hlo := quadratic_nonneg _
    (matrixValue_posSemidef lowerDegree lowerCoeff (cubePoint_mem_Icc hS hs) hlower)
    (coordinates c d Y)
  have hhi := quadratic_nonneg _
    (matrixValue_posSemidef upperDegree upperCoeff (cubePoint_mem_Icc hS hs) hupper)
    (coordinates c d Y)
  rw [← hlowerIdentity c d Y hY] at hlo
  rw [← hupperIdentity c d Y hY] at hhi
  exact ⟨sub_nonneg.mp hlo, sub_nonneg.mp hhi⟩

/-- Finite coefficient PSD, actual residual reconstruction and the physical
cube inclusion now suffice for arbitrary probability-clock comparison. -/
theorem clockEnergy_comparison_of_residual_coefficients (order : Perm)
    (lowerDegree upperDegree : Fin 5 → ℕ)
    (lowerCoeff : CoefficientIndex lowerDegree → Matrix n n ℂ)
    (upperCoeff : CoefficientIndex upperDegree → Matrix n n ℂ)
    (coordinates : ℂ → ℂ → Operator 4 → n → ℂ)
    (m B β S s : ℝ) (hm : 0 < m) (hB : 0 ≤ B) (hS : 0 ≤ S) (hs : 0 ≤ s)
    (hlowerIdentity : ∀ c d Y, IsFast order Y →
      stackSquare order S s c d Y - m * coordinateMass c d Y =
        quadratic (matrixValue lowerDegree lowerCoeff (cubePoint S s)) (coordinates c d Y))
    (hupperIdentity : ∀ c d Y, IsFast order Y →
      B * coordinateMass c d Y - stackSquare order S s c d Y =
        quadratic (matrixValue upperDegree upperCoeff (cubePoint S s)) (coordinates c d Y))
    (hlower : ∀ index, (lowerCoeff index).PosSemidef)
    (hupper : ∀ index, (upperCoeff index).PosSemidef)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy order β S s ν X ≤ (B/m) * clockEnergy order β S s μ X :=
  clockEnergy_comparison order β S s m B hm hB
    (scaledStackBounds_of_residual_coefficients order lowerDegree upperDegree
      lowerCoeff upperCoeff coordinates m B S s hS hs
      hlowerIdentity hupperIdentity hlower hupper) μ ν X

/-- Univariate Weight zero for the stated finite source data. -/
theorem univariateWeight_zero (degree index : ℕ) :
    univariateWeight degree index 0 = if index = 0 then 1 else 0 := by
  simpa [univariateWeight, bernsteinPolynomial] using
    (bernsteinPolynomial.eval_at_0 ℝ degree index)

/-- Univariate Weight one for the stated finite source data. -/
theorem univariateWeight_one (degree index : ℕ) :
    univariateWeight degree index 1 = if index = degree then 1 else 0 := by
  simpa [univariateWeight, bernsteinPolynomial] using
    (bernsteinPolynomial.eval_at_1 ℝ degree index)

def lastIndex (degree : Fin 5 → ℕ) : CoefficientIndex degree :=
  fun i => Fin.last (degree i)

/-- Weight one for the stated finite source data. -/
theorem weight_one (degree : Fin 5 → ℕ) (index : CoefficientIndex degree) :
    weight degree index (fun _ => 1) = if index = lastIndex degree then 1 else 0 := by
  classical
  by_cases h : index = lastIndex degree
  · subst index
    simp [weight, lastIndex, univariateWeight_one]
  · rw [ite_eq_right h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    have hval : (index i : ℕ) ≠ degree i := by
      intro heq
      apply hi
      apply Fin.ext
      simpa only [lastIndex, Fin.val_last] using heq
    exact Finset.prod_eq_zero (Finset.mem_univ i)
      (by simp only [univariateWeight_one, ite_eq_right hval])

omit [Fintype n] in
/-- Matrix Value one for the stated finite source data. -/
theorem matrixValue_one (degree : Fin 5 → ℕ)
    (coeff : CoefficientIndex degree → Matrix n n ℂ) :
    matrixValue degree coeff (fun _ => 1) = coeff (lastIndex degree) := by
  classical
  simp only [matrixValue, weight_one]
  simp

omit [Fintype n] in
/-- Matrix Value zero spacings for the stated finite source data. -/
theorem matrixValue_zero_spacings (degree : Fin 5 → ℕ)
    (coeff : CoefficientIndex degree → Matrix n n ℂ) :
    matrixValue degree coeff (cubePoint 0 0) = coeff (lastIndex degree) := by
  rw [cubePoint_zero, matrixValue_one]


end

end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelBernstein
