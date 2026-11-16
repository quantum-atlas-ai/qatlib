/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Concepts.GibbsSource.SourceForms.PhaseAlgebra
public import Qatlib.Concepts.GibbsSource.SourceForms.FullUnitaryTransport
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClusterColumns
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
# Actual population coordinates and clock-invariant source forms

All operators use the fixed complex three-projector model and the complete
six original Pauli sources. The finite scaled-stack certificate remains an
explicit hypothesis. No all-temperature Bernstein floor is postulated as an
axiom and no arbitrary external gap is used.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCluster
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.Elementwise MatrixOrder ComplexOrder

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelInvariant

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

/-- Hs Pair eq hs Inner for the stated finite source data. -/
theorem hsPair_eq_hsInner (X Y : Operator 4) : hsPair X Y = hsInner X Y := rfl

/-- Rank ne zero for the stated finite source data. -/
theorem rank_ne_zero (σ : Perm) (i : Fin 3) :
    (projectorRank (σ i) : ℂ) ≠ 0 := by
  exact_mod_cast (Nat.ne_of_gt (projectorRank_pos (σ i)))

/-- Population add for the stated finite source data. -/
theorem population_add (σ : Perm) (v w : Fin 3 → ℂ) :
    population σ (fun i => v i + w i) = population σ v + population σ w := by
  simp [population, add_smul, Finset.sum_add_distrib]

/-- Hs Inner projector population for the stated finite source data. -/
theorem hsInner_projector_population (σ : Perm) (i : Fin 3) (v : Fin 3 → ℂ) :
    hsInner (spectralProjectors σ i) (population σ v) =
      v i * (projectorRank (σ i) : ℂ) := by
  rw [hsInner, spectralProjectors_adjoint, projector_mul_population,
    Matrix.trace_smul, trace_spectralProjectors]
  rfl

/-- Hs Inner population left for the stated finite source data. -/
theorem hsInner_population_left (σ : Perm) (v : Fin 3 → ℂ) (X : Operator 4) :
    hsInner (population σ v) X =
      ∑ i, star (v i) * hsInner (spectralProjectors σ i) X := by
  simp [population, hsInner, Matrix.conjTranspose_sum, Finset.sum_mul,
    Matrix.trace_sum, spectralProjectors_adjoint]

def populationCoefficient (σ : Perm) (X : Operator 4) (i : Fin 3) : ℂ :=
  hsInner (spectralProjectors σ i) X / (projectorRank (σ i) : ℂ)

def populationPart (σ : Perm) (X : Operator 4) : Operator 4 :=
  population σ (populationCoefficient σ X)

def fastPart (σ : Perm) (X : Operator 4) : Operator 4 :=
  X - populationPart σ X

def IsFast (σ : Perm) (X : Operator 4) : Prop :=
  ∀ i, hsInner (spectralProjectors σ i) X = 0

/-- Population Coefficient population for the stated finite source data. -/
theorem populationCoefficient_population (σ : Perm) (v : Fin 3 → ℂ) :
    populationCoefficient σ (population σ v) = v := by
  funext i
  dsimp only [populationCoefficient]
  rw [hsInner_projector_population]
  exact mul_div_cancel_right₀ _ (rank_ne_zero σ i)

/-- Population Part population for the stated finite source data. -/
theorem populationPart_population (σ : Perm) (v : Fin 3 → ℂ) :
    populationPart σ (population σ v) = population σ v := by
  rw [populationPart, populationCoefficient_population]

/-- Population Coefficient add for the stated finite source data. -/
theorem populationCoefficient_add (σ : Perm) (X Y : Operator 4) :
    populationCoefficient σ (X+Y) =
      fun i => populationCoefficient σ X i + populationCoefficient σ Y i := by
  funext i
  simp [populationCoefficient, hsInner, Matrix.mul_add, Matrix.trace_add, add_div]

/-- Population Coefficient smul for the stated finite source data. -/
theorem populationCoefficient_smul (σ : Perm) (c : ℂ) (X : Operator 4) :
    populationCoefficient σ (c • X) =
      fun i => c * populationCoefficient σ X i := by
  funext i
  simp [populationCoefficient, hsInner_smul_right, mul_div_assoc]

/-- Fast Part is Fast for the stated finite source data. -/
theorem fastPart_isFast (σ : Perm) (X : Operator 4) : IsFast σ (fastPart σ X) := by
  intro i
  rw [fastPart, hsInner_sub_right]
  change hsInner (spectralProjectors σ i) X -
    hsInner (spectralProjectors σ i) (population σ (populationCoefficient σ X)) = 0
  rw [hsInner_projector_population]
  simp [populationCoefficient, div_mul_cancel₀ _ (rank_ne_zero σ i)]

/-- Population Part add fast Part for the stated finite source data. -/
theorem populationPart_add_fastPart (σ : Perm) (X : Operator 4) :
    populationPart σ X + fastPart σ X = X := by
  simp [fastPart]

/-- Fast Part population for the stated finite source data. -/
theorem fastPart_population (σ : Perm) (v : Fin 3 → ℂ) :
    fastPart σ (population σ v) = 0 := by
  simp [fastPart, populationPart_population]

/-- Population Part is Fast zero for the stated finite source data. -/
theorem populationPart_isFast_zero (σ : Perm) (X : Operator 4) (hX : IsFast σ X) :
    populationPart σ X = 0 := by
  change ∀ i, hsInner (spectralProjectors σ i) X = 0 at hX
  simp [populationPart, populationCoefficient, hX, population]

/-- Fast Part eq self for the stated finite source data. -/
theorem fastPart_eq_self (σ : Perm) (X : Operator 4) (hX : IsFast σ X) :
    fastPart σ X = X := by
  rw [fastPart, populationPart_isFast_zero σ X hX, sub_zero]

/-- Population Part idempotent for the stated finite source data. -/
theorem populationPart_idempotent (σ : Perm) (X : Operator 4) :
    populationPart σ (populationPart σ X) = populationPart σ X :=
  populationPart_population σ _

/-- Hs Inner population fast for the stated finite source data. -/
theorem hsInner_population_fast (σ : Perm) (v : Fin 3 → ℂ)
    (X : Operator 4) (hX : IsFast σ X) :
    hsInner (population σ v) X = 0 := by
  rw [hsInner_population_left]
  change ∀ i, hsInner (spectralProjectors σ i) X = 0 at hX
  simp [hX]

def halfAmplitude (s : ℝ) : ℂ := cexp (-s/2)

def seedOne (σ : Perm) (s : ℝ) : Operator 4 :=
  spectralProjectors σ 1 + halfAmplitude s • spectralProjectors σ 2

def seedTwo (σ : Perm) : Operator 4 := spectralProjectors σ 2

def firstCoordinate (σ : Perm) (S : ℝ) (X : Operator 4) : ℂ :=
  populationCoefficient σ X 1 - halfAmplitude S * populationCoefficient σ X 0

def secondCoordinate (σ : Perm) (s : ℝ) (X : Operator 4) : ℂ :=
  populationCoefficient σ X 2 - halfAmplitude s * populationCoefficient σ X 1

/-- Seed One eq cluster Root for the stated finite source data. -/
theorem seedOne_eq_clusterRoot (σ : Perm) (s : ℝ) :
    seedOne σ s = clusterRoot σ (quarterAmplitude s) := by
  rw [clusterRoot_formula, quarterAmplitude_square]
  rfl

/-- Low gibbs profile for the stated finite source data. -/
theorem low_gibbs_profile (σ : Perm) (S s : ℝ) :
    gibbsRoot σ (lowEnergies S s) =
      population σ ![1, halfAmplitude S, halfAmplitude S * halfAmplitude s] := by
  unfold gibbsRoot
  congr 1
  funext i
  fin_cases i <;> simp [lowEnergies, halfAmplitude, cexp_zero]
  rw [← cexp_add]
  congr 1
  ring

/-- Population triangular for the stated finite source data. -/
theorem population_triangular (σ : Perm) (a b : ℂ) (v : Fin 3 → ℂ) :
    population σ v =
      v 0 • population σ ![1,a,a*b] +
      (v 1-a*v 0) • (spectralProjectors σ 1+b • spectralProjectors σ 2) +
      (v 2-b*v 1) • spectralProjectors σ 2 := by
  ext i j
  simp [population, Fin.sum_univ_succ, Matrix.smul_apply, smul_eq_mul]
  ring

/-- Actual decomposition for the stated finite source data. -/
theorem actual_decomposition (σ : Perm) (S s : ℝ) (X : Operator 4) :
    X = populationCoefficient σ X 0 • gibbsRoot σ (lowEnergies S s) +
      firstCoordinate σ S X • seedOne σ s +
      secondCoordinate σ s X • seedTwo σ + fastPart σ X := by
  conv_lhs => rw [← populationPart_add_fastPart σ X]
  conv_lhs =>
    arg 1
    unfold populationPart
    rw [population_triangular σ (halfAmplitude S) (halfAmplitude s)]
  rw [← low_gibbs_profile]
  rfl

/-- Center add for the stated finite source data. -/
theorem center_add (X Y g : Operator 4) :
    orthogonalCenter (X+Y) g = orthogonalCenter X g + orthogonalCenter Y g := by
  have h : hsPair g (X+Y) = hsPair g X + hsPair g Y := by
    simp [hsPair, Matrix.mul_add, Matrix.trace_add]
  simp only [orthogonalCenter, h, add_div, add_smul]
  abel

/-- Center smul for the stated finite source data. -/
theorem center_smul (c : ℂ) (X g : Operator 4) :
    orthogonalCenter (c • X) g = c • orthogonalCenter X g := by
  simp only [orthogonalCenter, hsPair_smul_right, mul_div_assoc, smul_sub, smul_smul]

/-- Center self for the stated finite source data. -/
theorem center_self (g : Operator 4) (hg : hsPair g g ≠ 0) :
    orthogonalCenter g g = 0 := by
  simp [orthogonalCenter, hg]

/-- Center fast for the stated finite source data. -/
theorem center_fast (σ : Perm) (E : Fin 3 → ℝ) (X : Operator 4)
    (hX : IsFast σ X) :
    orthogonalCenter X (gibbsRoot σ E) = X := by
  have h : hsPair (gibbsRoot σ E) X = 0 :=
    hsInner_population_fast σ _ X hX
  simp [orthogonalCenter, h]

/-- Actual centered decomposition for the stated finite source data. -/
theorem actual_centered_decomposition (σ : Perm) (S s : ℝ) (X : Operator 4) :
    orthogonalCenter X (gibbsRoot σ (lowEnergies S s)) =
      firstCoordinate σ S X •
        orthogonalCenter (seedOne σ s) (gibbsRoot σ (lowEnergies S s)) +
      secondCoordinate σ s X •
        orthogonalCenter (seedTwo σ) (gibbsRoot σ (lowEnergies S s)) +
      fastPart σ X := by
  conv_lhs => arg 1; rw [actual_decomposition σ S s X]
  rw [center_add, center_add, center_add, center_smul, center_smul, center_smul,
    center_self _ (hsPair_gibbs_ne_zero σ _),
    center_fast σ _ _ (fastPart_isFast σ X)]
  simp

/-! ## Spectral time unitary of the same actual projectors -/

def timeUnitary (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ) : Operator 4 :=
  population σ (fun i => bohrPhase (E i) t)

def timeConjugation (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ)
    (X : Operator 4) : Operator 4 :=
  timeUnitary σ E t * X * (timeUnitary σ E t)ᴴ

/-- Phase star self for the stated finite source data. -/
theorem phase_star_self (e t : ℝ) :
    star (bohrPhase e t) * bohrPhase e t = 1 := by
  rw [bohrPhase_star_mul]
  simp [bohrPhase]

/-- Phase self star for the stated finite source data. -/
theorem phase_self_star (e t : ℝ) :
    bohrPhase e t * star (bohrPhase e t) = 1 := by
  rw [mul_comm]
  exact phase_star_self e t

/-- Time Unitary star mul for the stated finite source data. -/
theorem timeUnitary_star_mul (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ) :
    (timeUnitary σ E t)ᴴ * timeUnitary σ E t = 1 := by
  simp only [timeUnitary, population_adjoint, population_mul, phase_star_self]
  exact population_one σ

/-- Time Conjugation population for the stated finite source data. -/
theorem timeConjugation_population (σ : Perm) (E : Fin 3 → ℝ)
    (t : ℝ) (v : Fin 3 → ℂ) :
    timeConjugation σ E t (population σ v) = population σ v := by
  simp only [timeConjugation, timeUnitary, population_adjoint, population_mul]
  congr 1
  funext i
  rw [mul_right_comm, phase_self_star, one_mul]

/-- Time Conjugation projector for the stated finite source data. -/
theorem timeConjugation_projector (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ) (i : Fin 3) :
    timeConjugation σ E t (spectralProjectors σ i) = spectralProjectors σ i := by
  simp only [timeConjugation, timeUnitary, population_mul_projector,
    population_adjoint, Matrix.smul_mul, projector_mul_population, smul_smul,
    phase_self_star, one_smul]

/-- Hs Inner time Conjugation for the stated finite source data. -/
theorem hsInner_timeConjugation (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ) (X Y : Operator 4) :
    hsInner (timeConjugation σ E t X) (timeConjugation σ E t Y) = hsInner X Y :=
  fullUnitaryConj_hsInner _ _ _ (timeUnitary_star_mul σ E t)

/-- Population Coefficient time Conjugation for the stated finite source data. -/
theorem populationCoefficient_timeConjugation (σ : Perm) (E : Fin 3 → ℝ)
    (t : ℝ) (X : Operator 4) :
    populationCoefficient σ (timeConjugation σ E t X) = populationCoefficient σ X := by
  funext i
  have h := hsInner_timeConjugation σ E t (spectralProjectors σ i) X
  rw [timeConjugation_projector] at h
  simp only [populationCoefficient, h]

/-- Time Conjugation sub for the stated finite source data. -/
theorem timeConjugation_sub (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ) (X Y : Operator 4) :
    timeConjugation σ E t (X-Y) =
      timeConjugation σ E t X - timeConjugation σ E t Y := by
  simp [timeConjugation, Matrix.mul_sub, Matrix.sub_mul]

/-- Fast Part time Conjugation for the stated finite source data. -/
theorem fastPart_timeConjugation (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ) (X : Operator 4) :
    fastPart σ (timeConjugation σ E t X) = timeConjugation σ E t (fastPart σ X) := by
  simp only [fastPart, populationPart, populationCoefficient_timeConjugation,
    timeConjugation_sub, timeConjugation_population]

/-- Is Fast time Conjugation for the stated finite source data. -/
theorem isFast_timeConjugation (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ)
    (X : Operator 4) (hX : IsFast σ X) : IsFast σ (timeConjugation σ E t X) := by
  intro i
  have h := hsInner_timeConjugation σ E t (spectralProjectors σ i) X
  rw [timeConjugation_projector, hX i] at h
  exact h

def hsSquare (X : Operator 4) : ℝ := (hsInner X X).re

def invariantMass (σ : Perm) (S s : ℝ) (X : Operator 4) : ℝ :=
  Complex.normSq (smallAmplitude S * firstCoordinate σ S X) +
  Complex.normSq (smallAmplitude s * secondCoordinate σ s X) +
  hsSquare (fastPart σ X)

/-- Invariant Mass nonneg for the stated finite source data. -/
theorem invariantMass_nonneg (σ : Perm) (S s : ℝ) (X : Operator 4) :
    0 ≤ invariantMass σ S s X := by
  exact add_nonneg (add_nonneg (Complex.normSq_nonneg _) (Complex.normSq_nonneg _))
    (hsInner_self_nonneg _)

/-- Invariant Mass time Conjugation for the stated finite source data. -/
theorem invariantMass_timeConjugation (σ : Perm) (S s : ℝ)
    (E : Fin 3 → ℝ) (t : ℝ) (X : Operator 4) :
    invariantMass σ S s (timeConjugation σ E t X) = invariantMass σ S s X := by
  simp only [invariantMass, firstCoordinate, secondCoordinate,
    populationCoefficient_timeConjugation, fastPart_timeConjugation,
    hsSquare, hsInner_timeConjugation]


/-! ## Exact scaled columns of the actual Gaussian source -/

/-- Every real Gaussian small-amplitude coefficient is nonzero. -/
theorem smallAmplitude_ne_zero (s : ℝ) : smallAmplitude s ≠ 0 :=
  cexp_ne_zero _

/-- Actual Gradient add for the stated finite source data. -/
theorem actualGradient_add (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (X Y : Operator 4) :
    actualGradient σ E k (X+Y) = actualGradient σ E k X + actualGradient σ E k Y := by
  simp only [actualGradient, thermalGradient, Matrix.mul_add, Matrix.add_mul]
  abel

/-- Actual Gradient smul for the stated finite source data. -/
theorem actualGradient_smul (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (c : ℂ) (X : Operator 4) :
    actualGradient σ E k (c • X) = c • actualGradient σ E k X :=
  thermalGradient_smul _ _ _ _ _ _

def columnOne (σ : Perm) (S s : ℝ) (k : Fin 6) : Operator 4 :=
  (smallAmplitude S)⁻¹ • actualGradient σ (lowEnergies S s) k (seedOne σ s)

def columnTwo (σ : Perm) (S s : ℝ) (k : Fin 6) : Operator 4 :=
  (smallAmplitude s)⁻¹ • actualGradient σ (lowEnergies S s) k (seedTwo σ)

/-- Column One eq edges for the stated finite source data. -/
theorem columnOne_eq_edges (σ : Perm) (S s : ℝ) (k : Fin 6) :
    columnOne σ S s k =
      edge σ (ThreeLevelWordDual.source k) 0 1 +
        ((quarterAmplitude s)^2 * farRatio S s) •
          edge σ (ThreeLevelWordDual.source k) 0 2 := by
  rw [columnOne, seedOne_eq_clusterRoot, gaussian_low_column]
  simp [smul_smul, smallAmplitude_ne_zero]

def highCrossWeights (c d : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0,0,c; 0,0,d; -c,-d,0]

/-- Spectral Filter high Cross Weights for the stated finite source data. -/
theorem spectralFilter_highCrossWeights (σ : Perm) (A : Operator 4) (c d : ℂ) :
    spectralFilter σ (highCrossWeights c d) A =
      c • edge σ A 0 2 + d • edge σ A 1 2 := by
  simp [spectralFilter, highCrossWeights, edge, Fin.sum_univ_succ, smul_sub]
  abel

/-- Population seed Two for the stated finite source data. -/
theorem population_seedTwo (σ : Perm) :
    population σ ![0,0,1] = seedTwo σ := by
  simp [population, seedTwo, Fin.sum_univ_succ]

/-- Low high column for the stated finite source data. -/
theorem low_high_column (σ : Perm) (A : Operator 4) (a g e v R : ℂ)
    (ha : a ≠ 0) (hg : g ≠ 0) :
    thermalGradient σ (lowQuarter a g) (lowWeights a g e v R) A (seedTwo σ) =
      (R*e) • edge σ A 0 2 + (v/a) • edge σ A 1 2 := by
  rw [← population_seedTwo, thermalGradient_population]
  have hw : (fun i j =>
      lowQuarter a g i * lowWeights a g e v R i j *
          (lowQuarter a g j)⁻¹ * (![0,0,1] : Fin 3 → ℂ) j -
        (![0,0,1] : Fin 3 → ℂ) i * ((lowQuarter a g i)⁻¹ *
          lowWeights a g e v R i j * lowQuarter a g j)) =
      highCrossWeights (R*e) (v/a) := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowQuarter, lowWeights, highCrossWeights] <;>
      field_simp [ha, hg]
    all_goals ring
  rw [hw, spectralFilter_highCrossWeights]

/-- Far Ratio eq small mul collision for the stated finite source data. -/
theorem farRatio_eq_small_mul_collision (S s : ℝ) :
    farRatio S s = smallAmplitude s * collisionParameter S s := by
  unfold farRatio smallAmplitude collisionParameter
  rw [← cexp_add]
  congr 1
  ring

/-- Gaussian second column for the stated finite source data. -/
theorem gaussian_second_column (σ : Perm) (S s : ℝ) (k : Fin 6) :
    actualGradient σ (lowEnergies S s) k (seedTwo σ) =
      smallAmplitude s •
        (edge σ (ThreeLevelWordDual.source k) 1 2 +
          (smallAmplitude S * collisionParameter S s) •
            edge σ (ThreeLevelWordDual.source k) 0 2) := by
  unfold actualGradient
  rw [low_quarter_profile, low_gaussian_weights, low_high_column σ _ _ _ _ _ _
    (quarterAmplitude_ne_zero s) (quarterAmplitude_ne_zero S)]
  rw [← small_mul_quarter s, mul_div_cancel_right₀ _ (quarterAmplitude_ne_zero s),
    farRatio_eq_small_mul_collision]
  simp only [smul_add, smul_smul]
  rw [show (smallAmplitude s * collisionParameter S s) * smallAmplitude S =
    smallAmplitude s * (smallAmplitude S * collisionParameter S s) by ring]
  abel

/-- Column Two eq edges for the stated finite source data. -/
theorem columnTwo_eq_edges (σ : Perm) (S s : ℝ) (k : Fin 6) :
    columnTwo σ S s k =
      edge σ (ThreeLevelWordDual.source k) 1 2 +
        (smallAmplitude S * collisionParameter S s) •
          edge σ (ThreeLevelWordDual.source k) 0 2 := by
  rw [columnTwo, gaussian_second_column]
  simp [smul_smul, smallAmplitude_ne_zero]

def scaledSource (σ : Perm) (S s : ℝ) (c d : ℂ) (Y : Operator 4)
    (k : Fin 6) : Operator 4 :=
  c • columnOne σ S s k + d • columnTwo σ S s k +
    actualGradient σ (lowEnergies S s) k Y

def coordinateMass (c d : ℂ) (Y : Operator 4) : ℝ :=
  Complex.normSq c + Complex.normSq d + hsSquare Y

def stackSquare (σ : Perm) (S s : ℝ) (c d : ℂ) (Y : Operator 4) : ℝ :=
  ∑ k : Fin 6, hsSquare (scaledSource σ S s c d Y k)

/-- This is the unresolved finite matrix certificate on the actual source
columns, for all complex coefficients and all true population-orthogonal
operators. Neither an external energy function nor an external gap occurs. -/
def ScaledStackBounds (σ : Perm) (S s m B : ℝ) : Prop :=
  ∀ (c d : ℂ) (Y : Operator 4), IsFast σ Y →
    m * coordinateMass c d Y ≤ stackSquare σ S s c d Y ∧
    stackSquare σ S s c d Y ≤ B * coordinateMass c d Y

/-- Actual Gradient coordinates for the stated finite source data. -/
theorem actualGradient_coordinates (σ : Perm) (S s : ℝ) (k : Fin 6)
    (X : Operator 4) :
    actualGradient σ (lowEnergies S s) k X =
      firstCoordinate σ S X • actualGradient σ (lowEnergies S s) k (seedOne σ s) +
      secondCoordinate σ s X • actualGradient σ (lowEnergies S s) k (seedTwo σ) +
      actualGradient σ (lowEnergies S s) k (fastPart σ X) := by
  conv_lhs => arg 4; rw [actual_decomposition σ S s X]
  simp only [actualGradient_add, actualGradient_smul, actualGradient_gibbs,
    smul_zero, zero_add]

/-- Actual Gradient eq scaled Source for the stated finite source data. -/
theorem actualGradient_eq_scaledSource (σ : Perm) (S s : ℝ) (k : Fin 6)
    (X : Operator 4) :
    actualGradient σ (lowEnergies S s) k X =
      scaledSource σ S s
        (smallAmplitude S * firstCoordinate σ S X)
        (smallAmplitude s * secondCoordinate σ s X) (fastPart σ X) k := by
  rw [actualGradient_coordinates]
  simp only [scaledSource, columnOne, columnTwo, smul_smul]
  have h1 : smallAmplitude S * firstCoordinate σ S X * (smallAmplitude S)⁻¹ =
      firstCoordinate σ S X := by
    field_simp [smallAmplitude_ne_zero S]
  have h2 : smallAmplitude s * secondCoordinate σ s X * (smallAmplitude s)⁻¹ =
      secondCoordinate σ s X := by
    field_simp [smallAmplitude_ne_zero s]
  rw [h1, h2]

def plainEnergy (σ : Perm) (S s : ℝ) (X : Operator 4) : ℝ :=
  (1/12 : ℝ) * ∑ k : Fin 6, hsSquare (actualGradient σ (lowEnergies S s) k X)

/-- Plain Energy nonneg for the stated finite source data. -/
theorem plainEnergy_nonneg (σ : Perm) (S s : ℝ) (X : Operator 4) :
    0 ≤ plainEnergy σ S s X := by
  unfold plainEnergy hsSquare
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => hsInner_self_nonneg _)

/-- Plain Energy eq scaled for the stated finite source data. -/
theorem plainEnergy_eq_scaled (σ : Perm) (S s : ℝ) (X : Operator 4) :
    plainEnergy σ S s X =
      (1/12 : ℝ) * stackSquare σ S s
        (smallAmplitude S * firstCoordinate σ S X)
        (smallAmplitude s * secondCoordinate σ s X) (fastPart σ X) := by
  unfold plainEnergy stackSquare
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  rw [actualGradient_eq_scaledSource]

/-- Plain Energy bounds for the stated finite source data. -/
theorem plainEnergy_bounds (σ : Perm) (S s m B : ℝ)
    (hcert : ScaledStackBounds σ S s m B) (X : Operator 4) :
    (m/12) * invariantMass σ S s X ≤ plainEnergy σ S s X ∧
    plainEnergy σ S s X ≤ (B/12) * invariantMass σ S s X := by
  have h := hcert (smallAmplitude S * firstCoordinate σ S X)
    (smallAmplitude s * secondCoordinate σ s X) (fastPart σ X) (fastPart_isFast σ X)
  rw [plainEnergy_eq_scaled]
  change m * invariantMass σ S s X ≤ _ ∧ _ ≤ B * invariantMass σ S s X at h
  constructor <;> nlinarith [h.1, h.2]

/-- Plain Energy eq normalized source for the stated finite source data. -/
theorem plainEnergy_eq_normalized_source (σ : Perm) (S s : ℝ) (X : Operator 4) :
    plainEnergy σ S s X =
      (1/2 : ℝ) * ∑ k : Fin 6,
        hsSquare (normalizedActualGradient σ (lowEnergies S s) k X) := by
  have h := congrArg Complex.re (normalized_parent_mass σ (lowEnergies S s) X)
  norm_num [plainEnergy, hsSquare, hsPair_eq_hsInner, Complex.mul_re] at h ⊢
  exact h.symm

/-! ## Probability clocks, with the actual spectral time scale -/

def physicalEnergies (β S s : ℝ) (i : Fin 3) : ℝ := lowEnergies S s i / β

/-- Physical Energies dimensionless for the stated finite source data. -/
theorem physicalEnergies_dimensionless (β S s : ℝ) (hβ : β ≠ 0) (i : Fin 3) :
    β * physicalEnergies β S s i = lowEnergies S s i := by
  unfold physicalEnergies
  field_simp

def clockEnergy (σ : Perm) (β S s : ℝ) (μ : Measure ℝ) (X : Operator 4) : ℝ :=
  ∫ t : ℝ, plainEnergy σ S s
    (timeConjugation σ (physicalEnergies β S s) t X) ∂μ

/-- Continuous time plain Energy for the stated finite source data. -/
theorem continuous_time_plainEnergy (σ : Perm) (S s : ℝ)
    (E : Fin 3 → ℝ) (X : Operator 4) :
    Continuous (fun t : ℝ => plainEnergy σ S s (timeConjugation σ E t X)) := by
  unfold plainEnergy hsSquare hsInner actualGradient thermalGradient
    timeConjugation timeUnitary population bohrPhase Matrix.trace
  fun_prop

/-- Time plain Energy integrable for the stated finite source data. -/
theorem time_plainEnergy_integrable (σ : Perm) (S s m B : ℝ)
    (hcert : ScaledStackBounds σ S s m B)
    (E : Fin 3 → ℝ) (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Operator 4) :
    Integrable (fun t : ℝ => plainEnergy σ S s (timeConjugation σ E t X)) μ := by
  apply Integrable.of_bound (C := (B/12) * invariantMass σ S s X)
  · exact (continuous_time_plainEnergy σ S s E X).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg (plainEnergy_nonneg σ S s _)]
      have h := (plainEnergy_bounds σ S s m B hcert (timeConjugation σ E t X)).2
      rwa [invariantMass_timeConjugation] at h

/-- Clock Energy bounds for the stated finite source data. -/
theorem clockEnergy_bounds (σ : Perm) (β S s m B : ℝ)
    (hcert : ScaledStackBounds σ S s m B)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Operator 4) :
    (m/12) * invariantMass σ S s X ≤ clockEnergy σ β S s μ X ∧
    clockEnergy σ β S s μ X ≤ (B/12) * invariantMass σ S s X := by
  have hint := time_plainEnergy_integrable σ S s m B hcert
    (physicalEnergies β S s) μ X
  have hp (t : ℝ) := plainEnergy_bounds σ S s m B hcert
    (timeConjugation σ (physicalEnergies β S s) t X)
  simp only [invariantMass_timeConjugation] at hp
  constructor
  · have h := integral_mono (integrable_const ((m/12) * invariantMass σ S s X)) hint
      (fun t => (hp t).1)
    simpa only [integral_const, probReal_univ, one_smul, clockEnergy] using h
  · have h := integral_mono hint (integrable_const ((B/12) * invariantMass σ S s X))
      (fun t => (hp t).2)
    simpa only [integral_const, probReal_univ, one_smul, clockEnergy] using h

/-- Clock Energy comparison for the stated finite source data. -/
theorem clockEnergy_comparison (σ : Perm) (β S s m B : ℝ)
    (hm : 0 < m) (hB : 0 ≤ B) (hcert : ScaledStackBounds σ S s m B)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy σ β S s ν X ≤ (B/m) * clockEnergy σ β S s μ X := by
  have hlo := (clockEnergy_bounds σ β S s m B hcert μ X).1
  have hhi := (clockEnergy_bounds σ β S s m B hcert ν X).2
  have h1 := mul_le_mul_of_nonneg_left hlo hB
  have h2 := mul_le_mul_of_nonneg_left hhi hm.le
  have h : m * clockEnergy σ β S s ν X ≤ B * clockEnergy σ β S s μ X := by
    nlinarith
  calc
    _ ≤ (B * clockEnergy σ β S s μ X) / m := (le_div_iff₀ hm).mpr (by simpa [mul_comm] using h)
    _ = _ := by ring

/-- Clock Energy comparison 928 for the stated finite source data. -/
theorem clockEnergy_comparison_928 (σ : Perm) (β S s : ℝ)
    (hcert : ScaledStackBounds σ S s (1/8) 116)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy σ β S s ν X ≤ 928 * clockEnergy σ β S s μ X := by
  convert clockEnergy_comparison σ β S s (1/8) 116
    (by norm_num) (by norm_num) hcert μ ν X using 1
  norm_num

/-- Clock Energy comparison 204 for the stated finite source data. -/
theorem clockEnergy_comparison_204 (σ : Perm) (β S s : ℝ)
    (hcert : ScaledStackBounds σ S s (1/6) 34)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy σ β S s ν X ≤ 204 * clockEnergy σ β S s μ X := by
  convert clockEnergy_comparison σ β S s (1/6) 34
    (by norm_num) (by norm_num) hcert μ ν X using 1
  norm_num


/-! ## Actual Gibbs line and the positive invariant reference form -/

/-- The actual Hilbert--Schmidt square is nonnegative for every complex input. -/
theorem hsSquare_nonneg (X : Operator 4) : 0 ≤ hsSquare X :=
  hsInner_self_nonneg X

/-- Hs Square eq zero iff for the stated finite source data. -/
theorem hsSquare_eq_zero_iff (X : Operator 4) : hsSquare X = 0 ↔ X = 0 := by
  constructor
  · intro h
    by_contra hX
    have hp := hsInner_self_pos hX
    change (hsInner X X).re = 0 at h
    linarith
  · rintro rfl
    simp [hsSquare, hsInner]

/-- Population Coefficient gibbs low for the stated finite source data. -/
theorem populationCoefficient_gibbs_low (σ : Perm) (S s : ℝ) :
    populationCoefficient σ (gibbsRoot σ (lowEnergies S s)) =
      ![1, halfAmplitude S, halfAmplitude S * halfAmplitude s] := by
  rw [low_gibbs_profile, populationCoefficient_population]

/-- First Coordinate gibbs smul for the stated finite source data. -/
theorem firstCoordinate_gibbs_smul (σ : Perm) (S s : ℝ) (c : ℂ) :
    firstCoordinate σ S (c • gibbsRoot σ (lowEnergies S s)) = 0 := by
  simp [firstCoordinate, populationCoefficient_smul, populationCoefficient_gibbs_low]
  ring

/-- Second Coordinate gibbs smul for the stated finite source data. -/
theorem secondCoordinate_gibbs_smul (σ : Perm) (S s : ℝ) (c : ℂ) :
    secondCoordinate σ s (c • gibbsRoot σ (lowEnergies S s)) = 0 := by
  simp [secondCoordinate, populationCoefficient_smul, populationCoefficient_gibbs_low]
  ring

/-- Fast Part gibbs smul for the stated finite source data. -/
theorem fastPart_gibbs_smul (σ : Perm) (E : Fin 3 → ℝ) (c : ℂ) :
    fastPart σ (c • gibbsRoot σ E) = 0 := by
  rw [gibbsRoot, ← population_smul, fastPart_population]

/-- Invariant Mass gibbs smul for the stated finite source data. -/
theorem invariantMass_gibbs_smul (σ : Perm) (S s : ℝ) (c : ℂ) :
    invariantMass σ S s (c • gibbsRoot σ (lowEnergies S s)) = 0 := by
  simp [invariantMass, firstCoordinate_gibbs_smul, secondCoordinate_gibbs_smul,
    fastPart_gibbs_smul, hsSquare, hsInner]

/-- Invariant Mass eq zero iff for the stated finite source data. -/
theorem invariantMass_eq_zero_iff (σ : Perm) (S s : ℝ) (X : Operator 4) :
    invariantMass σ S s X = 0 ↔
      ∃ c : ℂ, X = c • gibbsRoot σ (lowEnergies S s) := by
  constructor
  · intro h
    have h1 := Complex.normSq_nonneg (smallAmplitude S * firstCoordinate σ S X)
    have h2 := Complex.normSq_nonneg (smallAmplitude s * secondCoordinate σ s X)
    have h3 := hsSquare_nonneg (fastPart σ X)
    change Complex.normSq (smallAmplitude S * firstCoordinate σ S X) +
      Complex.normSq (smallAmplitude s * secondCoordinate σ s X) +
      hsSquare (fastPart σ X) = 0 at h
    have h10 : Complex.normSq (smallAmplitude S * firstCoordinate σ S X) = 0 := by
      linarith
    have h20 : Complex.normSq (smallAmplitude s * secondCoordinate σ s X) = 0 := by
      linarith
    have h30 : hsSquare (fastPart σ X) = 0 := by linarith
    have hc1 : firstCoordinate σ S X = 0 :=
      (mul_eq_zero.mp (Complex.normSq_eq_zero.mp h10)).resolve_left (smallAmplitude_ne_zero S)
    have hc2 : secondCoordinate σ s X = 0 :=
      (mul_eq_zero.mp (Complex.normSq_eq_zero.mp h20)).resolve_left (smallAmplitude_ne_zero s)
    have hf := (hsSquare_eq_zero_iff _).mp h30
    refine ⟨populationCoefficient σ X 0, ?_⟩
    simpa only [hc1, hc2, hf, zero_smul, add_zero] using actual_decomposition σ S s X
  · rintro ⟨c, rfl⟩
    exact invariantMass_gibbs_smul σ S s c

/-- Plain Energy gibbs smul for the stated finite source data. -/
theorem plainEnergy_gibbs_smul (σ : Perm) (S s : ℝ) (c : ℂ) :
    plainEnergy σ S s (c • gibbsRoot σ (lowEnergies S s)) = 0 := by
  simp [plainEnergy, actualGradient_smul, actualGradient_gibbs, hsSquare, hsInner]

/-- Time Conjugation smul for the stated finite source data. -/
theorem timeConjugation_smul (σ : Perm) (E : Fin 3 → ℝ) (t : ℝ)
    (c : ℂ) (X : Operator 4) :
    timeConjugation σ E t (c • X) = c • timeConjugation σ E t X := by
  simp [timeConjugation]

/-- Clock Energy gibbs smul for the stated finite source data. -/
theorem clockEnergy_gibbs_smul (σ : Perm) (β S s : ℝ) (μ : Measure ℝ) (c : ℂ) :
    clockEnergy σ β S s μ (c • gibbsRoot σ (lowEnergies S s)) = 0 := by
  have ht (t : ℝ) :
      timeConjugation σ (physicalEnergies β S s) t
        (c • gibbsRoot σ (lowEnergies S s)) = c • gibbsRoot σ (lowEnergies S s) := by
    rw [timeConjugation_smul, gibbsRoot, timeConjugation_population]
  simp only [clockEnergy, ht, plainEnergy_gibbs_smul, integral_zero]

/-- Clock Energy eq zero iff for the stated finite source data. -/
theorem clockEnergy_eq_zero_iff (σ : Perm) (β S s m B : ℝ)
    (hm : 0 < m) (hcert : ScaledStackBounds σ S s m B)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Operator 4) :
    clockEnergy σ β S s μ X = 0 ↔
      ∃ c : ℂ, X = c • gibbsRoot σ (lowEnergies S s) := by
  constructor
  · intro h
    have hlo := (clockEnergy_bounds σ β S s m B hcert μ X).1
    rw [h] at hlo
    have hmass : invariantMass σ S s X ≤ 0 := by
      by_contra hpos
      have hp : 0 < invariantMass σ S s X := lt_of_not_ge hpos
      have hprod := mul_pos (div_pos hm (by norm_num : (0 : ℝ) < 12)) hp
      linarith
    exact (invariantMass_eq_zero_iff σ S s X).mp
      (le_antisymm hmass (invariantMass_nonneg σ S s X))
  · rintro ⟨c, rfl⟩
    exact clockEnergy_gibbs_smul σ β S s μ c

/-- Clock Energy pos of not gibbs for the stated finite source data. -/
theorem clockEnergy_pos_of_not_gibbs (σ : Perm) (β S s m B : ℝ)
    (hm : 0 < m) (hcert : ScaledStackBounds σ S s m B)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Operator 4)
    (hX : ¬ ∃ c : ℂ, X = c • gibbsRoot σ (lowEnergies S s)) :
    0 < clockEnergy σ β S s μ X := by
  have hmass : 0 < invariantMass σ S s X :=
    lt_of_le_of_ne (invariantMass_nonneg σ S s X)
      (Ne.symm (fun h => hX ((invariantMass_eq_zero_iff σ S s X).mp h)))
  exact (mul_pos (div_pos hm (by norm_num)) hmass).trans_le
    (clockEnergy_bounds σ β S s m B hcert μ X).1

/-- First Coordinate smul for the stated finite source data. -/
theorem firstCoordinate_smul (σ : Perm) (S : ℝ) (c : ℂ) (X : Operator 4) :
    firstCoordinate σ S (c • X) = c * firstCoordinate σ S X := by
  simp only [firstCoordinate, populationCoefficient_smul]
  ring

/-- Second Coordinate smul for the stated finite source data. -/
theorem secondCoordinate_smul (σ : Perm) (s : ℝ) (c : ℂ) (X : Operator 4) :
    secondCoordinate σ s (c • X) = c * secondCoordinate σ s X := by
  simp only [secondCoordinate, populationCoefficient_smul]
  ring

/-- Fast Part smul for the stated finite source data. -/
theorem fastPart_smul (σ : Perm) (c : ℂ) (X : Operator 4) :
    fastPart σ (c • X) = c • fastPart σ X := by
  simp only [fastPart, populationPart, populationCoefficient_smul, population_smul, smul_sub]

/-- Hs Square smul for the stated finite source data. -/
theorem hsSquare_smul (c : ℂ) (X : Operator 4) :
    hsSquare (c • X) = Complex.normSq c * hsSquare X := by
  rw [hsSquare, hsInner_smul_left, hsInner_smul_right, ← mul_assoc]
  rw [show star c * c = (Complex.normSq c : ℂ) from
    Complex.normSq_eq_conj_mul_self.symm, ofReal_mul_re]
  rfl

/-- Invariant Mass smul for the stated finite source data. -/
theorem invariantMass_smul (σ : Perm) (S s : ℝ) (c : ℂ) (X : Operator 4) :
    invariantMass σ S s (c • X) = Complex.normSq c * invariantMass σ S s X := by
  simp only [invariantMass, firstCoordinate_smul, secondCoordinate_smul, fastPart_smul,
    hsSquare_smul, Complex.normSq_mul]
  ring

/-- Time Conjugation zero for the stated finite source data. -/
theorem timeConjugation_zero (σ : Perm) (E : Fin 3 → ℝ) (X : Operator 4) :
    timeConjugation σ E 0 X = X := by
  simp [timeConjugation, timeUnitary, bohrPhase, population_one]

/-- Clock Energy dirac for the stated finite source data. -/
theorem clockEnergy_dirac (σ : Perm) (β S s t : ℝ) (X : Operator 4) :
    clockEnergy σ β S s (Measure.dirac t) X =
      plainEnergy σ S s (timeConjugation σ (physicalEnergies β S s) t X) := by
  simp [clockEnergy]

/-- Clock Energy dirac zero for the stated finite source data. -/
theorem clockEnergy_dirac_zero (σ : Perm) (β S s : ℝ) (X : Operator 4) :
    clockEnergy σ β S s (Measure.dirac 0) X = plainEnergy σ S s X := by
  rw [clockEnergy_dirac, timeConjugation_zero]

/-- Zero spacings profile for the stated finite source data. -/
theorem zero_spacings_profile : lowEnergies 0 0 = fun _ => 0 := by
  funext i
  fin_cases i <;> norm_num [lowEnergies]

/-- Plain Energy zero spacings for the stated finite source data. -/
theorem plainEnergy_zero_spacings (σ : Perm) (X : Operator 4) :
    plainEnergy σ 0 0 X =
      (1/12 : ℝ) * ∑ k : Fin 6,
        hsSquare (ThreeLevelWordDual.source k * X - X * ThreeLevelWordDual.source k) := by
  simp only [plainEnergy, zero_spacings_profile, actualGradient_zero_energies]

/-- Clock Energy zero spacings for the stated finite source data. -/
theorem clockEnergy_zero_spacings (σ : Perm) (β : ℝ)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (X : Operator 4) :
    clockEnergy σ β 0 0 μ X = plainEnergy σ 0 0 X := by
  have he : physicalEnergies β 0 0 = fun _ => 0 := by
    funext i
    change lowEnergies 0 0 i / β = 0
    rw [zero_spacings_profile]
    simp
  have ht (t : ℝ) : timeConjugation σ (fun _ => 0) t X = X := by
    simp [timeConjugation, timeUnitary, bohrPhase, population_one]
  simp [clockEnergy, he, ht]

/-- Clock Energy comparison 34 for the stated finite source data. -/
theorem clockEnergy_comparison_34 (σ : Perm) (β S s : ℝ)
    (hcert : ScaledStackBounds σ S s 1 34)
    (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : Operator 4) :
    clockEnergy σ β S s ν X ≤ 34 * clockEnergy σ β S s μ X := by
  simpa using clockEnergy_comparison σ β S s 1 34
    (by norm_num) (by norm_num) hcert μ ν X


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelInvariant
