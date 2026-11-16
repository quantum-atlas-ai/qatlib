/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCompactDomain
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockInvariantForm

@[expose] public section


/-!
# The complete five-variable Gaussian source

The two thermal legs retain their opposite spectral block directions. The
polynomial source uses the six original complex Pauli matrices, both population
columns, and arbitrary complex operator inputs. Its physical substitution is
proved without a fast-space hypothesis or any finite positivity certificate.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelFullCubeSource

open ThreeLevelCluster ThreeLevelCompactDomain ThreeLevelInvariant

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

/-- Adjacent low/middle gain, in variable order `(A,G,p,q,v)`. -/
def firstGain (z : Fin 5 → ℝ) : ℝ := z 2 * (3-z 0)/2

/-- Adjacent middle/high gain, in variable order `(A,G,p,q,v)`. -/
def secondGain (z : Fin 5 → ℝ) : ℝ := z 3 * (3-z 1)/2

/-- The far gain includes the mixed Gaussian factor. -/
def farGain (z : Fin 5 → ℝ) : ℝ := firstGain z * secondGain z * z 4

/-- The left thermal leg, with spectral block order unchanged. -/
def sharpWeights (z : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1, (firstGain z : ℂ), (farGain z : ℂ);
    (z 0 : ℂ) * (firstGain z : ℂ), 1, (secondGain z : ℂ);
    (z 0 : ℂ) * (z 1 : ℂ) * (farGain z : ℂ),
      (z 1 : ℂ) * (secondGain z : ℂ), 1]

/-- The right thermal leg has the reversed weight indices. -/
def flatWeights (z : Fin 5 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  (sharpWeights z).transpose

/-- This operator is defined on every complex matrix; its name only identifies
its use for the fast input in the complete source. -/
def fastSource (σ : Perm) (z : Fin 5 → ℝ) (k : Fin 6)
    (Y : Operator 4) : Operator 4 :=
  spectralFilter σ (sharpWeights z) (ThreeLevelWordDual.source k) * Y -
    Y * spectralFilter σ (flatWeights z) (ThreeLevelWordDual.source k)

def firstColumn (σ : Perm) (z : Fin 5 → ℝ) (k : Fin 6) : Operator 4 :=
  edge σ (ThreeLevelWordDual.source k) 0 1 +
    ((z 1 : ℂ) * (secondGain z : ℂ) * (z 4 : ℂ)) •
      edge σ (ThreeLevelWordDual.source k) 0 2

def secondColumn (σ : Perm) (z : Fin 5 → ℝ) (k : Fin 6) : Operator 4 :=
  edge σ (ThreeLevelWordDual.source k) 1 2 +
    ((firstGain z : ℂ) * (z 4 : ℂ)) •
      edge σ (ThreeLevelWordDual.source k) 0 2

/-- Both population coordinates and the complete complex operator input. -/
def cubeSource (σ : Perm) (z : Fin 5 → ℝ) (c d : ℂ) (Y : Operator 4)
    (k : Fin 6) : Operator 4 :=
  c • firstColumn σ z k + d • secondColumn σ z k + fastSource σ z k Y

/-- Fast Source add for the stated finite source data. -/
theorem fastSource_add (σ : Perm) (z : Fin 5 → ℝ) (k : Fin 6)
    (X Y : Operator 4) :
    fastSource σ z k (X+Y) = fastSource σ z k X + fastSource σ z k Y := by
  simp only [fastSource, Matrix.mul_add, Matrix.add_mul]
  abel

/-- Fast Source smul for the stated finite source data. -/
theorem fastSource_smul (σ : Perm) (z : Fin 5 → ℝ) (k : Fin 6)
    (c : ℂ) (X : Operator 4) :
    fastSource σ z k (c • X) = c • fastSource σ z k X := by
  simp only [fastSource, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- Fast Source zero for the stated finite source data. -/
theorem fastSource_zero (σ : Perm) (z : Fin 5 → ℝ) (k : Fin 6) :
    fastSource σ z k 0 = 0 := by
  simp [fastSource]

/-- Fast Source sum for the stated finite source data. -/
theorem fastSource_sum {ι : Type*} [Fintype ι] (σ : Perm)
    (z : Fin 5 → ℝ) (k : Fin 6) (v : ι → ℂ) (X : ι → Operator 4) :
    fastSource σ z k (∑ j, v j • X j) =
      ∑ j, v j • fastSource σ z k (X j) := by
  simp only [fastSource, Matrix.mul_sum, Matrix.sum_mul,
    Matrix.mul_smul, Matrix.smul_mul, smul_sub, Finset.sum_sub_distrib]

/-- First Gain cube Point for the stated finite source data. -/
theorem firstGain_cubePoint (S s : ℝ) (hS : 0 ≤ S) :
    firstGain (cubePoint S s) = gain S := by
  simpa [firstGain, cubePoint] using (gain_eq_compactAmplitude hS).symm

/-- Second Gain cube Point for the stated finite source data. -/
theorem secondGain_cubePoint (S s : ℝ) (hs : 0 ≤ s) :
    secondGain (cubePoint S s) = gain s := by
  simpa [secondGain, cubePoint] using (gain_eq_compactAmplitude hs).symm

/-- Far Gain cube Point for the stated finite source data. -/
theorem farGain_cubePoint (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s) :
    farGain (cubePoint S s) = gain (S+s) := by
  change firstGain (cubePoint S s) * secondGain (cubePoint S s) * mixedWeight S s = _
  rw [firstGain_cubePoint S s hS, secondGain_cubePoint S s hs, ← gain_add]

/-- First Gain complex cube Point for the stated finite source data. -/
theorem firstGain_complex_cubePoint (S s : ℝ) (hS : 0 ≤ S) :
    (firstGain (cubePoint S s) : ℂ) = smallAmplitude S := by
  rw [firstGain_cubePoint S s hS]
  rfl

/-- Second Gain complex cube Point for the stated finite source data. -/
theorem secondGain_complex_cubePoint (S s : ℝ) (hs : 0 ≤ s) :
    (secondGain (cubePoint S s) : ℂ) = smallAmplitude s := by
  rw [secondGain_cubePoint S s hs]
  rfl

/-- Far Gain complex cube Point for the stated finite source data. -/
theorem farGain_complex_cubePoint (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s) :
    (farGain (cubePoint S s) : ℂ) =
      smallAmplitude S * smallAmplitude s * collisionParameter S s := by
  simp only [farGain, Complex.ofReal_mul, firstGain_complex_cubePoint S s hS,
    secondGain_complex_cubePoint S s hs]
  rfl

/-- Every one of the nine sharp weights is the corresponding actual thermal
Gaussian coefficient. The equality retains the original row and column order. -/
theorem sharpWeights_cubePoint (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s) :
    sharpWeights (cubePoint S s) = fun i j =>
      quarterAmplitude (lowEnergies S s i) * gaussianWeights (lowEnergies S s) i j *
        (quarterAmplitude (lowEnergies S s j))⁻¹ := by
  have hA : (cubePoint S s 0 : ℂ) = (quarterAmplitude S)^2 :=
    (quarterAmplitude_sq_eq_halfWeight S).symm
  have hG : (cubePoint S s 1 : ℂ) = (quarterAmplitude s)^2 :=
    (quarterAmplitude_sq_eq_halfWeight s).symm
  have hq := low_quarter_profile S s
  have hw := low_gaussian_weights S s
  ext i j
  change sharpWeights (cubePoint S s) i j =
    (fun i => quarterAmplitude (lowEnergies S s i)) i *
      gaussianWeights (lowEnergies S s) i j *
        ((fun i => quarterAmplitude (lowEnergies S s i)) j)⁻¹
  rw [hq, hw]
  fin_cases i <;> fin_cases j <;>
    simp [sharpWeights, lowQuarter, lowWeights, hA, hG,
      firstGain_complex_cubePoint S s hS, secondGain_complex_cubePoint S s hs,
      farGain_complex_cubePoint S s hS hs, farRatio_eq_small_mul_collision,
      ← small_mul_quarter s] <;>
    field_simp [quarterAmplitude_ne_zero S, quarterAmplitude_ne_zero s]

/-- Gaussian Weights swap for the stated finite source data. -/
theorem gaussianWeights_swap (E : Fin 3 → ℝ) (i j : Fin 3) :
    gaussianWeights E j i = gaussianWeights E i j := by
  unfold gaussianWeights
  rw [← gaussianAmplitude_neg (E i-E j)]
  congr 1
  ring

/-- The flat coefficient is proved separately, with inverse quarter amplitude
on its row and quarter amplitude on its column. -/
theorem flatWeights_cubePoint (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s) :
    flatWeights (cubePoint S s) = fun i j =>
      (quarterAmplitude (lowEnergies S s i))⁻¹ *
        gaussianWeights (lowEnergies S s) i j * quarterAmplitude (lowEnergies S s j) := by
  ext i j
  change sharpWeights (cubePoint S s) j i = _
  rw [sharpWeights_cubePoint S s hS hs, gaussianWeights_swap]
  ring

/-- Exact identification of the complete left thermal leg. -/
theorem sharpFilter_cubePoint (σ : Perm) (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s)
    (A : Operator 4) :
    spectralFilter σ (sharpWeights (cubePoint S s)) A =
      population σ (fun i => quarterAmplitude (lowEnergies S s i)) *
        spectralFilter σ (gaussianWeights (lowEnergies S s)) A *
          population σ (fun i => (quarterAmplitude (lowEnergies S s i))⁻¹) := by
  rw [population_filter_population, sharpWeights_cubePoint S s hS hs]

/-- Exact identification of the complete right thermal leg. -/
theorem flatFilter_cubePoint (σ : Perm) (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s)
    (A : Operator 4) :
    spectralFilter σ (flatWeights (cubePoint S s)) A =
      population σ (fun i => (quarterAmplitude (lowEnergies S s i))⁻¹) *
        spectralFilter σ (gaussianWeights (lowEnergies S s)) A *
          population σ (fun i => quarterAmplitude (lowEnergies S s i)) := by
  rw [population_filter_population, flatWeights_cubePoint S s hS hs]

/-- Physical substitution holds for every complex matrix, not only fast inputs. -/
theorem fastSource_cubePoint (σ : Perm) (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s)
    (k : Fin 6) (Y : Operator 4) :
    fastSource σ (cubePoint S s) k Y = actualGradient σ (lowEnergies S s) k Y := by
  rw [fastSource, sharpFilter_cubePoint σ S s hS hs,
    flatFilter_cubePoint σ S s hS hs]
  rfl

/-- First Column cube Point for the stated finite source data. -/
theorem firstColumn_cubePoint (σ : Perm) (S s : ℝ) (hs : 0 ≤ s)
    (k : Fin 6) :
    firstColumn σ (cubePoint S s) k = columnOne σ S s k := by
  rw [columnOne_eq_edges, firstColumn, secondGain_complex_cubePoint S s hs,
    farRatio_eq_small_mul_collision, quarterAmplitude_sq_eq_halfWeight]
  simp [cubePoint, collisionParameter_eq_mixedWeight, mul_assoc]

/-- Second Column cube Point for the stated finite source data. -/
theorem secondColumn_cubePoint (σ : Perm) (S s : ℝ) (hS : 0 ≤ S)
    (k : Fin 6) :
    secondColumn σ (cubePoint S s) k = columnTwo σ S s k := by
  rw [columnTwo_eq_edges, secondColumn, firstGain_complex_cubePoint S s hS]
  rfl

/-- The complete polynomial source reconstructs the actual scaled source with
both complex population coefficients and an arbitrary complex operator input. -/
theorem cubeSource_cubePoint (σ : Perm) (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s)
    (c d : ℂ) (Y : Operator 4) (k : Fin 6) :
    cubeSource σ (cubePoint S s) c d Y k = scaledSource σ S s c d Y k := by
  rw [cubeSource, firstColumn_cubePoint σ S s hs,
    secondColumn_cubePoint σ S s hS, fastSource_cubePoint σ S s hS hs]
  rfl


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelFullCubeSource
