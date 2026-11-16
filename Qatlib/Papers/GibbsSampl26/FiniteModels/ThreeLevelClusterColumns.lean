/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelWordDual
public import Qatlib.Concepts.GibbsSource.SourceForms.LocalPauliNormalization

@[expose] public section


/-!
# Actual Gibbs-adapted columns at a three-level collision

The existing nonparity spectral projectors and all six original Pauli sources
are retained under every permutation of the three spectral labels. Spectral
block algebra proves the exact slow columns before any small-scale division.
Actual Gaussian weights, positive Gibbs mass, Hilbert--Schmidt centering,
register coordinates, and the physical one-twelfth source mass are connected
internally. No Schur inverse, finite gap estimate, or asymptotic conclusion is
assumed or proved by this matrix-bridge module.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators

open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCluster

set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

noncomputable section

abbrev Perm := Equiv.Perm (Fin 3)

def spectralProjectors (σ : Perm) (i : Fin 3) : Operator 4 :=
  ThreeLevelWordDual.projectors (σ i)

/-- Spectral Projectors mul for the stated finite source data. -/
theorem spectralProjectors_mul (σ : Perm) (i j : Fin 3) :
    spectralProjectors σ i * spectralProjectors σ j =
      if i = j then spectralProjectors σ i else 0 := by
  simp [spectralProjectors, ThreeLevelWordDual.projectors_mul]

/-- Spectral Projectors sum for the stated finite source data. -/
theorem spectralProjectors_sum (σ : Perm) :
    (∑ i : Fin 3, spectralProjectors σ i) = 1 := by
  simpa only [spectralProjectors] using
    (Equiv.sum_comp σ ThreeLevelWordDual.projectors).trans
      ThreeLevelWordDual.projectors_sum

def population (σ : Perm) (v : Fin 3 → ℂ) : Operator 4 :=
  ∑ i, v i • spectralProjectors σ i

def spectralFilter (σ : Perm) (W : Matrix (Fin 3) (Fin 3) ℂ)
    (A : Operator 4) : Operator 4 :=
  ∑ i, ∑ j, W i j • (spectralProjectors σ i * A * spectralProjectors σ j)

/-- Population mul projector for the stated finite source data. -/
theorem population_mul_projector (σ : Perm) (v : Fin 3 → ℂ) (j : Fin 3) :
    population σ v * spectralProjectors σ j =
      v j • spectralProjectors σ j := by
  classical
  simp only [population, Finset.sum_mul, Matrix.smul_mul, spectralProjectors_mul]
  simp [smul_ite]

/-- Projector mul population for the stated finite source data. -/
theorem projector_mul_population (σ : Perm) (v : Fin 3 → ℂ) (i : Fin 3) :
    spectralProjectors σ i * population σ v =
      v i • spectralProjectors σ i := by
  classical
  simp only [population, Finset.mul_sum, Matrix.mul_smul, spectralProjectors_mul]
  simp [smul_ite]

/-- Population mul for the stated finite source data. -/
theorem population_mul (σ : Perm) (v w : Fin 3 → ℂ) :
    population σ v * population σ w =
      population σ (fun i => v i * w i) := by
  simp only [population, Finset.mul_sum, Matrix.mul_smul]
  change (∑ i, w i • (population σ v * spectralProjectors σ i)) = _
  simp only [population_mul_projector, smul_smul]
  simp [mul_comm]

/-- Population one for the stated finite source data. -/
theorem population_one (σ : Perm) :
    population σ (fun _ => 1) = 1 := by
  simpa [population] using spectralProjectors_sum σ

/-- Population mul filter for the stated finite source data. -/
theorem population_mul_filter (σ : Perm) (v : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A : Operator 4) :
    population σ v * spectralFilter σ W A =
      spectralFilter σ (fun i j => v i * W i j) A := by
  simp only [spectralFilter, Finset.mul_sum, Matrix.mul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← mul_assoc, ← mul_assoc, population_mul_projector, Matrix.smul_mul,
    Matrix.smul_mul, smul_smul]
  congr 1
  ring

/-- Filter mul population for the stated finite source data. -/
theorem filter_mul_population (σ : Perm) (v : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A : Operator 4) :
    spectralFilter σ W A * population σ v =
      spectralFilter σ (fun i j => W i j * v j) A := by
  simp only [spectralFilter, Finset.sum_mul, Matrix.smul_mul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [mul_assoc, projector_mul_population, Matrix.mul_smul, smul_smul]

/-- Population filter population for the stated finite source data. -/
theorem population_filter_population (σ : Perm) (v w : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A : Operator 4) :
    population σ v * spectralFilter σ W A * population σ w =
      spectralFilter σ (fun i j => v i * W i j * w j) A := by
  let L : Matrix (Fin 3) (Fin 3) ℂ := fun i j => v i * W i j
  have hL : population σ v * spectralFilter σ W A = spectralFilter σ L A := by
    simpa only [L] using! population_mul_filter σ v W A
  calc
    _ = spectralFilter σ L A * population σ w :=
      congrArg (fun Z : Operator 4 => Z * population σ w) hL
    _ = _ := by
      simpa only [L] using! filter_mul_population σ w L A

/-- Spectral Filter sub for the stated finite source data. -/
theorem spectralFilter_sub (σ : Perm)
    (W V : Matrix (Fin 3) (Fin 3) ℂ) (A : Operator 4) :
    spectralFilter σ W A - spectralFilter σ V A =
      spectralFilter σ (W - V) A := by
  simp only [spectralFilter, Matrix.sub_apply, sub_smul, Finset.sum_sub_distrib]

/-- Spectral Filter zero for the stated finite source data. -/
theorem spectralFilter_zero (σ : Perm) (A : Operator 4) :
    spectralFilter σ 0 A = 0 := by
  simp [spectralFilter]

def thermalGradient (σ : Perm) (d : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A X : Operator 4) : Operator 4 :=
  (population σ d * spectralFilter σ W A * population σ (fun i => (d i)⁻¹)) * X -
    X * (population σ (fun i => (d i)⁻¹) * spectralFilter σ W A * population σ d)

/-- Thermal Gradient population for the stated finite source data. -/
theorem thermalGradient_population (σ : Perm) (d v : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A : Operator 4) :
    thermalGradient σ d W A (population σ v) =
      spectralFilter σ
        (fun i j => d i * W i j * (d j)⁻¹ * v j -
          v i * ((d i)⁻¹ * W i j * d j)) A := by
  let L : Matrix (Fin 3) (Fin 3) ℂ := fun i j => d i * W i j * (d j)⁻¹
  let R : Matrix (Fin 3) (Fin 3) ℂ := fun i j => (d i)⁻¹ * W i j * d j
  let LV : Matrix (Fin 3) (Fin 3) ℂ := fun i j => L i j * v j
  let VR : Matrix (Fin 3) (Fin 3) ℂ := fun i j => v i * R i j
  have hL : population σ d * spectralFilter σ W A *
      population σ (fun i => (d i)⁻¹) = spectralFilter σ L A := by
    simpa only [L] using! population_filter_population σ d (fun i => (d i)⁻¹) W A
  have hR : population σ (fun i => (d i)⁻¹) * spectralFilter σ W A *
      population σ d = spectralFilter σ R A := by
    simpa only [R] using! population_filter_population σ (fun i => (d i)⁻¹) d W A
  have hLV : spectralFilter σ L A * population σ v = spectralFilter σ LV A := by
    simpa only [LV] using! filter_mul_population σ v L A
  have hVR : population σ v * spectralFilter σ R A = spectralFilter σ VR A := by
    simpa only [VR] using! population_mul_filter σ v R A
  have hcoeff : LV - VR =
      (fun i j => d i * W i j * (d j)⁻¹ * v j -
        v i * ((d i)⁻¹ * W i j * d j) : Matrix (Fin 3) (Fin 3) ℂ) := by
    ext i j
    rfl
  unfold thermalGradient
  calc
    _ = spectralFilter σ L A * population σ v -
        population σ v * spectralFilter σ R A :=
      congrArg₂ (fun X Y : Operator 4 => X * population σ v - population σ v * Y) hL hR
    _ = spectralFilter σ LV A - spectralFilter σ VR A :=
      congrArg₂ (fun X Y : Operator 4 => X - Y) hLV hVR
    _ = spectralFilter σ (LV - VR) A := spectralFilter_sub σ LV VR A
    _ = _ := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => spectralFilter σ M A) hcoeff

/-- Thermal Gradient gibbs for the stated finite source data. -/
theorem thermalGradient_gibbs (σ : Perm) (d : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A : Operator 4) :
    thermalGradient σ d W A (population σ (fun i => (d i)^2)) = 0 := by
  rw [thermalGradient_population]
  have hz : (fun i j => d i * W i j * (d j)⁻¹ * (d j)^2 -
      (d i)^2 * ((d i)⁻¹ * W i j * d j)) =
      (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
    funext i j
    simp only [Matrix.zero_apply]
    field_simp
    ring
  rw [hz, spectralFilter_zero]


/-- Population inverse for the stated finite source data. -/
theorem population_inverse (σ : Perm) (d : Fin 3 → ℂ)
    (hd : ∀ i, d i ≠ 0) :
    population σ d * population σ (fun i => (d i)⁻¹) = 1 := by
  rw [population_mul]
  simpa [hd] using population_one σ

/-- Population inverse left for the stated finite source data. -/
theorem population_inverse_left (σ : Perm) (d : Fin 3 → ℂ)
    (hd : ∀ i, d i ≠ 0) :
    population σ (fun i => (d i)⁻¹) * population σ d = 1 := by
  rw [population_mul]
  simpa [hd] using population_one σ

/-- Population square for the stated finite source data. -/
theorem population_square (σ : Perm) (d : Fin 3 → ℂ) :
    population σ d * population σ d = population σ (fun i => (d i)^2) := by
  simpa only [pow_two] using population_mul σ d d

/-- Thermal Gradient sub for the stated finite source data. -/
theorem thermalGradient_sub (σ : Perm) (d : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A X Y : Operator 4) :
    thermalGradient σ d W A (X-Y) =
      thermalGradient σ d W A X - thermalGradient σ d W A Y := by
  simp only [thermalGradient, mul_sub, sub_mul]
  abel

/-- Thermal Gradient smul for the stated finite source data. -/
theorem thermalGradient_smul (σ : Perm) (d : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A X : Operator 4) (c : ℂ) :
    thermalGradient σ d W A (c • X) = c • thermalGradient σ d W A X := by
  simp only [thermalGradient, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- Subtracting any Gibbs component preserves the exact small source column.
The orthogonal projection coefficient is allowed without an error estimate. -/
theorem thermalGradient_center (σ : Perm) (d : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A X : Operator 4) (c : ℂ) :
    thermalGradient σ d W A (X - c • population σ (fun i => (d i)^2)) =
      thermalGradient σ d W A X := by
  rw [thermalGradient_sub, thermalGradient_smul, thermalGradient_gibbs,
    smul_zero, sub_zero]

def edge (σ : Perm) (A : Operator 4) (i j : Fin 3) : Operator 4 :=
  spectralProjectors σ i * A * spectralProjectors σ j -
    spectralProjectors σ j * A * spectralProjectors σ i

def crossWeights (c d : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0,c,d; -c,0,0; -d,0,0]

/-- Spectral Filter cross Weights for the stated finite source data. -/
theorem spectralFilter_crossWeights (σ : Perm) (A : Operator 4) (c d : ℂ) :
    spectralFilter σ (crossWeights c d) A =
      c • edge σ A 0 1 + d • edge σ A 0 2 := by
  simp [spectralFilter, crossWeights, edge, Fin.sum_univ_succ, smul_sub]
  abel

/-- Internal cluster quarter ratio and the separated-cluster quarter ratio. -/
def lowQuarter (a g : ℂ) : Fin 3 → ℂ := ![1,g,g*a]

def highQuarter (a g : ℂ) : Fin 3 → ℂ := ![a*g,1,a]

def clusterWeights (a : ℂ) : Fin 3 → ℂ := ![0,1,a^2]

def isolatedWeights : Fin 3 → ℂ := ![1,0,0]

def lowWeights (a g e v R : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,e*g,R*e*g*a; e*g,1,v; R*e*g*a,v,1]

def highWeights (a g e v R : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,R*e*g*a,e*g; R*e*g*a,1,v; e*g,v,1]

def clusterRoot (σ : Perm) (a : ℂ) : Operator 4 :=
  population σ (clusterWeights a)

/-- Cluster Root formula for the stated finite source data. -/
theorem clusterRoot_formula (σ : Perm) (a : ℂ) :
    clusterRoot σ a = spectralProjectors σ 1 + a^2 • spectralProjectors σ 2 := by
  simp [clusterRoot, population, clusterWeights, Fin.sum_univ_succ]

/-- Isolated population for the stated finite source data. -/
theorem isolated_population (σ : Perm) :
    population σ isolatedWeights = spectralProjectors σ 0 := by
  simp [population, isolatedWeights, Fin.sum_univ_succ]

/-- Low Quarter ne zero for the stated finite source data. -/
theorem lowQuarter_ne_zero (a g : ℂ) (ha : a ≠ 0) (hg : g ≠ 0) (i : Fin 3) :
    lowQuarter a g i ≠ 0 := by
  fin_cases i <;> simp [lowQuarter, ha, hg]

/-- High Quarter ne zero for the stated finite source data. -/
theorem highQuarter_ne_zero (a g : ℂ) (ha : a ≠ 0) (hg : g ≠ 0) (i : Fin 3) :
    highQuarter a g i ≠ 0 := by
  fin_cases i <;> simp [highQuarter, ha, hg]

/-- The original Gaussian proposal is reconstructed before sharp/flat dressing.
All six physical sources are obtained by substituting ThreeLevelWordDual.source. -/
theorem low_cluster_column (σ : Perm) (A : Operator 4) (a g e v R : ℂ)
    (ha : a ≠ 0) (hg : g ≠ 0) :
    thermalGradient σ (lowQuarter a g) (lowWeights a g e v R) A
        (clusterRoot σ a) =
      e • (edge σ A 0 1 + (a^2*R) • edge σ A 0 2) := by
  rw [clusterRoot, thermalGradient_population]
  have hw : (fun i j =>
      lowQuarter a g i * lowWeights a g e v R i j *
          (lowQuarter a g j)⁻¹ * clusterWeights a j -
        clusterWeights a i * ((lowQuarter a g i)⁻¹ *
          lowWeights a g e v R i j * lowQuarter a g j)) =
      crossWeights e (e*(a^2*R)) := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowQuarter, lowWeights, clusterWeights, crossWeights] <;>
      field_simp [ha, hg] <;> ring
  rw [hw, spectralFilter_crossWeights]
  simp only [smul_add, smul_smul]

/-- High isolated column for the stated finite source data. -/
theorem high_isolated_column (σ : Perm) (A : Operator 4) (a g e v R : ℂ)
    (ha : a ≠ 0) (hg : g ≠ 0) :
    thermalGradient σ (highQuarter a g) (highWeights a g e v R) A
        (spectralProjectors σ 0) =
      (-e) • (R • edge σ A 0 1 + edge σ A 0 2) := by
  rw [← isolated_population σ, thermalGradient_population]
  have hw : (fun i j =>
      highQuarter a g i * highWeights a g e v R i j *
          (highQuarter a g j)⁻¹ * isolatedWeights j -
        isolatedWeights i * ((highQuarter a g i)⁻¹ *
          highWeights a g e v R i j * highQuarter a g j)) =
      crossWeights ((-e)*R) (-e) := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [highQuarter, highWeights, isolatedWeights, crossWeights] <;>
      field_simp [ha, hg]
    all_goals ring
  rw [hw, spectralFilter_crossWeights]
  simp only [smul_add, smul_smul]

/-- Low cluster centered for the stated finite source data. -/
theorem low_cluster_centered (σ : Perm) (A : Operator 4) (a g e v R c : ℂ)
    (ha : a ≠ 0) (hg : g ≠ 0) :
    thermalGradient σ (lowQuarter a g) (lowWeights a g e v R) A
      (clusterRoot σ a -
        c • population σ (fun i => (lowQuarter a g i)^2)) =
      e • (edge σ A 0 1 + (a^2*R) • edge σ A 0 2) := by
  rw [thermalGradient_center]
  exact low_cluster_column σ A a g e v R ha hg

/-- High isolated centered for the stated finite source data. -/
theorem high_isolated_centered (σ : Perm) (A : Operator 4) (a g e v R c : ℂ)
    (ha : a ≠ 0) (hg : g ≠ 0) :
    thermalGradient σ (highQuarter a g) (highWeights a g e v R) A
      (spectralProjectors σ 0 -
        c • population σ (fun i => (highQuarter a g i)^2)) =
      (-e) • (R • edge σ A 0 1 + edge σ A 0 2) := by
  rw [thermalGradient_center]
  exact high_isolated_column σ A a g e v R ha hg


def backgroundWeights (v : ℂ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![1,0,0; 0,1,v; 0,v,1]

/-- Low background weights for the stated finite source data. -/
theorem low_background_weights (a g v R : ℂ) :
    lowWeights a g 0 v R = backgroundWeights v := by
  simp [lowWeights, backgroundWeights]

/-- High background weights for the stated finite source data. -/
theorem high_background_weights (a g v R : ℂ) :
    highWeights a g 0 v R = backgroundWeights v := by
  simp [highWeights, backgroundWeights]

/-- Low background cluster for the stated finite source data. -/
theorem low_background_cluster (σ : Perm) (A : Operator 4) (a g v : ℂ)
    (ha : a ≠ 0) (hg : g ≠ 0) :
    thermalGradient σ (lowQuarter a g) (backgroundWeights v) A
      (clusterRoot σ a) = 0 := by
  simpa only [low_background_weights, zero_smul] using
    low_cluster_column σ A a g 0 v 1 ha hg

/-- High background isolated for the stated finite source data. -/
theorem high_background_isolated (σ : Perm) (A : Operator 4) (a g v : ℂ)
    (ha : a ≠ 0) (hg : g ≠ 0) :
    thermalGradient σ (highQuarter a g) (backgroundWeights v) A
      (spectralProjectors σ 0) = 0 := by
  simpa only [high_background_weights, neg_zero, zero_smul] using
    high_isolated_column σ A a g 0 v 1 ha hg

/-- Low background isolated for the stated finite source data. -/
theorem low_background_isolated (σ : Perm) (A : Operator 4) (a g v : ℂ) :
    thermalGradient σ (lowQuarter a g) (backgroundWeights v) A
      (spectralProjectors σ 0) = 0 := by
  rw [← isolated_population σ, thermalGradient_population]
  have hz : (fun i j =>
      lowQuarter a g i * backgroundWeights v i j * (lowQuarter a g j)⁻¹ *
          isolatedWeights j -
        isolatedWeights i * ((lowQuarter a g i)⁻¹ *
          backgroundWeights v i j * lowQuarter a g j)) =
      (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowQuarter, backgroundWeights, isolatedWeights]
  rw [hz, spectralFilter_zero]

/-- High background cluster for the stated finite source data. -/
theorem high_background_cluster (σ : Perm) (A : Operator 4) (a g v : ℂ) :
    thermalGradient σ (highQuarter a g) (backgroundWeights v) A
      (clusterRoot σ a) = 0 := by
  rw [clusterRoot, thermalGradient_population]
  have hz : (fun i j =>
      highQuarter a g i * backgroundWeights v i j * (highQuarter a g j)⁻¹ *
          clusterWeights a j -
        clusterWeights a i * ((highQuarter a g i)⁻¹ *
          backgroundWeights v i j * highQuarter a g j)) =
      (0 : Matrix (Fin 3) (Fin 3) ℂ) := by
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [highQuarter, backgroundWeights, clusterWeights] <;>
      field_simp <;> ring
  rw [hz, spectralFilter_zero]

def cexp (x : ℝ) : ℂ := (Real.exp x : ℂ)

/-- Cexp add for the stated finite source data. -/
theorem cexp_add (x y : ℝ) : cexp (x+y) = cexp x * cexp y := by
  simp [cexp, Real.exp_add]

/-- Cexp ne zero for the stated finite source data. -/
theorem cexp_ne_zero (x : ℝ) : cexp x ≠ 0 := by
  unfold cexp
  exact_mod_cast Real.exp_ne_zero x

/-- Cexp zero for the stated finite source data. -/
theorem cexp_zero : cexp 0 = 1 := by simp [cexp]

def quarterAmplitude (z : ℝ) : ℂ := cexp (-z/4)
def gaussianAmplitude (z : ℝ) : ℂ := cexp (-z^2/8)
def smallAmplitude (z : ℝ) : ℂ := cexp (-z^2/8+z/4)
def farRatio (S s : ℝ) : ℂ := cexp (-S*s/4-s^2/8+s/4)
def collisionParameter (S s : ℝ) : ℂ := cexp (-S*s/4)

/-- Quarter Amplitude ne zero for the stated finite source data. -/
theorem quarterAmplitude_ne_zero (z : ℝ) : quarterAmplitude z ≠ 0 :=
  cexp_ne_zero _

/-- Gaussian Amplitude neg for the stated finite source data. -/
theorem gaussianAmplitude_neg (z : ℝ) :
    gaussianAmplitude (-z) = gaussianAmplitude z := by
  simp [gaussianAmplitude]

/-- Gaussian Amplitude neg sub for the stated finite source data. -/
theorem gaussianAmplitude_neg_sub (S s : ℝ) :
    gaussianAmplitude (-S-s) = gaussianAmplitude (S+s) := by
  unfold gaussianAmplitude
  congr 1
  ring

/-- Gaussian Amplitude zero for the stated finite source data. -/
theorem gaussianAmplitude_zero : gaussianAmplitude 0 = 1 := by
  simp [gaussianAmplitude, cexp]

/-- Quarter Amplitude zero for the stated finite source data. -/
theorem quarterAmplitude_zero : quarterAmplitude 0 = 1 := by
  simp [quarterAmplitude, cexp]

/-- Quarter Amplitude add for the stated finite source data. -/
theorem quarterAmplitude_add (S s : ℝ) :
    quarterAmplitude (S+s) = quarterAmplitude S * quarterAmplitude s := by
  unfold quarterAmplitude
  rw [← cexp_add]
  congr 1
  ring

/-- Quarter Amplitude square for the stated finite source data. -/
theorem quarterAmplitude_square (s : ℝ) :
    (quarterAmplitude s)^2 = cexp (-s/2) := by
  rw [pow_two, quarterAmplitude, ← cexp_add]
  congr 1
  ring

/-- Small mul quarter for the stated finite source data. -/
theorem small_mul_quarter (S : ℝ) :
    smallAmplitude S * quarterAmplitude S = gaussianAmplitude S := by
  unfold smallAmplitude quarterAmplitude gaussianAmplitude
  rw [← cexp_add]
  congr 1
  ring

/-- Far small mul quarters for the stated finite source data. -/
theorem far_small_mul_quarters (S s : ℝ) :
    farRatio S s * smallAmplitude S * quarterAmplitude S * quarterAmplitude s =
      gaussianAmplitude (S+s) := by
  unfold farRatio smallAmplitude quarterAmplitude gaussianAmplitude
  rw [← cexp_add, ← cexp_add, ← cexp_add]
  congr 1
  ring

/-- Far Ratio factor for the stated finite source data. -/
theorem farRatio_factor (S s : ℝ) :
    farRatio S s = collisionParameter S s * cexp (-s^2/8+s/4) := by
  unfold farRatio collisionParameter
  rw [← cexp_add]
  congr 1
  ring

/-- Low far Ratio factor for the stated finite source data. -/
theorem low_farRatio_factor (S s : ℝ) :
    (quarterAmplitude s)^2 * farRatio S s =
      collisionParameter S s * cexp (-s^2/8-s/4) := by
  rw [quarterAmplitude_square]
  unfold farRatio collisionParameter
  rw [← cexp_add, ← cexp_add]
  congr 1
  ring

def lowEnergies (S s : ℝ) : Fin 3 → ℝ := ![0,S,S+s]
def highEnergies (S s : ℝ) : Fin 3 → ℝ := ![S+s,0,s]

def gaussianWeights (E : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  fun i j => gaussianAmplitude (E i-E j)

/-- Gaussian proposal from every true spectral block and the original source. -/
def gaussianSource (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6) : Operator 4 :=
  spectralFilter σ (gaussianWeights E) (ThreeLevelWordDual.source k)

def actualGradient (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (X : Operator 4) : Operator 4 :=
  thermalGradient σ (fun i => quarterAmplitude (E i))
    (gaussianWeights E) (ThreeLevelWordDual.source k) X

def gibbsRoot (σ : Perm) (E : Fin 3 → ℝ) : Operator 4 :=
  population σ (fun i => cexp (-E i/2))

/-- Quarter square population for the stated finite source data. -/
theorem quarter_square_population (σ : Perm) (E : Fin 3 → ℝ) :
    population σ (fun i => (quarterAmplitude (E i))^2) = gibbsRoot σ E := by
  simp only [quarterAmplitude_square, gibbsRoot]

/-- Actual Gradient gibbs for the stated finite source data. -/
theorem actualGradient_gibbs (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6) :
    actualGradient σ E k (gibbsRoot σ E) = 0 := by
  rw [← quarter_square_population]
  exact thermalGradient_gibbs _ _ _ _

/-- Actual Gradient center for the stated finite source data. -/
theorem actualGradient_center (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (X : Operator 4) (c : ℂ) :
    actualGradient σ E k (X - c • gibbsRoot σ E) = actualGradient σ E k X := by
  rw [← quarter_square_population]
  exact thermalGradient_center _ _ _ _ _ _

/-- Low quarter profile for the stated finite source data. -/
theorem low_quarter_profile (S s : ℝ) :
    (fun i => quarterAmplitude (lowEnergies S s i)) =
      lowQuarter (quarterAmplitude s) (quarterAmplitude S) := by
  funext i
  fin_cases i <;>
    simp [lowEnergies, lowQuarter, quarterAmplitude_zero, quarterAmplitude_add]

/-- High quarter profile for the stated finite source data. -/
theorem high_quarter_profile (S s : ℝ) :
    (fun i => quarterAmplitude (highEnergies S s i)) =
      highQuarter (quarterAmplitude s) (quarterAmplitude S) := by
  funext i
  fin_cases i <;>
    simp [highEnergies, highQuarter, quarterAmplitude_zero, quarterAmplitude_add, mul_comm]

/-- Low gaussian weights for the stated finite source data. -/
theorem low_gaussian_weights (S s : ℝ) :
    gaussianWeights (lowEnergies S s) =
      lowWeights (quarterAmplitude s) (quarterAmplitude S)
        (smallAmplitude S) (gaussianAmplitude s) (farRatio S s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaussianWeights, lowEnergies, lowWeights, gaussianAmplitude_zero,
      gaussianAmplitude_neg, gaussianAmplitude_neg_sub, small_mul_quarter, far_small_mul_quarters,
      sub_add_eq_sub_sub]

/-- High gaussian weights for the stated finite source data. -/
theorem high_gaussian_weights (S s : ℝ) :
    gaussianWeights (highEnergies S s) =
      highWeights (quarterAmplitude s) (quarterAmplitude S)
        (smallAmplitude S) (gaussianAmplitude s) (farRatio S s) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [gaussianWeights, highEnergies, highWeights, gaussianAmplitude_zero,
      gaussianAmplitude_neg, gaussianAmplitude_neg_sub, small_mul_quarter, far_small_mul_quarters,
      sub_add_eq_sub_sub]

/-- J1 for the actual Gaussian source at arbitrary dimensionless S and s. -/
theorem gaussian_low_column (σ : Perm) (S s : ℝ) (k : Fin 6) :
    actualGradient σ (lowEnergies S s) k (clusterRoot σ (quarterAmplitude s)) =
      smallAmplitude S •
        (edge σ (ThreeLevelWordDual.source k) 0 1 +
          ((quarterAmplitude s)^2 * farRatio S s) •
            edge σ (ThreeLevelWordDual.source k) 0 2) := by
  unfold actualGradient
  rw [low_quarter_profile, low_gaussian_weights]
  exact low_cluster_column σ _ _ _ _ _ _
    (quarterAmplitude_ne_zero s) (quarterAmplitude_ne_zero S)

/-- J2 retains the farther/nearer amplitudes for the reverse energy orientation. -/
theorem gaussian_high_column (σ : Perm) (S s : ℝ) (k : Fin 6) :
    actualGradient σ (highEnergies S s) k (spectralProjectors σ 0) =
      (-smallAmplitude S) •
        (farRatio S s • edge σ (ThreeLevelWordDual.source k) 0 1 +
          edge σ (ThreeLevelWordDual.source k) 0 2) := by
  unfold actualGradient
  rw [high_quarter_profile, high_gaussian_weights]
  exact high_isolated_column σ _ _ _ _ _ _
    (quarterAmplitude_ne_zero s) (quarterAmplitude_ne_zero S)

/-- Gaussian low centered for the stated finite source data. -/
theorem gaussian_low_centered (σ : Perm) (S s : ℝ) (k : Fin 6) (c : ℂ) :
    actualGradient σ (lowEnergies S s) k
      (clusterRoot σ (quarterAmplitude s) - c • gibbsRoot σ (lowEnergies S s)) =
      smallAmplitude S •
        (edge σ (ThreeLevelWordDual.source k) 0 1 +
          (collisionParameter S s * cexp (-s^2/8-s/4)) •
            edge σ (ThreeLevelWordDual.source k) 0 2) := by
  rw [actualGradient_center, gaussian_low_column, low_farRatio_factor]

/-- Gaussian high centered for the stated finite source data. -/
theorem gaussian_high_centered (σ : Perm) (S s : ℝ) (k : Fin 6) (c : ℂ) :
    actualGradient σ (highEnergies S s) k
      (spectralProjectors σ 0 - c • gibbsRoot σ (highEnergies S s)) =
      (-smallAmplitude S) •
        ((collisionParameter S s * cexp (-s^2/8+s/4)) •
          edge σ (ThreeLevelWordDual.source k) 0 1 +
          edge σ (ThreeLevelWordDual.source k) 0 2) := by
  rw [actualGradient_center, gaussian_high_column, farRatio_factor]


/-! ## Actual Hilbert--Schmidt centering and the rank data -/

def projectorRank : Fin 3 → ℕ := ![2,1,1]

/-- Projector Rank pos for the stated finite source data. -/
theorem projectorRank_pos (i : Fin 3) : 0 < projectorRank i := by
  fin_cases i <;> norm_num [projectorRank]

/-- Trace projectors for the stated finite source data. -/
theorem trace_projectors (i : Fin 3) :
    Matrix.trace (ThreeLevelWordDual.projectors i) = (projectorRank i : ℂ) := by
  fin_cases i <;>
    norm_num [ThreeLevelWordDual.projectors, ThreeLevelWordDual.pZero,
      ThreeLevelWordDual.pOne, ThreeLevelWordDual.pTwo_entries, projectorRank,
      Matrix.trace, Fin.sum_univ_succ]

/-- Trace spectral Projectors for the stated finite source data. -/
theorem trace_spectralProjectors (σ : Perm) (i : Fin 3) :
    Matrix.trace (spectralProjectors σ i) = (projectorRank (σ i) : ℂ) :=
  trace_projectors (σ i)

/-- Spectral Projectors adjoint for the stated finite source data. -/
theorem spectralProjectors_adjoint (σ : Perm) (i : Fin 3) :
    (spectralProjectors σ i)ᴴ = spectralProjectors σ i :=
  ThreeLevelWordDual.projectors_hermitian (σ i)

/-- Population adjoint for the stated finite source data. -/
theorem population_adjoint (σ : Perm) (v : Fin 3 → ℂ) :
    (population σ v)ᴴ = population σ (fun i => star (v i)) := by
  simp only [population, Matrix.conjTranspose_sum, Matrix.conjTranspose_smul,
    spectralProjectors_adjoint]

/-- The complex Hilbert--Schmidt pairing, in the original physical coordinates. -/
def hsPair (X Y : Operator 4) : ℂ := Matrix.trace (Xᴴ * Y)

/-- Hs Pair population for the stated finite source data. -/
theorem hsPair_population (σ : Perm) (v w : Fin 3 → ℂ) :
    hsPair (population σ v) (population σ w) =
      ∑ i, star (v i) * w i * (projectorRank (σ i) : ℂ) := by
  unfold hsPair
  rw [population_adjoint, population_mul]
  simp only [population, Matrix.trace_sum, Matrix.trace_smul,
    trace_spectralProjectors, smul_eq_mul]

/-- Hs Pair sub right for the stated finite source data. -/
theorem hsPair_sub_right (X Y Z : Operator 4) :
    hsPair X (Y-Z) = hsPair X Y - hsPair X Z := by
  simp [hsPair, mul_sub]

/-- Hs Pair smul right for the stated finite source data. -/
theorem hsPair_smul_right (X Y : Operator 4) (c : ℂ) :
    hsPair X (c • Y) = c * hsPair X Y := by
  simp [hsPair]

/-- Cexp star for the stated finite source data. -/
theorem cexp_star (x : ℝ) : star (cexp x) = cexp x := by
  simp only [cexp, Complex.star_def, Complex.conj_ofReal]

/-- Cexp half mul for the stated finite source data. -/
theorem cexp_half_mul (x : ℝ) :
    cexp (-x/2) * cexp (-x/2) = cexp (-x) := by
  rw [← cexp_add]
  congr 1
  ring

def gibbsMass (σ : Perm) (E : Fin 3 → ℝ) : ℝ :=
  ∑ i, Real.exp (-E i) * (projectorRank (σ i) : ℝ)

/-- Gibbs Mass pos for the stated finite source data. -/
theorem gibbsMass_pos (σ : Perm) (E : Fin 3 → ℝ) :
    0 < gibbsMass σ E := by
  apply Finset.sum_pos
  · intro i _
    exact mul_pos (Real.exp_pos _) (Nat.cast_pos.mpr (projectorRank_pos (σ i)))
  · exact Finset.univ_nonempty

/-- Hs Pair gibbs for the stated finite source data. -/
theorem hsPair_gibbs (σ : Perm) (E : Fin 3 → ℝ) :
    hsPair (gibbsRoot σ E) (gibbsRoot σ E) = (gibbsMass σ E : ℂ) := by
  rw [gibbsRoot, hsPair_population]
  simp only [cexp_star, cexp_half_mul]
  simp [gibbsMass, cexp]

/-- Hs Pair gibbs ne zero for the stated finite source data. -/
theorem hsPair_gibbs_ne_zero (σ : Perm) (E : Fin 3 → ℝ) :
    hsPair (gibbsRoot σ E) (gibbsRoot σ E) ≠ 0 := by
  rw [hsPair_gibbs]
  exact_mod_cast (gibbsMass_pos σ E).ne'

def orthogonalCenter (X g : Operator 4) : Operator 4 :=
  X - (hsPair g X / hsPair g g) • g

/-- Hs Pair orthogonal Center for the stated finite source data. -/
theorem hsPair_orthogonalCenter (X g : Operator 4) (hg : hsPair g g ≠ 0) :
    hsPair g (orthogonalCenter X g) = 0 := by
  rw [orthogonalCenter, hsPair_sub_right, hsPair_smul_right]
  field_simp
  ring

/-- Actual center orthogonal for the stated finite source data. -/
theorem actual_center_orthogonal (σ : Perm) (E : Fin 3 → ℝ) (X : Operator 4) :
    hsPair (gibbsRoot σ E) (orthogonalCenter X (gibbsRoot σ E)) = 0 :=
  hsPair_orthogonalCenter X _ (hsPair_gibbs_ne_zero σ E)

/-- Actual Gradient orthogonal Center for the stated finite source data. -/
theorem actualGradient_orthogonalCenter (σ : Perm) (E : Fin 3 → ℝ)
    (k : Fin 6) (X : Operator 4) :
    actualGradient σ E k (orthogonalCenter X (gibbsRoot σ E)) =
      actualGradient σ E k X :=
  actualGradient_center σ E k X _

/-- Gaussian low orthogonal for the stated finite source data. -/
theorem gaussian_low_orthogonal (σ : Perm) (S s : ℝ) (k : Fin 6) :
    actualGradient σ (lowEnergies S s) k
      (orthogonalCenter (clusterRoot σ (quarterAmplitude s))
        (gibbsRoot σ (lowEnergies S s))) =
      smallAmplitude S •
        (edge σ (ThreeLevelWordDual.source k) 0 1 +
          (collisionParameter S s * cexp (-s^2/8-s/4)) •
            edge σ (ThreeLevelWordDual.source k) 0 2) := by
  rw [actualGradient_orthogonalCenter, gaussian_low_column, low_farRatio_factor]

/-- Gaussian high orthogonal for the stated finite source data. -/
theorem gaussian_high_orthogonal (σ : Perm) (S s : ℝ) (k : Fin 6) :
    actualGradient σ (highEnergies S s) k
      (orthogonalCenter (spectralProjectors σ 0)
        (gibbsRoot σ (highEnergies S s))) =
      (-smallAmplitude S) •
        ((collisionParameter S s * cexp (-s^2/8+s/4)) •
          edge σ (ThreeLevelWordDual.source k) 0 1 +
          edge σ (ThreeLevelWordDual.source k) 0 2) := by
  rw [actualGradient_orthogonalCenter, gaussian_high_column, farRatio_factor]

def clusterProjector (σ : Perm) : Operator 4 :=
  spectralProjectors σ 1 + spectralProjectors σ 2

/-- Cluster Projector eq complement for the stated finite source data. -/
theorem clusterProjector_eq_complement (σ : Perm) :
    clusterProjector σ = 1 - spectralProjectors σ 0 := by
  have h := spectralProjectors_sum σ
  simp only [Fin.sum_univ_succ] at h
  apply eq_sub_iff_add_eq.mpr
  calc
    clusterProjector σ + spectralProjectors σ 0 =
        spectralProjectors σ 0 + (spectralProjectors σ 1 + (spectralProjectors σ 2 + 0)) := by
      unfold clusterProjector
      abel
    _ = 1 := h

/-- Cluster Root one for the stated finite source data. -/
theorem clusterRoot_one (σ : Perm) :
    clusterRoot σ 1 = clusterProjector σ := by
  simp [clusterRoot_formula, clusterProjector]

/-- Cluster Root zero for the stated finite source data. -/
theorem clusterRoot_zero (σ : Perm) :
    clusterRoot σ (quarterAmplitude 0) = clusterProjector σ := by
  simp [clusterRoot_formula, quarterAmplitude_zero, clusterProjector]

/-- Edge cluster for the stated finite source data. -/
theorem edge_cluster (σ : Perm) (A : Operator 4) :
    edge σ A 0 1 + edge σ A 0 2 =
      spectralProjectors σ 0 * A * clusterProjector σ -
        clusterProjector σ * A * spectralProjectors σ 0 := by
  simp only [edge, clusterProjector, mul_add, add_mul]
  abel

/-- Far Ratio zero for the stated finite source data. -/
theorem farRatio_zero (S : ℝ) : farRatio S 0 = 1 := by
  simp [farRatio, cexp]

/-- Endpoint low column for the stated finite source data. -/
theorem endpoint_low_column (σ : Perm) (S : ℝ) (k : Fin 6) :
    actualGradient σ (lowEnergies S 0) k (clusterProjector σ) =
      smallAmplitude S •
        (spectralProjectors σ 0 * ThreeLevelWordDual.source k * clusterProjector σ -
          clusterProjector σ * ThreeLevelWordDual.source k * spectralProjectors σ 0) := by
  have h := gaussian_low_column σ S 0 k
  simpa only [quarterAmplitude_zero, clusterRoot_one, one_pow, farRatio_zero,
    one_mul, one_smul, edge_cluster] using h

/-- Endpoint high column for the stated finite source data. -/
theorem endpoint_high_column (σ : Perm) (S : ℝ) (k : Fin 6) :
    actualGradient σ (highEnergies S 0) k (spectralProjectors σ 0) =
      (-smallAmplitude S) •
        (spectralProjectors σ 0 * ThreeLevelWordDual.source k * clusterProjector σ -
          clusterProjector σ * ThreeLevelWordDual.source k * spectralProjectors σ 0) := by
  have h := gaussian_high_column σ S 0 k
  simpa only [farRatio_zero, one_smul, edge_cluster] using h

/-- Trace cluster Projector for the stated finite source data. -/
theorem trace_clusterProjector (σ : Perm) :
    Matrix.trace (clusterProjector σ) =
      (projectorRank (σ 1) + projectorRank (σ 2) : ℂ) := by
  simp [clusterProjector, trace_spectralProjectors]

/-! ## Original register Pauli coordinates -/

def physicalGaussianSource (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6) :
    Operator (fullPauliDim 2) :=
  ∑ i : Fin 3, ∑ j : Fin 3, gaussianWeights E i j •
    (ExchangeCell.liftAlg (spectralProjectors σ i) *
      fullPauliFamily 2 (ThreeLevelWordDual.sourceLabel k) *
        ExchangeCell.liftAlg (spectralProjectors σ j))

/-- Physical Gaussian Source eq lift for the stated finite source data. -/
theorem physicalGaussianSource_eq_lift (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6) :
    physicalGaussianSource σ E k = ExchangeCell.liftAlg (gaussianSource σ E k) := by
  simp only [physicalGaussianSource, gaussianSource, spectralFilter,
    ThreeLevelWordDual.original_source, map_sum, map_smul, map_mul]

def physicalGradient (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (X : Operator (fullPauliDim 2)) : Operator (fullPauliDim 2) :=
  (ExchangeCell.liftAlg (population σ (fun i => quarterAmplitude (E i))) *
      physicalGaussianSource σ E k *
        ExchangeCell.liftAlg (population σ (fun i => (quarterAmplitude (E i))⁻¹))) * X -
    X * (ExchangeCell.liftAlg (population σ (fun i => (quarterAmplitude (E i))⁻¹)) *
      physicalGaussianSource σ E k *
        ExchangeCell.liftAlg (population σ (fun i => quarterAmplitude (E i))))

/-- Physical Gradient lift for the stated finite source data. -/
theorem physicalGradient_lift (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (X : Operator 4) :
    physicalGradient σ E k (ExchangeCell.liftAlg X) =
      ExchangeCell.liftAlg (actualGradient σ E k X) := by
  simp only [physicalGradient, physicalGaussianSource_eq_lift,
    actualGradient, thermalGradient, gaussianSource, map_sub, map_mul]

/-- Physical gaussian low orthogonal for the stated finite source data. -/
theorem physical_gaussian_low_orthogonal (σ : Perm) (S s : ℝ) (k : Fin 6) :
    physicalGradient σ (lowEnergies S s) k
      (ExchangeCell.liftAlg
        (orthogonalCenter (clusterRoot σ (quarterAmplitude s))
          (gibbsRoot σ (lowEnergies S s)))) =
      ExchangeCell.liftAlg
        (smallAmplitude S •
          (edge σ (ThreeLevelWordDual.source k) 0 1 +
            (collisionParameter S s * cexp (-s^2/8-s/4)) •
              edge σ (ThreeLevelWordDual.source k) 0 2)) := by
  rw [physicalGradient_lift, gaussian_low_orthogonal]

/-- Physical gaussian high orthogonal for the stated finite source data. -/
theorem physical_gaussian_high_orthogonal (σ : Perm) (S s : ℝ) (k : Fin 6) :
    physicalGradient σ (highEnergies S s) k
      (ExchangeCell.liftAlg
        (orthogonalCenter (spectralProjectors σ 0)
          (gibbsRoot σ (highEnergies S s)))) =
      ExchangeCell.liftAlg
        ((-smallAmplitude S) •
          ((collisionParameter S s * cexp (-s^2/8+s/4)) •
            edge σ (ThreeLevelWordDual.source k) 0 1 +
            edge σ (ThreeLevelWordDual.source k) 0 2)) := by
  rw [physicalGradient_lift, gaussian_high_orthogonal]



/-! ## Normalization and original-coordinate metric transport -/

/-- A common scalar coefficient factors out of the spectral population operator. -/
theorem population_smul (σ : Perm) (v : Fin 3 → ℂ) (c : ℂ) :
    population σ (fun i => c * v i) = c • population σ v := by
  simp only [population, Finset.smul_sum, smul_smul]

/-- Population inverse smul for the stated finite source data. -/
theorem population_inverse_smul (σ : Perm) (v : Fin 3 → ℂ) (c : ℂ) :
    population σ (fun i => (c * v i)⁻¹) =
      c⁻¹ • population σ (fun i => (v i)⁻¹) := by
  rw [← population_smul]
  congr 1
  funext i
  simp only [_root_.mul_inv_rev, mul_comm]

/-- The common partition-function factor in a Gibbs fourth root cancels
from both thermal conjugations. This applies to the complete gradient. -/
theorem thermalGradient_quarter_scale (σ : Perm) (d : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A X : Operator 4)
    (c : ℂ) (hc : c ≠ 0) :
    thermalGradient σ (fun i => c * d i) W A X = thermalGradient σ d W A X := by
  unfold thermalGradient
  simp only [population_smul, population_inverse_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul,
    mul_inv_cancel₀ hc, inv_mul_cancel₀ hc, one_smul]

/-- Gaussian Weights shift for the stated finite source data. -/
theorem gaussianWeights_shift (E : Fin 3 → ℝ) (c : ℝ) :
    gaussianWeights (fun i => E i + c) = gaussianWeights E := by
  ext i j
  simp [gaussianWeights]

/-- Actual Gradient energy shift for the stated finite source data. -/
theorem actualGradient_energy_shift (σ : Perm) (E : Fin 3 → ℝ)
    (k : Fin 6) (X : Operator 4) (c : ℝ) :
    actualGradient σ (fun i => E i + c) k X = actualGradient σ E k X := by
  have hq : (fun i => quarterAmplitude (E i+c)) =
      (fun i => quarterAmplitude c * quarterAmplitude (E i)) := by
    funext i
    rw [quarterAmplitude_add, mul_comm]
  unfold actualGradient
  rw [gaussianWeights_shift, hq]
  exact thermalGradient_quarter_scale _ _ _ _ _ _ (quarterAmplitude_ne_zero c)

/-- Hs Pair smul left for the stated finite source data. -/
theorem hsPair_smul_left (X Y : Operator 4) (c : ℂ) :
    hsPair (c • X) Y = star c * hsPair X Y := by
  simp [hsPair, Matrix.conjTranspose_smul]

/-- Orthogonal Center scale for the stated finite source data. -/
theorem orthogonalCenter_scale (X g : Operator 4) (c : ℂ)
    (hc : c ≠ 0) :
    orthogonalCenter X (c • g) = orthogonalCenter X g := by
  unfold orthogonalCenter
  rw [hsPair_smul_left, hsPair_smul_left, hsPair_smul_right, smul_smul]
  congr 1
  have hstar : star c ≠ 0 := by simpa using hc
  field_simp

/-- Trace lift for the stated finite source data. -/
theorem trace_lift (X : Operator 4) :
    Matrix.trace (ExchangeCell.liftAlg X) = Matrix.trace X := by
  calc
    Matrix.trace (ExchangeCell.liftAlg X) =
        ∑ i : Fin 4, ExchangeCell.liftAlg X (ExchangeCell.equiv i) (ExchangeCell.equiv i) :=
      (Equiv.sum_comp ExchangeCell.equiv
        (fun i => ExchangeCell.liftAlg X i i)).symm
    _ = Matrix.trace X := by
      simp only [ExchangeCell.liftAlg_apply_eq, Matrix.trace, Matrix.diag_apply]

/-- Hs Pair lift for the stated finite source data. -/
theorem hsPair_lift (X Y : Operator 4) :
    Matrix.trace ((ExchangeCell.liftAlg X)ᴴ * ExchangeCell.liftAlg Y) =
      hsPair X Y := by
  rw [ExchangeCell.liftAlg_star, ← map_mul, trace_lift]
  rfl

/-- Physical center orthogonal for the stated finite source data. -/
theorem physical_center_orthogonal (σ : Perm) (E : Fin 3 → ℝ) (X : Operator 4) :
    Matrix.trace ((ExchangeCell.liftAlg (gibbsRoot σ E))ᴴ *
      ExchangeCell.liftAlg (orthogonalCenter X (gibbsRoot σ E))) = 0 := by
  rw [hsPair_lift]
  exact actual_center_orthogonal σ E X



/-- This spectral Gaussian is definitionally the existing source model at the
original projector order; it is not an unrelated replacement proposal. -/
theorem gaussianSource_original_family (x c : ℝ) (k : Fin 6) :
    gaussianSource (Equiv.refl (Fin 3)) (ThreeLevelWordDual.energies x c) k =
      ThreeLevelWordDual.gaussianSource x c k := by
  rfl

/-- Spectral Filter one for the stated finite source data. -/
theorem spectralFilter_one (σ : Perm) (A : Operator 4) :
    spectralFilter σ (fun _ _ => 1) A = A := by
  calc
    spectralFilter σ (fun _ _ => 1) A =
        (∑ i, spectralProjectors σ i) * A * (∑ j, spectralProjectors σ j) := by
      simp only [spectralFilter, one_smul, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = A := by rw [spectralProjectors_sum, one_mul, mul_one]

/-- Actual Gradient zero energies for the stated finite source data. -/
theorem actualGradient_zero_energies (σ : Perm) (k : Fin 6) (X : Operator 4) :
    actualGradient σ (fun _ => 0) k X = ThreeLevelWordDual.source k * X -
      X * ThreeLevelWordDual.source k := by
  have hw : gaussianWeights (fun _ => 0) = (fun _ _ => 1) := by
    ext i j
    simp [gaussianWeights, gaussianAmplitude_zero]
  simp only [actualGradient, quarterAmplitude_zero, hw,
    thermalGradient, inv_one, population_one, spectralFilter_one, one_mul, mul_one]


/-! ## The original normalized six-source mass -/

/-- The complete spectral filter is linear in its original source operator. -/
theorem spectralFilter_smul_source (σ : Perm)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A : Operator 4) (c : ℂ) :
    spectralFilter σ W (c • A) = c • spectralFilter σ W A := by
  simp only [spectralFilter, Matrix.mul_smul, Matrix.smul_mul,
    Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- Thermal Gradient smul source for the stated finite source data. -/
theorem thermalGradient_smul_source (σ : Perm) (d : Fin 3 → ℂ)
    (W : Matrix (Fin 3) (Fin 3) ℂ) (A X : Operator 4) (c : ℂ) :
    thermalGradient σ d W (c • A) X = c • thermalGradient σ d W A X := by
  simp only [thermalGradient, spectralFilter_smul_source,
    Matrix.mul_smul, Matrix.smul_mul, smul_sub]

/-- Normalized original source for the stated finite source data. -/
theorem normalized_original_source (k : Fin 6) :
    ExchangeCell.liftAlg (localPauliScale 2 • ThreeLevelWordDual.source k) =
      normalizedLocalPauli 2 (ThreeLevelWordDual.sourceLabel k) := by
  rw [map_smul, normalizedLocalPauli, ThreeLevelWordDual.original_source]

def normalizedActualGradient (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (X : Operator 4) : Operator 4 :=
  thermalGradient σ (fun i => quarterAmplitude (E i)) (gaussianWeights E)
    (localPauliScale 2 • ThreeLevelWordDual.source k) X

/-- Normalized Actual Gradient eq for the stated finite source data. -/
theorem normalizedActualGradient_eq (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (X : Operator 4) :
    normalizedActualGradient σ E k X = localPauliScale 2 • actualGradient σ E k X :=
  thermalGradient_smul_source _ _ _ _ _ _

/-- Normalized gradient hs mass for the stated finite source data. -/
theorem normalized_gradient_hs_mass (σ : Perm) (E : Fin 3 → ℝ) (k : Fin 6)
    (X : Operator 4) :
    hsPair (normalizedActualGradient σ E k X) (normalizedActualGradient σ E k X) =
      (1/6 : ℂ) * hsPair (actualGradient σ E k X) (actualGradient σ E k X) := by
  rw [normalizedActualGradient_eq, hsPair_smul_left, hsPair_smul_right,
    ← mul_assoc, star_localPauliScale, localPauliScale_mul_self (by norm_num : 0 < 2)]
  norm_num

/-- The one-half Dirichlet convention and the actual 1/sqrt(6) source
normalization give exactly one-twelfth of the complete raw six-source sum. -/
theorem normalized_parent_mass (σ : Perm) (E : Fin 3 → ℝ) (X : Operator 4) :
    (1/2 : ℂ) * (∑ k : Fin 6,
      hsPair (normalizedActualGradient σ E k X) (normalizedActualGradient σ E k X)) =
    (1/12 : ℂ) * (∑ k : Fin 6,
      hsPair (actualGradient σ E k X) (actualGradient σ E k X)) := by
  simp only [normalized_gradient_hs_mass, ← Finset.mul_sum]
  ring

/-- Normalized low orthogonal for the stated finite source data. -/
theorem normalized_low_orthogonal (σ : Perm) (S s : ℝ) (k : Fin 6) :
    normalizedActualGradient σ (lowEnergies S s) k
      (orthogonalCenter (clusterRoot σ (quarterAmplitude s))
        (gibbsRoot σ (lowEnergies S s))) =
      (localPauliScale 2 * smallAmplitude S) •
        (edge σ (ThreeLevelWordDual.source k) 0 1 +
          (collisionParameter S s * cexp (-s^2/8-s/4)) •
            edge σ (ThreeLevelWordDual.source k) 0 2) := by
  rw [normalizedActualGradient_eq, gaussian_low_orthogonal, smul_smul]


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCluster
