/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelClockInvariantForm
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelFullCubeSource
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCompactDomain
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelPermutations

@[expose] public section

/-!
# The physical population bound for every three-level ordering

The complete two-column source is reduced to the exact summed Hilbert--Schmidt
Gram of the three original spectral edges. All six ordered projector labels
retain their signs. Physical Gaussian cross gains and rational complex square
bounds give raw constant20 and normalized constant5/3, for every nonnegative
spacing pair and every complex population input. No finite PSD premise is used.
The estimate is not asserted on the larger relaxed five-dimensional cube.
-/


open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Qatlib.Concepts.GibbsSource.CkgBounds
open Matrix MeasureTheory
open scoped BigOperators ComplexOrder
open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelFullCubePopulation
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelCompactDomain
open ThreeLevelFullCubeSource
open ThreeLevelCollisionRelabeling ThreeLevelOrder120 ThreeLevelOrder201
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000
noncomputable section

def baseEdge (j : Fin 3) (k : Fin 6) : Operator 4 :=
  ![edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source k) 0 1,
    edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source k) 1 2,
    edge (Equiv.refl (Fin 3)) (ThreeLevelWordDual.source k) 0 2] j

def baseWeight : Fin 3 → ℝ := ![52/9,20/9,532/81]

/-- Base Edge gram for the stated finite source data. -/
theorem baseEdge_gram (i j : Fin 3) :
    (∑ k : Fin 6, hsInner (baseEdge i k) (baseEdge j k)) =
      if i = j then (baseWeight i : ℂ) else 0 := by
  fin_cases i <;> fin_cases j <;>
    norm_num [baseEdge, baseWeight, edge, spectralProjectors,
      ThreeLevelWordDual.projectors, ThreeLevelWordDual.pZero,
      ThreeLevelWordDual.pOne, ThreeLevelWordDual.pTwo, ThreeLevelWordDual.psi,
      ThreeLevelWordDual.source, ThreeLevelWordDual.sourceLabel, ExchangeCell.proposals,
      hsInner, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.vecMul,
      dotProduct, Matrix.sub_apply, Matrix.one_apply,
      Matrix.conjTranspose_apply, Fin.sum_univ_succ,
      Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
      Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
      Complex.div_re, Complex.div_im, Complex.normSq_apply, Complex.conj_re, Complex.conj_im]

/-- Base Edge sum square for the stated finite source data. -/
theorem baseEdge_sum_square (v : Fin 3 → ℂ) :
    (∑ k : Fin 6, hsSquare (∑ i : Fin 3, v i • baseEdge i k)) =
      ∑ i : Fin 3, baseWeight i * Complex.normSq (v i) := by
  calc
    _ = (∑ i : Fin 3, ∑ j : Fin 3,
        star (v i) * v j * ∑ k : Fin 6, hsInner (baseEdge i k) (baseEdge j k)).re := by
      simp only [hsSquare, hsInner_sum_self, hsInner_smul_left, hsInner_smul_right,
        ← Complex.re_sum, ← mul_assoc]
      congr 1
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by
      simp only [baseEdge_gram]
      norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.vecHead, Matrix.vecTail, Fin.sum_univ_succ, baseWeight, Complex.normSq_apply,
        Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring

def edgeWeight : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0,52/9,532/81; 52/9,0,20/9; 532/81,20/9,0]

def orderedWeight (σ : Perm) : Fin 3 → ℝ :=
  ![edgeWeight (σ 0) (σ 1), edgeWeight (σ 1) (σ 2), edgeWeight (σ 0) (σ 2)]

/-- Edge Combination square for the stated finite source data. -/
theorem edgeCombination_square (σ : Perm) (c d b : ℂ) :
    (∑ k : Fin 6, hsSquare
      (c • edge σ (ThreeLevelWordDual.source k) 0 1 +
       d • edge σ (ThreeLevelWordDual.source k) 1 2 +
       b • edge σ (ThreeLevelWordDual.source k) 0 2)) =
    orderedWeight σ 0 * Complex.normSq c +
      orderedWeight σ 1 * Complex.normSq d +
      orderedWeight σ 2 * Complex.normSq b := by
  rcases ThreeLevelCollisionCoverage.permutation_cases σ with h | h | h | h | h | h
  all_goals subst σ
  · convert baseEdge_sum_square ![c,d,b] using 1
    · apply Finset.sum_congr rfl
      intro k _
      congr 1
      simp [Fin.sum_univ_succ, baseEdge]
      module
    · simp [Fin.sum_univ_succ, baseWeight, orderedWeight, edgeWeight]
      ring
  · convert baseEdge_sum_square ![-c,b,d] using 1
    · apply Finset.sum_congr rfl
      intro k _
      congr 1
      simp [Fin.sum_univ_succ, baseEdge, edge, spectralProjectors, order102_apply]
      module
    · simp [Fin.sum_univ_succ, baseWeight, orderedWeight, edgeWeight, order102_apply]
      ring
  · convert baseEdge_sum_square ![b,-d,c] using 1
    · apply Finset.sum_congr rfl
      intro k _
      congr 1
      simp [Fin.sum_univ_succ, baseEdge, edge, spectralProjectors, order021_apply]
      module
    · simp [Fin.sum_univ_succ, baseWeight, orderedWeight, edgeWeight, order021_apply]
      ring
  · convert baseEdge_sum_square ![d,-b,-c] using 1
    · apply Finset.sum_congr rfl
      intro k _
      congr 1
      simp [Fin.sum_univ_succ, baseEdge, edge, spectralProjectors, order201_apply]
      module
    · simp [Fin.sum_univ_succ, baseWeight, orderedWeight, edgeWeight, order201_apply]
      ring
  · convert baseEdge_sum_square ![-b,c,-d] using 1
    · apply Finset.sum_congr rfl
      intro k _
      congr 1
      simp [Fin.sum_univ_succ, baseEdge, edge, spectralProjectors, order120_apply]
      module
    · simp [Fin.sum_univ_succ, baseWeight, orderedWeight, edgeWeight, order120_apply]
      ring
  · convert baseEdge_sum_square ![-d,-c,-b] using 1
    · apply Finset.sum_congr rfl
      intro k _
      congr 1
      simp [Fin.sum_univ_succ, baseEdge, edge, spectralProjectors, order210_apply]
      module
    · simp [Fin.sum_univ_succ, baseWeight, orderedWeight, edgeWeight, order210_apply]
      ring

def firstCross (S s : ℝ) : ℝ := halfWeight s * gain s * mixedWeight S s

def secondCross (S s : ℝ) : ℝ := gain S * mixedWeight S s

/-- Population stack formula for the stated finite source data. -/
theorem population_stack_formula (σ : Perm) (S s : ℝ)
    (hS : 0 ≤ S) (hs : 0 ≤ s) (c d : ℂ) :
    stackSquare σ S s c d 0 =
      orderedWeight σ 0 * Complex.normSq c + orderedWeight σ 1 * Complex.normSq d +
      orderedWeight σ 2 * Complex.normSq ((firstCross S s : ℂ)*c +
        (secondCross S s : ℂ)*d) := by
  have he (k : Fin 6) : scaledSource σ S s c d 0 k =
      c • edge σ (ThreeLevelWordDual.source k) 0 1 +
      d • edge σ (ThreeLevelWordDual.source k) 1 2 +
      ((firstCross S s : ℂ)*c + (secondCross S s : ℂ)*d) •
        edge σ (ThreeLevelWordDual.source k) 0 2 := by
    rw [← cubeSource_cubePoint σ S s hS hs]
    simp only [cubeSource, firstColumn, secondColumn, fastSource_zero, add_zero,
      firstGain_cubePoint S s hS, secondGain_cubePoint S s hs]
    change c • (edge σ (ThreeLevelWordDual.source k) 0 1 +
      ((halfWeight s : ℂ) * (gain s : ℂ) * (mixedWeight S s : ℂ)) •
        edge σ (ThreeLevelWordDual.source k) 0 2) +
      d • (edge σ (ThreeLevelWordDual.source k) 1 2 +
      ((gain S : ℂ) * (mixedWeight S s : ℂ)) •
        edge σ (ThreeLevelWordDual.source k) 0 2) = _
    simp only [firstCross, secondCross, Complex.ofReal_mul]
    module
  simp only [stackSquare, he]
  exact edgeCombination_square σ c d _

/-- First Cross sq le one for the stated finite source data. -/
theorem firstCross_sq_le_one (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s) :
    (firstCross S s)^2 ≤ 1 := by
  have hu := first_cross_coefficient_le_one hS hs
  have hp : 0 ≤ firstCross S s :=
    (mul_pos (mul_pos (halfWeight_pos s) (gain_pos s)) (mixedWeight_pos S s)).le
  change firstCross S s ≤ 1 at hu
  nlinarith

/-- Second Cross sq le four thirds for the stated finite source data. -/
theorem secondCross_sq_le_four_thirds (S s : ℝ) (hS : 0 ≤ S) (hs : 0 ≤ s) :
    (secondCross S s)^2 ≤ (4/3 : ℝ) :=
  (second_cross_coefficient_sq_lt_four_thirds hS hs).le

/-- Complex young two for the stated finite source data. -/
theorem complex_young_two (c d : ℂ) :
    Complex.normSq (c+d) ≤ 2*Complex.normSq c + 2*Complex.normSq d :=
by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (c.re-d.re), sq_nonneg (c.im-d.im)]

/-- Complex young three for the stated finite source data. -/
theorem complex_young_three (c d : ℂ) :
    Complex.normSq (c+d) ≤ 3*Complex.normSq c + (3/2:ℝ)*Complex.normSq d :=
by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (2*c.re-d.re), sq_nonneg (2*c.im-d.im)]

/-- Complex young eight for the stated finite source data. -/
theorem complex_young_eight (c d : ℂ) :
    Complex.normSq (c+d) ≤ (8/3:ℝ)*Complex.normSq c + (8/5:ℝ)*Complex.normSq d := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (5*c.re-3*d.re), sq_nonneg (5*c.im-3*d.im)]

/-- Population expression le twenty for the stated finite source data. -/
theorem population_expression_le_twenty (σ : Perm) (r t : ℝ)
    (hr : r^2 ≤ 1) (ht : t^2 ≤ (4/3:ℝ)) (c d : ℂ) :
    orderedWeight σ 0 * Complex.normSq c + orderedWeight σ 1 * Complex.normSq d +
      orderedWeight σ 2 * Complex.normSq ((r:ℂ)*c+(t:ℂ)*d) ≤
        20 * (Complex.normSq c + Complex.normSq d) := by
  have hc := Complex.normSq_nonneg c
  have hd := Complex.normSq_nonneg d
  have hrc := mul_le_mul_of_nonneg_right hr hc
  have htd := mul_le_mul_of_nonneg_right ht hd
  have hy2 := complex_young_two ((r:ℂ)*c) ((t:ℂ)*d)
  have hy3 := complex_young_three ((r:ℂ)*c) ((t:ℂ)*d)
  have hy8 := complex_young_eight ((r:ℂ)*c) ((t:ℂ)*d)
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at hy2 hy3 hy8
  rcases ThreeLevelCollisionCoverage.permutation_cases σ with h | h | h | h | h | h
  all_goals subst σ
  all_goals
    norm_num [Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
        Matrix.vecHead, Matrix.vecTail, orderedWeight, edgeWeight, order102_apply, order021_apply,
      order201_apply, order120_apply, order210_apply]
    nlinarith

/-- Population stack le twenty for the stated finite source data. -/
theorem population_stack_le_twenty (σ : Perm) (S s : ℝ)
    (hS : 0 ≤ S) (hs : 0 ≤ s) (c d : ℂ) :
    stackSquare σ S s c d 0 ≤ 20 * (Complex.normSq c + Complex.normSq d) := by
  rw [population_stack_formula σ S s hS hs]
  exact population_expression_le_twenty σ (firstCross S s) (secondCross S s)
    (firstCross_sq_le_one S s hS hs) (secondCross_sq_le_four_thirds S s hS hs) c d

/-- Population energy le five thirds for the stated finite source data. -/
theorem population_energy_le_five_thirds (σ : Perm) (S s : ℝ)
    (hS : 0 ≤ S) (hs : 0 ≤ s) (X : Operator 4) (hf : fastPart σ X = 0) :
    plainEnergy σ S s X ≤ (5/3:ℝ) * invariantMass σ S s X := by
  rw [plainEnergy_eq_scaled, hf]
  have h := population_stack_le_twenty σ S s hS hs
    (smallAmplitude S * firstCoordinate σ S X)
    (smallAmplitude s * secondCoordinate σ s X)
  have hm : invariantMass σ S s X =
      Complex.normSq (smallAmplitude S * firstCoordinate σ S X) +
      Complex.normSq (smallAmplitude s * secondCoordinate σ s X) := by
    simp [invariantMass, hf, hsSquare, hsInner]
  rw [hm]
  linarith

end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelFullCubePopulation
