/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120LowFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionPopulationBounds

@[expose] public section


/-!
# Order120 population bounds on the two actual collision curves

The complete checked source/Gram identities are restricted to the two actual
population coordinates. Their exact complex edge weights are 20/9, 52/9,
and 532/81. Physical Gaussian amplitudes and two weighted complex square
estimates give raw constant 20, hence normalized constant 5/3 with the
original 1/12 source normalization. The source matrices, coordinate chart, and physical
amplitude constraints are all retained. No Rayleigh conclusion is assumed.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120PopulationBounds
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelCompactDomain ThreeLevelCoordinateMetric
open ThreeLevelCollisionPopulationBounds ThreeLevelOrder120
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section

/-- High literal population formula for the stated finite source data. -/
theorem high_literal_population_formula (G q : ℝ) (c d : ℂ) :
    ThreeLevelBernstein.quadratic (ThreeLevelOrder120HighFace.literalFaceGram G q)
      (fullCoordinates c d 0) =
      (20/9 : ℝ) * Complex.normSq c +
      (52/9 : ℝ) * Complex.normSq (c+((q*(3-G)/2:ℝ):ℂ)*d) +
      (532/81 : ℝ) * Complex.normSq d := by
  rw [ThreeLevelOrder120HighFace.literalFaceGram,
    ThreeLevelCollisionFace.polynomialStack_gram,
    ThreeLevelOrder120HighFace.gramPieces_eq_literal, quadratic_population]
  norm_num [ThreeLevelCollisionFace.polynomialWeight,
    ThreeLevelOrder120HighCoefficientTables.gramPiece,
    ThreeLevelOrder120HighCoefficientTables.gramBB,
    ThreeLevelOrder120HighCoefficientTables.gramBBReal,
    ThreeLevelOrder120HighCoefficientTables.gramBBImag,
    ThreeLevelOrder120HighCoefficientTables.gramBU,
    ThreeLevelOrder120HighCoefficientTables.gramBUReal,
    ThreeLevelOrder120HighCoefficientTables.gramBUImag,
    ThreeLevelOrder120HighCoefficientTables.gramBV,
    ThreeLevelOrder120HighCoefficientTables.gramBVReal,
    ThreeLevelOrder120HighCoefficientTables.gramBVImag,
    ThreeLevelOrder120HighCoefficientTables.gramUU,
    ThreeLevelOrder120HighCoefficientTables.gramUUReal,
    ThreeLevelOrder120HighCoefficientTables.gramUUImag,
    ThreeLevelOrder120HighCoefficientTables.gramUV,
    ThreeLevelOrder120HighCoefficientTables.gramUVReal,
    ThreeLevelOrder120HighCoefficientTables.gramUVImag,
    ThreeLevelOrder120HighCoefficientTables.gramVV,
    ThreeLevelOrder120HighCoefficientTables.gramVVReal,
    ThreeLevelOrder120HighCoefficientTables.gramVVImag,
    ThreeLevelGramCertificate.fromParts,
    Fin.sum_univ_succ,
    Matrix.sum_apply,
    Matrix.smul_apply,
    Complex.real_smul,
    smul_eq_mul,
    pow_two,
    Complex.normSq_apply,
    Complex.add_re,
    Complex.add_im,
    Complex.mul_re,
    Complex.mul_im,
    Complex.div_re,
    Complex.div_im,
    Complex.sub_re,
    Complex.sub_im,
    Complex.conj_re,
    Complex.conj_im]
  ring

/-- Low literal population formula for the stated finite source data. -/
theorem low_literal_population_formula (G q : ℝ) (c d : ℂ) :
    ThreeLevelBernstein.quadratic (ThreeLevelOrder120LowFace.literalFaceGram G q)
      (fullCoordinates c d 0) =
      (20/9 : ℝ) * Complex.normSq c +
      (52/9 : ℝ) * Complex.normSq (((G*(q*(3-G)/2):ℝ):ℂ)*c+d) +
      (532/81 : ℝ) * Complex.normSq d := by
  rw [ThreeLevelOrder120LowFace.literalFaceGram,
    ThreeLevelCollisionFace.polynomialStack_gram,
    ThreeLevelOrder120LowFace.gramPieces_eq_literal, quadratic_population]
  norm_num [ThreeLevelCollisionFace.polynomialWeight,
    ThreeLevelOrder120LowCoefficientTables.gramPiece,
    ThreeLevelOrder120LowCoefficientTables.gramBB,
    ThreeLevelOrder120LowCoefficientTables.gramBBReal,
    ThreeLevelOrder120LowCoefficientTables.gramBBImag,
    ThreeLevelOrder120LowCoefficientTables.gramBU,
    ThreeLevelOrder120LowCoefficientTables.gramBUReal,
    ThreeLevelOrder120LowCoefficientTables.gramBUImag,
    ThreeLevelOrder120LowCoefficientTables.gramBV,
    ThreeLevelOrder120LowCoefficientTables.gramBVReal,
    ThreeLevelOrder120LowCoefficientTables.gramBVImag,
    ThreeLevelOrder120LowCoefficientTables.gramUU,
    ThreeLevelOrder120LowCoefficientTables.gramUUReal,
    ThreeLevelOrder120LowCoefficientTables.gramUUImag,
    ThreeLevelOrder120LowCoefficientTables.gramUV,
    ThreeLevelOrder120LowCoefficientTables.gramUVReal,
    ThreeLevelOrder120LowCoefficientTables.gramUVImag,
    ThreeLevelOrder120LowCoefficientTables.gramVV,
    ThreeLevelOrder120LowCoefficientTables.gramVVReal,
    ThreeLevelOrder120LowCoefficientTables.gramVVImag,
    ThreeLevelGramCertificate.fromParts,
    Fin.sum_univ_succ,
    Matrix.sum_apply,
    Matrix.smul_apply,
    Complex.real_smul,
    smul_eq_mul,
    pow_two,
    Complex.normSq_apply,
    Complex.add_re,
    Complex.add_im,
    Complex.mul_re,
    Complex.mul_im,
    Complex.div_re,
    Complex.div_im,
    Complex.sub_re,
    Complex.sub_im,
    Complex.conj_re,
    Complex.conj_im]
  ring

/-- Norm Sq add le three three halves for the stated finite source data. -/
theorem normSq_add_le_three_three_halves (c d : ℂ) :
    Complex.normSq (c+d) ≤
      3*Complex.normSq c+(3/2 : ℝ)*Complex.normSq d := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (2*c.re-d.re), sq_nonneg (2*c.im-d.im)]

/-- High population expression le for the stated finite source data. -/
theorem high_population_expression_le (e : ℝ) (he : e^2 ≤ (4/3 : ℝ)) (c d : ℂ) :
    (20/9 : ℝ) * Complex.normSq c +
      (52/9 : ℝ) * Complex.normSq (c+(e:ℂ)*d) +
      (532/81 : ℝ) * Complex.normSq d ≤
      20 * (Complex.normSq c + Complex.normSq d) := by
  have hy := normSq_add_le_three_three_halves c ((e:ℂ)*d)
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at hy
  have hed := mul_le_mul_of_nonneg_right he (Complex.normSq_nonneg d)
  nlinarith [Complex.normSq_nonneg c, Complex.normSq_nonneg d]

/-- Low population expression le for the stated finite source data. -/
theorem low_population_expression_le (r : ℝ) (hr : r^2 ≤ 1) (c d : ℂ) :
    (20/9 : ℝ) * Complex.normSq c +
      (52/9 : ℝ) * Complex.normSq ((r:ℂ)*c+d) +
      (532/81 : ℝ) * Complex.normSq d ≤
      20 * (Complex.normSq c + Complex.normSq d) := by
  have hy := normSq_add_le_twice ((r:ℂ)*c) d
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at hy
  have hrc := mul_le_mul_of_nonneg_right hr (Complex.normSq_nonneg c)
  nlinarith [Complex.normSq_nonneg c, Complex.normSq_nonneg d]


/-- Exact whole-complex population energy for the actual high collision source. -/
theorem high_population_stack_formula (S : ℝ) (hs : 0 ≤ S) (c d : ℂ) :
    stackSquare order120 S 0 c d 0 =
      (20/9 : ℝ) * Complex.normSq c +
      (52/9 : ℝ) * Complex.normSq (c+(gain S:ℂ)*d) +
      (532/81 : ℝ) * Complex.normSq d := by
  have hzero : IsFast order120 (0 : Operator 4) := by
    simp [IsFast, hsInner]
  rw [← ThreeLevelOrder120HighFace.literalFaceGram_fullCoordinates S hs c d 0 hzero,
    high_literal_population_formula, ← gain_eq_compactAmplitude hs]

/-- Exact whole-complex population energy for the actual low collision source. -/
theorem low_population_stack_formula (s : ℝ) (hs : 0 ≤ s) (c d : ℂ) :
    stackSquare order120 0 s c d 0 =
      (20/9 : ℝ) * Complex.normSq c +
      (52/9 : ℝ) * Complex.normSq (((halfWeight s*gain s:ℝ):ℂ)*c+d) +
      (532/81 : ℝ) * Complex.normSq d := by
  have hzero : IsFast order120 (0 : Operator 4) := by
    simp [IsFast, hsInner]
  rw [← ThreeLevelOrder120LowFace.literalFaceGram_fullCoordinates s hs c d 0 hzero,
    low_literal_population_formula, ← gain_eq_compactAmplitude hs]

/-- The relaxed square does not preserve the physical raw constant 20. -/
theorem relaxed_high_population_counterexample :
    40 < ThreeLevelBernstein.quadratic (ThreeLevelOrder120HighFace.literalFaceGram 0 1)
      (fullCoordinates 1 1 0) := by
  rw [high_literal_population_formula]
  norm_num [Complex.normSq_apply]

/-- High population stack le twenty for the stated finite source data. -/
theorem high_population_stack_le_twenty (S : ℝ) (hs : 0 ≤ S) (c d : ℂ) :
    stackSquare order120 S 0 c d 0 ≤
      20 * (Complex.normSq c + Complex.normSq d) := by
  rw [high_population_stack_formula S hs]
  exact high_population_expression_le (gain S) (gain_sq_lt_four_thirds S).le c d

/-- Low population stack le twenty for the stated finite source data. -/
theorem low_population_stack_le_twenty (s : ℝ) (hs : 0 ≤ s) (c d : ℂ) :
    stackSquare order120 0 s c d 0 ≤
      20 * (Complex.normSq c + Complex.normSq d) := by
  rw [low_population_stack_formula s hs]
  apply low_population_expression_le
  have h := halfWeight_mul_gain_le_one hs
  have hp := mul_pos (halfWeight_pos s) (gain_pos s)
  nlinarith

/-- The intrinsic population premise, with the original source normalization. -/
theorem high_population_plainEnergy_le (S : ℝ) (hs : 0 ≤ S) (X : Operator 4)
    (hX : fastPart order120 X = 0) :
    plainEnergy order120 S 0 X ≤
      (5/3 : ℝ)*invariantMass order120 S 0 X := by
  rw [plainEnergy_eq_scaled, hX]
  have h := high_population_stack_le_twenty S hs
    (smallAmplitude S * firstCoordinate order120 S X)
    (smallAmplitude 0 * secondCoordinate order120 0 X)
  have hm : invariantMass order120 S 0 X =
      Complex.normSq (smallAmplitude S * firstCoordinate order120 S X) +
      Complex.normSq (smallAmplitude 0 * secondCoordinate order120 0 X) := by
    simp [invariantMass, hX, hsSquare, hsInner]
  rw [hm]
  linarith

/-- Low population plain Energy le for the stated finite source data. -/
theorem low_population_plainEnergy_le (s : ℝ) (hs : 0 ≤ s) (X : Operator 4)
    (hX : fastPart order120 X = 0) :
    plainEnergy order120 0 s X ≤
      (5/3 : ℝ)*invariantMass order120 0 s X := by
  rw [plainEnergy_eq_scaled, hX]
  have h := low_population_stack_le_twenty s hs
    (smallAmplitude 0 * firstCoordinate order120 0 X)
    (smallAmplitude s * secondCoordinate order120 s X)
  have hm : invariantMass order120 0 s X =
      Complex.normSq (smallAmplitude 0 * firstCoordinate order120 0 X) +
      Complex.normSq (smallAmplitude s * secondCoordinate order120 s X) := by
    simp [invariantMass, hX, hsSquare, hsInner]
  rw [hm]
  linarith


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120PopulationBounds
