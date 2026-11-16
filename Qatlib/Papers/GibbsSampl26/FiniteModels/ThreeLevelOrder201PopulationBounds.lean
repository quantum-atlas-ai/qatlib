/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201LowFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201HighFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionPopulationBounds

@[expose] public section


/-!
# Order201 population bounds on the two actual collision curves

The complete checked source/Gram identities are restricted to the two actual
population coordinates. Their exact complex edge weights are 532/81, 20/9,
and 52/9. Physical Gaussian amplitudes and the complex two-square estimate
give raw constant 12, hence normalized constant 1 with the original 1/12
source normalization. The source matrices, coordinate chart, and physical
amplitude constraints are all retained. No Rayleigh conclusion is assumed.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201PopulationBounds
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelCompactDomain ThreeLevelCoordinateMetric
open ThreeLevelCollisionPopulationBounds ThreeLevelOrder201
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section

/-- High literal population formula for the stated finite source data. -/
theorem high_literal_population_formula (G q : ℝ) (c d : ℂ) :
    ThreeLevelBernstein.quadratic (ThreeLevelOrder201HighFace.literalFaceGram G q)
      (fullCoordinates c d 0) =
      (532/81 : ℝ) * Complex.normSq c +
      (20/9 : ℝ) * Complex.normSq (c+((q*(3-G)/2:ℝ):ℂ)*d) +
      (52/9 : ℝ) * Complex.normSq d := by
  rw [ThreeLevelOrder201HighFace.literalFaceGram,
    ThreeLevelCollisionFace.polynomialStack_gram,
    ThreeLevelOrder201HighFace.gramPieces_eq_literal, quadratic_population]
  norm_num [ThreeLevelCollisionFace.polynomialWeight,
    ThreeLevelOrder201HighCoefficientTables.gramPiece,
    ThreeLevelOrder201HighCoefficientTables.gramBB,
    ThreeLevelOrder201HighCoefficientTables.gramBBReal,
    ThreeLevelOrder201HighCoefficientTables.gramBBImag,
    ThreeLevelOrder201HighCoefficientTables.gramBU,
    ThreeLevelOrder201HighCoefficientTables.gramBUReal,
    ThreeLevelOrder201HighCoefficientTables.gramBUImag,
    ThreeLevelOrder201HighCoefficientTables.gramBV,
    ThreeLevelOrder201HighCoefficientTables.gramBVReal,
    ThreeLevelOrder201HighCoefficientTables.gramBVImag,
    ThreeLevelOrder201HighCoefficientTables.gramUU,
    ThreeLevelOrder201HighCoefficientTables.gramUUReal,
    ThreeLevelOrder201HighCoefficientTables.gramUUImag,
    ThreeLevelOrder201HighCoefficientTables.gramUV,
    ThreeLevelOrder201HighCoefficientTables.gramUVReal,
    ThreeLevelOrder201HighCoefficientTables.gramUVImag,
    ThreeLevelOrder201HighCoefficientTables.gramVV,
    ThreeLevelOrder201HighCoefficientTables.gramVVReal,
    ThreeLevelOrder201HighCoefficientTables.gramVVImag,
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
    ThreeLevelBernstein.quadratic (ThreeLevelOrder201LowFace.literalFaceGram G q)
      (fullCoordinates c d 0) =
      (532/81 : ℝ) * Complex.normSq c +
      (20/9 : ℝ) * Complex.normSq (((G*(q*(3-G)/2):ℝ):ℂ)*c+d) +
      (52/9 : ℝ) * Complex.normSq d := by
  rw [ThreeLevelOrder201LowFace.literalFaceGram,
    ThreeLevelCollisionFace.polynomialStack_gram,
    ThreeLevelOrder201LowFace.gramPieces_eq_literal, quadratic_population]
  norm_num [ThreeLevelCollisionFace.polynomialWeight,
    ThreeLevelOrder201LowCoefficientTables.gramPiece,
    ThreeLevelOrder201LowCoefficientTables.gramBB,
    ThreeLevelOrder201LowCoefficientTables.gramBBReal,
    ThreeLevelOrder201LowCoefficientTables.gramBBImag,
    ThreeLevelOrder201LowCoefficientTables.gramBU,
    ThreeLevelOrder201LowCoefficientTables.gramBUReal,
    ThreeLevelOrder201LowCoefficientTables.gramBUImag,
    ThreeLevelOrder201LowCoefficientTables.gramBV,
    ThreeLevelOrder201LowCoefficientTables.gramBVReal,
    ThreeLevelOrder201LowCoefficientTables.gramBVImag,
    ThreeLevelOrder201LowCoefficientTables.gramUU,
    ThreeLevelOrder201LowCoefficientTables.gramUUReal,
    ThreeLevelOrder201LowCoefficientTables.gramUUImag,
    ThreeLevelOrder201LowCoefficientTables.gramUV,
    ThreeLevelOrder201LowCoefficientTables.gramUVReal,
    ThreeLevelOrder201LowCoefficientTables.gramUVImag,
    ThreeLevelOrder201LowCoefficientTables.gramVV,
    ThreeLevelOrder201LowCoefficientTables.gramVVReal,
    ThreeLevelOrder201LowCoefficientTables.gramVVImag,
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

/-- High population expression le for the stated finite source data. -/
theorem high_population_expression_le (e : ℝ) (he : e^2 ≤ (4/3 : ℝ)) (c d : ℂ) :
    (532/81 : ℝ) * Complex.normSq c +
      (20/9 : ℝ) * Complex.normSq (c+(e:ℂ)*d) +
      (52/9 : ℝ) * Complex.normSq d ≤
      12 * (Complex.normSq c + Complex.normSq d) := by
  have hy := normSq_add_le_twice c ((e:ℂ)*d)
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at hy
  have hed := mul_le_mul_of_nonneg_right he (Complex.normSq_nonneg d)
  nlinarith [Complex.normSq_nonneg c, Complex.normSq_nonneg d]

/-- Low population expression le for the stated finite source data. -/
theorem low_population_expression_le (r : ℝ) (hr : r^2 ≤ 1) (c d : ℂ) :
    (532/81 : ℝ) * Complex.normSq c +
      (20/9 : ℝ) * Complex.normSq ((r:ℂ)*c+d) +
      (52/9 : ℝ) * Complex.normSq d ≤
      12 * (Complex.normSq c + Complex.normSq d) := by
  have hy := normSq_add_le_twice ((r:ℂ)*c) d
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at hy
  have hrc := mul_le_mul_of_nonneg_right hr (Complex.normSq_nonneg c)
  nlinarith [Complex.normSq_nonneg c, Complex.normSq_nonneg d]


/-- Exact whole-complex population energy for the actual high collision source. -/
theorem high_population_stack_formula (S : ℝ) (hs : 0 ≤ S) (c d : ℂ) :
    stackSquare order201 S 0 c d 0 =
      (532/81 : ℝ) * Complex.normSq c +
      (20/9 : ℝ) * Complex.normSq (c+(gain S:ℂ)*d) +
      (52/9 : ℝ) * Complex.normSq d := by
  have hzero : IsFast order201 (0 : Operator 4) := by
    simp [IsFast, hsInner]
  rw [← ThreeLevelOrder201HighFace.literalFaceGram_fullCoordinates S hs c d 0 hzero,
    high_literal_population_formula, ← gain_eq_compactAmplitude hs]

/-- Exact whole-complex population energy for the actual low collision source. -/
theorem low_population_stack_formula (s : ℝ) (hs : 0 ≤ s) (c d : ℂ) :
    stackSquare order201 0 s c d 0 =
      (532/81 : ℝ) * Complex.normSq c +
      (20/9 : ℝ) * Complex.normSq (((halfWeight s*gain s:ℝ):ℂ)*c+d) +
      (52/9 : ℝ) * Complex.normSq d := by
  have hzero : IsFast order201 (0 : Operator 4) := by
    simp [IsFast, hsInner]
  rw [← ThreeLevelOrder201LowFace.literalFaceGram_fullCoordinates s hs c d 0 hzero,
    low_literal_population_formula, ← gain_eq_compactAmplitude hs]

/-- The relaxed square does not preserve the physical raw constant 12. -/
theorem relaxed_high_population_counterexample :
    24 < ThreeLevelBernstein.quadratic (ThreeLevelOrder201HighFace.literalFaceGram 0 1)
      (fullCoordinates 1 1 0) := by
  rw [high_literal_population_formula]
  norm_num [Complex.normSq_apply]

/-- High population stack le twelve for the stated finite source data. -/
theorem high_population_stack_le_twelve (S : ℝ) (hs : 0 ≤ S) (c d : ℂ) :
    stackSquare order201 S 0 c d 0 ≤
      12 * (Complex.normSq c + Complex.normSq d) := by
  rw [high_population_stack_formula S hs]
  exact high_population_expression_le (gain S) (gain_sq_lt_four_thirds S).le c d

/-- Low population stack le twelve for the stated finite source data. -/
theorem low_population_stack_le_twelve (s : ℝ) (hs : 0 ≤ s) (c d : ℂ) :
    stackSquare order201 0 s c d 0 ≤
      12 * (Complex.normSq c + Complex.normSq d) := by
  rw [low_population_stack_formula s hs]
  apply low_population_expression_le
  have h := halfWeight_mul_gain_le_one hs
  have hp := mul_pos (halfWeight_pos s) (gain_pos s)
  nlinarith

/-- The intrinsic population premise, with the original source normalization. -/
theorem high_population_plainEnergy_le (S : ℝ) (hs : 0 ≤ S) (X : Operator 4)
    (hX : fastPart order201 X = 0) :
    plainEnergy order201 S 0 X ≤
      invariantMass order201 S 0 X := by
  rw [plainEnergy_eq_scaled, hX]
  have h := high_population_stack_le_twelve S hs
    (smallAmplitude S * firstCoordinate order201 S X)
    (smallAmplitude 0 * secondCoordinate order201 0 X)
  have hm : invariantMass order201 S 0 X =
      Complex.normSq (smallAmplitude S * firstCoordinate order201 S X) +
      Complex.normSq (smallAmplitude 0 * secondCoordinate order201 0 X) := by
    simp [invariantMass, hX, hsSquare, hsInner]
  rw [hm]
  linarith

/-- Low population plain Energy le for the stated finite source data. -/
theorem low_population_plainEnergy_le (s : ℝ) (hs : 0 ≤ s) (X : Operator 4)
    (hX : fastPart order201 X = 0) :
    plainEnergy order201 0 s X ≤
      invariantMass order201 0 s X := by
  rw [plainEnergy_eq_scaled, hX]
  have h := low_population_stack_le_twelve s hs
    (smallAmplitude 0 * firstCoordinate order201 0 X)
    (smallAmplitude s * secondCoordinate order201 s X)
  have hm : invariantMass order201 0 s X =
      Complex.normSq (smallAmplitude 0 * firstCoordinate order201 0 X) +
      Complex.normSq (smallAmplitude s * secondCoordinate order201 s X) := by
    simp [invariantMass, hX, hsSquare, hsInner]
  rw [hm]
  linarith


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder201PopulationBounds
