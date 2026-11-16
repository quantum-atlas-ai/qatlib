/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionFace
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelHighCollisionFace

@[expose] public section

/-!
# Actual population energy bounds on both collision faces

The already checked complete source/Gram identities are restricted to the two
population coordinates with zero fast input. Exact rational entries give the
whole complex quadratic formulas. The physical Gaussian bounds then yield
raw upper constant 20 and the original normalized constant 5/3.

A formal counterexample on the relaxed compact square records why the physical
gain restriction is necessary. No population-Rayleigh or gap conclusion is
assumed or proved by this module.
-/

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.QuantumGibbs.FormAlgebra
open Qatlib.Concepts.GibbsSource.FormAlgebra
open Matrix
open scoped BigOperators
open Qatlib.Concepts.GibbsSource.SourceForms

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionPopulationBounds
open ThreeLevelCluster ThreeLevelInvariant ThreeLevelCompactDomain ThreeLevelCoordinateMetric
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section


/-- Quadratic population for the stated finite source data. -/
theorem quadratic_population (M : Matrix (Fin 15) (Fin 15) ℂ) (c d : ℂ) :
    ThreeLevelBernstein.quadratic M (fullCoordinates c d 0) =
      (star c*(M 0 0*c+M 0 1*d)+star d*(M 1 0*c+M 1 1*d)).re := by
  simp [ThreeLevelBernstein.quadratic, fullCoordinates,
    ThreeLevelCornerFastChart.fastCoordinates, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Pi.single_apply, Matrix.vecHead, Matrix.vecTail]

/-- High literal population formula for the stated finite source data. -/
theorem high_literal_population_formula (G q : ℝ) (c d : ℂ) :
    ThreeLevelBernstein.quadratic (ThreeLevelHighCollisionFace.literalFaceGram G q)
      (fullCoordinates c d 0) =
      (52/9 : ℝ) * Complex.normSq c +
      (532/81 : ℝ) * Complex.normSq (c+((q*(3-G)/2:ℝ):ℂ)*d) +
      (20/9 : ℝ) * Complex.normSq d := by
  rw [ThreeLevelHighCollisionFace.literalFaceGram,
    ThreeLevelCollisionFace.polynomialStack_gram,
    ThreeLevelHighCollisionFace.gramPieces_eq_literal, quadratic_population]
  norm_num [ThreeLevelCollisionFace.polynomialWeight,
    ThreeLevelHighCollisionCoefficientTables.gramPiece,
    ThreeLevelHighCollisionCoefficientTables.gramBB,
    ThreeLevelHighCollisionCoefficientTables.gramBBReal,
    ThreeLevelHighCollisionCoefficientTables.gramBBImag,
    ThreeLevelHighCollisionCoefficientTables.gramBU,
    ThreeLevelHighCollisionCoefficientTables.gramBUReal,
    ThreeLevelHighCollisionCoefficientTables.gramBUImag,
    ThreeLevelHighCollisionCoefficientTables.gramBV,
    ThreeLevelHighCollisionCoefficientTables.gramBVReal,
    ThreeLevelHighCollisionCoefficientTables.gramBVImag,
    ThreeLevelHighCollisionCoefficientTables.gramUU,
    ThreeLevelHighCollisionCoefficientTables.gramUUReal,
    ThreeLevelHighCollisionCoefficientTables.gramUUImag,
    ThreeLevelHighCollisionCoefficientTables.gramUV,
    ThreeLevelHighCollisionCoefficientTables.gramUVReal,
    ThreeLevelHighCollisionCoefficientTables.gramUVImag,
    ThreeLevelHighCollisionCoefficientTables.gramVV,
    ThreeLevelHighCollisionCoefficientTables.gramVVReal,
    ThreeLevelHighCollisionCoefficientTables.gramVVImag,
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
    ThreeLevelBernstein.quadratic (ThreeLevelCollisionFace.literalFaceGram G q)
      (fullCoordinates c d 0) =
      (52/9 : ℝ) * Complex.normSq c +
      (532/81 : ℝ) * Complex.normSq (((G*(q*(3-G)/2):ℝ):ℂ)*c+d) +
      (20/9 : ℝ) * Complex.normSq d := by
  rw [ThreeLevelCollisionFace.literalFaceGram,
    ThreeLevelCollisionFace.polynomialStack_gram,
    ThreeLevelCollisionFace.gramPieces_eq_literal, quadratic_population]
  norm_num [ThreeLevelCollisionFace.polynomialWeight,
    ThreeLevelCollisionCoefficientTables.gramPiece,
    ThreeLevelCollisionCoefficientTables.gramBB,
    ThreeLevelCollisionCoefficientTables.gramBBReal,
    ThreeLevelCollisionCoefficientTables.gramBBImag,
    ThreeLevelCollisionCoefficientTables.gramBU,
    ThreeLevelCollisionCoefficientTables.gramBUReal,
    ThreeLevelCollisionCoefficientTables.gramBUImag,
    ThreeLevelCollisionCoefficientTables.gramBV,
    ThreeLevelCollisionCoefficientTables.gramBVReal,
    ThreeLevelCollisionCoefficientTables.gramBVImag,
    ThreeLevelCollisionCoefficientTables.gramUU,
    ThreeLevelCollisionCoefficientTables.gramUUReal,
    ThreeLevelCollisionCoefficientTables.gramUUImag,
    ThreeLevelCollisionCoefficientTables.gramUV,
    ThreeLevelCollisionCoefficientTables.gramUVReal,
    ThreeLevelCollisionCoefficientTables.gramUVImag,
    ThreeLevelCollisionCoefficientTables.gramVV,
    ThreeLevelCollisionCoefficientTables.gramVVReal,
    ThreeLevelCollisionCoefficientTables.gramVVImag,
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

/-- Norm Sq add le twice for the stated finite source data. -/
theorem normSq_add_le_twice (a b : ℂ) :
    Complex.normSq (a+b) ≤ 2 * Complex.normSq a + 2 * Complex.normSq b := by
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im]
  nlinarith [sq_nonneg (a.re-b.re), sq_nonneg (a.im-b.im)]


/-- High population expression le for the stated finite source data. -/
theorem high_population_expression_le (e : ℝ) (he : e^2 ≤ (4/3 : ℝ)) (c d : ℂ) :
    (52/9 : ℝ) * Complex.normSq c +
      (532/81 : ℝ) * Complex.normSq (c+(e:ℂ)*d) +
      (20/9 : ℝ) * Complex.normSq d ≤
      20 * (Complex.normSq c + Complex.normSq d) := by
  have hy := normSq_add_le_twice c ((e:ℂ)*d)
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at hy
  have hed := mul_le_mul_of_nonneg_right he (Complex.normSq_nonneg d)
  nlinarith [Complex.normSq_nonneg c, Complex.normSq_nonneg d]

/-- Low population expression le for the stated finite source data. -/
theorem low_population_expression_le (r : ℝ) (hr : r^2 ≤ 1) (c d : ℂ) :
    (52/9 : ℝ) * Complex.normSq c +
      (532/81 : ℝ) * Complex.normSq ((r:ℂ)*c+d) +
      (20/9 : ℝ) * Complex.normSq d ≤
      20 * (Complex.normSq c + Complex.normSq d) := by
  have hy := normSq_add_le_twice ((r:ℂ)*c) d
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← pow_two] at hy
  have hrc := mul_le_mul_of_nonneg_right hr (Complex.normSq_nonneg c)
  nlinarith [Complex.normSq_nonneg c, Complex.normSq_nonneg d]


/-- Exact whole-complex population energy for the actual high collision source. -/
theorem high_population_stack_formula (S : ℝ) (hs : 0 ≤ S) (c d : ℂ) :
    stackSquare (Equiv.refl (Fin 3)) S 0 c d 0 =
      (52/9 : ℝ) * Complex.normSq c +
      (532/81 : ℝ) * Complex.normSq (c+(gain S:ℂ)*d) +
      (20/9 : ℝ) * Complex.normSq d := by
  have hzero : IsFast (Equiv.refl (Fin 3)) (0 : Operator 4) := by
    simp [IsFast, hsInner]
  rw [← ThreeLevelHighCollisionFace.literalFaceGram_fullCoordinates S hs c d 0 hzero,
    high_literal_population_formula, ← gain_eq_compactAmplitude hs]

/-- Exact whole-complex population energy for the actual low collision source. -/
theorem low_population_stack_formula (s : ℝ) (hs : 0 ≤ s) (c d : ℂ) :
    stackSquare (Equiv.refl (Fin 3)) 0 s c d 0 =
      (52/9 : ℝ) * Complex.normSq c +
      (532/81 : ℝ) * Complex.normSq (((halfWeight s*gain s:ℝ):ℂ)*c+d) +
      (20/9 : ℝ) * Complex.normSq d := by
  have hzero : IsFast (Equiv.refl (Fin 3)) (0 : Operator 4) := by
    simp [IsFast, hsInner]
  rw [← ThreeLevelCollisionFace.literalFaceGram_fullCoordinates s hs c d 0 hzero,
    low_literal_population_formula, ← gain_eq_compactAmplitude hs]

/-- The full relaxed compact square does not satisfy this population bound;
the physical gain constraint is essential. -/
theorem relaxed_high_population_counterexample :
    40 < ThreeLevelBernstein.quadratic (ThreeLevelHighCollisionFace.literalFaceGram 0 1)
      (fullCoordinates 1 1 0) := by
  rw [high_literal_population_formula]
  norm_num [Complex.normSq_apply]
/-- High population stack le twenty for the stated finite source data. -/
theorem high_population_stack_le_twenty (S : ℝ) (hs : 0 ≤ S) (c d : ℂ) :
    stackSquare (Equiv.refl (Fin 3)) S 0 c d 0 ≤
      20 * (Complex.normSq c + Complex.normSq d) := by
  rw [high_population_stack_formula S hs]
  exact high_population_expression_le (gain S) (gain_sq_lt_four_thirds S).le c d

/-- Low population stack le twenty for the stated finite source data. -/
theorem low_population_stack_le_twenty (s : ℝ) (hs : 0 ≤ s) (c d : ℂ) :
    stackSquare (Equiv.refl (Fin 3)) 0 s c d 0 ≤
      20 * (Complex.normSq c + Complex.normSq d) := by
  rw [low_population_stack_formula s hs]
  apply low_population_expression_le
  have h := halfWeight_mul_gain_le_one hs
  have hp := mul_pos (halfWeight_pos s) (gain_pos s)
  nlinarith

/-- The intrinsic population premise, with the original source normalization. -/
theorem high_population_plainEnergy_le (S : ℝ) (hs : 0 ≤ S) (X : Operator 4)
    (hX : fastPart (Equiv.refl (Fin 3)) X = 0) :
    plainEnergy (Equiv.refl (Fin 3)) S 0 X ≤
      (5/3 : ℝ) * invariantMass (Equiv.refl (Fin 3)) S 0 X := by
  rw [plainEnergy_eq_scaled, hX]
  have h := high_population_stack_le_twenty S hs
    (smallAmplitude S * firstCoordinate (Equiv.refl (Fin 3)) S X)
    (smallAmplitude 0 * secondCoordinate (Equiv.refl (Fin 3)) 0 X)
  have hm : invariantMass (Equiv.refl (Fin 3)) S 0 X =
      Complex.normSq (smallAmplitude S * firstCoordinate (Equiv.refl (Fin 3)) S X) +
      Complex.normSq (smallAmplitude 0 * secondCoordinate (Equiv.refl (Fin 3)) 0 X) := by
    simp [invariantMass, hX, hsSquare, hsInner]
  rw [hm]
  linarith

/-- Low population plain Energy le for the stated finite source data. -/
theorem low_population_plainEnergy_le (s : ℝ) (hs : 0 ≤ s) (X : Operator 4)
    (hX : fastPart (Equiv.refl (Fin 3)) X = 0) :
    plainEnergy (Equiv.refl (Fin 3)) 0 s X ≤
      (5/3 : ℝ) * invariantMass (Equiv.refl (Fin 3)) 0 s X := by
  rw [plainEnergy_eq_scaled, hX]
  have h := low_population_stack_le_twenty s hs
    (smallAmplitude 0 * firstCoordinate (Equiv.refl (Fin 3)) 0 X)
    (smallAmplitude s * secondCoordinate (Equiv.refl (Fin 3)) s X)
  have hm : invariantMass (Equiv.refl (Fin 3)) 0 s X =
      Complex.normSq (smallAmplitude 0 * firstCoordinate (Equiv.refl (Fin 3)) 0 X) +
      Complex.normSq (smallAmplitude s * secondCoordinate (Equiv.refl (Fin 3)) s X) := by
    simp [invariantMass, hX, hsSquare, hsInner]
  rw [hm]
  linarith


end
end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelCollisionPopulationBounds
