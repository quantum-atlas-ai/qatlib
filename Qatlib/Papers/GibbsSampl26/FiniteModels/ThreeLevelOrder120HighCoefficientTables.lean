/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighCoefficientData
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow00
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow01
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow02
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow03
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow04
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow05
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow06
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow07
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow08
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow09
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow10
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow11
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow12
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow13
public import Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighGramRow14

@[expose] public section


set_option backward.isDefEq.respectTransparency false

/-!
# Exact finite coefficient incidence on the order120 high collision face

The six fixed Gram products of the literal stack B+eU+GeV are checked
entrywise. They are then bound to all30certified degree(4,2) coefficients.
The actual physical interpretation of B,U,V and generic Bernstein
reconstruction are supplied separately by ThreeLevelOrder120HighFace.
-/

namespace Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighCoefficientTables
open ThreeLevelGramCertificate ThreeLevelOrder120HighCertificates Matrix
open scoped BigOperators ComplexOrder
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option Elab.async true


/-- Gram BBReal matches for the stated finite source data. -/
theorem gramBBReal_matches :
    ∀ i j, gramBBReal i j = (faceBaseReal.transpose * faceBaseReal + faceBaseImag.transpose * faceBaseImag) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.1 j
  · exact gram_row_1.1 j
  · exact gram_row_2.1 j
  · exact gram_row_3.1 j
  · exact gram_row_4.1 j
  · exact gram_row_5.1 j
  · exact gram_row_6.1 j
  · exact gram_row_7.1 j
  · exact gram_row_8.1 j
  · exact gram_row_9.1 j
  · exact gram_row_10.1 j
  · exact gram_row_11.1 j
  · exact gram_row_12.1 j
  · exact gram_row_13.1 j
  · exact gram_row_14.1 j

/-- Gram BBImag matches for the stated finite source data. -/
theorem gramBBImag_matches :
    ∀ i j, gramBBImag i j = (faceBaseReal.transpose * faceBaseImag - faceBaseImag.transpose * faceBaseReal) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.1 j
  · exact gram_row_1.2.1 j
  · exact gram_row_2.2.1 j
  · exact gram_row_3.2.1 j
  · exact gram_row_4.2.1 j
  · exact gram_row_5.2.1 j
  · exact gram_row_6.2.1 j
  · exact gram_row_7.2.1 j
  · exact gram_row_8.2.1 j
  · exact gram_row_9.2.1 j
  · exact gram_row_10.2.1 j
  · exact gram_row_11.2.1 j
  · exact gram_row_12.2.1 j
  · exact gram_row_13.2.1 j
  · exact gram_row_14.2.1 j

/-- Gram BUReal matches for the stated finite source data. -/
theorem gramBUReal_matches :
    ∀ i j, gramBUReal i j = (faceBaseReal.transpose * faceUpReal + faceBaseImag.transpose * faceUpImag + faceUpReal.transpose * faceBaseReal + faceUpImag.transpose * faceBaseImag) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.1 j
  · exact gram_row_1.2.2.1 j
  · exact gram_row_2.2.2.1 j
  · exact gram_row_3.2.2.1 j
  · exact gram_row_4.2.2.1 j
  · exact gram_row_5.2.2.1 j
  · exact gram_row_6.2.2.1 j
  · exact gram_row_7.2.2.1 j
  · exact gram_row_8.2.2.1 j
  · exact gram_row_9.2.2.1 j
  · exact gram_row_10.2.2.1 j
  · exact gram_row_11.2.2.1 j
  · exact gram_row_12.2.2.1 j
  · exact gram_row_13.2.2.1 j
  · exact gram_row_14.2.2.1 j

/-- Gram BUImag matches for the stated finite source data. -/
theorem gramBUImag_matches :
    ∀ i j, gramBUImag i j = (faceBaseReal.transpose * faceUpImag - faceBaseImag.transpose * faceUpReal + faceUpReal.transpose * faceBaseImag - faceUpImag.transpose * faceBaseReal) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.2.1 j
  · exact gram_row_1.2.2.2.1 j
  · exact gram_row_2.2.2.2.1 j
  · exact gram_row_3.2.2.2.1 j
  · exact gram_row_4.2.2.2.1 j
  · exact gram_row_5.2.2.2.1 j
  · exact gram_row_6.2.2.2.1 j
  · exact gram_row_7.2.2.2.1 j
  · exact gram_row_8.2.2.2.1 j
  · exact gram_row_9.2.2.2.1 j
  · exact gram_row_10.2.2.2.1 j
  · exact gram_row_11.2.2.2.1 j
  · exact gram_row_12.2.2.2.1 j
  · exact gram_row_13.2.2.2.1 j
  · exact gram_row_14.2.2.2.1 j

/-- Gram BVReal matches for the stated finite source data. -/
theorem gramBVReal_matches :
    ∀ i j, gramBVReal i j = (faceBaseReal.transpose * faceDownReal + faceBaseImag.transpose * faceDownImag + faceDownReal.transpose * faceBaseReal + faceDownImag.transpose * faceBaseImag) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.2.2.1 j
  · exact gram_row_1.2.2.2.2.1 j
  · exact gram_row_2.2.2.2.2.1 j
  · exact gram_row_3.2.2.2.2.1 j
  · exact gram_row_4.2.2.2.2.1 j
  · exact gram_row_5.2.2.2.2.1 j
  · exact gram_row_6.2.2.2.2.1 j
  · exact gram_row_7.2.2.2.2.1 j
  · exact gram_row_8.2.2.2.2.1 j
  · exact gram_row_9.2.2.2.2.1 j
  · exact gram_row_10.2.2.2.2.1 j
  · exact gram_row_11.2.2.2.2.1 j
  · exact gram_row_12.2.2.2.2.1 j
  · exact gram_row_13.2.2.2.2.1 j
  · exact gram_row_14.2.2.2.2.1 j

/-- Gram BVImag matches for the stated finite source data. -/
theorem gramBVImag_matches :
    ∀ i j, gramBVImag i j = (faceBaseReal.transpose * faceDownImag - faceBaseImag.transpose * faceDownReal + faceDownReal.transpose * faceBaseImag - faceDownImag.transpose * faceBaseReal) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.2.2.2.1 j
  · exact gram_row_1.2.2.2.2.2.1 j
  · exact gram_row_2.2.2.2.2.2.1 j
  · exact gram_row_3.2.2.2.2.2.1 j
  · exact gram_row_4.2.2.2.2.2.1 j
  · exact gram_row_5.2.2.2.2.2.1 j
  · exact gram_row_6.2.2.2.2.2.1 j
  · exact gram_row_7.2.2.2.2.2.1 j
  · exact gram_row_8.2.2.2.2.2.1 j
  · exact gram_row_9.2.2.2.2.2.1 j
  · exact gram_row_10.2.2.2.2.2.1 j
  · exact gram_row_11.2.2.2.2.2.1 j
  · exact gram_row_12.2.2.2.2.2.1 j
  · exact gram_row_13.2.2.2.2.2.1 j
  · exact gram_row_14.2.2.2.2.2.1 j

/-- Gram UUReal matches for the stated finite source data. -/
theorem gramUUReal_matches :
    ∀ i j, gramUUReal i j = (faceUpReal.transpose * faceUpReal + faceUpImag.transpose * faceUpImag) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.2.2.2.2.1 j
  · exact gram_row_1.2.2.2.2.2.2.1 j
  · exact gram_row_2.2.2.2.2.2.2.1 j
  · exact gram_row_3.2.2.2.2.2.2.1 j
  · exact gram_row_4.2.2.2.2.2.2.1 j
  · exact gram_row_5.2.2.2.2.2.2.1 j
  · exact gram_row_6.2.2.2.2.2.2.1 j
  · exact gram_row_7.2.2.2.2.2.2.1 j
  · exact gram_row_8.2.2.2.2.2.2.1 j
  · exact gram_row_9.2.2.2.2.2.2.1 j
  · exact gram_row_10.2.2.2.2.2.2.1 j
  · exact gram_row_11.2.2.2.2.2.2.1 j
  · exact gram_row_12.2.2.2.2.2.2.1 j
  · exact gram_row_13.2.2.2.2.2.2.1 j
  · exact gram_row_14.2.2.2.2.2.2.1 j

/-- Gram UUImag matches for the stated finite source data. -/
theorem gramUUImag_matches :
    ∀ i j, gramUUImag i j = (faceUpReal.transpose * faceUpImag - faceUpImag.transpose * faceUpReal) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.2.2.2.2.2.1 j
  · exact gram_row_1.2.2.2.2.2.2.2.1 j
  · exact gram_row_2.2.2.2.2.2.2.2.1 j
  · exact gram_row_3.2.2.2.2.2.2.2.1 j
  · exact gram_row_4.2.2.2.2.2.2.2.1 j
  · exact gram_row_5.2.2.2.2.2.2.2.1 j
  · exact gram_row_6.2.2.2.2.2.2.2.1 j
  · exact gram_row_7.2.2.2.2.2.2.2.1 j
  · exact gram_row_8.2.2.2.2.2.2.2.1 j
  · exact gram_row_9.2.2.2.2.2.2.2.1 j
  · exact gram_row_10.2.2.2.2.2.2.2.1 j
  · exact gram_row_11.2.2.2.2.2.2.2.1 j
  · exact gram_row_12.2.2.2.2.2.2.2.1 j
  · exact gram_row_13.2.2.2.2.2.2.2.1 j
  · exact gram_row_14.2.2.2.2.2.2.2.1 j

/-- Gram UVReal matches for the stated finite source data. -/
theorem gramUVReal_matches :
    ∀ i j, gramUVReal i j = (faceUpReal.transpose * faceDownReal + faceUpImag.transpose * faceDownImag + faceDownReal.transpose * faceUpReal + faceDownImag.transpose * faceUpImag) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_1.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_3.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_4.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_5.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_6.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_7.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_8.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_9.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_10.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_11.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_12.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_13.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_14.2.2.2.2.2.2.2.2.1 j

/-- Gram UVImag matches for the stated finite source data. -/
theorem gramUVImag_matches :
    ∀ i j, gramUVImag i j = (faceUpReal.transpose * faceDownImag - faceUpImag.transpose * faceDownReal + faceDownReal.transpose * faceUpImag - faceDownImag.transpose * faceUpReal) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_1.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_3.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_4.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_5.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_6.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_7.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_8.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_9.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_10.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_11.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_12.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_13.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_14.2.2.2.2.2.2.2.2.2.1 j

/-- Gram VVReal matches for the stated finite source data. -/
theorem gramVVReal_matches :
    ∀ i j, gramVVReal i j = (faceDownReal.transpose * faceDownReal + faceDownImag.transpose * faceDownImag) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_1.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_2.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_3.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_4.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_5.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_6.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_7.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_8.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_9.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_10.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_11.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_12.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_13.2.2.2.2.2.2.2.2.2.2.1 j
  · exact gram_row_14.2.2.2.2.2.2.2.2.2.2.1 j

/-- Gram VVImag matches for the stated finite source data. -/
theorem gramVVImag_matches :
    ∀ i j, gramVVImag i j = (faceDownReal.transpose * faceDownImag - faceDownImag.transpose * faceDownReal) i j := by
  intro i j
  fin_cases i
  · exact gram_row_0.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_1.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_2.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_3.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_4.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_5.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_6.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_7.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_8.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_9.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_10.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_11.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_12.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_13.2.2.2.2.2.2.2.2.2.2.2 j
  · exact gram_row_14.2.2.2.2.2.2.2.2.2.2.2 j

/-- From Parts adjoint mul for the stated finite source data. -/
theorem fromParts_adjoint_mul {m n p : ℕ}
    (R I : Matrix (Fin m) (Fin n) ℚ) (S T : Matrix (Fin m) (Fin p) ℚ) :
    (fromParts R I)ᴴ * fromParts S T =
      fromParts (R.transpose * S + I.transpose * T)
        (R.transpose * T - I.transpose * S) := by
  ext i j : 2
  apply Complex.ext <;>
    simp [fromParts, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.transpose_apply,
      Complex.mul_re, Complex.mul_im, Finset.sum_add_distrib, sub_eq_add_neg]

/-- From Parts add for the stated finite source data. -/
theorem fromParts_add {m n : ℕ} (R I S T : Matrix (Fin m) (Fin n) ℚ) :
    fromParts (R+S) (I+T) = fromParts R I + fromParts S T := by
  ext i j
  simp [fromParts]
  ring

/-- Gram BB eq for the stated finite source data. -/
theorem gramBB_eq : gramBB = faceBaseᴴ * faceBase := by
  unfold gramBB
  rw [faceBase, fromParts_gram]
  congr 1 <;> ext i j
  · exact gramBBReal_matches i j
  · exact gramBBImag_matches i j

/-- Gram BU eq for the stated finite source data. -/
theorem gramBU_eq : gramBU = faceBaseᴴ * faceUp + faceUpᴴ * faceBase := by
  unfold gramBU
  rw [faceBase, faceUp, fromParts_adjoint_mul, fromParts_adjoint_mul,
    ← fromParts_add]
  congr 1 <;> ext i j
  · have h := gramBUReal_matches i j
    simp only [Matrix.add_apply] at h ⊢
    rw [h]
    ring
  · have h := gramBUImag_matches i j
    simp only [Matrix.add_apply, Matrix.sub_apply] at h ⊢
    rw [h]
    ring

/-- Gram BV eq for the stated finite source data. -/
theorem gramBV_eq : gramBV = faceBaseᴴ * faceDown + faceDownᴴ * faceBase := by
  unfold gramBV
  rw [faceBase, faceDown, fromParts_adjoint_mul, fromParts_adjoint_mul,
    ← fromParts_add]
  congr 1 <;> ext i j
  · have h := gramBVReal_matches i j
    simp only [Matrix.add_apply] at h ⊢
    rw [h]
    ring
  · have h := gramBVImag_matches i j
    simp only [Matrix.add_apply, Matrix.sub_apply] at h ⊢
    rw [h]
    ring

/-- Gram UU eq for the stated finite source data. -/
theorem gramUU_eq : gramUU = faceUpᴴ * faceUp := by
  unfold gramUU
  rw [faceUp, fromParts_gram]
  congr 1 <;> ext i j
  · exact gramUUReal_matches i j
  · exact gramUUImag_matches i j

/-- Gram UV eq for the stated finite source data. -/
theorem gramUV_eq : gramUV = faceUpᴴ * faceDown + faceDownᴴ * faceUp := by
  unfold gramUV
  rw [faceUp, faceDown, fromParts_adjoint_mul, fromParts_adjoint_mul,
    ← fromParts_add]
  congr 1 <;> ext i j
  · have h := gramUVReal_matches i j
    simp only [Matrix.add_apply] at h ⊢
    rw [h]
    ring
  · have h := gramUVImag_matches i j
    simp only [Matrix.add_apply, Matrix.sub_apply] at h ⊢
    rw [h]
    ring

/-- Gram VV eq for the stated finite source data. -/
theorem gramVV_eq : gramVV = faceDownᴴ * faceDown := by
  unfold gramVV
  rw [faceDown, fromParts_gram]
  congr 1 <;> ext i j
  · exact gramVVReal_matches i j
  · exact gramVVImag_matches i j

def coefficientWeight (t : Fin 6) (i : Fin 5) (j : Fin 3) : ℚ :=
  ![1,
    (j : ℚ)*(12-(i : ℚ))/16,
    (j : ℚ)*(i : ℚ)*(10-(i : ℚ))/48,
    if j = 2 then ((i : ℚ)^2-19*(i : ℚ)+108)/48 else 0,
    if j = 2 then ((i : ℚ)^3-15*(i : ℚ)^2+68*(i : ℚ))/96 else 0,
    if j = 2 then (i : ℚ)*((i : ℚ)-1)*((i : ℚ)^2-11*(i : ℚ)+36)/96 else 0] t

def gramReal : Fin 6 → Matrix (Fin 15) (Fin 15) ℚ :=
  ![gramBBReal,gramBUReal,gramBVReal,gramUUReal,gramUVReal,gramVVReal]

def gramImag : Fin 6 → Matrix (Fin 15) (Fin 15) ℚ :=
  ![gramBBImag,gramBUImag,gramBVImag,gramUUImag,gramUVImag,gramVVImag]

noncomputable def gramPiece : Fin 6 → Matrix (Fin 15) (Fin 15) ℂ :=
  ![gramBB,gramBU,gramBV,gramUU,gramUV,gramVV]

def coefficientGramReal (i : Fin 5) (j : Fin 3) : Matrix (Fin 15) (Fin 15) ℚ :=
  ∑ t, coefficientWeight t i j • gramReal t

def coefficientGramImag (i : Fin 5) (j : Fin 3) : Matrix (Fin 15) (Fin 15) ℚ :=
  ∑ t, coefficientWeight t i j • gramImag t

noncomputable def coefficientGram (i : Fin 5) (j : Fin 3) :
    Matrix (Fin 15) (Fin 15) ℂ :=
  ∑ t, (coefficientWeight t i j : ℝ) • gramPiece t

/-- Coefficient Gram eq from Parts for the stated finite source data. -/
theorem coefficientGram_eq_fromParts (i : Fin 5) (j : Fin 3) :
    coefficientGram i j = fromParts (coefficientGramReal i j) (coefficientGramImag i j) := by
  simp only [coefficientGram, coefficientGramReal, coefficientGramImag,
    gramPiece, gramReal, gramImag, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  simp only [gramBB,gramBU,gramBV,gramUU,gramUV,gramVV,
    ← fromParts_rat_smul, ← fromParts_add]


/-- Incidence 0 0 for the stated finite source data. -/
private theorem incidence_0_0 :
    (∀ a b, lowerCoefficientReal 0 0 a b = (coefficientGramReal 0 0 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 0 0 a b = (coefficientGramImag 0 0 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 0 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 0 0) a b) ∧
    (∀ a b, upperCoefficientImag 0 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 0 0) a b) := by
  decide +kernel

/-- Incidence 0 1 for the stated finite source data. -/
private theorem incidence_0_1 :
    (∀ a b, lowerCoefficientReal 0 1 a b = (coefficientGramReal 0 1 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 0 1 a b = (coefficientGramImag 0 1 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 0 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 0 1) a b) ∧
    (∀ a b, upperCoefficientImag 0 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 0 1) a b) := by
  decide +kernel

/-- Incidence 0 2 for the stated finite source data. -/
private theorem incidence_0_2 :
    (∀ a b, lowerCoefficientReal 0 2 a b = (coefficientGramReal 0 2 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 0 2 a b = (coefficientGramImag 0 2 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 0 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 0 2) a b) ∧
    (∀ a b, upperCoefficientImag 0 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 0 2) a b) := by
  decide +kernel

/-- Incidence 1 0 for the stated finite source data. -/
private theorem incidence_1_0 :
    (∀ a b, lowerCoefficientReal 1 0 a b = (coefficientGramReal 1 0 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 1 0 a b = (coefficientGramImag 1 0 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 1 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 1 0) a b) ∧
    (∀ a b, upperCoefficientImag 1 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 1 0) a b) := by
  decide +kernel

/-- Incidence 1 1 for the stated finite source data. -/
private theorem incidence_1_1 :
    (∀ a b, lowerCoefficientReal 1 1 a b = (coefficientGramReal 1 1 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 1 1 a b = (coefficientGramImag 1 1 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 1 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 1 1) a b) ∧
    (∀ a b, upperCoefficientImag 1 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 1 1) a b) := by
  decide +kernel

/-- Incidence 1 2 for the stated finite source data. -/
private theorem incidence_1_2 :
    (∀ a b, lowerCoefficientReal 1 2 a b = (coefficientGramReal 1 2 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 1 2 a b = (coefficientGramImag 1 2 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 1 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 1 2) a b) ∧
    (∀ a b, upperCoefficientImag 1 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 1 2) a b) := by
  decide +kernel

/-- Incidence 2 0 for the stated finite source data. -/
private theorem incidence_2_0 :
    (∀ a b, lowerCoefficientReal 2 0 a b = (coefficientGramReal 2 0 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 2 0 a b = (coefficientGramImag 2 0 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 2 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 2 0) a b) ∧
    (∀ a b, upperCoefficientImag 2 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 2 0) a b) := by
  decide +kernel

/-- Incidence 2 1 for the stated finite source data. -/
private theorem incidence_2_1 :
    (∀ a b, lowerCoefficientReal 2 1 a b = (coefficientGramReal 2 1 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 2 1 a b = (coefficientGramImag 2 1 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 2 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 2 1) a b) ∧
    (∀ a b, upperCoefficientImag 2 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 2 1) a b) := by
  decide +kernel

/-- Incidence 2 2 for the stated finite source data. -/
private theorem incidence_2_2 :
    (∀ a b, lowerCoefficientReal 2 2 a b = (coefficientGramReal 2 2 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 2 2 a b = (coefficientGramImag 2 2 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 2 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 2 2) a b) ∧
    (∀ a b, upperCoefficientImag 2 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 2 2) a b) := by
  decide +kernel

/-- Incidence 3 0 for the stated finite source data. -/
private theorem incidence_3_0 :
    (∀ a b, lowerCoefficientReal 3 0 a b = (coefficientGramReal 3 0 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 3 0 a b = (coefficientGramImag 3 0 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 3 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 3 0) a b) ∧
    (∀ a b, upperCoefficientImag 3 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 3 0) a b) := by
  decide +kernel

/-- Incidence 3 1 for the stated finite source data. -/
private theorem incidence_3_1 :
    (∀ a b, lowerCoefficientReal 3 1 a b = (coefficientGramReal 3 1 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 3 1 a b = (coefficientGramImag 3 1 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 3 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 3 1) a b) ∧
    (∀ a b, upperCoefficientImag 3 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 3 1) a b) := by
  decide +kernel

/-- Incidence 3 2 for the stated finite source data. -/
private theorem incidence_3_2 :
    (∀ a b, lowerCoefficientReal 3 2 a b = (coefficientGramReal 3 2 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 3 2 a b = (coefficientGramImag 3 2 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 3 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 3 2) a b) ∧
    (∀ a b, upperCoefficientImag 3 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 3 2) a b) := by
  decide +kernel

/-- Incidence 4 0 for the stated finite source data. -/
private theorem incidence_4_0 :
    (∀ a b, lowerCoefficientReal 4 0 a b = (coefficientGramReal 4 0 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 4 0 a b = (coefficientGramImag 4 0 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 4 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 4 0) a b) ∧
    (∀ a b, upperCoefficientImag 4 0 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 4 0) a b) := by
  decide +kernel

/-- Incidence 4 1 for the stated finite source data. -/
private theorem incidence_4_1 :
    (∀ a b, lowerCoefficientReal 4 1 a b = (coefficientGramReal 4 1 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 4 1 a b = (coefficientGramImag 4 1 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 4 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 4 1) a b) ∧
    (∀ a b, upperCoefficientImag 4 1 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 4 1) a b) := by
  decide +kernel

/-- Incidence 4 2 for the stated finite source data. -/
private theorem incidence_4_2 :
    (∀ a b, lowerCoefficientReal 4 2 a b = (coefficientGramReal 4 2 - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag 4 2 a b = (coefficientGramImag 4 2 - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal 4 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal 4 2) a b) ∧
    (∀ a b, upperCoefficientImag 4 2 a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag 4 2) a b) := by
  decide +kernel

/-- Coefficient incidence parts for the stated finite source data. -/
theorem coefficient_incidence_parts (i : Fin 5) (j : Fin 3) :
    (∀ a b, lowerCoefficientReal i j a b = (coefficientGramReal i j - ThreeLevelGramCertificateCorner.metricReal) a b) ∧
    (∀ a b, lowerCoefficientImag i j a b = (coefficientGramImag i j - ThreeLevelGramCertificateCorner.metricImag) a b) ∧
    (∀ a b, upperCoefficientReal i j a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricReal - coefficientGramReal i j) a b) ∧
    (∀ a b, upperCoefficientImag i j a b = ((34 : ℚ) • ThreeLevelGramCertificateCorner.metricImag - coefficientGramImag i j) a b) := by
  fin_cases i <;> fin_cases j
  · exact incidence_0_0
  · exact incidence_0_1
  · exact incidence_0_2
  · exact incidence_1_0
  · exact incidence_1_1
  · exact incidence_1_2
  · exact incidence_2_0
  · exact incidence_2_1
  · exact incidence_2_2
  · exact incidence_3_0
  · exact incidence_3_1
  · exact incidence_3_2
  · exact incidence_4_0
  · exact incidence_4_1
  · exact incidence_4_2

/-- Lower Coefficient eq gram sub metric for the stated finite source data. -/
theorem lowerCoefficient_eq_gram_sub_metric (i : Fin 5) (j : Fin 3) :
    lowerCoefficient i j = coefficientGram i j - ThreeLevelGramCertificateCorner.cornerMetric := by
  rw [lowerCoefficient_eq_fromParts, coefficientGram_eq_fromParts,
    ThreeLevelGramCertificateCorner.cornerMetric, ← fromParts_sub]
  congr 1
  · ext a b; exact (coefficient_incidence_parts i j).1 a b
  · ext a b; exact (coefficient_incidence_parts i j).2.1 a b

/-- Upper Coefficient eq metric sub gram for the stated finite source data. -/
theorem upperCoefficient_eq_metric_sub_gram (i : Fin 5) (j : Fin 3) :
    upperCoefficient i j = (34 : ℝ) • ThreeLevelGramCertificateCorner.cornerMetric - coefficientGram i j := by
  rw [upperCoefficient_eq_fromParts, coefficientGram_eq_fromParts,
    ThreeLevelGramCertificateCorner.cornerMetric]
  have h := fromParts_rat_smul (34 : ℚ)
    ThreeLevelGramCertificateCorner.metricReal ThreeLevelGramCertificateCorner.metricImag
  norm_num only [Rat.cast_ofNat] at h
  rw [← h, ← fromParts_sub]
  congr 1
  · ext a b; exact (coefficient_incidence_parts i j).2.2.1 a b
  · ext a b; exact (coefficient_incidence_parts i j).2.2.2 a b


end Qatlib.Papers.GibbsSampl26.FiniteModels.ThreeLevelOrder120HighCoefficientTables
