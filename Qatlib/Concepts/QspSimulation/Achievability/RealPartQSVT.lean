/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QspSimulation.Achievability.RealPartResponse
import Qatlib.Concepts.CoherentSim.CoherentOAA.OddApproximation
import Qatlib.Concepts.BlockEncoding.LCU

/-!
# Real parts of QSVT responses by averaging

The circuit `realPartQSVT` selects between a phased alternating circuit and the circuit obtained
by conjugating every phase. The normalized two-branch preparation `realPartAmplitude` and the
lifted frame `averageFrame` make compression of `averageCircuit` equal the arithmetic mean of
the two compressed matrices.

This averaging realizes `realPartPolynomial (responseP base zs)`. Odd phase-list length gives
the off-diagonal block of polynomial evaluation on the Hermitian dilation, while even length
gives its left or right diagonal block. The corresponding singular-transform formulas apply the
real part of the scalar response to singular values, following the QSVT framework of
[GilyenSuLowWiebe2019].

## Main statements

* `average_projectedEncoding` encodes the arithmetic mean of two matrices encoded with common
  frames.
* `realPartQSVT_odd_projectedEncoding` gives the odd off-diagonal real-part response encoding.
* `realPartQSVT_even_left_projectedEncoding` and `realPartQSVT_even_right_projectedEncoding`
  give the two even diagonal response encodings.
* `realPartQSVT_odd_singularEncoding` and the even variants express these encodings as singular
  transforms.

## References

* [Gilyén et al., 2019][GilyenSuLowWiebe2019]
-/

open Qatlib.Concepts.WalkSearch.Spectral

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Concepts.CoherentSim.CoherentOAA
open Qatlib.Concepts.TrotterFormula.SuzukiFourth
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.BlockEncoding.LCU

namespace Qatlib.Concepts.QspSimulation.Achievability

open Matrix Polynomial
open Qatlib
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib
open Qatlib
open Qatlib

/-- The common complex amplitude `(1 + Complex.I) / 2` for the two branches used in real-part
averaging. -/
noncomputable def realPartAmplitude (_ : Bool) : ℂ := (1 + Complex.I) / 2

/-- Each branch of `realPartAmplitude` has squared magnitude equal to one half. -/
@[simp] theorem realPartAmplitude_weight (b : Bool) :
    star (realPartAmplitude b) * realPartAmplitude b = (2 : ℂ)⁻¹ := by
  apply Complex.ext <;> norm_num [realPartAmplitude, Complex.mul_re, Complex.mul_im]

/-- The squared magnitudes of `realPartAmplitude` sum to one over the two Boolean branches. -/
theorem realPartAmplitude_normalized :
    ∑ b : Bool, star (realPartAmplitude b) * realPartAmplitude b = 1 := by
  simp only [Fintype.sum_bool, realPartAmplitude_weight]
  norm_num

/-- Taking the upper-right block commutes with the arithmetic mean of two matrices. -/
private theorem realPart_toBlocks₁₂_average {I O : Type*}
    (M N : Matrix (O ⊕ I) (O ⊕ I) ℂ) :
    ((2 : ℂ)⁻¹ • (M + N)).toBlocks₁₂ =
      (2 : ℂ)⁻¹ • (M.toBlocks₁₂ + N.toBlocks₁₂) := rfl

/-- Taking the upper-left block commutes with the arithmetic mean of two matrices. -/
private theorem realPart_toBlocks₁₁_average {I O : Type*}
    (M N : Matrix (O ⊕ I) (O ⊕ I) ℂ) :
    ((2 : ℂ)⁻¹ • (M + N)).toBlocks₁₁ =
      (2 : ℂ)⁻¹ • (M.toBlocks₁₁ + N.toBlocks₁₁) := rfl

/-- Taking the lower-right block commutes with the arithmetic mean of two matrices. -/
private theorem realPart_toBlocks₂₂_average {I O : Type*}
    (M N : Matrix (O ⊕ I) (O ⊕ I) ℂ) :
    ((2 : ℂ)⁻¹ • (M + N)).toBlocks₂₂ =
      (2 : ℂ)⁻¹ • (M.toBlocks₂₂ + N.toBlocks₂₂) := rfl

section Average

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

/-- The Boolean selection circuit that applies `U` on the true branch and `V` on the false
branch. -/
noncomputable def averageCircuit (U V : Matrix H H ℂ) :
    Matrix (Bool × H) (Bool × H) ℂ := select (fun b : Bool => if b then U else V)

/-- The frame obtained by composing `L` with the preparation lift for the normalized two-branch
amplitudes `realPartAmplitude`. -/
noncomputable def averageFrame (L : Matrix H O ℂ) : Matrix (Bool × H) O ℂ :=
  prepareLift (I := H) realPartAmplitude * L

omit [Fintype O] in

/-- Lifting an isometric frame with `averageFrame` preserves its isometry property. -/
theorem averageFrame_isIsometry {L : Matrix H O ℂ} (hL : IsIsometry L) :
    IsIsometry (averageFrame L) := by
  have hp := prepareLift_isIsometry (I := H) realPartAmplitude realPartAmplitude_normalized
  unfold IsIsometry at hp hL ⊢
  simp only [averageFrame, Matrix.conjTranspose_mul]
  calc
    Lᴴ * (prepareLift (I := H) realPartAmplitude)ᴴ *
        (prepareLift (I := H) realPartAmplitude * L) =
        Lᴴ * ((prepareLift (I := H) realPartAmplitude)ᴴ *
          prepareLift (I := H) realPartAmplitude) * L := by
      simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hp, Matrix.mul_one, hL]

omit [Fintype H] [DecidableEq H] in

/-- The linear combination selected with `realPartAmplitude` is the arithmetic mean of `U` and
`V`. -/
private theorem realPart_average_lcu (U V : Matrix H H ℂ) :
    lcuMatrix realPartAmplitude (fun b : Bool => if b then U else V) =
      (2 : ℂ)⁻¹ • (U + V) := by
  simp only [lcuMatrix, Fintype.sum_bool, Bool.false_eq_true, ↓reduceIte,
    realPartAmplitude_weight, smul_add]

omit [Fintype I] [Fintype O] [DecidableEq I] [DecidableEq O] in

/-- Compressing `averageCircuit U V` between the lifted frames gives the arithmetic mean of the
two original compressions. -/
theorem averageCircuit_compress (L : Matrix H O ℂ) (R : Matrix H I ℂ)
    (U V : Matrix H H ℂ) :
    compress (averageFrame L) (averageCircuit U V) (averageFrame R) =
      (2 : ℂ)⁻¹ • (compress L U R + compress L V R) := by
  calc
    compress (averageFrame L) (averageCircuit U V) (averageFrame R) =
        compress L (compress (prepareLift realPartAmplitude)
          (select (fun b : Bool => if b then U else V))
          (prepareLift realPartAmplitude)) R := by
      simp only [averageFrame, averageCircuit, compress, Matrix.conjTranspose_mul,
        Matrix.mul_assoc]
    _ = (2 : ℂ)⁻¹ • (compress L U R + compress L V R) := by
      rw [prepare_select_compress, realPart_average_lcu, compress_smul, compress_add]

omit [Fintype I] [Fintype O] in

/-- Two projected unitary encodings with common frames yield an encoding of their arithmetic
mean using `averageCircuit` and the lifted frames. -/
theorem average_projectedEncoding {A B : Matrix O I ℂ} {U V : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (hA : ProjectedUnitaryEncoding A U L R) (hB : ProjectedUnitaryEncoding B V L R) :
    ProjectedUnitaryEncoding ((2 : ℂ)⁻¹ • (A + B))
      (averageCircuit U V) (averageFrame L) (averageFrame R) := by
  refine ⟨select_unitary _ ?_, averageFrame_isIsometry hA.left_isometry,
    averageFrame_isIsometry hA.right_isometry, ?_⟩
  · intro b
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact hB.unitary
    · exact hA.unitary
  · rw [averageCircuit_compress, hA.encoded, hB.encoded]

/-- The Boolean selection circuit pairing a phased alternating circuit with the circuit obtained
by conjugating its base and phase list. -/
noncomputable def realPartQSVT (U P Q : Matrix H H ℂ) (base : ℂ) (zs : List ℂ) :
    Matrix (Bool × H) (Bool × H) ℂ :=
  averageCircuit (phasedAlternating U P Q base zs)
    (phasedAlternating U P Q (star base) (zs.map star))

/-- For an odd phase-list length and phase-valued parameters, `realPartQSVT` encodes the
upper-right block of the real-part response evaluated on the Hermitian dilation of `A`. See
[GilyenSuLowWiebe2019] for the QSVT setting. -/
theorem realPartQSVT_odd_projectedEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1) :
    ProjectedUnitaryEncoding
      (aeval (hermitianDilation A) (realPartPolynomial (responseP base zs))).toBlocks₁₂
      (realPartQSVT U (rangeProjector R) (rangeProjector L) base zs)
      (averageFrame L) (averageFrame R) := by
  have hc := average_projectedEncoding (qsvt_odd_projectedEncoding h hb zs hzs hodd)
    (qsvt_odd_projectedEncoding h (Qatlib.Concepts.QspSimulation.Achievability.IsPhase.conjugate hb) (zs.map star) (phases_conjugate zs hzs)
      (by simpa using hodd))
  simpa only [realPartQSVT, realPartPolynomial_responseP, map_smul, map_add,
    realPart_toBlocks₁₂_average] using hc

/-- For an even phase-list length and phase-valued parameters, `realPartQSVT` with the lifted
left frame encodes the upper-left block of the real-part response evaluated on the Hermitian
dilation of `A`. See [GilyenSuLowWiebe2019]. -/
theorem realPartQSVT_even_left_projectedEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ProjectedUnitaryEncoding
      (aeval (hermitianDilation A) (realPartPolynomial (responseP base zs))).toBlocks₁₁
      (realPartQSVT U (rangeProjector R) (rangeProjector L) base zs)
      (averageFrame L) (averageFrame L) := by
  have hc := average_projectedEncoding (qsvt_even_left_projectedEncoding h hb zs hzs heven)
    (qsvt_even_left_projectedEncoding h (Qatlib.Concepts.QspSimulation.Achievability.IsPhase.conjugate hb) (zs.map star) (phases_conjugate zs hzs)
      (by simpa using heven))
  simpa only [realPartQSVT, realPartPolynomial_responseP, map_smul, map_add,
    realPart_toBlocks₁₁_average] using hc

/-- For an even phase-list length and phase-valued parameters, `realPartQSVT` built from `Uᴴ`
with the lifted right frame encodes the lower-right block of the real-part response
evaluated on the Hermitian dilation of `A`. See [GilyenSuLowWiebe2019]. -/
theorem realPartQSVT_even_right_projectedEncoding {A : Matrix O I ℂ} {U : Matrix H H ℂ}
    {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ProjectedUnitaryEncoding
      (aeval (hermitianDilation A) (realPartPolynomial (responseP base zs))).toBlocks₂₂
      (realPartQSVT Uᴴ (rangeProjector L) (rangeProjector R) base zs)
      (averageFrame R) (averageFrame R) := by
  have hc := average_projectedEncoding (qsvt_even_right_projectedEncoding h hb zs hzs heven)
    (qsvt_even_right_projectedEncoding h (Qatlib.Concepts.QspSimulation.Achievability.IsPhase.conjugate hb) (zs.map star) (phases_conjugate zs hzs)
      (by simpa using heven))
  simpa only [realPartQSVT, realPartPolynomial_responseP, map_smul, map_add,
    realPart_toBlocks₂₂_average] using hc

end Average

/-- The arithmetic mean of two products with common outer matrices and diagonal middle factors
equals the product with the pointwise average on the diagonal. -/
private theorem realPart_diagonal_average {J I O : Type*} [Fintype J] [DecidableEq J]
    (B : Matrix O J ℂ) (C : Matrix J I ℂ) (f g : J → ℂ) :
    (2 : ℂ)⁻¹ • (B * diagonal f * C + B * diagonal g * C) =
      B * diagonal (fun j => (2 : ℂ)⁻¹ * (f j + g j)) * C := by
  have hd : diagonal (fun j => (2 : ℂ)⁻¹ * (f j + g j)) =
      (2 : ℂ)⁻¹ • (diagonal f + diagonal g) := by
    ext i j
    by_cases hij : i = j <;> simp [hij, mul_add]
  rw [hd]
  simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, smul_add]

section SingularTargets

variable {H I O : Type*} [Fintype H] [Fintype I] [Fintype O]
  [DecidableEq H] [DecidableEq I] [DecidableEq O]

/-- For odd phase-list length, the upper-right dilation block of the real-part response is the
odd singular transform of `A` with scalar function given by the real part of `responseP`.
See [GilyenSuLowWiebe2019]. -/
theorem realPartResponse_odd_eq_singularTransform
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (hodd : zs.length % 2 = 1) :
    (aeval (hermitianDilation A) (realPartPolynomial (responseP base zs))).toBlocks₁₂ =
      oddSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ)) := by
  simp only [realPartPolynomial_responseP, map_smul, map_add,
    realPart_toBlocks₁₂_average]
  rw [← qsvt_odd_eq_dilation h base zs hodd, qsvt_odd_eq_oddSingularTransform h base zs hodd,
    ← qsvt_odd_eq_dilation h (star base) (zs.map star) (by simpa using hodd),
    qsvt_odd_eq_oddSingularTransform h (star base) (zs.map star) (by simpa using hodd)]
  unfold oddSingularTransform
  rw [realPart_diagonal_average]
  simp only [responseP_conjugate_eval, half_add_star]

/-- For even phase-list length, the upper-left dilation block of the real-part response is the
left singular transform of `A` with scalar function given by the real part of `responseP`.
See [GilyenSuLowWiebe2019]. -/
theorem realPartResponse_even_left_eq_singularTransform
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    (aeval (hermitianDilation A) (realPartPolynomial (responseP base zs))).toBlocks₁₁ =
      leftSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ)) := by
  simp only [realPartPolynomial_responseP, map_smul, map_add,
    realPart_toBlocks₁₁_average]
  rw [← qsvt_even_left_eq_dilation h base zs heven,
    qsvt_even_left_eq_leftSingularTransform h base zs heven,
    ← qsvt_even_left_eq_dilation h (star base) (zs.map star) (by simpa using heven),
    qsvt_even_left_eq_leftSingularTransform h (star base) (zs.map star) (by simpa using heven)]
  unfold leftSingularTransform spectralDiagonal
  rw [realPart_diagonal_average]
  simp only [responseP_conjugate_eval, half_add_star]

/-- For even phase-list length, the lower-right dilation block of the real-part response is the
right singular transform of `A` with scalar function given by the real part of `responseP`.
See [GilyenSuLowWiebe2019]. -/
theorem realPartResponse_even_right_eq_singularTransform
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) (base : ℂ) (zs : List ℂ)
    (heven : zs.length % 2 = 0) :
    (aeval (hermitianDilation A) (realPartPolynomial (responseP base zs))).toBlocks₂₂ =
      rightSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ)) := by
  simp only [realPartPolynomial_responseP, map_smul, map_add,
    realPart_toBlocks₂₂_average]
  rw [← qsvt_even_right_eq_dilation h base zs heven,
    qsvt_even_right_eq_rightSingularTransform h base zs heven,
    ← qsvt_even_right_eq_dilation h (star base) (zs.map star) (by simpa using heven),
    qsvt_even_right_eq_rightSingularTransform h (star base) (zs.map star) (by simpa using heven)]
  unfold rightSingularTransform spectralDiagonal
  rw [realPart_diagonal_average]
  simp only [responseP_conjugate_eval, half_add_star]

/-- For odd phase-list length and phase-valued parameters, the real-part circuit encodes the odd
singular transform of `A` with scalar function given by the real part of `responseP`. See
[GilyenSuLowWiebe2019]. -/
theorem realPartQSVT_odd_singularEncoding
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (hodd : zs.length % 2 = 1) :
    ProjectedUnitaryEncoding
      (oddSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ)))
      (realPartQSVT U (rangeProjector R) (rangeProjector L) base zs)
      (averageFrame L) (averageFrame R) := by
  rw [← realPartResponse_odd_eq_singularTransform h base zs hodd]
  exact realPartQSVT_odd_projectedEncoding h hb zs hzs hodd

/-- For even phase-list length and phase-valued parameters, the real-part circuit with lifted
left frames encodes the left singular transform of `A` with scalar function given by the
real part of `responseP`. See [GilyenSuLowWiebe2019]. -/
theorem realPartQSVT_even_left_singularEncoding
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ProjectedUnitaryEncoding
      (leftSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ)))
      (realPartQSVT U (rangeProjector R) (rangeProjector L) base zs)
      (averageFrame L) (averageFrame L) := by
  rw [← realPartResponse_even_left_eq_singularTransform h base zs heven]
  exact realPartQSVT_even_left_projectedEncoding h hb zs hzs heven

/-- For even phase-list length and phase-valued parameters, the real-part circuit built from
`Uᴴ` with lifted right frames encodes the right singular transform of `A` with scalar
function given by the real part of `responseP`. See [GilyenSuLowWiebe2019]. -/
theorem realPartQSVT_even_right_singularEncoding
    {A : Matrix O I ℂ} {U : Matrix H H ℂ} {L : Matrix H O ℂ} {R : Matrix H I ℂ}
    (h : ProjectedUnitaryEncoding A U L R) {base : ℂ} (hb : IsPhase base)
    (zs : List ℂ) (hzs : ∀ z ∈ zs, IsPhase z) (heven : zs.length % 2 = 0) :
    ProjectedUnitaryEncoding
      (rightSingularTransform A (fun x => (((responseP base zs).eval (x : ℂ)).re : ℂ)))
      (realPartQSVT Uᴴ (rangeProjector L) (rangeProjector R) base zs)
      (averageFrame R) (averageFrame R) := by
  rw [← realPartResponse_even_right_eq_singularTransform h base zs heven]
  exact realPartQSVT_even_right_projectedEncoding h hb zs hzs heven

end SingularTargets

end Qatlib.Concepts.QspSimulation.Achievability
