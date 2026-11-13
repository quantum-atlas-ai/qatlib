/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SketchSpectral.EvenSVT.EvenSVTDecompositionNormBoundsStat
import Qatlib.Foundations.OperatorErrors.OperatorError
import Qatlib.Concepts.SketchSpectral.SketchPerturb.SketchSingularValueStabilitySamp

/-!
# Norm bounds for even SVT decompositions

The module bounds the two-sketch Gram spectra and transfers scalar envelopes to operator-norm
bounds for Hermitian matrix functions in the setting of [ChiaEtAl2022].
`evenSVTDecompositionNormBounds` uses a Lipschitz hypothesis to obtain a finite envelope;
`not_evenSVTDecompositionNormBounds` disproves the separately defined statement with no
regularity hypothesis.

## Main statements

* `evenSVTDecompositionNormBounds`: Proves the even-SVT decomposition norm statement with its
  spectral-band Lipschitz hypothesis and supplied-envelope conclusion. See [ChiaEtAl2022].
* `even_svt_decomposition_supplied_envelope`: A supplied nonnegative envelope on the enlarged
  squared-singular-value bands and zero bounds the operator norm of the outer sketch's matrix
  function.
* `not_evenSVTDecompositionNormBounds`: The unrestricted statement
  `OriginalEvenSVTDecompositionNormBounds` is false.

## References

* [Chia et al., 2022][ChiaEtAl2022]
-/

open Qatlib.Concepts.SketchSpectral.SketchPerturb
open Qatlib.Concepts.SpectralSketch.SpectrumPerturb
open Qatlib.Concepts.WalkSearch.Spectral
open Qatlib.Concepts.RandCompile.ChannelBudget

open Qatlib.Concepts.CoherentSim.CoherentOAA Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
namespace Qatlib.Concepts.SketchSpectral.EvenSVT
open Qatlib.Concepts.PhaseGeometry.Phase
open Qatlib.Concepts.OperatorErrors.Robustness.SignalProcessing Matrix
open scoped Classical BigOperators Matrix.Norms.L2Operator

/-- A Frobenius bound `η` on the inner Gram error gives `‖Rᴴ * R‖ ≤ ‖Aᴴ * A‖ + η`. -/
theorem sketch_inner_gram_op_norm_bound {K C RS : Type} [Fintype K] [DecidableEq K]
    [Fintype C] [DecidableEq C] [Fintype RS] [DecidableEq RS]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (η : ℝ)
    (h : spectralFrobenius (Rᴴ*R-Aᴴ*A) ≤ η) : ‖Rᴴ*R‖ ≤ ‖Aᴴ*A‖+η := by
  have hn : ‖Rᴴ*R-Aᴴ*A‖ ≤ η := (spectral_operator_norm_le_frobenius _).trans h
  have he : Rᴴ*R = (Rᴴ*R-Aᴴ*A)+Aᴴ*A := by abel
  rw [he]
  exact (norm_add_le _ _).trans (by linarith)

/-- A nonnegative scalar bound on a function at every ordered eigenvalue bounds the operator
norm of its Hermitian matrix function. -/
theorem hermitian_function_op_norm_le_spectral_envelope {I : Type} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (hH : H.IsHermitian) (g : ℝ → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hg : ∀ i, ‖g (orderedHermitianValues hH i)‖ ≤ B) :
    ‖hermitianFunction H hH g‖ ≤ B := by
  let V := basisColumns (orderedHermitianBasis hH)
  have hV : ‖V‖ ≤ 1 := by
    have he := Matrix.l2_opNorm_conjTranspose_mul_self V
    change ‖(basisColumns (orderedHermitianBasis hH))ᴴ*basisColumns
        (orderedHermitianBasis hH)‖ = ‖V‖*‖V‖ at he
    rw [basisColumns_adjoint_mul] at he
    have hn := l2_norm_one_le (I := Fin (Fintype.card I))
    nlinarith [norm_nonneg V]
  have hdiag : ‖Matrix.diagonal (fun i => g (orderedHermitianValues hH i))‖ ≤ B := by
    rw [Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg hB).mpr hg
  unfold hermitianFunction spectralDiagonal
  change ‖V * Matrix.diagonal (fun i => g (orderedHermitianValues hH i)) * Vᴴ‖ ≤ B
  calc
    _ ≤ (‖V‖*‖Matrix.diagonal (fun i => g (orderedHermitianValues hH i))‖)*‖Vᴴ‖ :=
      (Matrix.l2_opNorm_mul _ _).trans
        (mul_le_mul_of_nonneg_right (Matrix.l2_opNorm_mul _ _) (norm_nonneg _))
    _ ≤ (1*B)*1 := by rw [Matrix.l2_opNorm_conjTranspose]; gcongr
    _ = B := by ring

/-- The ordered eigenvalues of the outer sketch Gram matrix differ from the corresponding
squared singular values of `A` by at most `2 * η₁ + 2 * η₂`. -/
theorem two_sketch_outer_gram_spectral_band
    {K C RS CT : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (T : Matrix C CT ℂ)
    (η₁ η₂ : ℝ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (h₁ : spectralFrobenius (Rᴴ*R - Aᴴ*A) ≤ η₁)
    (h₂ : spectralFrobenius ((R*T)*(R*T)ᴴ - R*Rᴴ) ≤ η₂)
    (i : Fin (Fintype.card RS)) :
    |orderedHermitianValues (Matrix.isHermitian_mul_conjTranspose_self (R*T)) i -
      (matrixSingularValues A i)^2| ≤ 2*η₁ + 2*η₂ := by
  have hw := (ordered_hermitian_weyl_and_hoffman_wielandt RS
    ((R*T)*(R*T)ᴴ) (R*Rᴴ)
    (Matrix.isHermitian_mul_conjTranspose_self (R*T))
    (Matrix.isHermitian_mul_conjTranspose_self R)).1 i
  rw [sketchSingularValueStability_outer_gram RS CT (R*T),
    sketchSingularValueStability_outer_gram RS C R] at hw
  have ho := hw.trans ((spectral_operator_norm_le_frobenius _).trans h₂)
  rw [sketchSingularValueStability_outer_gram RS CT (R*T)]
  by_cases hi : i.val < Fintype.card C
  · have hin := sketchSingularValueStability_inner K C RS A R η₁ h₁ i.val hi
    have ht := abs_sub_le ((matrixSingularValues (R*T) i)^2)
      ((matrixSingularValues R i)^2) ((matrixSingularValues A i)^2)
    nlinarith only [ho, hin, ht, hη₁, hη₂]
  · have hiC : Fintype.card C ≤ i.val := Nat.le_of_not_gt hi
    rw [matrixSingularValues_of_card_le R hiC] at ho
    rw [matrixSingularValues_of_card_le A hiC]
    simpa only [zero_pow (by decide : (2 : ℕ) ≠ 0), sub_zero] using
      ho.trans (by linarith : η₂ ≤ 2*η₁ + 2*η₂)

/-- A function that is Lipschitz on a finite union of bounded spectral bands is bounded there
and at zero. -/
theorem finite_band_envelope_of_lipschitz (n : ℕ) (s : ℕ → ℝ) (ρ L : ℝ)
    (g : ℝ → ℂ) (hρ : 0 ≤ ρ) (hL : 0 ≤ L)
    (hLip : ∀ x y : ℝ,
      (∃ i : ℕ, i < n ∧ |x-s i| ≤ ρ) →
      (∃ i : ℕ, i < n ∧ |y-s i| ≤ ρ) → ‖g x-g y‖ ≤ L*|x-y|) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x : ℝ,
      ((∃ i : ℕ, i < n ∧ |x-s i| ≤ ρ) ∨ x=0) → ‖g x‖ ≤ B := by
  let S : ℝ := ∑ i : Fin n, ‖g (s i)‖
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => norm_nonneg _)
  refine ⟨‖g 0‖ + S + L*ρ, by positivity, ?_⟩
  intro x hx
  rcases hx with ⟨i, hi, hx⟩ | rfl
  · have hc : ∃ j : ℕ, j < n ∧ |s i-s j| ≤ ρ := ⟨i, hi, by simpa using hρ⟩
    have hd := (hLip x (s i) ⟨i,hi,hx⟩ hc).trans
      (mul_le_mul_of_nonneg_left hx hL)
    have ht : ‖g (s i)‖ ≤ S := by
      dsimp [S]
      exact Finset.single_le_sum (fun (j : Fin n) _ => norm_nonneg (g (s j)))
        (Finset.mem_univ (⟨i,hi⟩ : Fin n))
    have hn : ‖g x‖ ≤ ‖g x-g (s i)‖ + ‖g (s i)‖ := by
      calc
        ‖g x‖ = ‖(g x-g (s i))+g (s i)‖ := by congr 1; abel
        _ ≤ _ := norm_add_le _ _
    linarith [norm_nonneg (g 0)]
  · linarith [mul_nonneg hL hρ]

/-- A supplied nonnegative envelope on the enlarged squared-singular-value bands and zero bounds
the operator norm of the outer sketch's matrix function. -/
theorem even_svt_decomposition_supplied_envelope
    {K C RS CT : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (T : Matrix C CT ℂ)
    (g : ℝ → ℂ) (η₁ η₂ B : ℝ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (h₁ : spectralFrobenius (Rᴴ*R-Aᴴ*A) ≤ η₁)
    (h₂ : spectralFrobenius ((R*T)*(R*T)ᴴ-R*Rᴴ) ≤ η₂) (hB : 0 ≤ B)
    (hg : ∀ x : ℝ,
      ((∃ i : ℕ, i < Fintype.card RS ∧ |x-(matrixSingularValues A i)^2| ≤
        2*η₁+2*η₂) ∨ x=0) → ‖g x‖ ≤ B) :
    ‖hermitianFunction ((R*T)*(R*T)ᴴ)
      (Matrix.isHermitian_mul_conjTranspose_self (R*T)) g‖ ≤ B := by
  apply hermitian_function_op_norm_le_spectral_envelope _ _ g B hB
  intro i
  exact hg _ (Or.inl ⟨i.val, i.isLt,
    two_sketch_outer_gram_spectral_band A R T η₁ η₂ hη₁ hη₂ h₁ h₂ i⟩)

/-- Proves the even-SVT decomposition norm statement with its spectral-band Lipschitz hypothesis
and supplied-envelope conclusion. See [ChiaEtAl2022]. -/
theorem evenSVTDecompositionNormBounds : EvenSVTDecompositionNormBounds := by
  intro K C RS CT _ _ _ _ _ _ _ _ A R T g η₁ η₂ L hη₁ hη₂ h₁ h₂ hL hLip
  have hρ : 0 ≤ 2*η₁+2*η₂ := by positivity
  obtain ⟨B,hB,hg⟩ := finite_band_envelope_of_lipschitz (Fintype.card RS)
    (fun i => (matrixSingularValues A i)^2) (2*η₁+2*η₂) L g hρ hL hLip
  exact ⟨sketch_inner_gram_op_norm_bound A R η₁ h₁,
    ⟨B,hg,even_svt_decomposition_supplied_envelope A R T g η₁ η₂ B
      hη₁ hη₂ h₁ h₂ hB hg⟩,
    fun B hB hg => even_svt_decomposition_supplied_envelope A R T g η₁ η₂ B
      hη₁ hη₂ h₁ h₂ hB hg⟩

/-- A constant scalar function gives an outer sketch matrix function with operator norm at most
the norm of that constant. -/
theorem even_svt_constant_function_consumer
    {K C RS CT : Type} [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (T : Matrix C CT ℂ)
    (z : ℂ) (η₁ η₂ : ℝ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (h₁ : spectralFrobenius (Rᴴ*R-Aᴴ*A) ≤ η₁)
    (h₂ : spectralFrobenius ((R*T)*(R*T)ᴴ-R*Rᴴ) ≤ η₂) :
    ‖hermitianFunction ((R*T)*(R*T)ᴴ)
      (Matrix.isHermitian_mul_conjTranspose_self (R*T)) (fun _ => z)‖ ≤ ‖z‖ := by
  have h := evenSVTDecompositionNormBounds K C RS CT A R T (fun _ => z)
    η₁ η₂ 0 hη₁ hη₂ h₁ h₂ (le_refl 0) (by intros; simp)
  exact h.2.2 ‖z‖ (norm_nonneg _) (by intros; exact le_refl _)

/-- The proposed decomposition norm statement that requires a finite spectral-band envelope for
every scalar function without a regularity hypothesis. -/
def OriginalEvenSVTDecompositionNormBounds : Prop :=
  ∀ (K C RS CT : Type) [Fintype K] [DecidableEq K] [Fintype C] [DecidableEq C]
    [Fintype RS] [DecidableEq RS] [Fintype CT] [DecidableEq CT]
    (A : Matrix K C ℂ) (R : Matrix RS C ℂ) (T : Matrix C CT ℂ)
    (g : ℝ → ℂ) (η₁ η₂ : ℝ),
    0 ≤ η₁ → 0 ≤ η₂ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius (Rᴴ*R - Aᴴ*A) ≤ η₁ →
    Qatlib.Concepts.SpectralSketch.SpectrumPerturb.spectralFrobenius ((R*T)*(R*T)ᴴ - R*Rᴴ) ≤ η₂ →
    ‖Rᴴ*R‖ ≤ ‖Aᴴ*A‖ + η₁ ∧
    ∃ B : ℝ,
      (∀ x : ℝ,
        ((∃ i : ℕ, i < Fintype.card RS ∧
          |x - (Qatlib.Concepts.RandCompile.ChannelBudget.matrixSingularValues A i)^2| ≤
            2*η₁ + 2*η₂) ∨ x = 0) →
        ‖g x‖ ≤ B) ∧
      ‖Qatlib.Concepts.SpectralSketch.SpectrumPerturb.hermitianFunction ((R*T)*(R*T)ᴴ)
          (Matrix.isHermitian_mul_conjTranspose_self (R*T)) g‖ ≤ B

/-- Every singular value of the zero `1 × 1` matrix is zero. -/
private theorem zero_singular_value (i : ℕ) :
    matrixSingularValues (0 : Matrix (Fin 1) (Fin 1) ℂ) i = 0 := by
  apply le_antisymm _ (matrixSingularValues_nonneg _ _)
  apply not_lt.mp
  rw [matrixSingularValues_pos_iff_lt_finrank_range]
  have hz : (0 : Matrix (Fin 1) (Fin 1) ℂ).toEuclideanLin = 0 :=
    map_zero (Matrix.toEuclideanLin (m := Fin 1) (n := Fin 1) (𝕜 := ℂ))
  rw [hz, LinearMap.range_zero, finrank_bot]
  exact Nat.not_lt_zero i

/-- The unrestricted statement `OriginalEvenSVTDecompositionNormBounds` is false. -/
theorem not_evenSVTDecompositionNormBounds : ¬ OriginalEvenSVTDecompositionNormBounds := by
  intro h
  let g : ℝ → ℂ := fun x => ((x⁻¹ : ℝ) : ℂ)
  obtain ⟨_,B,hB,_⟩ := h (Fin 1) (Fin 1) (Fin 1) (Fin 1) 0 0 0 g 1 0
    (by norm_num) (by norm_num)
    (by norm_num [spectralFrobenius]) (by norm_num [spectralFrobenius])
  have hden : 0 < |B|+1 := by positivity
  let x : ℝ := 1/(|B|+1)
  have hx : 0 < x := div_pos (by norm_num) hden
  have hx1 : x ≤ 1 := (div_le_iff₀ hden).mpr (by linarith [abs_nonneg B])
  have hband : (∃ i : ℕ, i < Fintype.card (Fin 1) ∧
      |x - (matrixSingularValues (0 : Matrix (Fin 1) (Fin 1) ℂ) i)^2| ≤ 2*(1:ℝ)+2*0) ∨ x=0 := by
    apply Or.inl
    refine ⟨0,by simp,?_⟩
    rw [zero_singular_value, zero_pow (by decide), sub_zero, abs_of_pos hx]
    linarith
  have hg := hB x hband
  have he : ‖g x‖ = |B|+1 := by
    dsimp [g,x]
    rw [Complex.norm_real,Real.norm_eq_abs]
    simp only [one_div,inv_inv,abs_of_pos hden]
  rw [he] at hg
  linarith [le_abs_self B]
end Qatlib.Concepts.SketchSpectral.EvenSVT
