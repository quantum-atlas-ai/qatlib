/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.OrderedSearch06.SdpForm.Basic
import Mathlib.Data.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option linter.unusedSimpArgs false
noncomputable section

namespace Qatlib.Papers.OrderedSearch06.SdpForm

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder

open Qatlib.Papers.OrderedSearch06.LaurentDefs

open Qatlib.Concepts.OrderedOracle.TiSdpBridge

theorem posSemidef_fromBlocks_zero {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (X : Matrix m m ℂ) (Y : Matrix n n ℂ) :
    (fromBlocks X 0 0 Y : Matrix (m ⊕ n) (m ⊕ n) ℂ).PosSemidef ↔
      X.PosSemidef ∧ Y.PosSemidef := by
  constructor
  · intro h
    exact ⟨h.submatrix Sum.inl, h.submatrix Sum.inr⟩
  · rintro ⟨hX, hY⟩
    classical
    have hH : (fromBlocks X 0 0 Y : Matrix (m ⊕ n) (m ⊕ n) ℂ).IsHermitian :=
      Matrix.isHermitian_fromBlocks_iff.mpr ⟨hX.1, by simp, by simp, hY.1⟩
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH ?_
    intro x
    have hsplit : star x ⬝ᵥ ((fromBlocks X 0 0 Y : Matrix (m ⊕ n) (m ⊕ n) ℂ) *ᵥ x)
        = star (fun i => x (Sum.inl i)) ⬝ᵥ (X *ᵥ fun i => x (Sum.inl i))
          + star (fun i => x (Sum.inr i)) ⬝ᵥ (Y *ᵥ fun i => x (Sum.inr i)) := by
      simp only [dotProduct, Matrix.mulVec, Fintype.sum_sum_type, fromBlocks_apply₁₁,
        fromBlocks_apply₁₂, fromBlocks_apply₂₁, fromBlocks_apply₂₂]
      simp [Finset.mul_sum]
    rw [hsplit]
    exact add_nonneg (hX.dotProduct_mulVec_nonneg _) (hY.dotProduct_mulVec_nonneg _)

theorem counteridentity_mul_mul_assoc_apply {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    counteridentity N * (counteridentity N * X) = X := by
  rw [← Matrix.mul_assoc, counteridentity_mul_self N, Matrix.one_mul]

theorem counteridentity_mul_mul_assoc_apply_right {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    (X * counteridentity N) * counteridentity N = X := by
  rw [Matrix.mul_assoc, counteridentity_mul_self N, Matrix.mul_one]

theorem counteridentity_mul_conj_mul {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    counteridentity N * (counteridentity N * X * counteridentity N) = X * counteridentity N := by
  rw [show counteridentity N * (counteridentity N * X * counteridentity N)
      = (counteridentity N * (counteridentity N * X)) * counteridentity N by
    rw [← Matrix.mul_assoc]]
  rw [counteridentity_mul_mul_assoc_apply X]

theorem neg_counteridentity_mul_conj_mul {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    (-counteridentity N) * (counteridentity N * X * counteridentity N) = -(X * counteridentity N) := by
  rw [Matrix.neg_mul, counteridentity_mul_conj_mul]

theorem counteridentity_conj_conj {N : ℕ} (X : Matrix (Fin N) (Fin N) ℂ) :
    counteridentity N * (counteridentity N * X * counteridentity N) * counteridentity N = X := by
  rw [counteridentity_mul_conj_mul, counteridentity_mul_mul_assoc_apply_right]

theorem isRealSymmetric_add {N : ℕ} {A B : Matrix (Fin N) (Fin N) ℂ}
    (hA : IsRealSymmetric A) (hB : IsRealSymmetric B) : IsRealSymmetric (A + B) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_add, hA.1, hB.1]
  · intro i j
    simp only [Matrix.add_apply, Complex.add_im, hA.2 i j, hB.2 i j, add_zero]

theorem isRealSymmetric_real_smul {N : ℕ} {A : Matrix (Fin N) (Fin N) ℂ} (c : ℝ)
    (hA : IsRealSymmetric A) : IsRealSymmetric ((c : ℂ) • A) := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.transpose_smul, hA.1]
  · intro i j
    simp only [Matrix.smul_apply, smul_eq_mul, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, hA.2 i j]
    ring

def jsymPart (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (2 : ℂ)⁻¹ • (Q + counteridentity N * Q * counteridentity N)

theorem jsymPart_commutes (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℂ) :
    counteridentity N * jsymPart N Q * counteridentity N = jsymPart N Q := by
  unfold jsymPart
  rw [Matrix.mul_smul, Matrix.smul_mul]
  have hinner : counteridentity N * (Q + counteridentity N * Q * counteridentity N) *
      counteridentity N = counteridentity N * Q * counteridentity N + Q := by
    rw [Matrix.mul_add, Matrix.add_mul, counteridentity_conj_conj]
  rw [hinner, add_comm]

theorem jsymPart_posSemidef {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℂ}
    (hQ : Q.PosSemidef) : (jsymPart N Q).PosSemidef := by
  unfold jsymPart
  have hconj : (counteridentity N * Q * counteridentity N).PosSemidef := by
    simpa only [counteridentity_conjTranspose] using
      hQ.mul_mul_conjTranspose_same (counteridentity N)
  have hsum : (Q + counteridentity N * Q * counteridentity N).PosSemidef := hQ.add hconj
  have hhalf : (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ) := by
    exact Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
  rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num]
  exact hsum.smul hhalf

theorem jsymPart_isRealSymmetric {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℂ}
    (hQ : IsRealSymmetric Q) : IsRealSymmetric (jsymPart N Q) := by
  unfold jsymPart
  have hconj : IsRealSymmetric (counteridentity N * Q * counteridentity N) :=
    counteridentity_conj_isRealSymmetric N Q hQ
  have hsum : IsRealSymmetric (Q + counteridentity N * Q * counteridentity N) :=
    isRealSymmetric_add hQ hconj
  rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num]
  exact isRealSymmetric_real_smul (1 / 2) hsum

theorem jsymPart_apply_entries {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℂ}
    (h0 : ∀ i j, Q i j = (N : ℂ)⁻¹) (i j : Fin N) :
    jsymPart N Q i j = (N : ℂ)⁻¹ := by
  unfold jsymPart
  simp only [Matrix.smul_apply, Matrix.add_apply, counteridentity_mul_apply, h0, smul_eq_mul]
  ring

theorem jsymPart_trace (N : ℕ) (Q : Matrix (Fin N) (Fin N) ℂ) :
    (jsymPart N Q).trace = Q.trace := by
  unfold jsymPart
  rw [Matrix.trace_smul, Matrix.trace_add, counteridentity_conj_trace, smul_eq_mul]
  ring

theorem jsymPart_genTrace {N : ℕ} {Q : Matrix (Fin N) (Fin N) ℂ} (hQ : Qᵀ = Q) (j : ℤ) :
    genTrace (jsymPart N Q) j = genTrace Q j := by
  unfold jsymPart
  rw [LaurentDefs.genTrace_smul, LaurentDefs.genTrace_add, counteridentity_conj_genTrace,
      genTrace_neg_eq_of_transpose_eq Q hQ j]
  ring

theorem solvesPaperSDP_jsym (N k : ℕ) (Q : ℕ → Matrix (Fin N) (Fin N) ℂ)
    (h : SolvesPaperSDP N k Q) :
    SolvesPaperSDP N k (fun t => jsymPart N (Q t)) ∧
      ∀ t, counteridentity N * jsymPart N (Q t) * counteridentity N = jsymPart N (Q t) := by
  obtain ⟨hPSD, hreal, h0, htr, hk, hstep⟩ := h
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun t => jsymPart_commutes N (Q t)⟩
  · intro t; exact jsymPart_posSemidef (hPSD t)
  · intro t; exact jsymPart_isRealSymmetric (hreal t)
  · intro i j; exact jsymPart_apply_entries (N := N) h0 i j
  · intro t ht; rw [jsymPart_trace]; exact htr t ht
  · change jsymPart N (Q k) = (N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)
    rw [hk]
    unfold jsymPart
    rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, counteridentity_mul_self]
    rw [← two_smul ℂ ((N : ℂ)⁻¹ • (1 : Matrix (Fin N) (Fin N) ℂ)), smul_smul,
      show (2 : ℂ)⁻¹ * 2 = 1 by norm_num, one_smul]
  · intro t ht i hi
    beta_reduce
    simp only [jsymPart_genTrace (hreal t).1, jsymPart_genTrace (hreal (t - 1)).1]
    exact hstep t ht i hi

def paperJ (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  fromBlocks 0 (counteridentity m) (counteridentity m) 0

def paperU (m : ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  fromBlocks 1 1 (counteridentity m) (-(counteridentity m))

def paperBlockQ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  fromBlocks A B (counteridentity m * B * counteridentity m)
    (counteridentity m * A * counteridentity m)

theorem paperU_conjTranspose (m : ℕ) :
    (paperU m)ᴴ = fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) (counteridentity m)
      1 (-(counteridentity m)) := by
  rw [paperU, fromBlocks_conjTranspose]
  simp [counteridentity_conjTranspose]

theorem paperU_mul_conjTranspose (m : ℕ) :
    paperU m * (paperU m)ᴴ = (2 : ℂ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ) := by
  rw [paperU_conjTranspose, paperU, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul,
    fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_one, Matrix.one_mul, zero_mul, mul_zero,
      add_zero, zero_add, neg_mul, mul_neg, sub_self, add_neg_cancel, neg_neg,
      counteridentity_mul_self, two_smul]

theorem paperU_conjTranspose_mul (m : ℕ) :
    (paperU m)ᴴ * paperU m = (2 : ℂ) • (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ) := by
  rw [paperU_conjTranspose, paperU, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_smul,
    fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_one, Matrix.one_mul, zero_mul, mul_zero,
      add_zero, zero_add, neg_mul, mul_neg, sub_self, add_neg_cancel, neg_neg,
      counteridentity_mul_self, two_smul]

theorem paperJ_mul_self (m : ℕ) :
    paperJ m * paperJ m = (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ) := by
  rw [paperJ, fromBlocks_multiply, ← fromBlocks_one, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [zero_mul, mul_zero, add_zero, zero_add, counteridentity_mul_self,
      mul_one, one_mul, two_smul]

theorem paperU_conj_paperJ (m : ℕ) :
    (paperU m)ᴴ * paperJ m * paperU m =
      (2 : ℂ) • fromBlocks (1 : Matrix (Fin m) (Fin m) ℂ) 0 0 (-(1 : Matrix (Fin m) (Fin m) ℂ)) := by
  rw [paperU_conjTranspose, paperJ, paperU, fromBlocks_multiply, fromBlocks_multiply,
    fromBlocks_smul, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Matrix.mul_one, Matrix.one_mul, zero_mul, mul_zero,
      add_zero, zero_add, neg_mul, mul_neg, counteridentity_mul_self,
      neg_neg, sub_self, neg_zero, two_smul, add_neg_cancel, neg_add_cancel]

theorem paperBlockQ_commutes (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ) :
    paperJ m * paperBlockQ m A B * paperJ m = paperBlockQ m A B := by
  rw [paperJ, paperBlockQ, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [zero_mul, mul_zero, add_zero, zero_add,
      Matrix.mul_one, Matrix.one_mul, counteridentity_mul_conj_mul,
      counteridentity_mul_mul_assoc_apply_right]

theorem paperU_conj_blockQ (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ) :
    (paperU m)ᴴ * paperBlockQ m A B * paperU m =
      (2 : ℂ) • fromBlocks (A + B * counteridentity m) 0 0
        (A - B * counteridentity m) := by
  have hJ := counteridentity_mul_self m
  have hfirst : (paperU m)ᴴ * paperBlockQ m A B =
      fromBlocks (A + B * counteridentity m) (B + A * counteridentity m)
        (A - B * counteridentity m) (B - A * counteridentity m) := by
    rw [paperU_conjTranspose, paperBlockQ, fromBlocks_multiply, fromBlocks_inj]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      simp only [Matrix.mul_one, Matrix.one_mul, zero_mul, mul_zero,
        add_zero, zero_add, neg_mul, mul_neg,
        counteridentity_mul_conj_mul, sub_eq_add_neg]
  rw [hfirst, paperU, fromBlocks_multiply, fromBlocks_smul, fromBlocks_inj]
  have hBA : (B + A * counteridentity m) * counteridentity m = B * counteridentity m + A := by
    rw [add_mul, Matrix.mul_assoc, counteridentity_mul_self m, Matrix.mul_one]
  have hsub : (B - A * counteridentity m) * counteridentity m = B * counteridentity m - A := by
    rw [sub_mul, Matrix.mul_assoc, counteridentity_mul_self m, Matrix.mul_one]
  have hBAneg : (B + A * counteridentity m) * (-counteridentity m) =
      -(B * counteridentity m) - A := by
    rw [mul_neg, hBA]
    abel
  have hsubneg : (B - A * counteridentity m) * (-counteridentity m) =
      -(B * counteridentity m) + A := by
    rw [mul_neg, hsub]
    abel
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [Matrix.mul_one, zero_mul, mul_zero, add_zero, zero_add]
    rw [hBA, two_smul]
    abel
  · simp only [Matrix.mul_one, zero_mul, mul_zero, add_zero, zero_add]
    rw [hBAneg, smul_zero]
    abel
  · simp only [Matrix.mul_one, zero_mul, mul_zero, add_zero, zero_add]
    rw [hsub, smul_zero]
    abel
  · simp only [Matrix.mul_one, zero_mul, mul_zero, add_zero, zero_add]
    rw [hsubneg, two_smul]
    abel

theorem paperBlockQ_psd_iff (m : ℕ) (A B : Matrix (Fin m) (Fin m) ℂ) :
    (paperBlockQ m A B).PosSemidef ↔
      (A + B * counteridentity m).PosSemidef ∧
        (A - B * counteridentity m).PosSemidef := by
  have hhalf : (0 : ℂ) ≤ ((1 / 2 : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have htwo : (0 : ℂ) ≤ (2 : ℂ) :=
    Complex.zero_le_real.mpr (by norm_num : (0 : ℝ) ≤ 2)
  have hW : paperU m * ((1 / 2 : ℂ) • (paperU m)ᴴ) = 1 := by
    rw [Matrix.mul_smul, paperU_mul_conjTranspose, smul_smul]
    norm_num
  have hU : IsUnit (paperU m) := IsUnit.of_mul_eq_one _ hW
  have hif : ((paperU m)ᴴ * paperBlockQ m A B * paperU m).PosSemidef ↔
      (paperBlockQ m A B).PosSemidef := by
    simpa only [Matrix.star_eq_conjTranspose] using
      (IsUnit.posSemidef_star_left_conjugate_iff (x := paperBlockQ m A B) hU)
  rw [← hif, paperU_conj_blockQ]
  constructor
  · intro h
    have hD : (fromBlocks (A + B * counteridentity m) 0 0
        (A - B * counteridentity m)).PosSemidef := by
      have hh := h.smul hhalf
      rwa [show ((1 / 2 : ℝ) : ℂ) •
          ((2 : ℂ) • fromBlocks (A + B * counteridentity m) 0 0
            (A - B * counteridentity m))
          = fromBlocks (A + B * counteridentity m) 0 0
            (A - B * counteridentity m) from by
        rw [smul_smul, show ((1 / 2 : ℝ) : ℂ) * 2 = 1 by norm_num, one_smul]] at hh
    exact (posSemidef_fromBlocks_zero _ _).mp hD
  · rintro ⟨hE1, hE2⟩
    have hD : (fromBlocks (A + B * counteridentity m) 0 0
        (A - B * counteridentity m)).PosSemidef :=
      (posSemidef_fromBlocks_zero _ _).mpr ⟨hE1, hE2⟩
    exact hD.smul htwo

def TwistedSymmetric (m : ℕ) (B : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  B = counteridentity m * Bᵀ * counteridentity m

theorem twistedSymmetric_iff_symm (m : ℕ) (B : Matrix (Fin m) (Fin m) ℂ) :
    TwistedSymmetric m B ↔ (counteridentity m * B)ᵀ = counteridentity m * B := by
  have hJ := counteridentity_mul_self m
  constructor
  · intro h
    have hJB : counteridentity m * B = Bᵀ * counteridentity m := by
      calc counteridentity m * B
          = counteridentity m * (counteridentity m * Bᵀ * counteridentity m) :=
              congrArg (fun X => counteridentity m * X) h
        _ = Bᵀ * counteridentity m := counteridentity_mul_conj_mul Bᵀ
    rw [hJB, Matrix.transpose_mul, counteridentity_transpose, Matrix.transpose_transpose]
    exact hJB
  · intro h
    change B = counteridentity m * Bᵀ * counteridentity m
    have hBJ : Bᵀ * counteridentity m = counteridentity m * B := by
      rw [← h, Matrix.transpose_mul, counteridentity_transpose]
    have hBt : Bᵀ = counteridentity m * B * counteridentity m := by
      calc Bᵀ = (Bᵀ * counteridentity m) * counteridentity m := by
            rw [Matrix.mul_assoc, hJ, Matrix.mul_one]
        _ = (counteridentity m * B) * counteridentity m := by rw [hBJ]
    rw [hBt]
    exact (counteridentity_conj_conj B).symm

theorem paper_param_even (m k : ℕ) :
    (2 * (m : ℚ)) * ((2 * (m : ℚ)) / 2 + 1) * ((k : ℚ) - 1) / 2
      = (m : ℚ) * ((m : ℚ) + 1) * ((k : ℚ) - 1) := by
  ring

theorem paper_param_odd (m k : ℕ) :
    ((2 * (m : ℚ) + 1) + 1) ^ 2 * ((k : ℚ) - 1) / 4
      = ((m : ℚ) + 1) ^ 2 * ((k : ℚ) - 1) := by
  ring

theorem paper_param_blocks (m : ℕ) :
    (m : ℚ) * ((m : ℚ) + 1) = 2 * ((m : ℚ) * ((m : ℚ) + 1) / 2) := by
  ring

theorem paper_card_even (m : ℕ) : Fintype.card (Fin m ⊕ Fin m) = 2 * m := by
  rw [Fintype.card_sum, Fintype.card_fin]
  ring

end Qatlib.Papers.OrderedSearch06.SdpForm
