/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleFactorization
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleGramCharacterizationTran
import Qatlib.Concepts.OrderedOracle.TiSdpBridge.LaurentCircleSpectralFactorTran
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.OrderedSearch06.LaurentDefs

open Matrix
open scoped BigOperators ComplexOrder

open Qatlib.Concepts.OrderedOracle.TiSdpBridge

def paperLaurent (N : ℕ) (q : ℤ → ℂ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.Icc (-(N : ℤ) + 1) ((N : ℤ) - 1), q i * z ^ i

def PaperNonnegative (N : ℕ) (q : ℤ → ℂ) : Prop :=
  (∀ z : ℂ, ‖z‖ = 1 → (paperLaurent N q z).im = 0) ∧
  ∀ z : ℂ, ‖z‖ = 1 → 0 ≤ (paperLaurent N q z).re

def PaperSymmetric (q : ℤ → ℂ) : Prop := ∀ i : ℤ, q (-i) = q i

def paperHermite (N : ℕ) : ℤ → ℂ :=
  fun i => if |i| < (N : ℤ) then (((N : ℝ) - ((|i| : ℤ) : ℝ)) / (N : ℝ) : ℂ) else 0

def IsRealSymmetric {N : ℕ} (Q : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  Qᵀ = Q ∧ ∀ i j, (Q i j).im = 0

theorem paperLaurent_coeff_eval (N : ℕ) (a : Fin N → ℂ) (z : ℂ) :
    paperLaurent N (fun i => complexLaurentCoefficient a i) z = complexLaurentEval a z := rfl

theorem genTrace_add {N : ℕ} (A B : Matrix (Fin N) (Fin N) ℂ) (j : ℤ) :
    genTrace (A + B) j = genTrace A j + genTrace B j := by
  simp only [genTrace, Matrix.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i' _
  by_cases h : ((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ) = j
  · simp [h]
  · simp [h]

theorem genTrace_smul {N : ℕ} (c : ℂ) (A : Matrix (Fin N) (Fin N) ℂ) (j : ℤ) :
    genTrace (c • A) j = c * genTrace A j := by
  simp only [genTrace, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i' _
  by_cases h : ((i' : ℕ) : ℤ) - ((i : ℕ) : ℤ) = j
  · simp [h]
  · simp [h]

theorem lemma1_laurentNonnegative_iff_psdGram (N : ℕ) (a : Fin N → ℂ) :
    complexLaurentNonnegative a ↔
      ∃ Q : Matrix (Fin N) (Fin N) ℂ,
        Q.PosSemidef ∧ ∀ i : ℤ, genTrace Q i = complexLaurentCoefficient a i := by
  constructor
  · intro ha
    obtain ⟨A, hA, hcoeff, -, -⟩ := (laurentCircleGramCharacterization N a).mp ha
    exact ⟨A, hA, hcoeff⟩
  · rintro ⟨A, hA, hcoeff⟩
    refine (laurentCircleGramCharacterization N a).mpr ⟨A, hA, hcoeff, ?_, ?_⟩
    · intro z
      exact (complexLaurentEval_eq_matrixLaurent_of_genTrace a A hcoeff z).symm
    · rw [← genTrace_zero, hcoeff 0]

theorem lemma2_real_symmetric_gram (N : ℕ) (a : Fin N → ℂ)
    (hnn : complexLaurentNonnegative a)
    (hsym : ∀ i : ℤ, complexLaurentCoefficient a (-i) = complexLaurentCoefficient a i) :
    ∃ Q : Matrix (Fin N) (Fin N) ℂ,
      Q.PosSemidef ∧ IsRealSymmetric Q ∧
        ∀ i : ℤ, genTrace Q i = complexLaurentCoefficient a i := by
  obtain ⟨A, hA, hcoeff⟩ := (lemma1_laurentNonnegative_iff_psdGram N a).mp hnn
  refine ⟨(2 : ℂ)⁻¹ • (A + Aᵀ), ?_, ?_, ?_⟩
  · refine (hA.add hA.transpose).smul ?_
    rw [show (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) by norm_num, Complex.zero_le_real]
    norm_num
  · refine ⟨?_, ?_⟩
    · rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]
    · intro i j
      have h := congrFun (congrFun hA.isHermitian j) i
      simp only [Matrix.conjTranspose_apply] at h
      simp only [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul, Matrix.transpose_apply]
      rw [← h]
      rw [Complex.star_def, Complex.add_conj]
      have hhalf : (2 : ℂ)⁻¹ = ((1 / 2 : ℝ) : ℂ) := by norm_num
      rw [hhalf, ← Complex.ofReal_mul]
      simp
  · intro i
    rw [genTrace_smul, genTrace_add, genTrace_transpose]
    rw [hcoeff i, hcoeff (-i), hsym i]
    have h2 : (2 : ℂ)⁻¹ * (2 : ℂ) = 1 := by norm_num
    calc (2 : ℂ)⁻¹ * (complexLaurentCoefficient a i + complexLaurentCoefficient a i)
        = ((2 : ℂ)⁻¹ * 2) * complexLaurentCoefficient a i := by ring
      _ = complexLaurentCoefficient a i := by rw [h2, one_mul]

theorem theorem2_fejer_riesz (N : ℕ) (a : Fin N → ℂ) :
    complexLaurentNonnegative a ↔
      ∃ p : Fin N → ℂ, ∀ z : ℂ, ‖z‖ = 1 →
        complexLaurentEval a z = ((‖(laurentCoefficientPolynomial p).eval z‖ ^ 2 : ℝ) : ℂ) := by
  constructor
  · intro ha
    obtain ⟨p, -, hc, -, -, -⟩ := laurentCircleSpectralFactor N a ha
    exact ⟨p, hc⟩
  · rintro ⟨p, hp⟩
    exact complexLaurentNonnegative_of_gram_posSemidef a (gramOuter p) (gramOuter_posSemidef p)
      (fun j => gramOuter_coeff_of_circle_factor a p hp j)

end Qatlib.Papers.OrderedSearch06.LaurentDefs
