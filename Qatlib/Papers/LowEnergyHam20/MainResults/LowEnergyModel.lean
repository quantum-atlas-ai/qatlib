/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import QuantumInfo.ForMathlib.HermitianMat.CFC
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef

set_option backward.isDefEq.respectTransparency false

/-!
# Low-energy Hamiltonian simulation: basic model

Fixed paper version: arXiv:2006.02660v2 (2021-09-09), *Hamiltonian simulation in the
low-energy subspace* (Şahinoğlu–Somma).

This module sets up the objects used in the paper's Main Results:

* `projLE H Λ` and `projGT H Λ` are the spectral projectors `Π_{≤Λ}` and `Π_{>Λ}` of a
  Hermitian matrix `H`, defined by continuous functional calculus with the indicator
  functions of `(-∞, Λ]` and `(Λ, ∞)` (Supplementary Information, definitions before
  Supplementary Note 1).
* `evU A s` is `e^{-i s A}` (the paper's `U(s) = e^{-isH}` when `A = H`).
* `effTerm H Δ A = Π_{≤Δ} A Π_{≤Δ}` is the `Δ`-effective operator `Ā` (Supplementary
  Information: "the Δ₀-effective Hamiltonians are H̄ = Π_{≤Δ₀} H Π_{≤Δ₀}, H̄_l = ...").
* `wordProd E q` is the product `E_{q-1} ... E_1 E_0` of a sequence of factors; this is
  the paper's product formula `W(s) = e^{-is_q H_{l_q}} ... e^{-is_1 H_{l_1}}` (Eq. (35)).
* `projWordProd P E q` is `P_{q-1}E_{q-1} ... P_0E_0`, the projected product
  `W^Λ(s) = Π_{≤Λ_q} e^{-is_q H_{l_q}} ... Π_{≤Λ_1} e^{-is_1 H_{l_1}}` (Eq. (37)).
* `tel P E Pinit q` is the telescoping defect sum underlying Eq. (40) and Eq. (46); the
  identity `wordProd E q * Pinit - projWordProd P E q * Pinit = tel P E Pinit q`
  is proven by induction, and `norm_tel_le` gives the triangle-inequality bound used in
  Corollaries 1–4.

All proofs in this file are complete; no `sorry` occurs here.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder BigOperators

namespace Qatlib.Papers.LowEnergyHam20.MainResults.LowEnergyModel

variable {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]

/-! ## Spectral projectors -/

/-- `Π_{≤Λ}`: the spectral projector of `H` onto eigenvalues at most `Λ`.
Defined by CFC with the indicator of `(-∞, Λ]`. -/
def projLE (H : HermitianMat n ℂ) (Λ : ℝ) : Matrix n n ℂ :=
  (H.cfc (fun x : ℝ => if x ≤ Λ then (1 : ℝ) else 0)).mat

/-- `Π_{>Λ}`: the spectral projector of `H` onto eigenvalues strictly larger than `Λ`.
Defined by CFC with the indicator of `(Λ, ∞)`. -/
def projGT (H : HermitianMat n ℂ) (Λ : ℝ) : Matrix n n ℂ :=
  (H.cfc (fun x : ℝ => if Λ < x then (1 : ℝ) else 0)).mat

/-- The complementary relation `Π_{≤Λ} + Π_{>Λ} = 1`. -/
theorem projLE_add_projGT (H : HermitianMat n ℂ) (Λ : ℝ) :
    projLE H Λ + projGT H Λ = 1 := by
  have hfun : (fun x : ℝ => (if x ≤ Λ then (1 : ℝ) else 0) +
        (if Λ < x then (1 : ℝ) else 0)) = (fun _ : ℝ => (1 : ℝ)) := by
    funext x
    by_cases hx : x ≤ Λ
    · have hx' : ¬ Λ < x := not_lt.mpr hx
      simp [hx, hx']
    · have hx' : Λ < x := not_le.mp hx
      simp [hx, hx']
  have hadd := HermitianMat.cfc_add_apply (A := H)
    (f := fun x : ℝ => if x ≤ Λ then (1 : ℝ) else 0)
    (g := fun x : ℝ => if Λ < x then (1 : ℝ) else 0)
  show (H.cfc _).mat + (H.cfc _).mat = 1
  rw [← HermitianMat.mat_add, ← hadd, hfun]
  simp [HermitianMat.cfc_const]

/-- `1 - Π_{≤Λ} = Π_{>Λ}`. -/
theorem one_sub_projLE (H : HermitianMat n ℂ) (Λ : ℝ) :
    (1 : Matrix n n ℂ) - projLE H Λ = projGT H Λ := by
  have h := projLE_add_projGT H Λ
  rw [← h]
  abel

/-- `Π_{≤Λ}` is idempotent. -/
theorem projLE_mul_self (H : HermitianMat n ℂ) (Λ : ℝ) :
    projLE H Λ * projLE H Λ = projLE H Λ := by
  have hfun : (fun x : ℝ => (if x ≤ Λ then (1 : ℝ) else 0) *
        (if x ≤ Λ then (1 : ℝ) else 0)) =
      (fun x : ℝ => if x ≤ Λ then (1 : ℝ) else 0) := by
    funext x
    by_cases hx : x ≤ Λ <;> simp [hx]
  show (H.cfc _).mat * (H.cfc _).mat = (H.cfc _).mat
  rw [← HermitianMat.mat_cfc_mul_apply, hfun]

/-- `Π_{>Λ}` is idempotent. -/
theorem projGT_mul_self (H : HermitianMat n ℂ) (Λ : ℝ) :
    projGT H Λ * projGT H Λ = projGT H Λ := by
  have hfun : (fun x : ℝ => (if Λ < x then (1 : ℝ) else 0) *
        (if Λ < x then (1 : ℝ) else 0)) =
      (fun x : ℝ => if Λ < x then (1 : ℝ) else 0) := by
    funext x
    by_cases hx : Λ < x <;> simp [hx]
  show (H.cfc _).mat * (H.cfc _).mat = (H.cfc _).mat
  rw [← HermitianMat.mat_cfc_mul_apply, hfun]

/-- A self-adjoint idempotent matrix is a contraction (this is the spectral-projector
norm bound `‖Π_{≤Λ}‖ = 1` used throughout the paper). -/
theorem norm_le_one_of_idempotent_selfAdjoint (P : Matrix n n ℂ)
    (hidem : P * P = P) (hsa : star P = P) : ‖P‖ ≤ 1 := by
  have hsq : ‖P‖ * ‖P‖ = ‖P‖ := by
    rw [← CStarRing.norm_star_mul_self, hsa, hidem]
  have hnn := norm_nonneg P
  nlinarith [sq_nonneg (‖P‖ - 1)]

/-- `Π_{≤Λ}` is self-adjoint. -/
theorem star_projLE (H : HermitianMat n ℂ) (Λ : ℝ) : star (projLE H Λ) = projLE H Λ := by
  rw [Matrix.star_eq_conjTranspose]
  rw [projLE, HermitianMat.mat_cfc]
  exact HermitianMat.conjTranspose_cfc (A := H)
    (f := fun x : ℝ => if x ≤ Λ then (1 : ℝ) else 0)

/-- `Π_{>Λ}` is self-adjoint. -/
theorem star_projGT (H : HermitianMat n ℂ) (Λ : ℝ) : star (projGT H Λ) = projGT H Λ := by
  rw [Matrix.star_eq_conjTranspose]
  rw [projGT, HermitianMat.mat_cfc]
  exact HermitianMat.conjTranspose_cfc (A := H)
    (f := fun x : ℝ => if Λ < x then (1 : ℝ) else 0)

/-- The norm of `Π_{≤Λ}` is at most one (spectral projectors are contractions). -/
theorem norm_projLE_le_one (H : HermitianMat n ℂ) (Λ : ℝ) : ‖projLE H Λ‖ ≤ 1 :=
  norm_le_one_of_idempotent_selfAdjoint _ (projLE_mul_self H Λ) (star_projLE H Λ)

/-- The norm of `Π_{>Λ}` is at most one. -/
theorem norm_projGT_le_one (H : HermitianMat n ℂ) (Λ : ℝ) : ‖projGT H Λ‖ ≤ 1 :=
  norm_le_one_of_idempotent_selfAdjoint _ (projGT_mul_self H Λ) (star_projGT H Λ)

/-! ## Exponential unitaries `e^{-i s A}` -/

/-- `e^{-i s A}`, the time-evolution unitary for time `s` under `A`. -/
def evU (A : Matrix n n ℂ) (s : ℝ) : Matrix n n ℂ :=
  NormedSpace.exp ((-((s : ℂ) * Complex.I)) • A)

/-- `(e^{-isA})` is unitary when `A` is Hermitian. -/
theorem evU_mem_unitary (A : Matrix n n ℂ) (hA : A.IsHermitian) (s : ℝ) :
    evU A s ∈ unitary (Matrix n n ℂ) := by
  unfold evU
  letI : NormedAlgebra ℚ (Matrix n n ℂ) := NormedAlgebra.restrictScalars ℚ ℂ (Matrix n n ℂ)
  refine NormedSpace.exp_mem_unitary_of_mem_skewAdjoint ?_
  rw [skewAdjoint.mem_iff]
  have hstarA : star A = A := by
    rw [Matrix.star_eq_conjTranspose]
    exact hA.eq
  have hsm : star ((s : ℂ) * Complex.I) = -((s : ℂ) * Complex.I) := by
    rw [star_mul]
    have hs : star (s : ℂ) = (s : ℂ) := by
      rw [Complex.star_def]
      exact Complex.conj_ofReal s
    have hI : star Complex.I = -Complex.I := by
      rw [Complex.star_def]
      exact Complex.conj_I
    rw [hs, hI, mul_comm (-Complex.I) (s : ℂ), mul_neg]
  have hneg : star (-((s : ℂ) * Complex.I)) = ((s : ℂ) * Complex.I) := by
    rw [star_neg, hsm, neg_neg]
  show star ((-((s : ℂ) * Complex.I)) • A) = -((-((s : ℂ) * Complex.I)) • A)
  rw [star_smul, hneg, hstarA, neg_smul, neg_neg]

/-- `‖e^{-isA}‖ = 1` for Hermitian `A`. -/
theorem norm_evU (A : Matrix n n ℂ) (hA : A.IsHermitian) (s : ℝ) : ‖evU A s‖ = 1 :=
  CStarRing.norm_of_mem_unitary (evU_mem_unitary A hA s)

/-- `‖e^{-isA}‖ ≤ 1` for Hermitian `A`. -/
theorem norm_evU_le_one (A : Matrix n n ℂ) (hA : A.IsHermitian) (s : ℝ) :
    ‖evU A s‖ ≤ 1 := (norm_evU A hA s).le

/-! ## Effective (low-energy) operators -/

/-- The `Δ`-effective operator `Ā = Π_{≤Δ} A Π_{≤Δ}`. -/
def effTerm (H : HermitianMat n ℂ) (Δ : ℝ) (A : Matrix n n ℂ) : Matrix n n ℂ :=
  projLE H Δ * A * projLE H Δ

/-- The norm of an effective operator is bounded by the norm of the operator. -/
theorem norm_effTerm_le (H : HermitianMat n ℂ) (Δ : ℝ) (A : Matrix n n ℂ) :
    ‖effTerm H Δ A‖ ≤ ‖A‖ := by
  refine (norm_mul_le _ _).trans ?_
  have h1 : ‖projLE H Δ * A‖ ≤ ‖A‖ := by
    calc ‖projLE H Δ * A‖ ≤ ‖projLE H Δ‖ * ‖A‖ := norm_mul_le _ _
      _ ≤ 1 * ‖A‖ := by
          have h := norm_projLE_le_one H Δ
          nlinarith [norm_nonneg A]
      _ = ‖A‖ := one_mul _
  calc ‖projLE H Δ * A‖ * ‖projLE H Δ‖ ≤ ‖A‖ * 1 := by
        refine mul_le_mul h1 (norm_projLE_le_one H Δ) (norm_nonneg _) (norm_nonneg A)
    _ = ‖A‖ := mul_one _

/-- The effective operator `Π_{≤Δ} A Π_{≤Δ}` is Hermitian when `A` is. -/
theorem effTerm_isHermitian (H : HermitianMat n ℂ) (Δ : ℝ) (A : Matrix n n ℂ)
    (hA : A.IsHermitian) : (effTerm H Δ A).IsHermitian := by
  rw [Matrix.IsHermitian, effTerm, conjTranspose_mul, conjTranspose_mul]
  have hP : (projLE H Δ)ᴴ = projLE H Δ := by
    rw [← Matrix.star_eq_conjTranspose]
    exact star_projLE H Δ
  rw [hP, hA.eq, mul_assoc]

/-- The exponential of an effective operator is a contraction. -/
theorem norm_evU_effTerm_le_one (H : HermitianMat n ℂ) (Δ : ℝ) (A : Matrix n n ℂ)
    (hA : A.IsHermitian) (s : ℝ) : ‖evU (effTerm H Δ A) s‖ ≤ 1 :=
  norm_evU_le_one _ (effTerm_isHermitian H Δ A hA) s

/-! ## Products, projected products, and the telescoping identity -/

/-- The ordered product `E_{q-1} ⋯ E_1 E_0` (paper Eq. (35), later factors on the left). -/
def wordProd (E : ℕ → Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => 1
  | q + 1 => E q * wordProd E q

/-- The projected product `P_{q-1}E_{q-1} ⋯ P_0E_0` (paper Eq. (37)). -/
def projWordProd (P E : ℕ → Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => 1
  | q + 1 => P q * E q * projWordProd P E q

/-- Telescoping defect accumulator for Eq. (40): at step `q+1` it appends the term
`(1 - P_q) E_q (P_{q-1}E_{q-1} ⋯ P_0E_0 Π)` to `E_q` times the previous accumulator. -/
def tel (P E : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => 0
  | q + 1 =>
      E q * tel P E Pinit q +
        (1 - P q) * E q * (projWordProd P E q * Pinit)

/-- Telescoping identity (paper Eq. (40), with the initial projector `Π_{≤Δ}` inserted):
`W Π - W^Λ Π` is the sum of the one-step leakage defects. -/
theorem wordProd_mul_sub_projWordProd_mul (P E : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ) :
    ∀ q : ℕ,
      wordProd E q * Pinit - projWordProd P E q * Pinit = tel P E Pinit q := by
  intro q
  induction q with
  | zero => simp [wordProd, projWordProd, tel]
  | succ q ih =>
      rw [wordProd, projWordProd, tel, ← ih]
      noncomm_ring

/-- The projected product including the initial projector has norm at most one. -/
theorem norm_projWordProd_mul_le_one (P E : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ)
    (hP : ∀ i, ‖P i‖ ≤ 1) (hE : ∀ i, ‖E i‖ ≤ 1) (hPinit : ‖Pinit‖ ≤ 1) :
    ∀ q : ℕ, ‖projWordProd P E q * Pinit‖ ≤ 1 := by
  intro q
  induction q with
  | zero => simpa [projWordProd] using hPinit
  | succ q ih =>
      have hassoc : projWordProd P E (q + 1) * Pinit =
          (P q * E q) * (projWordProd P E q * Pinit) := by
        simp only [projWordProd]
        noncomm_ring
      rw [hassoc]
      calc ‖(P q * E q) * (projWordProd P E q * Pinit)‖
          ≤ ‖P q * E q‖ * ‖projWordProd P E q * Pinit‖ := norm_mul_le _ _
        _ ≤ (‖P q‖ * ‖E q‖) * 1 := by
              refine mul_le_mul (norm_mul_le _ _) ih (norm_nonneg _) (by positivity)
        _ ≤ (1 * 1) * 1 := by
              have := hP q
              have := hE q
              nlinarith [norm_nonneg (P q), norm_nonneg (E q)]
        _ = 1 := by norm_num

/-- The norm of an ordered product of contractions is at most one. -/
theorem norm_wordProd_le_one (E : ℕ → Matrix n n ℂ) (hE : ∀ i, ‖E i‖ ≤ 1) :
    ∀ q : ℕ, ‖wordProd E q‖ ≤ 1 := by
  intro q
  induction q with
  | zero => simp [wordProd]
  | succ q ih =>
      rw [wordProd]
      calc ‖E q * wordProd E q‖ ≤ ‖E q‖ * ‖wordProd E q‖ := norm_mul_le _ _
        _ ≤ 1 * 1 := by
              refine mul_le_mul (hE q) ih (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num

/-- A single telescoping defect `(1 - P_q) E_q (P_{q-1}E_{q-1}⋯P_0E_0 Π)` is bounded
by the one-step leakage `‖(1 - P_q) E_q P_{q-1}‖` when the remaining tail has norm ≤ 1.
This is the `i ≥ 1` step in the proof of Corollaries 1–3. -/
theorem norm_defect_succ_le (P E : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ)
    (hP : ∀ i, ‖P i‖ ≤ 1) (hE : ∀ i, ‖E i‖ ≤ 1) (hPinit : ‖Pinit‖ ≤ 1)
    (q : ℕ) {b : ℝ}
    (hleak : ‖(1 - P (q + 1)) * E (q + 1) * P q‖ ≤ b) :
    ‖(1 - P (q + 1)) * E (q + 1) * (projWordProd P E (q + 1) * Pinit)‖ ≤ b := by
  have htail : ‖projWordProd P E q * Pinit‖ ≤ 1 :=
    norm_projWordProd_mul_le_one P E Pinit hP hE hPinit q
  have hEt : ‖E q * (projWordProd P E q * Pinit)‖ ≤ 1 := by
    calc ‖E q * (projWordProd P E q * Pinit)‖
        ≤ ‖E q‖ * ‖projWordProd P E q * Pinit‖ := norm_mul_le _ _
      _ ≤ 1 * 1 := by
            refine mul_le_mul (hE q) htail (norm_nonneg _) (by norm_num)
      _ = 1 := by norm_num
  have hassoc : (1 - P (q + 1)) * E (q + 1) * (projWordProd P E (q + 1) * Pinit) =
      ((1 - P (q + 1)) * E (q + 1) * P q) *
        (E q * (projWordProd P E q * Pinit)) := by
    simp only [projWordProd]
    noncomm_ring
  rw [hassoc]
  calc ‖((1 - P (q + 1)) * E (q + 1) * P q) *
        (E q * (projWordProd P E q * Pinit))‖
      ≤ ‖(1 - P (q + 1)) * E (q + 1) * P q‖ *
          ‖E q * (projWordProd P E q * Pinit)‖ := norm_mul_le _ _
    _ ≤ b * 1 := by
          refine mul_le_mul hleak hEt (norm_nonneg _) (by
            have := hleak
            linarith [norm_nonneg ((1 - P (q + 1)) * E (q + 1) * P q)])
    _ = b := mul_one _

/-- Norm bound for the telescoping sum: if every one-step defect is bounded by `b i`,
then `‖W Π - W^Λ Π‖ ≤ ∑_{i<q} b i`. -/
theorem norm_tel_le (P E : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ) (b : ℕ → ℝ)
    (hE : ∀ i, ‖E i‖ ≤ 1)
    (hb : ∀ i, ‖(1 - P i) * E i * (projWordProd P E i * Pinit)‖ ≤ b i) :
    ∀ q : ℕ, ‖tel P E Pinit q‖ ≤ ∑ i ∈ Finset.range q, b i := by
  intro q
  induction q with
  | zero => simp [tel]
  | succ q ih =>
      rw [tel]
      have hstep : ‖E q * tel P E Pinit q‖ ≤ ∑ i ∈ Finset.range q, b i := by
        calc ‖E q * tel P E Pinit q‖ ≤ ‖E q‖ * ‖tel P E Pinit q‖ := norm_mul_le _ _
          _ ≤ 1 * (∑ i ∈ Finset.range q, b i) := by
                refine mul_le_mul (hE q) ih (norm_nonneg _) (by norm_num)
          _ = ∑ i ∈ Finset.range q, b i := one_mul _
      calc ‖E q * tel P E Pinit q +
            (1 - P q) * E q * (projWordProd P E q * Pinit)‖
          ≤ ‖E q * tel P E Pinit q‖ +
              ‖(1 - P q) * E q * (projWordProd P E q * Pinit)‖ := norm_add_le _ _
        _ ≤ (∑ i ∈ Finset.range q, b i) + b q := add_le_add hstep (hb q)
        _ = ∑ i ∈ Finset.range (q + 1), b i := by
              rw [Finset.sum_range_succ]

/-- Final norm bound in the shape of the paper's Corollaries 1–3:
`‖(W - W^Λ) Π‖ ≤ ∑_{i<q} b i`. -/
theorem norm_wordProd_sub_projWordProd_mul_le (P E : ℕ → Matrix n n ℂ)
    (Pinit : Matrix n n ℂ) (b : ℕ → ℝ) (hE : ∀ i, ‖E i‖ ≤ 1)
    (hb : ∀ i, ‖(1 - P i) * E i * (projWordProd P E i * Pinit)‖ ≤ b i) (q : ℕ) :
    ‖(wordProd E q - projWordProd P E q) * Pinit‖ ≤ ∑ i ∈ Finset.range q, b i := by
  have htel := wordProd_mul_sub_projWordProd_mul P E Pinit q
  calc ‖(wordProd E q - projWordProd P E q) * Pinit‖
      = ‖wordProd E q * Pinit - projWordProd P E q * Pinit‖ := by rw [sub_mul]
    _ = ‖tel P E Pinit q‖ := by rw [htel]
    _ ≤ ∑ i ∈ Finset.range q, b i := norm_tel_le P E Pinit b hE hb q

/-- The projected product is the ordered product of the combined factors `P_i E_i`. -/
theorem wordProd_mul_eq_projWordProd (P E : ℕ → Matrix n n ℂ) :
    ∀ q : ℕ, wordProd (fun i => P i * E i) q = projWordProd P E q := by
  intro q
  induction q with
  | zero => simp [wordProd, projWordProd]
  | succ q ih => simp [wordProd, projWordProd, ih]

/-- A product of contractions times the initial projector has norm at most one. -/
theorem norm_wordProd_mul_le_one (E : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ)
    (hE : ∀ i, ‖E i‖ ≤ 1) (hinit : ‖Pinit‖ ≤ 1) :
    ∀ q : ℕ, ‖wordProd E q * Pinit‖ ≤ 1 := by
  intro q
  induction q with
  | zero => simpa [wordProd] using hinit
  | succ q ih =>
      have hassoc : wordProd E (q + 1) * Pinit = E q * (wordProd E q * Pinit) := by
        simp only [wordProd]
        noncomm_ring
      rw [hassoc]
      calc ‖E q * (wordProd E q * Pinit)‖ ≤ ‖E q‖ * ‖wordProd E q * Pinit‖ :=
            norm_mul_le _ _
        _ ≤ 1 * 1 := mul_le_mul (hE q) ih (norm_nonneg _) (by norm_num)
        _ = 1 := one_mul 1

/-- Range-restricted version of `norm_tel_le`: the one-step bounds are only required for
the indices that actually occur in the sum. -/
theorem norm_tel_le_range (P E : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ) (b : ℕ → ℝ)
    (hE : ∀ i, ‖E i‖ ≤ 1) (q : ℕ)
    (hb : ∀ i, i < q → ‖(1 - P i) * E i * (projWordProd P E i * Pinit)‖ ≤ b i) :
    ‖tel P E Pinit q‖ ≤ ∑ i ∈ Finset.range q, b i := by
  induction q with
  | zero => simp [tel]
  | succ q ih =>
      have hbq : ‖(1 - P q) * E q * (projWordProd P E q * Pinit)‖ ≤ b q :=
        hb q (Nat.lt_succ_self q)
      have ih' : ‖tel P E Pinit q‖ ≤ ∑ i ∈ Finset.range q, b i :=
        ih (fun i hi => hb i (Nat.lt_trans hi (Nat.lt_succ_self q)))
      rw [tel]
      have hstep : ‖E q * tel P E Pinit q‖ ≤ ∑ i ∈ Finset.range q, b i := by
        calc ‖E q * tel P E Pinit q‖ ≤ ‖E q‖ * ‖tel P E Pinit q‖ := norm_mul_le _ _
          _ ≤ 1 * (∑ i ∈ Finset.range q, b i) := by
                refine mul_le_mul (hE q) ih' (norm_nonneg _) (by norm_num)
          _ = ∑ i ∈ Finset.range q, b i := one_mul _
      calc ‖E q * tel P E Pinit q +
            (1 - P q) * E q * (projWordProd P E q * Pinit)‖
          ≤ ‖E q * tel P E Pinit q‖ +
              ‖(1 - P q) * E q * (projWordProd P E q * Pinit)‖ := norm_add_le _ _
        _ ≤ (∑ i ∈ Finset.range q, b i) + b q := add_le_add hstep hbq
        _ = ∑ i ∈ Finset.range (q + 1), b i := by
              rw [Finset.sum_range_succ]

/-- Range-restricted version of `norm_wordProd_sub_projWordProd_mul_le`. -/
theorem norm_wordProd_sub_projWordProd_mul_le_range (P E : ℕ → Matrix n n ℂ)
    (Pinit : Matrix n n ℂ) (b : ℕ → ℝ) (hE : ∀ i, ‖E i‖ ≤ 1) (q : ℕ)
    (hb : ∀ i, i < q → ‖(1 - P i) * E i * (projWordProd P E i * Pinit)‖ ≤ b i) :
    ‖(wordProd E q - projWordProd P E q) * Pinit‖ ≤ ∑ i ∈ Finset.range q, b i := by
  have htel := wordProd_mul_sub_projWordProd_mul P E Pinit q
  calc ‖(wordProd E q - projWordProd P E q) * Pinit‖
      = ‖wordProd E q * Pinit - projWordProd P E q * Pinit‖ := by rw [sub_mul]
    _ = ‖tel P E Pinit q‖ := by rw [htel]
    _ ≤ ∑ i ∈ Finset.range q, b i := norm_tel_le_range P E Pinit b hE q hb

/-! ## Telescoping between two products (used for the effective vs. original comparison) -/

/-- Telescoping accumulator for the difference of two ordered products:
`wordProd F - wordProd G` equals the sum of the defects `(F_j - G_j)` conjugated by the
surrounding factors. This formalises the expansion behind Eqs. (46) and (52). -/
def telDiff (F G : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ) : ℕ → Matrix n n ℂ
  | 0 => 0
  | q + 1 => F q * telDiff F G Pinit q + (F q - G q) * (wordProd G q * Pinit)

/-- Difference identity for ordered products (paper Eqs. (46) and (52) in telescoping
form). -/
theorem wordProd_sub_wordProd_mul (F G : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ) :
    ∀ q : ℕ, wordProd F q * Pinit - wordProd G q * Pinit = telDiff F G Pinit q := by
  intro q
  induction q with
  | zero => simp [wordProd, telDiff]
  | succ q ih =>
      rw [wordProd, wordProd, telDiff, ← ih]
      noncomm_ring

/-- Norm bound for the difference telescope: if each one-step defect
`(F_j - G_j) (G_{j-1}⋯G_0 Π)` is bounded by `b j`, the whole difference is bounded by
`∑_{j<q} b j`. -/
theorem norm_telDiff_le_range (F G : ℕ → Matrix n n ℂ) (Pinit : Matrix n n ℂ) (b : ℕ → ℝ)
    (hF : ∀ i, ‖F i‖ ≤ 1) (q : ℕ)
    (hb : ∀ i, i < q → ‖(F i - G i) * (wordProd G i * Pinit)‖ ≤ b i) :
    ‖telDiff F G Pinit q‖ ≤ ∑ i ∈ Finset.range q, b i := by
  induction q with
  | zero => simp [telDiff]
  | succ q ih =>
      have ih' : ‖telDiff F G Pinit q‖ ≤ ∑ i ∈ Finset.range q, b i :=
        ih (fun i hi => hb i (Nat.lt_trans hi (Nat.lt_succ_self q)))
      have hbq : ‖(F q - G q) * (wordProd G q * Pinit)‖ ≤ b q :=
        hb q (Nat.lt_succ_self q)
      rw [telDiff]
      calc ‖F q * telDiff F G Pinit q + (F q - G q) * (wordProd G q * Pinit)‖
          ≤ ‖F q * telDiff F G Pinit q‖ +
              ‖(F q - G q) * (wordProd G q * Pinit)‖ := norm_add_le _ _
        _ ≤ (∑ i ∈ Finset.range q, b i) + b q := by
              refine add_le_add ?_ hbq
              calc ‖F q * telDiff F G Pinit q‖ ≤ ‖F q‖ * ‖telDiff F G Pinit q‖ :=
                    norm_mul_le _ _
                _ ≤ 1 * (∑ i ∈ Finset.range q, b i) := by
                      refine mul_le_mul (hF q) ih' (norm_nonneg _) (by norm_num)
                _ = ∑ i ∈ Finset.range q, b i := one_mul _
        _ = ∑ i ∈ Finset.range (q + 1), b i := by
              rw [Finset.sum_range_succ]

/-! ## Lightweight locality bookkeeping -/

/-- Quantitative locality data for a `k`-local Hamiltonian of constant degree `d`, with
term strength `J` and at most `M` local terms per group (Supplementary Information,
first paragraph). These are exactly the parameters entering the constants
`λ = 1/(2Jdk)`, `α = eJ` of Lemma 1 (Eq. (14)) and Lemma 2 (Eq. (25)). The structural
"k-local / constant degree" content is what Ref. [37, Theorem 2.1] uses; it is recorded
here as data and consumed by the (documented) `sorry` statements of Lemma 1 and Lemma 2. -/
structure LocalHamScale where
  k : ℕ
  d : ℕ
  J : ℝ
  M : ℝ
  hk : 0 < k
  hd : 0 < d
  hJ : 0 < J
  hM : 0 ≤ M

namespace LocalHamScale

/-- The paper's decay rate `λ = 1/(2Jdk)`. -/
def lam (S : LocalHamScale) : ℝ := 1 / (2 * S.J * S.d * S.k)

/-- The paper's rate `α = eJ`. -/
def alpha (S : LocalHamScale) : ℝ := Real.exp 1 * S.J

/-- Lam pos: the paper model identity or bound. -/
theorem lam_pos (S : LocalHamScale) : 0 < S.lam := by
  have hk : (0 : ℝ) < (S.k : ℝ) := by exact_mod_cast S.hk
  have hd : (0 : ℝ) < (S.d : ℝ) := by exact_mod_cast S.hd
  unfold lam
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hden : 0 < 2 * S.J * (S.d : ℝ) * (S.k : ℝ) :=
    mul_pos (mul_pos (mul_pos h2 S.hJ) hd) hk
  exact one_div_pos.mpr hden

/-- Alpha pos: the paper model identity or bound. -/
theorem alpha_pos (S : LocalHamScale) : 0 < S.alpha := by
  unfold alpha
  exact mul_pos (Real.exp_pos 1) S.hJ

/-- Alpha nonneg: the paper model identity or bound. -/
theorem alpha_nonneg (S : LocalHamScale) : 0 ≤ S.alpha := S.alpha_pos.le

end LocalHamScale

/-- A term is a local term of the given scale if its operator norm is at most `J M`
(Paper: "the strength of each local interaction term is bounded by `J > 0`, hence
`‖H_l‖ ≤ JM`"). -/
def IsLocalTerm (S : LocalHamScale) (A : Matrix n n ℂ) : Prop := ‖A‖ ≤ S.J * S.M

/-- A `k`-local Hamiltonian of constant degree, packaged with its local terms, the
locality scale, the number `N` of spins and the bound `M ≤ dN` (Supplementary
Information, first paragraph). The projectors `Π_{≤Λ}` are taken with respect to `H`,
as in the paper ("the operators Π≤Λ ... are the projectors into the subspaces spanned
by the eigenstates of H"). -/
structure LocalHam (n : Type*) [Fintype n] [DecidableEq n] where
  scale : LocalHamScale
  L : ℕ
  hL : 0 < L
  term : Fin L → Matrix n n ℂ
  H : HermitianMat n ℂ
  term_herm : ∀ l, (term l).IsHermitian
  term_nonneg : ∀ l, (term l).PosSemidef
  term_bound : ∀ l, ‖term l‖ ≤ scale.J * scale.M
  H_eq : H.mat = ∑ l : Fin L, term l
  N : ℕ
  hMN : scale.M ≤ (scale.d : ℝ) * (N : ℝ)

end Qatlib.Papers.LowEnergyHam20.MainResults.LowEnergyModel
