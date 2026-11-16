/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Foundations.PPTMatrix.OperatorCones.QubitBlocks
public import Qatlib.Foundations.PPTMatrix.OperatorCones.ForMathlib.PseudoInverse

@[expose] public section




/-!
# Equal diagonal blocks: reduction to unitaries

Towards Lemma 2 (Gurvits–Barnum): a positive operator `[[D, Y], [Yᴴ, D]]` with a qubit
reference is separable.

* `isSeparable_qubitBlocks_of_resolution`: if `D = ∑ Q_k` and `Y = ∑ c_k Q_k` with `Q_k ≥ 0` and
  `|c_k| ≤ 1`, then `[[D, Y], [Yᴴ, D]] = ∑ [[1, c_k], [c̄_k, 1]] ⊗ Q_k` is separable.
* `exists_unitary_dilation`: two matrices with the same Gram matrix are related by a unitary on
  a doubled space (Halmos dilation of the partial isometry `G₁ D⁺ G₀ᴴ`; no square roots needed).
* `isSeparable_qubitBlocks_of_posSemidef_of_resolution`: Lemma 2, assuming that every unitary on
  the doubled space has a positive resolution `1 = ∑ Q_k`, `U = ∑ c_k Q_k`.
-/

open Matrix
open scoped Kronecker ComplexOrder

namespace Qatlib.Foundations.PPTMatrix.OperatorCones

variable {n : Type*}

/-! ### The reference factor `[[1, c], [c̄, 1]]` -/

/-- Establishes `mul_star_eq_norm_sq`: `c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ)`, for the stated parameters. -/
theorem mul_star_eq_norm_sq (c : ℂ) : c * star c = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
  rw [← Complex.normSq_eq_norm_sq]
  apply Complex.ext <;> simp [Complex.normSq_apply]
  ring

/-- `[[1, c], [c̄, 1]]` is positive when `|c| ≤ 1`. -/
theorem posSemidef_two_by_two {c : ℂ} (hc : ‖c‖ ≤ 1) :
    (!![1, c; star c, 1] : Matrix (Fin 2) (Fin 2) ℂ).PosSemidef := by
  have h1 : (Matrix.vecMulVec ![c, 1] (star ![c, 1])).PosSemidef :=
    Matrix.posSemidef_vecMulVec_self_star _
  have hnn : (0 : ℝ) ≤ 1 - ‖c‖ ^ 2 := by nlinarith [norm_nonneg c]
  have h2 : (Matrix.diagonal ![((1 - ‖c‖ ^ 2 : ℝ) : ℂ), 0]).PosSemidef := by
    rw [Matrix.posSemidef_diagonal_iff]
    intro i
    fin_cases i
    · exact Complex.zero_le_real.mpr hnn
    · exact le_refl (0 : ℂ)
  have h3 : (!![1, c; star c, 1] : Matrix (Fin 2) (Fin 2) ℂ) =
      Matrix.vecMulVec ![c, 1] (star ![c, 1]) +
        Matrix.diagonal ![((1 - ‖c‖ ^ 2 : ℝ) : ℂ), 0] := by
    have hcc := mul_star_eq_norm_sq c
    ext i j
    fin_cases i <;> fin_cases j
    · show (1 : ℂ) = c * star c + ((1 - ‖c‖ ^ 2 : ℝ) : ℂ)
      rw [hcc]
      push_cast
      ring
    · show c = c * star (1 : ℂ) + 0
      simp
    · show star c = 1 * star c + 0
      simp
    · show (1 : ℂ) = 1 * star (1 : ℂ) + 0
      simp
  rw [h3]
  exact h1.add h2

/-! ### Separability from a positive resolution -/

/-- Establishes `two_by_two_kronecker`: `(!![1, c; star c, 1] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Q = qubitBlocks Q (c • Q) (star c • Q) Q`, for the stated parameters. -/
theorem two_by_two_kronecker (c : ℂ) (Q : Matrix n n ℂ) :
    (!![1, c; star c, 1] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Q = qubitBlocks Q (c • Q) (star c • Q) Q := by
  rw [kronecker_eq_qubitBlocks]
  have e00 : (!![1, c; star c, 1] : Matrix (Fin 2) (Fin 2) ℂ) 0 0 = 1 := rfl
  have e01 : (!![1, c; star c, 1] : Matrix (Fin 2) (Fin 2) ℂ) 0 1 = c := rfl
  have e10 : (!![1, c; star c, 1] : Matrix (Fin 2) (Fin 2) ℂ) 1 0 = star c := rfl
  have e11 : (!![1, c; star c, 1] : Matrix (Fin 2) (Fin 2) ℂ) 1 1 = 1 := rfl
  rw [e00, e01, e10, e11, one_smul]

/-- If `D = ∑ Q_k` and `Y = ∑ c_k Q_k` with `Q_k ≥ 0` and `|c_k| ≤ 1`, then
`[[D, Y], [Yᴴ, D]] = ∑ [[1, c_k], [c̄_k, 1]] ⊗ Q_k` is separable. -/
theorem isSeparable_qubitBlocks_of_resolution {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (Q : ι → Matrix n n ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (hQ : ∀ k, (Q k).PosSemidef) :
    IsSeparable
      (qubitBlocks (∑ k, Q k) (∑ k, c k • Q k) (∑ k, c k • Q k)ᴴ (∑ k, Q k)) := by
  have hH : (∑ k, c k • Q k)ᴴ = ∑ k, star (c k) • Q k := by
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.conjTranspose_smul, (hQ k).isHermitian.eq]
  have key : qubitBlocks (∑ k, Q k) (∑ k, c k • Q k) (∑ k, c k • Q k)ᴴ (∑ k, Q k) =
      ∑ k, (!![1, c k; star (c k), 1] : Matrix (Fin 2) (Fin 2) ℂ) ⊗ₖ Q k := by
    rw [hH, qubitBlocks_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [two_by_two_kronecker]
  rw [key]
  exact isSeparable_sum_kronecker _ _ (fun k => posSemidef_two_by_two (hc k)) hQ

/-- Establishes `isSeparable_qubitBlocks_of_resolution'`: `IsSeparable (qubitBlocks D Y Yᴴ D)`, for the stated parameters. -/
theorem isSeparable_qubitBlocks_of_resolution' {ι : Type*} [Fintype ι] {D Y : Matrix n n ℂ}
    (c : ι → ℂ) (Q : ι → Matrix n n ℂ) (hc : ∀ k, ‖c k‖ ≤ 1) (hQ : ∀ k, (Q k).PosSemidef)
    (hD : D = ∑ k, Q k) (hY : Y = ∑ k, c k • Q k) :
    IsSeparable (qubitBlocks D Y Yᴴ D) := by
  subst hD hY
  exact isSeparable_qubitBlocks_of_resolution c Q hc hQ

/-! ### Unitary dilation of two Gram factors -/

/-- Establishes `sandwich`: `X * P * Yᴴ * (Y' * P * Zᴴ) = X * P * Zᴴ`, for the stated parameters. -/
private theorem sandwich {r : Type*} [Fintype r] [Fintype n] (X Y Y' Z : Matrix r n ℂ)
    (P D : Matrix n n ℂ) (hY : Yᴴ * Y' = D) (hPDP : P * D * P = P) :
    X * P * Yᴴ * (Y' * P * Zᴴ) = X * P * Zᴴ := by
  calc X * P * Yᴴ * (Y' * P * Zᴴ) = X * (P * (Yᴴ * Y') * P) * Zᴴ := by
        simp only [Matrix.mul_assoc]
    _ = X * P * Zᴴ := by rw [hY, hPDP]

/-- Establishes `fromBlocks_eq_one`: `Matrix.fromBlocks X Y Z W = 1`, for the stated parameters. -/
private theorem fromBlocks_eq_one {l m : Type*} [DecidableEq l] [DecidableEq m]
    (X : Matrix l l ℂ) (Y : Matrix l m ℂ) (Z : Matrix m l ℂ) (W : Matrix m m ℂ)
    (hX : X = 1) (hY : Y = 0) (hZ : Z = 0) (hW : W = 1) : Matrix.fromBlocks X Y Z W = 1 := by
  subst hX hY hZ hW
  exact Matrix.fromBlocks_one

/-- Two matrices with the same Gram matrix are related by a unitary on a doubled space:
there are a unitary `U` and a matrix `G` with `GᴴG = G₀ᴴG₀` and `GᴴUG = G₀ᴴG₁`. -/
theorem exists_unitary_dilation {r : Type*} [Fintype r] [DecidableEq r] [Fintype n]
    [DecidableEq n] (G₀ G₁ : Matrix r n ℂ) (h : G₀ᴴ * G₀ = G₁ᴴ * G₁) :
    ∃ (U : Matrix (r ⊕ r) (r ⊕ r) ℂ) (G : Matrix (r ⊕ r) n ℂ),
      Uᴴ * U = 1 ∧ Gᴴ * G = G₀ᴴ * G₀ ∧ Gᴴ * U * G = G₀ᴴ * G₁ := by
  obtain ⟨D, hD⟩ : ∃ D, D = G₀ᴴ * G₀ := ⟨_, rfl⟩
  have hDh : D.IsHermitian := by
    rw [hD]
    exact Matrix.isHermitian_conjTranspose_mul_self G₀
  have h₀ : G₀ᴴ * G₀ = D := hD.symm
  have h₁ : G₁ᴴ * G₁ = D := by rw [← h, h₀]
  obtain ⟨P, hP⟩ : ∃ P, P = pinv D := ⟨_, rfl⟩
  have hPh : Pᴴ = P := by
    rw [hP]
    exact (isHermitian_pinv hDh).eq
  have hPDP : P * D * P = P := by
    rw [hP]
    exact pinv_mul_pinv hDh
  have hG₀ : G₀ * (P * D) = G₀ := by
    rw [hP, hD]
    exact gram_mul_pinv_mul G₀
  obtain ⟨T, hT⟩ : ∃ T, T = G₁ * P * G₀ᴴ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E, E = G₀ * P * G₀ᴴ := ⟨_, rfl⟩
  obtain ⟨F, hF⟩ : ∃ F, F = G₁ * P * G₁ᴴ := ⟨_, rfl⟩
  have hTh : Tᴴ = G₀ * P * G₁ᴴ := by
    rw [hT, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPh,
      ← Matrix.mul_assoc]
  have hEh : Eᴴ = E := by
    rw [hE, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPh,
      ← Matrix.mul_assoc]
  have hFh : Fᴴ = F := by
    rw [hF, conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hPh,
      ← Matrix.mul_assoc]
  have hTT : Tᴴ * T = E := by
    rw [hTh, hT, hE]
    exact sandwich G₀ G₁ G₁ G₀ P D h₁ hPDP
  have hTTh : T * Tᴴ = F := by
    rw [hTh, hT, hF]
    exact sandwich G₁ G₀ G₀ G₁ P D h₀ hPDP
  have hEE : E * E = E := by
    rw [hE]
    exact sandwich G₀ G₀ G₀ G₀ P D h₀ hPDP
  have hFF : F * F = F := by
    rw [hF]
    exact sandwich G₁ G₁ G₁ G₁ P D h₁ hPDP
  have hTF : Tᴴ * F = Tᴴ := by
    rw [hTh, hF]
    exact sandwich G₀ G₁ G₁ G₁ P D h₁ hPDP
  have hET : E * Tᴴ = Tᴴ := by
    rw [hTh, hE]
    exact sandwich G₀ G₀ G₀ G₁ P D h₀ hPDP
  have hFT : F * T = T := by
    rw [hT, hF]
    exact sandwich G₁ G₁ G₁ G₀ P D h₁ hPDP
  have hTE : T * E = T := by
    rw [hT, hE]
    exact sandwich G₁ G₀ G₀ G₀ P D h₀ hPDP
  have hTG : T * G₀ = G₁ := by
    have hG₁ : G₁ * (P * D) = G₁ := by
      rw [hP, ← h₁]
      exact gram_mul_pinv_mul G₁
    calc T * G₀ = G₁ * (P * (G₀ᴴ * G₀)) := by rw [hT]; simp only [Matrix.mul_assoc]
      _ = G₁ := by rw [h₀, hG₁]
  have b11 : Tᴴ * T + (1 - E) * (1 - E) = 1 := by
    simp only [hTT, hEE, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one]
    abel
  have b12 : Tᴴ * (1 - F) + (1 - E) * (-Tᴴ) = 0 := by
    simp only [hTF, hET, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.mul_neg]
    abel
  have b21 : (1 - F) * T + (-T) * (1 - E) = 0 := by
    simp only [hFT, hTE, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.neg_mul]
    abel
  have b22 : (1 - F) * (1 - F) + (-T) * (-Tᴴ) = 1 := by
    simp only [hTTh, hFF, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.neg_mul, Matrix.mul_neg, neg_neg]
    abel
  refine ⟨Matrix.fromBlocks T (1 - F) (1 - E) (-Tᴴ), Matrix.fromRows G₀ 0, ?_, ?_, ?_⟩
  · rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp only [conjTranspose_sub, conjTranspose_one, conjTranspose_neg,
      conjTranspose_conjTranspose, hEh, hFh]
    exact fromBlocks_eq_one _ _ _ _ b11 b12 b21 b22
  · rw [Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
    simp
  · rw [Matrix.mul_assoc, Matrix.fromBlocks_mul_fromRows,
      Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose, Matrix.fromCols_mul_fromRows]
    simp only [Matrix.mul_zero, add_zero, conjTranspose_zero, Matrix.zero_mul, hTG]

/-! ### Lemma 2 from a positive resolution of unitaries -/

/-- Lemma 2 (Gurvits–Barnum), assuming every unitary on the doubled space has a positive
resolution `1 = ∑ Q_k`, `U = ∑ c_k Q_k` with `|c_k| ≤ 1`. -/
theorem isSeparable_qubitBlocks_of_posSemidef_of_resolution [Fintype n] [DecidableEq n]
    (hres : ∀ U : Matrix ((Fin 2 × n) ⊕ (Fin 2 × n)) ((Fin 2 × n) ⊕ (Fin 2 × n)) ℂ,
      Uᴴ * U = 1 → ∃ (N : ℕ) (c : Fin N → ℂ)
        (Q : Fin N → Matrix ((Fin 2 × n) ⊕ (Fin 2 × n)) ((Fin 2 × n) ⊕ (Fin 2 × n)) ℂ),
        (∀ k, ‖c k‖ ≤ 1) ∧ (∀ k, (Q k).PosSemidef) ∧ ∑ k, Q k = 1 ∧ ∑ k, c k • Q k = U)
    (D Y : Matrix n n ℂ) (h : (qubitBlocks D Y Yᴴ D).PosSemidef) :
    IsSeparable (qubitBlocks D Y Yᴴ D) := by
  obtain ⟨R, hR⟩ : ∃ R, R = psqrt (qubitBlocks D Y Yᴴ D) := ⟨_, rfl⟩
  have hRR : Rᴴ * R = qubitBlocks D Y Yᴴ D := by
    rw [hR]
    exact conjTranspose_psqrt_mul_psqrt h
  have h00 : (R.submatrix id (fun a : n => ((0 : Fin 2), a)))ᴴ *
      R.submatrix id (fun a : n => ((0 : Fin 2), a)) = D := by
    rw [conjTranspose_submatrix_mul_submatrix, hRR]
    rfl
  have h11 : (R.submatrix id (fun a : n => ((1 : Fin 2), a)))ᴴ *
      R.submatrix id (fun a : n => ((1 : Fin 2), a)) = D := by
    rw [conjTranspose_submatrix_mul_submatrix, hRR]
    rfl
  have h01 : (R.submatrix id (fun a : n => ((0 : Fin 2), a)))ᴴ *
      R.submatrix id (fun a : n => ((1 : Fin 2), a)) = Y := by
    rw [conjTranspose_submatrix_mul_submatrix, hRR]
    rfl
  obtain ⟨U, G, hU, hGG, hGUG⟩ := exists_unitary_dilation _ _ (h00.trans h11.symm)
  obtain ⟨N, c, Q, hc, hQ, hQ1, hcQ⟩ := hres U hU
  refine isSeparable_qubitBlocks_of_resolution' c (fun k => Gᴴ * Q k * G) hc
    (fun k => (hQ k).conjTranspose_mul_mul_same G) ?_ ?_
  · calc D = Gᴴ * G := by rw [hGG, h00]
      _ = Gᴴ * (∑ k, Q k) * G := by rw [hQ1, Matrix.mul_one]
      _ = ∑ k, Gᴴ * Q k * G := by rw [Matrix.mul_sum, Matrix.sum_mul]
  · calc Y = Gᴴ * U * G := by rw [hGUG, h01]
      _ = Gᴴ * (∑ k, c k • Q k) * G := by rw [hcQ]
      _ = ∑ k, c k • (Gᴴ * Q k * G) := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Matrix.mul_smul, Matrix.smul_mul]

end Qatlib.Foundations.PPTMatrix.OperatorCones
