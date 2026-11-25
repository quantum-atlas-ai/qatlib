/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.HammingDist09.MainResults.Measurement

@[expose] public section

/-!
# Optimal square-root measurement under the equal-diagonal criterion

Proposition 6.1 of arXiv:0912.0583v1 invokes the square-root measurement
criterion. The dual upper bound uses a positive Gram square root whose
diagonal is constant. A signed square root can violate the proposed bound
even for two orthogonal states.
-/

set_option autoImplicit false

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder
open Qatlib.Papers.HammingDist09.MainResults
open Qatlib.Papers.HammingDist09.MainResults.Measurement

namespace Qatlib.Papers.HammingDist09.MainResults

private theorem paperPSD_iff {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) :
    IsPSD A ↔ A.PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]
  unfold IsPSD
  constructor
  · rintro ⟨hh, hq⟩
    refine ⟨hh, fun v => ?_⟩
    have hc : star (star v ⬝ᵥ (A *ᵥ v)) = star v ⬝ᵥ (A *ᵥ v) := by
      rw [← mul_rankOne_trace, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
        (rankOne_isHermitian v).eq, hh, Matrix.trace_mul_comm]
    have him := Complex.conj_eq_iff_im.mp hc
    have hre := hq v
    rw [← dot_mulVec_eq_sum] at hre
    exact RCLike.le_iff_re_im.mpr ⟨by simpa using hre, by simpa using him.symm⟩
  · rintro ⟨hh, hq⟩
    refine ⟨hh, fun v => ?_⟩
    rw [← dot_mulVec_eq_sum]
    simpa using (RCLike.le_iff_re_im.mp (hq v)).1

/-- For a positive Gram square root with constant positive diagonal, its squared
diagonal value bounds the success of every measurement. -/
theorem squareRoot_measurement_bound {N M : ℕ}
    (B : Matrix (Fin N) (Fin M) ℂ) (S T : Matrix (Fin M) (Fin M) ℂ)
    (hS : S.PosSemidef) (hT : T.IsHermitian)
    (hGram : S * S = Bᴴ * B) (hST : S * T = 1) (hTS : T * S = 1)
    (d : ℝ) (hd : 0 < d) (hdiag : ∀ i, S i i = (d : ℂ))
    (X : Fin M → Matrix (Fin N) (Fin N) ℂ) (hX : IsMeasurement X) :
    measurementSuccess B X ≤ (1 / (M : ℝ)) * ∑ i, ((S i i) ^ 2).re := by
  have hr : (CFC.sqrt S).IsHermitian := (IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg S)).isHermitian
  let R := CFC.sqrt S
  have hRh : Rᴴ = R := hr.eq
  have hR : Rᴴ * R = S := by rw [hRh]; exact CFC.sqrt_mul_sqrt_self S hS.nonneg
  let U := B * T
  have hU : Uᴴ * U = 1 := by
    dsimp [U]
    rw [Matrix.conjTranspose_mul, hT.eq]
    calc
      T * Bᴴ * (B * T) = T * (Bᴴ * B) * T := by simp only [Matrix.mul_assoc]
      _ = T * (S * S) * T := by rw [hGram]
      _ = (T * S) * (S * T) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hTS, hST, Matrix.one_mul]
  let q : ℂ := (Real.sqrt d : ℂ)
  have hq0 : q ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hd).ne'
  have hqstar : star q = q := by simp [q]
  have hqinv : star q⁻¹ = q⁻¹ := by simp [q]
  have hq2 : q * q = (d : ℂ) := by
    rw [← pow_two]
    dsimp [q]
    rw [← Complex.ofReal_pow, Real.sq_sqrt hd.le]
  let V := q • (U * R)
  let c (i : Fin M) : Fin M → ℂ := q⁻¹ • fun j => R j i
  have hc (i : Fin M) : star (c i) ⬝ᵥ c i = 1 := by
    have hstar : star (c i) = q⁻¹ • star (fun j => R j i) := by
      funext j
      simp only [c, Pi.star_apply, Pi.smul_apply, smul_eq_mul, star_mul', hqinv]
    rw [hstar]
    unfold c
    rw [smul_dotProduct, dotProduct_smul, col_inner_eq R R S hR, hdiag, ← hq2]
    simp only [smul_eq_mul]
    field_simp
  have hVcol (i : Fin M) : V *ᵥ c i = fun j => B j i := by
    have hprod : (U * R) * R = B := by
      rw [Matrix.mul_assoc, show R * R = S by simpa only [hRh] using hR]
      dsimp [U]
      rw [Matrix.mul_assoc, hTS, Matrix.mul_one]
    unfold V c
    rw [Matrix.smul_mulVec, Matrix.mulVec_smul, smul_smul, mul_inv_cancel₀ hq0, one_smul]
    ext j
    rw [← hprod, Matrix.mul_apply]
    rfl
  have hVV : Vᴴ * V = (d : ℂ) • S := by
    unfold V
    rw [Matrix.conjTranspose_smul, hqstar, Matrix.smul_mul, Matrix.mul_smul,
      smul_smul, hq2, Matrix.conjTranspose_mul]
    congr 1
    calc
      Rᴴ * Uᴴ * (U * R) = Rᴴ * (Uᴴ * U) * R := by simp only [Matrix.mul_assoc]
      _ = S := by rw [hU, Matrix.mul_one, hR]
  have hdual (i : Fin M) : (V * Vᴴ - rankOne (fun j => B j i)).PosSemidef := by
    rw [← hVcol i, rankOne_isometry_mulVec]
    have h := (posSemidef_one_sub_rankOne (c i) (hc i)).mul_mul_conjTranspose_same V
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one] using h
  have hbound (i : Fin M) :
      (star (fun j => B j i) ⬝ᵥ (X i *ᵥ fun j => B j i)).re ≤
        ((X i) * (V * Vᴴ)).trace.re := by
    have h := trace_mul_re_nonneg ((paperPSD_iff _).mp (hX.1 i)) (hdual i)
    rw [Matrix.mul_sub, Matrix.trace_sub, mul_rankOne_trace, Complex.sub_re] at h
    linarith
  have hsum : (∑ i, ((X i) * (V * Vᴴ)).trace.re) = (∑ i, ((S i i) ^ 2).re) := by
    rw [← Complex.re_sum, ← Matrix.trace_sum, ← Finset.sum_mul, hX.2, Matrix.one_mul,
      Matrix.trace_mul_comm, hVV, Matrix.trace_smul, Matrix.trace, smul_eq_mul, Finset.mul_sum,
      Complex.re_sum]
    apply Finset.sum_congr rfl
    intro i _
    simp [Matrix.diag_apply, hdiag, pow_two]
  rw [measurementSuccess_eq_sum_dot, ← hsum]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbound i) (by positivity)

/-- Completing the square-root effects by assigning the residual to one outcome gives
a measurement that attains the upper bound. -/
theorem squareRoot_measurement_optimal {N M : ℕ} (hM : 0 < M)
    (B : Matrix (Fin N) (Fin M) ℂ) (S T : Matrix (Fin M) (Fin M) ℂ)
    (hS : S.PosSemidef) (hT : T.IsHermitian)
    (hGram : S * S = Bᴴ * B) (hST : S * T = 1) (hTS : T * S = 1)
    (d : ℝ) (hd : 0 < d) (hdiag : ∀ i, S i i = (d : ℂ)) :
    ∃ X : Fin M → Matrix (Fin N) (Fin N) ℂ,
      IsMeasurement X ∧
      measurementSuccess B X = (1 / (M : ℝ)) * ∑ i, ((S i i) ^ 2).re ∧
      ∀ Y, IsMeasurement Y → measurementSuccess B Y ≤ measurementSuccess B X := by
  let first : Fin M := ⟨0, hM⟩
  let A (i : Fin M) := rankOne (fun j => (B * T) j i)
  let residual : Matrix (Fin N) (Fin N) ℂ := 1 - ∑ i, A i
  let X (i : Fin M) := A i + if i = first then residual else 0
  obtain ⟨hA, hR, _, _⟩ := prop_6_1 B S T hS.1 hT hGram hST hTS
  have hX : IsMeasurement X := by
    constructor
    · intro i
      apply (paperPSD_iff _).mpr
      by_cases hi : i = first
      · simpa only [X, ite_eq_left hi] using (hA i).add hR
      · simpa only [X, ite_eq_right hi, add_zero] using hA i
    · simp only [X, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true, residual]
      abel
  have hsuccessA := prop_6_1_measurementSuccess B S T hS.1 hT hGram hST hTS
  have hmono : measurementSuccess B A ≤ measurementSuccess B X := by
    rw [measurementSuccess_eq_sum_dot, measurementSuccess_eq_sum_dot]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro i _
    simp only [← mul_rankOne_trace, X, Matrix.add_mul, Matrix.trace_add, Complex.add_re]
    have hzero : (if i = first then residual else 0).PosSemidef := by
      split
      · exact hR
      · exact Matrix.PosSemidef.zero
    exact le_add_of_nonneg_right (trace_mul_re_nonneg hzero (rankOne_posSemidef _))
  rw [show measurementSuccess B A =
    (1 / (M : ℝ)) * ∑ i, ((S i i) ^ 2).re from hsuccessA] at hmono
  have hbound := squareRoot_measurement_bound B S T hS hT hGram hST hTS d hd hdiag
  have hEq := le_antisymm (hbound X hX) hmono
  refine ⟨X, hX, hEq, fun Y hY => ?_⟩
  rw [hEq]
  exact hbound Y hY

/-- A Hermitian signed square root with zero diagonal can square to the Gram identity.
The two orthogonal states then refute the unqualified squared-diagonal bound. -/
theorem signed_root_counterexample :
    ∃ (B S : Matrix (Fin 2) (Fin 2) ℂ) (X : Fin 2 → Matrix (Fin 2) (Fin 2) ℂ),
      S.IsHermitian ∧ S * S = Bᴴ * B ∧ S * S = 1 ∧ IsMeasurement X ∧
        (1 / (2 : ℝ)) * (∑ i : Fin 2, ((S i i) ^ 2).re) < measurementSuccess B X := by
  let I : Matrix (Fin 2) (Fin 2) ℂ := 1
  let S : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]
  let X := fun i : Fin 2 => rankOne (fun j => I j i)
  have hI : I.IsHermitian := Matrix.isHermitian_one
  have hS : S.IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [S, Matrix.conjTranspose_apply]
  have hSS : S * S = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [S, Matrix.mul_apply, Fin.sum_univ_two]
  have hX : IsMeasurement X := by
    constructor
    · intro i
      exact (paperPSD_iff _).mpr (rankOne_posSemidef _)
    · rw [show (∑ i, X i) = I * Iᴴ from sum_rankOne_eq I]
      simp [I]
  have hsucc : measurementSuccess I X = 1 := by
    have h := prop_6_1_measurementSuccess I I I hI hI
      (by simp [I]) (by simp [I]) (by simp [I])
    norm_num [I, X, Fin.sum_univ_two] at h ⊢
    exact h
  refine ⟨I, S, X, hS, by simp [I, hSS], hSS, hX, ?_⟩
  rw [hsucc]
  norm_num [S, Fin.sum_univ_two]

end Qatlib.Papers.HammingDist09.MainResults
