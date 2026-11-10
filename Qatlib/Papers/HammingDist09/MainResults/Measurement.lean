/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.HammingDist09.MainResults.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Complex.BigOperators
import Mathlib.Tactic
set_option warningAsError false

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace Qatlib.Papers.HammingDist09.MainResults.Measurement

noncomputable section

variable {N : ℕ}

def outer (v w : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ := fun a b => v a * star (w b)

def rankOne (v : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ := outer v v

lemma outer_eq_col_mul_row (v w : Fin N → ℂ) :
    outer v w = (Matrix.of (fun a (_ : Fin 1) => v a))
      * (Matrix.of (fun a (_ : Fin 1) => w a)).conjTranspose := by
  ext a b
  simp [outer, Matrix.mul_apply]

lemma rankOne_eq_col_mul_row (v : Fin N → ℂ) :
    rankOne v = (Matrix.of (fun a (_ : Fin 1) => v a))
      * (Matrix.of (fun a (_ : Fin 1) => v a)).conjTranspose :=
  outer_eq_col_mul_row v v

lemma rankOne_posSemidef (v : Fin N → ℂ) : (rankOne v).PosSemidef := by
  rw [rankOne_eq_col_mul_row]
  exact Matrix.posSemidef_self_mul_conjTranspose _

lemma rankOne_isHermitian (v : Fin N → ℂ) : (rankOne v).IsHermitian :=
  (rankOne_posSemidef v).1

lemma rankOne_trace (v : Fin N → ℂ) : (rankOne v).trace = star v ⬝ᵥ v := by
  rw [Matrix.trace, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  simp [rankOne, outer, Matrix.diag_apply, mul_comm]

lemma rankOne_mulVec_apply (v x : Fin N → ℂ) :
    rankOne v *ᵥ x = (star v ⬝ᵥ x) • v := by
  ext a
  simp only [rankOne, outer, Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro b _
  show v a * star (v b) * x b = star (v b) * x b * v a
  ring

lemma rankOne_mul_self (v : Fin N → ℂ) (hv : star v ⬝ᵥ v = 1) :
    rankOne v * rankOne v = rankOne v := by
  ext a b
  simp only [rankOne, outer, Matrix.mul_apply]
  have hv' : (∑ c, star (v c) * v c) = 1 := by
    rw [dotProduct] at hv
    exact hv
  calc ∑ c, v a * star (v c) * (v c * star (v b))
      = v a * (∑ c, star (v c) * v c) * star (v b) := by
        rw [Finset.mul_sum, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro c _
        ring
    _ = v a * 1 * star (v b) := by rw [hv']
    _ = v a * star (v b) := by ring

lemma posSemidef_of_isHermitian_idempotent {M : Matrix (Fin N) (Fin N) ℂ}
    (hH : M.IsHermitian) (hI : M * M = M) : M.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self M
  rwa [hH.eq, hI] at h

lemma posSemidef_one_sub_rankOne (v : Fin N → ℂ) (hv : star v ⬝ᵥ v = 1) :
    (1 - rankOne v).PosSemidef := by
  have hherm : (1 - rankOne v).IsHermitian := by
    rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_one]
    rw [(rankOne_isHermitian v).eq]
  refine posSemidef_of_isHermitian_idempotent hherm ?_
  have h1 : (1 - rankOne v) * (1 - rankOne v) = 1 - rankOne v := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
      rankOne_mul_self v hv]
    abel
  exact h1

lemma trace_mul_nonneg {A B : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hAeq : A = CFC.sqrt A * CFC.sqrt A := (CFC.sqrt_mul_sqrt_self A hA.nonneg).symm
  have hherm : (CFC.sqrt A)ᴴ = CFC.sqrt A := by
    have h : IsSelfAdjoint (CFC.sqrt A) := IsSelfAdjoint.of_nonneg (CFC.sqrt_nonneg A)
    exact IsSelfAdjoint.isHermitian h |>.eq
  have hpsd : (CFC.sqrt A * B * CFC.sqrt A).PosSemidef := by
    have h := hB.conjTranspose_mul_mul_same (CFC.sqrt A)
    rwa [hherm] at h
  have htr : (A * B).trace = (CFC.sqrt A * B * CFC.sqrt A).trace := by
    calc (A * B).trace
        = ((CFC.sqrt A * CFC.sqrt A) * B).trace := by
            conv_lhs => rw [hAeq]
      _ = (CFC.sqrt A * (CFC.sqrt A * B)).trace := by rw [Matrix.mul_assoc]
      _ = ((CFC.sqrt A * B) * CFC.sqrt A).trace := by rw [Matrix.trace_mul_comm]
      _ = (CFC.sqrt A * B * CFC.sqrt A).trace := rfl
  rw [htr]
  exact hpsd.trace_nonneg

lemma trace_mul_re_nonneg {A B : Matrix (Fin N) (Fin N) ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace.re := by
  have h := (RCLike.le_iff_re_im.mp (trace_mul_nonneg hA hB)).1
  simpa using h

lemma mul_rankOne_trace (X : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    (X * rankOne v).trace = star v ⬝ᵥ (X *ᵥ v) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rankOne, outer,
    Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

section Isometry

variable {k : ℕ}

lemma rankOne_isometry_mulVec (V : Matrix (Fin N) (Fin k) ℂ) (c : Fin k → ℂ) :
    rankOne (V *ᵥ c) = V * rankOne c * Vᴴ := by
  ext a b
  simp only [rankOne, outer, Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.conjTranspose_apply, star_sum, star_mul, Finset.mul_sum, Finset.sum_mul,
    mul_assoc]

lemma isometry_proj_mul_self (V : Matrix (Fin N) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    (V * Vᴴ) * (V * Vᴴ) = V * Vᴴ := by
  calc (V * Vᴴ) * (V * Vᴴ) = V * (Vᴴ * (V * Vᴴ)) := Matrix.mul_assoc V Vᴴ (V * Vᴴ)
    _ = V * ((Vᴴ * V) * Vᴴ) := by rw [Matrix.mul_assoc Vᴴ V Vᴴ]
    _ = V * Vᴴ := by rw [hV, Matrix.one_mul]

lemma isometry_proj_trace (V : Matrix (Fin N) (Fin k) ℂ) (hV : Vᴴ * V = 1) :
    (V * Vᴴ).trace = (k : ℂ) := by
  rw [Matrix.trace_mul_comm, hV]
  simp

theorem lemma_6_2 {n : ℕ} (hn : 0 < n) (V : Matrix (Fin N) (Fin k) ℂ)
    (hV : Vᴴ * V = 1) (c : Fin n → Fin k → ℂ) (hc : ∀ i, star (c i) ⬝ᵥ c i = 1)
    (X : Fin n → Matrix (Fin N) (Fin N) ℂ) (hX : ∀ i, (X i).PosSemidef)
    (hsum : ∑ i, X i = 1) :
    (1 / (n : ℝ)) * ∑ i : Fin n,
        (star (V *ᵥ c i) ⬝ᵥ ((X i) *ᵥ (V *ᵥ c i))).re ≤ (k : ℝ) / n := by
  classical
  have hDi : ∀ i : Fin n, ((V * Vᴴ) - rankOne (V *ᵥ c i)).PosSemidef := by
    intro i
    have hM : (1 - rankOne (c i)).PosSemidef := posSemidef_one_sub_rankOne (c i) (hc i)
    have h := hM.mul_mul_conjTranspose_same V
    have heq : V * Vᴴ - V * rankOne (c i) * Vᴴ = V * (1 - rankOne (c i)) * Vᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [rankOne_isometry_mulVec, heq]
    exact h
  have hineq : ∀ i : Fin n,
      (star (V *ᵥ c i) ⬝ᵥ ((X i) *ᵥ (V *ᵥ c i))).re ≤ ((X i) * (V * Vᴴ)).trace.re := by
    intro i
    have h0 : 0 ≤ ((X i) * ((V * Vᴴ) - rankOne (V *ᵥ c i))).trace.re :=
      trace_mul_re_nonneg (hX i) (hDi i)
    have hsplit : ((X i) * ((V * Vᴴ) - rankOne (V *ᵥ c i))).trace
        = (X i * (V * Vᴴ)).trace - (X i * rankOne (V *ᵥ c i)).trace := by
      rw [Matrix.mul_sub, Matrix.trace_sub]
    have hρ : (X i * rankOne (V *ᵥ c i)).trace
        = star (V *ᵥ c i) ⬝ᵥ ((X i) *ᵥ (V *ᵥ c i)) := mul_rankOne_trace _ _
    rw [hsplit, hρ, Complex.sub_re] at h0
    linarith
  have hsumineq : (∑ i : Fin n,
        (star (V *ᵥ c i) ⬝ᵥ ((X i) *ᵥ (V *ᵥ c i))).re)
      ≤ ∑ i : Fin n, ((X i) * (V * Vᴴ)).trace.re :=
    Finset.sum_le_sum (fun i _ => hineq i)
  have hsumtrace : (∑ i : Fin n, ((X i) * (V * Vᴴ)).trace) = ((V * Vᴴ)).trace := by
    rw [← Matrix.trace_sum, ← Finset.sum_mul, hsum, Matrix.one_mul]
  have hsumre : (∑ i : Fin n, ((X i) * (V * Vᴴ)).trace.re) = ((V * Vᴴ).trace).re := by
    rw [← Complex.re_sum, hsumtrace]
  have hk : (∑ i : Fin n,
        (star (V *ᵥ c i) ⬝ᵥ ((X i) *ᵥ (V *ᵥ c i))).re) ≤ (k : ℝ) := by
    calc (∑ i : Fin n, (star (V *ᵥ c i) ⬝ᵥ ((X i) *ᵥ (V *ᵥ c i))).re)
        ≤ ∑ i : Fin n, ((X i) * (V * Vᴴ)).trace.re := hsumineq
      _ = ((V * Vᴴ).trace).re := hsumre
      _ = (k : ℝ) := by rw [isometry_proj_trace V hV]; simp
  have h := mul_le_mul_of_nonneg_left hk (by positivity : (0 : ℝ) ≤ 1 / (n : ℝ))
  simpa [div_eq_mul_inv, mul_comm] using h

end Isometry

section PGM

variable {M : ℕ}

lemma sum_rankOne_eq (A : Matrix (Fin N) (Fin M) ℂ) :
    (∑ i, rankOne (fun a => A a i)) = A * Aᴴ := by
  ext a b
  rw [Matrix.sum_apply, Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp [rankOne, outer, Matrix.conjTranspose_apply]

lemma rankOne_mul_rankOne_trace (u v : Fin N → ℂ) :
    (rankOne u * rankOne v).trace = (star u ⬝ᵥ v) * (star v ⬝ᵥ u) := by
  rw [mul_rankOne_trace]
  rw [rankOne_mulVec_apply, dotProduct_smul, smul_eq_mul]

lemma posSemidef_one_sub_idempotent {P : Matrix (Fin N) (Fin N) ℂ}
    (hH : P.IsHermitian) (hI : P * P = P) : (1 - P).PosSemidef := by
  refine posSemidef_of_isHermitian_idempotent ?_ ?_
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hH.eq]
  · rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hI]
    abel

lemma col_inner_eq (U V : Matrix (Fin N) (Fin M) ℂ) (S : Matrix (Fin M) (Fin M) ℂ)
    (h : Uᴴ * V = S) (i : Fin M) :
    star (fun a => U a i) ⬝ᵥ (fun a => V a i) = S i i := by
  rw [← h, Matrix.mul_apply, dotProduct]
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.conjTranspose_apply]

theorem prop_6_1 (B : Matrix (Fin N) (Fin M) ℂ) (S T : Matrix (Fin M) (Fin M) ℂ)
    (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hSsq : S * S = Bᴴ * B) (hST : S * T = 1) (hTS : T * S = 1) :
    (∀ i, (rankOne (fun a => (B * T) a i)).PosSemidef) ∧
      (1 - ∑ i, rankOne (fun a => (B * T) a i)).PosSemidef ∧
      (∀ i, (S i i).im = 0) ∧
      (∑ i, (rankOne (fun a => (B * T) a i) * rankOne (fun a => B a i)).trace
        = ∑ i, (S i i) ^ 2) := by
  have hAherm : (B * T)ᴴ = T * Bᴴ := by
    rw [Matrix.conjTranspose_mul, hT.eq]
  have hiso : (B * T)ᴴ * (B * T) = 1 := by
    rw [hAherm]
    calc T * Bᴴ * (B * T) = T * (Bᴴ * B) * T := by simp only [Matrix.mul_assoc]
      _ = T * (S * S) * T := by rw [hSsq]
      _ = (T * S) * (S * T) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hTS, hST, Matrix.one_mul]
  have hsum_eq : (∑ i, rankOne (fun a => (B * T) a i)) = (B * T) * (B * T)ᴴ :=
    sum_rankOne_eq _
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    exact rankOne_posSemidef _
  · rw [hsum_eq]
    exact posSemidef_one_sub_idempotent (Matrix.isHermitian_mul_conjTranspose_self (B * T))
      (isometry_proj_mul_self (B * T) hiso)
  · intro i
    have h := hS.apply i i
    have h' : star (S i i) = S i i := h
    rw [Complex.star_def] at h'
    exact Complex.conj_eq_iff_im.mp h'
  · apply Finset.sum_congr rfl
    intro i _
    have hEq1 : (B * T)ᴴ * B = S := by
      rw [hAherm]
      calc T * Bᴴ * B = T * (Bᴴ * B) := by simp only [Matrix.mul_assoc]
        _ = T * (S * S) := by rw [hSsq]
        _ = (T * S) * S := by simp only [Matrix.mul_assoc]
        _ = S := by rw [hTS, Matrix.one_mul]
    have hEq2 : Bᴴ * (B * T) = S := by
      calc Bᴴ * (B * T) = (Bᴴ * B) * T := by simp only [Matrix.mul_assoc]
        _ = (S * S) * T := by rw [hSsq]
        _ = S * (S * T) := by simp only [Matrix.mul_assoc]
        _ = S := by rw [hST, Matrix.mul_one]
    rw [rankOne_mul_rankOne_trace, col_inner_eq (B * T) B S hEq1 i,
      col_inner_eq B (B * T) S hEq2 i, sq]

lemma dot_mulVec_eq_sum (X : Matrix (Fin N) (Fin N) ℂ) (v : Fin N → ℂ) :
    star v ⬝ᵥ (X *ᵥ v) = ∑ p, ∑ q, star (v p) * X p q * v q := by
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Pi.star_apply]
  apply Finset.sum_congr rfl
  intro p _
  apply Finset.sum_congr rfl
  intro q _
  ring

lemma measurementSuccess_eq_sum_dot (B : Matrix (Fin N) (Fin M) ℂ)
    (X : Fin M → Matrix (Fin N) (Fin N) ℂ) :
    measurementSuccess B X
      = (1 / (M : ℝ)) * ∑ i : Fin M,
          (star (fun p => B p i) ⬝ᵥ ((X i) *ᵥ (fun p => B p i))).re := by
  unfold measurementSuccess
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp only [dot_mulVec_eq_sum]

theorem prop_6_1_measurementSuccess (B : Matrix (Fin N) (Fin M) ℂ)
    (S T : Matrix (Fin M) (Fin M) ℂ) (hS : S.IsHermitian) (hT : T.IsHermitian)
    (hSsq : S * S = Bᴴ * B) (hST : S * T = 1) (hTS : T * S = 1) :
    measurementSuccess B (fun i => rankOne (fun a => (B * T) a i))
      = (1 / (M : ℝ)) * ∑ i : Fin M, ((S i i) ^ 2).re := by
  have h := (prop_6_1 B S T hS hT hSsq hST hTS).2.2.2
  rw [measurementSuccess_eq_sum_dot]
  congr 1
  have hdot : ∀ i : Fin M,
      star (fun p => B p i) ⬝ᵥ (rankOne (fun a => (B * T) a i) *ᵥ fun p => B p i)
        = (rankOne (fun a => (B * T) a i) * rankOne (fun a => B a i)).trace :=
    fun i => (mul_rankOne_trace _ _).symm
  simp only [hdot]
  rw [← Complex.re_sum, h, Complex.re_sum]

end PGM

end

end Qatlib.Papers.HammingDist09.MainResults.Measurement
