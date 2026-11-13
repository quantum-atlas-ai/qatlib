/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.AdiabBounds06.MainResults.NormBounds

/-!
# Sharp norm bounds for the twiddle operation

Matrix action on Euclidean space is related to adjoints, orthogonal decompositions, and operator
norms. These identities give the off-diagonal block estimate `norm_le_of_offdiag_blocks` and the
sharp spectral-band twiddle bound of [JansenRuskaiSeiler2007], with dependence `sqrt(m) / g`.

## Main statements

* `norm_le_of_offdiag_blocks`: a common bound on the off-diagonal blocks bounds the whole
  matrix.
* `twiddle_norm_sharp`: the norm of a twiddled matrix is at most `sqrt(m) * ‖X‖ / g`.
* `twiddle_twiddle_norm`: a second twiddle operation has bound `m * ‖X‖ / g²`.

## References

* [Jansen et al., 2007][JansenRuskaiSeiler2007]
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator ComplexOrder

namespace Qatlib.Papers.AdiabBounds06.MainResults
variable {n : ℕ}

/-- The zero matrix sends every Euclidean vector to zero under `applyMat`. -/
lemma applyMat_zero (x : EuclideanSpace ℂ (Fin n)) : applyMat 0 x = 0 := by
  simp [applyMat]

/-- The identity matrix acts as the identity under `applyMat`. -/
lemma applyMat_one (x : EuclideanSpace ℂ (Fin n)) : applyMat 1 x = x := by
  simp [applyMat]

/-- The action of a sum of matrices is the sum of their actions. -/
lemma applyMat_add (A B : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    applyMat (A + B) x = applyMat A x + applyMat B x := by
  simp [applyMat, Matrix.add_mulVec, WithLp.toLp_add]

/-- Negating a matrix negates its action on a vector. -/
lemma applyMat_neg (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    applyMat (-A) x = -applyMat A x := by
  simp [applyMat, Matrix.neg_mulVec, WithLp.toLp_neg]

/-- The action of a matrix product is the composition of the two matrix actions. -/
lemma applyMat_mul (A B : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    applyMat (A * B) x = applyMat A (applyMat B x) := by
  simp [applyMat, Matrix.mulVec_mulVec]

/-- The action of a finite sum of matrices is the finite sum of their actions. -/
lemma applyMat_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    applyMat (∑ i ∈ s, f i) x = ∑ i ∈ s, applyMat (f i) x := by
  simp [applyMat, Matrix.sum_mulVec]

/-- Matrix action satisfies the operator norm bound `‖applyMat A x‖ ≤ ‖A‖ * ‖x‖`. -/
lemma applyMat_norm_le (A : Matrix (Fin n) (Fin n) ℂ) (x : EuclideanSpace ℂ (Fin n)) :
    ‖applyMat A x‖ ≤ ‖A‖ * ‖x‖ :=
  Matrix.l2_opNorm_mulVec A x

/-- The continuous linear map associated with a matrix acts by `applyMat`. -/
lemma clm_applyMat (B : Matrix (Fin n) (Fin n) ℂ) (z : EuclideanSpace ℂ (Fin n)) :
    (Matrix.toEuclideanCLM (𝕜 := ℂ) B) z = applyMat B z := by
  conv_lhs => rw [← WithLp.toLp_ofLp 2 z]
  rw [Matrix.toEuclideanCLM_toLp]
  rfl

/-- The continuous linear map of the conjugate transpose is the adjoint of the continuous linear
map of the matrix. -/
lemma clm_conjTranspose (A : Matrix (Fin n) (Fin n) ℂ) :
    Matrix.toEuclideanCLM (𝕜 := ℂ) Aᴴ
      = ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) A) := by
  calc Matrix.toEuclideanCLM (𝕜 := ℂ) Aᴴ
      = star (Matrix.toEuclideanCLM (𝕜 := ℂ) A) := map_star _ A
    _ = ContinuousLinearMap.adjoint (Matrix.toEuclideanCLM (𝕜 := ℂ) A) :=
        ContinuousLinearMap.star_eq_adjoint _

/-- A matrix can be moved across the inner product by taking its conjugate transpose. -/
lemma inner_applyMat_adj (A : Matrix (Fin n) (Fin n) ℂ) (x y : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (applyMat A x) y = inner ℂ x (applyMat Aᴴ y) := by
  rw [← clm_applyMat A x, ← clm_applyMat Aᴴ y, clm_conjTranspose]
  exact (ContinuousLinearMap.adjoint_inner_right (Matrix.toEuclideanCLM (𝕜 := ℂ) A) x y).symm

/-- The inner product of `A u` and `A' w` equals the inner product of `u` and `(Aᴴ * A') w`. -/
lemma inner_applyMat_mul (A A' : Matrix (Fin n) (Fin n) ℂ)
    (u w : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (applyMat A u) (applyMat A' w) = inner ℂ u (applyMat (Aᴴ * A') w) := by
  rw [inner_applyMat_adj, ← applyMat_mul]

/-- An orthogonal projection and its complement decompose the squared norm of a vector into the
sum of the two squared projected norms. -/
lemma proj_decomp_norm_sq {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖x‖^2 = ‖applyMat P x‖^2 + ‖applyMat (1 - P) x‖^2 := by
  have hsplit : applyMat P x + applyMat (1 - P) x = x := by
    rw [← applyMat_add]
    have h1 : P + (1 - P) = (1 : Matrix (Fin n) (Fin n) ℂ) := by abel
    rw [h1, applyMat_one]
  have horth : inner ℂ (applyMat P x) (applyMat (1 - P) x) = 0 := by
    rw [inner_applyMat_adj, ← applyMat_mul]
    have h1 : Pᴴ * (1 - P) = 0 := by
      rw [hP.2, show P * (1 - P) = 0 from (mul_orthCompl hP).1]
    rw [h1, applyMat_zero, inner_zero_right]
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (applyMat P x) (applyMat (1 - P) x) horth
  rw [hsplit] at h
  simpa [pow_two] using! h

/-- The squared norm of a finite sum of pairwise orthogonal vectors equals the sum of their
squared norms. -/
lemma norm_sum_sq_of_orth {ι' : Type*} (s : Finset ι')
    (v : ι' → EuclideanSpace ℂ (Fin n))
    (h : ∀ j ∈ s, ∀ k ∈ s, j ≠ k → inner ℂ (v j) (v k) = 0) :
    ‖∑ j ∈ s, v j‖^2 = ∑ j ∈ s, ‖v j‖^2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  have hexp : inner ℂ (∑ j ∈ s, v j) (∑ j ∈ s, v j)
      = ∑ j ∈ s, ∑ k ∈ s, inner ℂ (v j) (v k) := by
    rw [sum_inner]
    exact Finset.sum_congr rfl (fun j _ => by rw [inner_sum])
  rw [hexp]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_sum]
  rw [Finset.sum_eq_single j]
  · rw [inner_self_eq_norm_sq (𝕜 := ℂ)]
  · intro k hk hkj
    rw [h j hj k hk (Ne.symm hkj), map_zero]
  · intro hj'
    exact absurd hj hj'

/-- If the diagonal blocks relative to an orthogonal projection vanish and both off-diagonal
blocks have norm at most `M`, the whole matrix has norm at most `M`. -/
theorem norm_le_of_offdiag_blocks {P A : Matrix (Fin n) (Fin n) ℂ} (hP : IsProj P)
    (hPAP : P * A * P = 0) (hQAQ : (1 - P) * A * (1 - P) = 0) (M : ℝ)
    (h1 : ‖P * A * (1 - P)‖ ≤ M) (h2 : ‖(1 - P) * A * P‖ ≤ M) :
    ‖A‖ ≤ M := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) h1
  have hdecomp : A = P * A * (1 - P) + (1 - P) * A * P := by
    calc A = (P + (1 - P)) * A * (P + (1 - P)) := by noncomm_ring
      _ = P * A * P + P * A * (1 - P) + (1 - P) * A * P + (1 - P) * A * (1 - P) := by
          noncomm_ring
      _ = P * A * (1 - P) + (1 - P) * A * P := by rw [hPAP, hQAQ]; noncomm_ring
  have hQA : (1 - P) * (1 - P) = (1 - P) := (IsProj.orthCompl_isProj hP).1
  have hpoint : ∀ x, ‖applyMat A x‖ ≤ M * ‖x‖ := by
    intro x
    have hx : applyMat A x
        = applyMat (P * A * (1 - P)) x + applyMat ((1 - P) * A * P) x := by
      rw [← applyMat_add, ← hdecomp]
    have horth : inner ℂ (applyMat (P * A * (1 - P)) x)
        (applyMat ((1 - P) * A * P) x) = 0 := by
      have e1 : applyMat (P * A * (1 - P)) x
          = applyMat P (applyMat (A * (1 - P)) x) := by
        rw [show P * A * (1 - P) = P * (A * (1 - P)) from by noncomm_ring, applyMat_mul]
      have e2 : applyMat ((1 - P) * A * P) x
          = applyMat (1 - P) (applyMat (A * P) x) := by
        rw [show (1 - P) * A * P = (1 - P) * (A * P) from by noncomm_ring, applyMat_mul]
      rw [e1, e2, inner_applyMat_adj, ← applyMat_mul]
      rw [hP.2, show P * (1 - P) = 0 from (mul_orthCompl hP).1, applyMat_zero,
        inner_zero_right]
    have hsq := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
      (applyMat (P * A * (1 - P)) x) (applyMat ((1 - P) * A * P) x) horth

    have hu : ‖applyMat (P * A * (1 - P)) x‖ ≤ M * ‖applyMat (1 - P) x‖ := by
      have hm1 : P * A * (1 - P) * (1 - P) = P * A * (1 - P) := by
        rw [show P * A * (1 - P) * (1 - P) = P * A * ((1 - P) * (1 - P)) from by
          noncomm_ring, hQA]
      have hEq : applyMat (P * A * (1 - P)) x
          = applyMat (P * A * (1 - P)) (applyMat (1 - P) x) := by
        rw [← applyMat_mul, hm1]
      rw [hEq]
      exact le_trans (applyMat_norm_le _ _) (mul_le_mul_of_nonneg_right h1 (norm_nonneg _))
    have hv : ‖applyMat ((1 - P) * A * P) x‖ ≤ M * ‖applyMat P x‖ := by
      have hPP : P * P = P := hP.1
      have hm2 : (1 - P) * A * P * P = (1 - P) * A * P := by
        rw [show (1 - P) * A * P * P = (1 - P) * A * (P * P) from by noncomm_ring, hPP]
      have hEq : applyMat ((1 - P) * A * P) x
          = applyMat ((1 - P) * A * P) (applyMat P x) := by
        rw [← applyMat_mul, hm2]
      rw [hEq]
      exact le_trans (applyMat_norm_le _ _) (mul_le_mul_of_nonneg_right h2 (norm_nonneg _))
    have hdec := proj_decomp_norm_sq hP x
    have hsum : ‖x‖^2 = ‖applyMat P x‖^2 + ‖applyMat (1 - P) x‖^2 := hdec
    have hsq2 : ‖applyMat (P * A * (1 - P)) x + applyMat ((1 - P) * A * P) x‖^2
        = ‖applyMat (P * A * (1 - P)) x‖^2 + ‖applyMat ((1 - P) * A * P) x‖^2 := by
      rw [pow_two, pow_two, pow_two]
      exact hsq
    have hb : ‖applyMat A x‖^2 ≤ M^2 * ‖x‖^2 := by
      rw [hx, hsq2]
      have h1' : ‖applyMat (P * A * (1 - P)) x‖^2
          ≤ (M * ‖applyMat (1 - P) x‖)^2 := pow_le_pow_left₀ (norm_nonneg _) hu 2
      have h2' : ‖applyMat ((1 - P) * A * P) x‖^2 ≤ (M * ‖applyMat P x‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) hv 2
      calc ‖applyMat (P * A * (1 - P)) x‖^2 + ‖applyMat ((1 - P) * A * P) x‖^2
          ≤ (M * ‖applyMat (1 - P) x‖)^2 + (M * ‖applyMat P x‖)^2 := add_le_add h1' h2'
        _ = M^2 * (‖applyMat (1 - P) x‖^2 + ‖applyMat P x‖^2) := by ring
        _ = M^2 * ‖x‖^2 := by
            rw [show ‖applyMat (1 - P) x‖^2 + ‖applyMat P x‖^2 = ‖x‖^2 from by
              rw [add_comm, ← hsum]]
    have hnormA : 0 ≤ ‖applyMat A x‖ := norm_nonneg _
    calc ‖applyMat A x‖ = Real.sqrt (‖applyMat A x‖^2) := (Real.sqrt_sq hnormA).symm
      _ ≤ Real.sqrt (M^2 * ‖x‖^2) := Real.sqrt_le_sqrt hb
      _ = M * ‖x‖ := by
          rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0, Real.sqrt_sq (norm_nonneg x)]
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 ?_
  intro x
  rw [clm_applyMat]
  exact hpoint x

/-- Matrix action commutes with summation over a finite index type. -/
lemma applyMat_sum' {ι : Type*} [Fintype ι] (f : ι → Matrix (Fin n) (Fin n) ℂ)
    (x : EuclideanSpace ℂ (Fin n)) :
    applyMat (∑ i, f i) x = ∑ i, applyMat (f i) x := by
  simpa using! applyMat_sum (Finset.univ) f x

/-- The squared norm of the left resolvent sum acting on `x` is bounded by `m * ‖X‖² / g²` times
the squared norm of the complementary projection of `x`, under the stated support and norm
bounds. -/
lemma left_block_sq {H : Matrix (Fin n) (Fin n) ℂ} (D : BandData H)
    (X : Matrix (Fin n) (Fin n) ℂ) (S : Fin D.m → Matrix (Fin n) (Fin n) ℂ)
    (hSQ : ∀ j, S j * (1 - D.P) = S j) (hSbd : ∀ j, ‖S j‖ ≤ 1 / D.g)
    (x : EuclideanSpace ℂ (Fin n)) :
    ‖applyMat (-∑ j, D.Pj j * X * S j) x‖^2
      ≤ (D.m : ℝ) * ‖X‖^2 / D.g^2 * ‖applyMat (1 - D.P) x‖^2 := by
  set v : Fin D.m → EuclideanSpace ℂ (Fin n) :=
    fun j => applyMat (D.Pj j * X * S j) x with hv
  have hL : applyMat (-∑ j, D.Pj j * X * S j) x = -(∑ j, v j) := by
    rw [applyMat_neg, applyMat_sum']
  have horth : ∀ j : Fin D.m, ∀ k : Fin D.m, j ≠ k → inner ℂ (v j) (v k) = 0 := by
    intro j k hjk
    have e1 : v j = applyMat (D.Pj j) (applyMat X (applyMat (S j) x)) := by
      rw [hv]; simp only
      rw [show D.Pj j * X * S j = D.Pj j * (X * S j) from by noncomm_ring,
        applyMat_mul, applyMat_mul]
    have e2 : v k = applyMat (D.Pj k) (applyMat X (applyMat (S k) x)) := by
      rw [hv]; simp only
      rw [show D.Pj k * X * S k = D.Pj k * (X * S k) from by noncomm_ring,
        applyMat_mul, applyMat_mul]
    rw [e1, e2, inner_applyMat_mul, (D.Pj_proj j).2]
    rw [D.Pj_orth j k hjk, applyMat_zero, inner_zero_right]
  have hsq : ‖applyMat (-∑ j, D.Pj j * X * S j) x‖^2 = ∑ j, ‖v j‖^2 := by
    rw [hL, norm_neg]
    exact norm_sum_sq_of_orth Finset.univ v
      (fun j _ k _ hjk => horth j k hjk)
  have hterm : ∀ j : Fin D.m,
      ‖v j‖ ≤ (‖X‖ / D.g) * ‖applyMat (1 - D.P) x‖ := by
    intro j
    have e1 : v j = applyMat (D.Pj j) (applyMat X (applyMat (S j) x)) := by
      rw [hv]; simp only
      rw [show D.Pj j * X * S j = D.Pj j * (X * S j) from by noncomm_ring,
        applyMat_mul, applyMat_mul]
    rw [e1]
    have hSx : ‖applyMat (S j) x‖ ≤ (1 / D.g) * ‖applyMat (1 - D.P) x‖ := by
      have e2 : applyMat (S j) x = applyMat (S j) (applyMat (1 - D.P) x) := by
        rw [← applyMat_mul, hSQ j]
      rw [e2]
      exact le_trans (applyMat_norm_le _ _)
        (mul_le_mul_of_nonneg_right (hSbd j) (norm_nonneg _))
    calc ‖applyMat (D.Pj j) (applyMat X (applyMat (S j) x))‖
        ≤ ‖D.Pj j‖ * ‖applyMat X (applyMat (S j) x)‖ := applyMat_norm_le _ _
      _ ≤ ‖D.Pj j‖ * (‖X‖ * ‖applyMat (S j) x‖) :=
          mul_le_mul_of_nonneg_left (applyMat_norm_le _ _) (norm_nonneg _)
      _ ≤ ‖D.Pj j‖ * (‖X‖ * ((1 / D.g) * ‖applyMat (1 - D.P) x‖)) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_left hSx (norm_nonneg _)
          · exact norm_nonneg _
      _ ≤ 1 * (‖X‖ * ((1 / D.g) * ‖applyMat (1 - D.P) x‖)) := by
          apply mul_le_mul_of_nonneg_right
          · exact isProj_norm_le_one (D.Pj_proj j)
          · exact mul_nonneg (norm_nonneg _)
              (mul_nonneg (le_of_lt (one_div_pos.mpr D.hg)) (norm_nonneg _))
      _ = (‖X‖ / D.g) * ‖applyMat (1 - D.P) x‖ := by
          rw [one_mul]
          field_simp
  have hsumle : ∑ j : Fin D.m, ‖v j‖^2
      ≤ ∑ j : Fin D.m, ((‖X‖ / D.g) * ‖applyMat (1 - D.P) x‖)^2 :=
    Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hterm j) 2)
  have hcard : (∑ j : Fin D.m, ((‖X‖ / D.g) * ‖applyMat (1 - D.P) x‖)^2)
      = (D.m : ℝ) * ((‖X‖ / D.g) * ‖applyMat (1 - D.P) x‖)^2 := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  calc ‖applyMat (-∑ j, D.Pj j * X * S j) x‖^2 = ∑ j, ‖v j‖^2 := hsq
    _ ≤ (D.m : ℝ) * ((‖X‖ / D.g) * ‖applyMat (1 - D.P) x‖)^2 := by
        rw [← hcard]; exact hsumle
    _ = (D.m : ℝ) * ‖X‖^2 / D.g^2 * ‖applyMat (1 - D.P) x‖^2 := by
        have hg0 : D.g ≠ 0 := ne_of_gt D.hg
        field_simp

/-- The left resolvent sum has operator norm at most `sqrt(m) * ‖X‖ / g` when each resolvent
factor has complementary right support and norm at most `1 / g`. -/
lemma left_block_norm {H : Matrix (Fin n) (Fin n) ℂ} (D : BandData H)
    (X : Matrix (Fin n) (Fin n) ℂ) (S : Fin D.m → Matrix (Fin n) (Fin n) ℂ)
    (hSQ : ∀ j, S j * (1 - D.P) = S j) (hSbd : ∀ j, ‖S j‖ ≤ 1 / D.g) :
    ‖-∑ j, D.Pj j * X * S j‖ ≤ Real.sqrt (D.m : ℝ) * ‖X‖ / D.g := by
  set M := Real.sqrt (D.m : ℝ) * ‖X‖ / D.g with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) D.hg.le
  have hMsq : M^2 = (D.m : ℝ) * ‖X‖^2 / D.g^2 := by
    rw [hM, div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg D.m)]
  have hcoef : 0 ≤ (D.m : ℝ) * ‖X‖^2 / D.g^2 :=
    div_nonneg (mul_nonneg (Nat.cast_nonneg D.m) (sq_nonneg ‖X‖)) (sq_nonneg D.g)
  rw [← Matrix.l2_opNorm_toEuclideanCLM]
  refine ContinuousLinearMap.opNorm_le_bound _ hM0 ?_
  intro x
  rw [clm_applyMat]
  have hb := left_block_sq D X S hSQ hSbd x
  have hQle : ‖applyMat (1 - D.P) x‖ ≤ ‖x‖ := by
    have h1 : ‖applyMat (1 - D.P) x‖ ≤ ‖(1 - D.P)‖ * ‖x‖ := applyMat_norm_le _ _
    have h2 : ‖(1 - D.P)‖ ≤ 1 := isProj_norm_le_one (IsProj.orthCompl_isProj D.P_proj)
    nlinarith [norm_nonneg x, norm_nonneg (applyMat (1 - D.P) x)]
  have hb2 : ‖applyMat (-∑ j, D.Pj j * X * S j) x‖^2 ≤ M^2 * ‖x‖^2 := by
    rw [hMsq]
    calc ‖applyMat (-∑ j, D.Pj j * X * S j) x‖^2
        ≤ (D.m : ℝ) * ‖X‖^2 / D.g^2 * ‖applyMat (1 - D.P) x‖^2 := hb
      _ ≤ (D.m : ℝ) * ‖X‖^2 / D.g^2 * ‖x‖^2 := by
          apply mul_le_mul_of_nonneg_left _ hcoef
          exact pow_le_pow_left₀ (norm_nonneg _) hQle 2
  calc ‖applyMat (-∑ j, D.Pj j * X * S j) x‖
      = Real.sqrt (‖applyMat (-∑ j, D.Pj j * X * S j) x‖^2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (M^2 * ‖x‖^2) := Real.sqrt_le_sqrt hb2
    _ = M * ‖x‖ := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq hM0, Real.sqrt_sq (norm_nonneg x)]

/-- The block `P * twiddle X * (1 - P)` has norm at most `sqrt(m) * ‖X‖ / g`. -/
lemma P_block_norm_le {H : Matrix (Fin n) (Fin n) ℂ} (D : BandData H)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖D.P * D.twiddle X * (1 - D.P)‖ ≤ Real.sqrt (D.m : ℝ) * ‖X‖ / D.g := by
  rw [D.P_twiddle_Q X]
  exact left_block_norm D X D.Rhat (fun j => D.Rhat_right j) (fun j => D.Rhat_bound j)

/-- The block `(1 - P) * twiddle X * P` has norm at most `sqrt(m) * ‖X‖ / g`. -/
lemma Q_block_norm_le {H : Matrix (Fin n) (Fin n) ℂ} (D : BandData H)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖(1 - D.P) * D.twiddle X * D.P‖ ≤ Real.sqrt (D.m : ℝ) * ‖X‖ / D.g := by
  have hH : ((1 - D.P) * D.twiddle X * D.P)ᴴ
      = -∑ j, D.Pj j * Xᴴ * (D.Rhat j)ᴴ := by
    rw [D.Q_twiddle_P X]
    simp only [Matrix.conjTranspose_neg, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    rw [(D.Pj_proj j).2]
    noncomm_ring
  have hSQ : ∀ j, (D.Rhat j)ᴴ * (1 - D.P) = (D.Rhat j)ᴴ := by
    intro j
    have h : ((1 - D.P) * D.Rhat j)ᴴ = (D.Rhat j)ᴴ := by rw [D.Rhat_left j]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      D.P_proj.2] at h
    simpa using! h
  have hSbd : ∀ j, ‖(D.Rhat j)ᴴ‖ ≤ 1 / D.g := by
    intro j
    rw [Matrix.l2_opNorm_conjTranspose]
    exact D.Rhat_bound j
  have hb := left_block_norm D Xᴴ (fun j => (D.Rhat j)ᴴ) hSQ hSbd
  rw [← Matrix.l2_opNorm_conjTranspose ((1 - D.P) * D.twiddle X * D.P), hH]
  rw [Matrix.l2_opNorm_conjTranspose X] at hb
  exact hb

/-- The spectral-band twiddle operation satisfies `‖D.twiddle X‖ ≤ sqrt(m) * ‖X‖ / g`. See
[JansenRuskaiSeiler2007]. -/
theorem twiddle_norm_sharp {H : Matrix (Fin n) (Fin n) ℂ} (D : BandData H)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖D.twiddle X‖ ≤ Real.sqrt (D.m : ℝ) * ‖X‖ / D.g :=
  norm_le_of_offdiag_blocks D.P_proj (D.P_twiddle_P X) (D.Q_twiddle_Q X) _
    (P_block_norm_le D X) (Q_block_norm_le D X)

/-- Applying the twiddle operation twice gives the bound `‖D.twiddle (D.twiddle X)‖ ≤ m * ‖X‖ /
g²`. See [JansenRuskaiSeiler2007]. -/
theorem twiddle_twiddle_norm {H : Matrix (Fin n) (Fin n) ℂ} (D : BandData H)
    (X : Matrix (Fin n) (Fin n) ℂ) :
    ‖D.twiddle (D.twiddle X)‖ ≤ (D.m : ℝ) * ‖X‖ / D.g^2 := by
  have hstep : Real.sqrt (D.m : ℝ) * ‖D.twiddle X‖ / D.g ≤
      Real.sqrt (D.m : ℝ) * (Real.sqrt (D.m : ℝ) * ‖X‖ / D.g) / D.g := by
    have hcoef : 0 ≤ Real.sqrt (D.m : ℝ) / D.g :=
      div_nonneg (Real.sqrt_nonneg _) D.hg.le
    calc Real.sqrt (D.m : ℝ) * ‖D.twiddle X‖ / D.g
        = Real.sqrt (D.m : ℝ) / D.g * ‖D.twiddle X‖ := by ring
      _ ≤ Real.sqrt (D.m : ℝ) / D.g *
            (Real.sqrt (D.m : ℝ) * ‖X‖ / D.g) :=
          mul_le_mul_of_nonneg_left (twiddle_norm_sharp D X) hcoef
      _ = Real.sqrt (D.m : ℝ) * (Real.sqrt (D.m : ℝ) * ‖X‖ / D.g) / D.g := by ring
  have hfin : Real.sqrt (D.m : ℝ) * (Real.sqrt (D.m : ℝ) * ‖X‖ / D.g) / D.g
      = (D.m : ℝ) * ‖X‖ / D.g^2 := by
    have hg0 : D.g ≠ 0 := ne_of_gt D.hg
    field_simp [hg0]
    rw [Real.sq_sqrt (Nat.cast_nonneg D.m)]
    ring
  calc ‖D.twiddle (D.twiddle X)‖
      ≤ Real.sqrt (D.m : ℝ) * ‖D.twiddle X‖ / D.g := twiddle_norm_sharp D (D.twiddle X)
    _ ≤ Real.sqrt (D.m : ℝ) * (Real.sqrt (D.m : ℝ) * ‖X‖ / D.g) / D.g := hstep
    _ = (D.m : ℝ) * ‖X‖ / D.g^2 := hfin

end Qatlib.Papers.AdiabBounds06.MainResults
