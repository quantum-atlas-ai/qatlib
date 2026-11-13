/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.PureStateMath.BornBridge.RelabelOperatorNorm
import Qatlib.Foundations.OperatorErrors.OperatorError

/-!
# Operator norms of tensor products

This module proves multiplicativity of the Euclidean operator norm for Kronecker products of
finite complex matrices, including rectangular matrices. It relates matrix-vector multiplication
to Euclidean continuous linear maps and proves the corresponding product formula for
tensor-state norms. Background on matrix norms is provided by [Bhatia1997].

The tensor-product norm formula yields error bounds for replacing either or both factors.
Tensoring an operator difference with the identity on a nonempty reference system preserves its
norm.

## Main statements

* `tensorState_l2_norm`: Euclidean norm of a tensor state.
* `l2_norm_kronecker`: multiplicativity of the operator norm.
* `l2_tensor_ancilla_error`: invariance under identity ancillas.
* `l2_kronecker_two_factor_error`: error bound for changing both factors.

## References

* [Bhatia, 1997][Bhatia1997]
-/

open Qatlib.Foundations.OperatorErrors.OperatorError
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.BornBridge

namespace Qatlib.Concepts.ReferenceError.RefTraceError

open Matrix

open scoped Matrix.Norms.L2Operator Kronecker

section Bridging

variable {O I P J : Type*} [Fintype O] [Fintype I] [DecidableEq I]
  [Fintype P] [DecidableEq P] [Fintype J] [DecidableEq J]

/-- The continuous linear map associated with a rectangular matrix agrees with matrix-vector
multiplication after converting between function vectors and Euclidean space. -/
theorem toEuclideanCLMRect_apply (A : Matrix O I ℂ) (x : EuclideanSpace ℂ I) :
    (Matrix.toEuclideanLin (𝕜 := ℂ) (m := O) (n := I)).trans
        LinearMap.toContinuousLinearMap A x
      = toEuclidean_fromVec (A *ᵥ WithLp.ofLp x) := rfl

/-- The Euclidean norm of `A *ᵥ v` is at most the operator norm of `A` times the Euclidean norm
of `v`. -/
theorem l2_norm_mulVec_fromVec_le (A : Matrix O I ℂ) (v : QState I) :
    ‖toEuclidean_fromVec (A *ᵥ v)‖ ≤ ‖A‖ * ‖toEuclidean_fromVec v‖ := by
  have h := Matrix.l2_opNorm_mulVec (𝕜 := ℂ) (m := O) A (toEuclidean_fromVec v)
  rwa [show WithLp.ofLp (toEuclidean_fromVec v) = v from rfl,
    show (EuclideanSpace.equiv O ℂ).symm (A *ᵥ v) = toEuclidean_fromVec (A *ᵥ v) from rfl] at h

/-- A nonnegative uniform bound on the norm expansion of all vectors bounds the Euclidean
operator norm. -/
theorem l2_opNorm_le_of_mulVec_le {C : ℝ} (hC : 0 ≤ C) (A : Matrix O I ℂ)
    (h : ∀ v : QState I, ‖toEuclidean_fromVec (A *ᵥ v)‖ ≤ C * ‖toEuclidean_fromVec v‖) :
    ‖A‖ ≤ C := by
  rw [Matrix.l2_opNorm_def (𝕜 := ℂ) (m := O) (n := I)]
  refine ContinuousLinearMap.opNorm_le_bound _ hC fun x => ?_
  rw [toEuclideanCLMRect_apply]
  exact h (WithLp.ofLp x)

end Bridging

section ProductState

variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

omit [DecidableEq I] [DecidableEq J] in
/-- The Euclidean norm of a tensor state is the product of the Euclidean norms of its factors. -/
theorem tensorState_l2_norm (ψ : QState I) (φ : QState J) :
    ‖toEuclidean_fromVec (TensorState ψ φ)‖ = ‖toEuclidean_fromVec ψ‖ * ‖toEuclidean_fromVec φ‖ := by
  have hsq : ‖toEuclidean_fromVec (TensorState ψ φ)‖ ^ 2
      = ‖toEuclidean_fromVec ψ‖ ^ 2 * ‖toEuclidean_fromVec φ‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, norm_toEuclidean_fromVec_sq,
      norm_toEuclidean_fromVec_sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    simp [TensorState, mul_pow]
  calc ‖toEuclidean_fromVec (TensorState ψ φ)‖
      = Real.sqrt (‖toEuclidean_fromVec (TensorState ψ φ)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ = Real.sqrt (‖toEuclidean_fromVec ψ‖ ^ 2 * ‖toEuclidean_fromVec φ‖ ^ 2) := by rw [hsq]
    _ = Real.sqrt (‖toEuclidean_fromVec ψ‖ ^ 2) * Real.sqrt (‖toEuclidean_fromVec φ‖ ^ 2) :=
        Real.sqrt_mul (sq_nonneg _) _
    _ = ‖toEuclidean_fromVec ψ‖ * ‖toEuclidean_fromVec φ‖ := by
        rw [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)]

end ProductState

section Kronecker

variable {O I P J : Type*} [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
  [Fintype P] [DecidableEq P] [Fintype J] [DecidableEq J]

/-- Squaring preserves an inequality between nonnegative real numbers. -/
private theorem sq_le_sq_of_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (h : a ≤ b) :
    a ^ 2 ≤ b ^ 2 :=
  sq_le_sq.mpr (by rwa [abs_of_nonneg ha, abs_of_nonneg hb])

omit [Fintype O] [DecidableEq O] [DecidableEq I] [Fintype P] [DecidableEq P] [DecidableEq J] in

/-- A Kronecker product acts on a tensor state by applying each matrix to its respective factor. -/
theorem kronecker_mulVec_tensorState (A : Matrix O I ℂ) (B : Matrix P J ℂ)
    (ψ : QState I) (φ : QState J) :
    (A ⊗ₖ B) *ᵥ TensorState ψ φ = TensorState (A *ᵥ ψ) (B *ᵥ φ) := by
  ext q
  obtain ⟨o, p⟩ := q
  simp only [Matrix.mulVec, dotProduct, Matrix.kronecker_apply, TensorState,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

omit [DecidableEq O] [DecidableEq P] in
/-- The squared Euclidean norm after a Kronecker-product action is bounded by the product of the
squared operator norms and the squared input norm. -/
theorem kronecker_mulVec_norm_sq_le (A : Matrix O I ℂ) (B : Matrix P J ℂ) (z : QState (I × J)) :
    ‖toEuclidean_fromVec ((A ⊗ₖ B) *ᵥ z)‖ ^ 2
      ≤ ‖A‖ ^ 2 * (‖B‖ ^ 2 * ‖toEuclidean_fromVec z‖ ^ 2) := by
  have hentry : ∀ (o : O) (p : P), ((A ⊗ₖ B) *ᵥ z) (o, p)
      = (A *ᵥ (fun i => ∑ j, B p j * z (i, j))) o := by
    intro o p
    simp only [Matrix.mulVec, dotProduct, Matrix.kronecker_apply, Fintype.sum_prod_type,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have h1 : ‖toEuclidean_fromVec ((A ⊗ₖ B) *ᵥ z)‖ ^ 2
      = ∑ p, ∑ o, ‖((A ⊗ₖ B) *ᵥ z) (o, p)‖ ^ 2 := by
    rw [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type, Finset.sum_comm]
  have h2 : ∀ p : P, ∑ o, ‖((A ⊗ₖ B) *ᵥ z) (o, p)‖ ^ 2
      ≤ ‖A‖ ^ 2 * ∑ i, ‖(B *ᵥ (fun j => z (i, j))) p‖ ^ 2 := by
    intro p
    have hn := l2_norm_mulVec_fromVec_le A (fun i => ∑ j, B p j * z (i, j))
    calc ∑ o, ‖((A ⊗ₖ B) *ᵥ z) (o, p)‖ ^ 2
        = ∑ o, ‖(A *ᵥ (fun i => ∑ j, B p j * z (i, j))) o‖ ^ 2 :=
          Finset.sum_congr rfl fun o _ => by rw [hentry o p]
      _ = ‖toEuclidean_fromVec (A *ᵥ (fun i => ∑ j, B p j * z (i, j)))‖ ^ 2 :=
          (norm_toEuclidean_fromVec_sq _).symm
      _ ≤ (‖A‖ * ‖toEuclidean_fromVec (fun i => ∑ j, B p j * z (i, j))‖) ^ 2 :=
          sq_le_sq_of_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hn
      _ = ‖A‖ ^ 2 * ∑ i, ‖(B *ᵥ (fun j => z (i, j))) p‖ ^ 2 := by
          rw [mul_pow, norm_toEuclidean_fromVec_sq]
          rfl
  have h3 : ∑ p, ∑ i, ‖(B *ᵥ (fun j => z (i, j))) p‖ ^ 2
      ≤ ‖B‖ ^ 2 * ‖toEuclidean_fromVec z‖ ^ 2 := by
    have hle : ∀ i, ‖toEuclidean_fromVec (B *ᵥ (fun j => z (i, j)))‖ ^ 2
        ≤ ‖B‖ ^ 2 * ∑ j, ‖z (i, j)‖ ^ 2 := by
      intro i
      have hn := l2_norm_mulVec_fromVec_le B (fun j => z (i, j))
      calc ‖toEuclidean_fromVec (B *ᵥ (fun j => z (i, j)))‖ ^ 2
          ≤ (‖B‖ * ‖toEuclidean_fromVec (fun j => z (i, j))‖) ^ 2 :=
            sq_le_sq_of_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hn
        _ = ‖B‖ ^ 2 * ∑ j, ‖z (i, j)‖ ^ 2 := by
            rw [mul_pow, norm_toEuclidean_fromVec_sq]
    calc ∑ p, ∑ i, ‖(B *ᵥ (fun j => z (i, j))) p‖ ^ 2
        = ∑ i, ∑ p, ‖(B *ᵥ (fun j => z (i, j))) p‖ ^ 2 := Finset.sum_comm
      _ = ∑ i, ‖toEuclidean_fromVec (B *ᵥ (fun j => z (i, j)))‖ ^ 2 :=
          Finset.sum_congr rfl fun i _ => (norm_toEuclidean_fromVec_sq _).symm
      _ ≤ ∑ i, ‖B‖ ^ 2 * ∑ j, ‖z (i, j)‖ ^ 2 := Finset.sum_le_sum fun i _ => hle i
      _ = ‖B‖ ^ 2 * ∑ i, ∑ j, ‖z (i, j)‖ ^ 2 := (Finset.mul_sum _ _ _).symm
      _ = ‖B‖ ^ 2 * ‖toEuclidean_fromVec z‖ ^ 2 := by
          congr 1
          rw [norm_toEuclidean_fromVec_sq, Fintype.sum_prod_type]
  calc ‖toEuclidean_fromVec ((A ⊗ₖ B) *ᵥ z)‖ ^ 2 = ∑ p, ∑ o, ‖((A ⊗ₖ B) *ᵥ z) (o, p)‖ ^ 2 := h1
    _ ≤ ∑ p, ‖A‖ ^ 2 * ∑ i, ‖(B *ᵥ (fun j => z (i, j))) p‖ ^ 2 :=
        Finset.sum_le_sum fun p _ => h2 p
    _ = ‖A‖ ^ 2 * ∑ p, ∑ i, ‖(B *ᵥ (fun j => z (i, j))) p‖ ^ 2 := (Finset.mul_sum _ _ _).symm
    _ ≤ ‖A‖ ^ 2 * (‖B‖ ^ 2 * ‖toEuclidean_fromVec z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h3 (sq_nonneg _)

/-- The Euclidean operator norm of a Kronecker product is at most the product of the factor
norms. -/
theorem l2_norm_kronecker_le (A : Matrix O I ℂ) (B : Matrix P J ℂ) : ‖A ⊗ₖ B‖ ≤ ‖A‖ * ‖B‖ := by
  refine l2_opNorm_le_of_mulVec_le (mul_nonneg (norm_nonneg _) (norm_nonneg _)) _ fun z => ?_
  have hsq := kronecker_mulVec_norm_sq_le A B z
  have hring : ‖A‖ ^ 2 * (‖B‖ ^ 2 * ‖toEuclidean_fromVec z‖ ^ 2)
      = (‖A‖ * (‖B‖ * ‖toEuclidean_fromVec z‖)) ^ 2 := by ring
  rw [hring] at hsq
  calc ‖toEuclidean_fromVec ((A ⊗ₖ B) *ᵥ z)‖
      = Real.sqrt (‖toEuclidean_fromVec ((A ⊗ₖ B) *ᵥ z)‖ ^ 2) :=
        (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((‖A‖ * (‖B‖ * ‖toEuclidean_fromVec z‖)) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = ‖A‖ * (‖B‖ * ‖toEuclidean_fromVec z‖) := Real.sqrt_sq (by positivity)
    _ ≤ ‖A‖ * ‖B‖ * ‖toEuclidean_fromVec z‖ := le_of_eq (by ring)

set_option maxHeartbeats 1000000 in

/-- The product of the Euclidean operator norms of two matrices is at most the norm of their
Kronecker product. -/
theorem l2_norm_kronecker_ge (A : Matrix O I ℂ) (B : Matrix P J ℂ) :
    ‖A‖ * ‖B‖ ≤ ‖A ⊗ₖ B‖ := by
  rcases eq_or_lt_of_le (norm_nonneg A) with hA0 | hA0
  · rw [← hA0, zero_mul]
    exact norm_nonneg _
  rcases eq_or_lt_of_le (norm_nonneg B) with hB0 | hB0
  · rw [← hB0, mul_zero]
    exact norm_nonneg _
  by_contra hcon
  rw [not_le] at hcon
  have hprod : (0 : ℝ) < ‖A‖ * ‖B‖ := mul_pos hA0 hB0
  have ht0 : 0 ≤ ‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖) := div_nonneg (norm_nonneg _) hprod.le
  have ht1 : ‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖) < 1 := (div_lt_one hprod).mpr hcon
  have hroot : Real.sqrt (‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖)) < 1 := by
    rw [Real.sqrt_lt' zero_lt_one, one_pow]
    exact ht1
  have hroot' : 0 ≤ Real.sqrt (‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖)) := Real.sqrt_nonneg _
  obtain ⟨s, hs0, hs1, hs2⟩ : ∃ s : ℝ, 0 < s ∧ s < 1 ∧
      ‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖) < s ^ 2 :=
    ⟨(Real.sqrt (‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖)) + 1) / 2, by positivity, by linarith, by
      have hlt : Real.sqrt (‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖))
          < (Real.sqrt (‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖)) + 1) / 2 := by linarith
      have h3 : 0 ≤ (Real.sqrt (‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖)) + 1) / 2 := by positivity
      nlinarith [Real.sq_sqrt ht0, hlt, hroot', h3]⟩
  have hr₁pos : 0 ≤ s * ‖A‖ := mul_nonneg hs0.le hA0.le
  have hr₂pos : 0 ≤ s * ‖B‖ := mul_nonneg hs0.le hB0.le
  have hr₁ : s * ‖A‖ < ‖A‖ := by
    have h1 : s * ‖A‖ < 1 * ‖A‖ := mul_lt_mul_of_pos_right hs1 hA0
    rwa [one_mul] at h1
  have hr₂ : s * ‖B‖ < ‖B‖ := by
    have h1 : s * ‖B‖ < 1 * ‖B‖ := mul_lt_mul_of_pos_right hs1 hB0
    rwa [one_mul] at h1
  obtain ⟨x, hx⟩ := ContinuousLinearMap.exists_mul_lt_of_lt_opNorm
    ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := O) (n := I)).trans LinearMap.toContinuousLinearMap A)
    hr₁pos (by
      have hn : ‖((Matrix.toEuclideanLin (𝕜 := ℂ) (m := O) (n := I)).trans
          LinearMap.toContinuousLinearMap) A‖ = ‖A‖ :=
        (Matrix.l2_opNorm_def (𝕜 := ℂ) (m := O) (n := I) A).symm
      rw [hn]
      exact hr₁)
  obtain ⟨y, hy⟩ := ContinuousLinearMap.exists_mul_lt_of_lt_opNorm
    ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := P) (n := J)).trans LinearMap.toContinuousLinearMap B)
    hr₂pos (by
      have hn : ‖((Matrix.toEuclideanLin (𝕜 := ℂ) (m := P) (n := J)).trans
          LinearMap.toContinuousLinearMap) B‖ = ‖B‖ :=
        (Matrix.l2_opNorm_def (𝕜 := ℂ) (m := P) (n := J) B).symm
      rw [hn]
      exact hr₂)
  rw [toEuclideanCLMRect_apply] at hx
  rw [toEuclideanCLMRect_apply] at hy
  set ψ : QState I := WithLp.ofLp x with hψ
  set φ : QState J := WithLp.ofLp y with hφ
  have hx' : s * ‖A‖ * ‖x‖ < ‖toEuclidean_fromVec (A *ᵥ ψ)‖ := hx
  have hy' : s * ‖B‖ * ‖y‖ < ‖toEuclidean_fromVec (B *ᵥ φ)‖ := hy
  have hzx : toEuclidean_fromVec ψ = x := rfl
  have hzy : toEuclidean_fromVec φ = y := rfl
  have hznorm : ‖toEuclidean_fromVec (TensorState ψ φ)‖ = ‖x‖ * ‖y‖ := by
    rw [tensorState_l2_norm, hzx, hzy]
  have hact : (A ⊗ₖ B) *ᵥ TensorState ψ φ = TensorState (A *ᵥ ψ) (B *ᵥ φ) :=
    kronecker_mulVec_tensorState A B ψ φ
  have hsplit : ‖toEuclidean_fromVec (TensorState (A *ᵥ ψ) (B *ᵥ φ))‖
      = ‖toEuclidean_fromVec (A *ᵥ ψ)‖ * ‖toEuclidean_fromVec (B *ᵥ φ)‖ :=
    tensorState_l2_norm _ _
  have hvs : (s * ‖A‖ * ‖x‖) * (s * ‖B‖ * ‖y‖)
      < ‖toEuclidean_fromVec (A *ᵥ ψ)‖ * ‖toEuclidean_fromVec (B *ᵥ φ)‖ := by
    have hP : 0 ≤ s * ‖A‖ * ‖x‖ :=
      mul_nonneg (mul_nonneg hs0.le (norm_nonneg A)) (norm_nonneg x)
    have hQ : 0 ≤ s * ‖B‖ * ‖y‖ :=
      mul_nonneg (mul_nonneg hs0.le (norm_nonneg B)) (norm_nonneg y)
    have hX : 0 < ‖toEuclidean_fromVec (A *ᵥ ψ)‖ := lt_of_le_of_lt hP hx'
    have hY : 0 < ‖toEuclidean_fromVec (B *ᵥ φ)‖ := lt_of_le_of_lt hQ hy'
    calc (s * ‖A‖ * ‖x‖) * (s * ‖B‖ * ‖y‖)
        ≤ ‖toEuclidean_fromVec (A *ᵥ ψ)‖ * (s * ‖B‖ * ‖y‖) :=
          mul_le_mul_of_nonneg_right (le_of_lt hx') hQ
      _ < ‖toEuclidean_fromVec (A *ᵥ ψ)‖ * ‖toEuclidean_fromVec (B *ᵥ φ)‖ :=
          mul_lt_mul_of_pos_left hy' hX
  have hnx : 0 < ‖x‖ := by
    have hbound := l2_norm_mulVec_fromVec_le A ψ
    rw [hzx] at hbound
    have hlt : s * ‖A‖ * ‖x‖ < ‖A‖ * ‖x‖ := lt_of_lt_of_le hx' hbound
    rcases eq_or_lt_of_le (norm_nonneg x) with h0 | h0
    · exfalso
      rw [← h0] at hlt
      simp at hlt
    · exact h0
  have hny : 0 < ‖y‖ := by
    have hbound := l2_norm_mulVec_fromVec_le B φ
    rw [hzy] at hbound
    have hlt : s * ‖B‖ * ‖y‖ < ‖B‖ * ‖y‖ := lt_of_lt_of_le hy' hbound
    rcases eq_or_lt_of_le (norm_nonneg y) with h0 | h0
    · exfalso
      rw [← h0] at hlt
      simp at hlt
    · exact h0
  have hgoal : ‖A ⊗ₖ B‖ * ‖toEuclidean_fromVec (TensorState ψ φ)‖
      < ‖toEuclidean_fromVec ((A ⊗ₖ B) *ᵥ TensorState ψ φ)‖ := by
    rw [hact, hsplit, hznorm]
    have h2 : ‖A ⊗ₖ B‖ < s ^ 2 * (‖A‖ * ‖B‖) := by
      have hc : ‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖) * (‖A‖ * ‖B‖) = ‖A ⊗ₖ B‖ :=
        div_mul_cancel₀ _ (ne_of_gt hprod)
      calc ‖A ⊗ₖ B‖ = ‖A ⊗ₖ B‖ / (‖A‖ * ‖B‖) * (‖A‖ * ‖B‖) := hc.symm
        _ < s ^ 2 * (‖A‖ * ‖B‖) := mul_lt_mul_of_pos_right hs2 hprod
    calc ‖A ⊗ₖ B‖ * (‖x‖ * ‖y‖)
        < s ^ 2 * (‖A‖ * ‖B‖) * (‖x‖ * ‖y‖) :=
          mul_lt_mul_of_pos_right h2 (mul_pos hnx hny)
      _ = (s * ‖A‖ * ‖x‖) * (s * ‖B‖ * ‖y‖) := by ring
      _ < ‖toEuclidean_fromVec (A *ᵥ ψ)‖ * ‖toEuclidean_fromVec (B *ᵥ φ)‖ := hvs
  have hle := ContinuousLinearMap.le_opNorm
    ((Matrix.toEuclideanLin (𝕜 := ℂ) (m := O × P) (n := I × J)).trans
      LinearMap.toContinuousLinearMap (A ⊗ₖ B))
    (toEuclidean_fromVec (TensorState ψ φ))
  have hnAB : ‖((Matrix.toEuclideanLin (𝕜 := ℂ) (m := O × P) (n := I × J)).trans
      LinearMap.toContinuousLinearMap) (A ⊗ₖ B)‖ = ‖A ⊗ₖ B‖ :=
    (Matrix.l2_opNorm_def (𝕜 := ℂ) (m := O × P) (n := I × J) (A ⊗ₖ B)).symm
  rw [hnAB, toEuclideanCLMRect_apply] at hle
  exact absurd hle (not_le.mpr hgoal)

/-- The Euclidean operator norm of a Kronecker product equals the product of the factor norms. -/
theorem l2_norm_kronecker (A : Matrix O I ℂ) (B : Matrix P J ℂ) : ‖A ⊗ₖ B‖ = ‖A‖ * ‖B‖ :=
  le_antisymm (l2_norm_kronecker_le A B) (l2_norm_kronecker_ge A B)

/-- The identity matrix on a nonempty finite index type has Euclidean operator norm one. -/
theorem l2_norm_one_eq [Nonempty I] : ‖(1 : Matrix I I ℂ)‖ = 1 := by
  refine le_antisymm l2_norm_one_le ?_
  obtain ⟨i₀⟩ := ‹Nonempty I›
  have h :=
      l2_norm_mulVec_fromVec_le (1 : Matrix I I ℂ) (Qatlib.Foundations.PureStateMath.Ket i₀)
  rw [Matrix.one_mulVec] at h
  have hnorm : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i₀)‖ = 1 := by
    have hsq : ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i₀)‖ ^ 2 = 1 := by
      rw [norm_toEuclidean_fromVec_sq, Finset.sum_eq_single i₀]
      · simp
      · intro b _ hb
        simp [Qatlib.Foundations.PureStateMath.Ket, hb]
      · simp
    rcases (_root_.sq_eq_one_iff (a := ‖toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i₀)‖)).mp hsq with h1 | h1
    · exact h1
    · exact absurd h1 (by
        have := norm_nonneg (toEuclidean_fromVec (Qatlib.Foundations.PureStateMath.Ket i₀))
        linarith)
  rw [hnorm] at h
  nlinarith [h, norm_nonneg (1 : Matrix I I ℂ)]

/-- A unitary matrix on a nonempty finite index type has Euclidean operator norm one. -/
theorem l2_norm_unitary_eq_one [Nonempty I] {U : Matrix I I ℂ}
    (hU : U ∈ Matrix.unitaryGroup I ℂ) : ‖U‖ = 1 := by
  refine le_antisymm (l2_norm_unitary_le_one hU) ?_
  have hUU : U * Uᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using (Matrix.mem_unitaryGroup_iff.mp hU)
  have h1 : ‖(1 : Matrix I I ℂ)‖ ≤ ‖U‖ * ‖Uᴴ‖ := by
    calc ‖(1 : Matrix I I ℂ)‖ = ‖U * Uᴴ‖ := by rw [hUU]
      _ ≤ ‖U‖ * ‖Uᴴ‖ := Matrix.l2_opNorm_mul U Uᴴ
  have hU' : ‖Uᴴ‖ ≤ 1 := by
    refine l2_norm_unitary_le_one ?_
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_conjTranspose]
    exact hUU
  have h2 : ‖(1 : Matrix I I ℂ)‖ = 1 := l2_norm_one_eq
  rw [h2] at h1
  nlinarith [h1, hU', norm_nonneg U, l2_norm_unitary_le_one hU]

/-- A difference of Kronecker products with the same right factor is the Kronecker product of
the left-factor difference. -/
theorem kronecker_sub_left (A B : Matrix O I ℂ) (C : Matrix P J ℂ) :
    A ⊗ₖ C - B ⊗ₖ C = (A - B) ⊗ₖ C := by
  let _ := (inferInstance : Fintype O)
  let _ := (inferInstance : DecidableEq O)
  let _ := (inferInstance : Fintype I)
  let _ := (inferInstance : DecidableEq I)
  let _ := (inferInstance : Fintype P)
  let _ := (inferInstance : DecidableEq P)
  let _ := (inferInstance : Fintype J)
  let _ := (inferInstance : DecidableEq J)
  ext x y
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Matrix.kronecker_apply, Matrix.sub_apply]
  ring

/-- A difference of Kronecker products with the same left factor is the Kronecker product of the
right-factor difference. -/
theorem kronecker_sub_right (C : Matrix O I ℂ) (B D : Matrix P J ℂ) :
    C ⊗ₖ B - C ⊗ₖ D = C ⊗ₖ (B - D) := by
  let _ := (inferInstance : Fintype O)
  let _ := (inferInstance : DecidableEq O)
  let _ := (inferInstance : Fintype I)
  let _ := (inferInstance : DecidableEq I)
  let _ := (inferInstance : Fintype P)
  let _ := (inferInstance : DecidableEq P)
  let _ := (inferInstance : Fintype J)
  let _ := (inferInstance : DecidableEq J)
  ext x y
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Matrix.kronecker_apply, Matrix.sub_apply]
  ring

/-- Decomposes a difference of two Kronecker products into a sum changing one factor at a time. -/
theorem kronecker_sub_add_decomp (A C : Matrix O I ℂ) (B D : Matrix P J ℂ) :
    A ⊗ₖ B - C ⊗ₖ D = (A - C) ⊗ₖ B + C ⊗ₖ (B - D) := by
  let _ := (inferInstance : Fintype O)
  let _ := (inferInstance : DecidableEq O)
  let _ := (inferInstance : Fintype I)
  let _ := (inferInstance : DecidableEq I)
  let _ := (inferInstance : Fintype P)
  let _ := (inferInstance : DecidableEq P)
  let _ := (inferInstance : Fintype J)
  let _ := (inferInstance : DecidableEq J)
  ext x y
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only [Matrix.kronecker_apply, Matrix.sub_apply, Matrix.add_apply]
  ring

/-- The Euclidean operator norm of a tensor gate equals the product of the operator norms of its
factors. -/
theorem l2_norm_tensorGate (A : Matrix I I ℂ) (B : Matrix J J ℂ) :
    ‖TensorGate A B‖ = ‖A‖ * ‖B‖ :=
  l2_norm_kronecker A B

/-- Subtracting tensor gates with a common right factor tensors the difference of the left
factors. -/
theorem tensorGate_sub_left (A B : Matrix I I ℂ) (V : Matrix J J ℂ) :
    TensorGate A V - TensorGate B V = TensorGate (A - B) V :=
  kronecker_sub_left A B V

/-- Subtracting tensor gates with a common left factor tensors the difference of the right
factors. -/
theorem tensorGate_sub_right (V : Matrix I I ℂ) (B D : Matrix J J ℂ) :
    TensorGate V B - TensorGate V D = TensorGate V (B - D) :=
  kronecker_sub_right V B D

/-- Tensoring an operator difference with the identity on a nonempty ancilla preserves its
Euclidean operator norm on either side. -/
theorem l2_tensor_ancilla_error [Nonempty J] (A B : Matrix I I ℂ) :
    ‖TensorGate A (1 : Matrix J J ℂ) - TensorGate B 1‖ = ‖A - B‖ ∧
      ‖TensorGate (1 : Matrix J J ℂ) A - TensorGate 1 B‖ = ‖A - B‖ := by
  constructor
  · rw [tensorGate_sub_left, l2_norm_tensorGate, l2_norm_one_eq, mul_one]
  · rw [tensorGate_sub_right, l2_norm_tensorGate, l2_norm_one_eq, one_mul]

/-- Bounds the norm of a difference of Kronecker products by `‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖`. -/
theorem l2_kronecker_two_factor_error (A C : Matrix O I ℂ) (B D : Matrix P J ℂ) :
    ‖A ⊗ₖ B - C ⊗ₖ D‖ ≤ ‖A - C‖ * ‖B‖ + ‖C‖ * ‖B - D‖ := by
  rw [kronecker_sub_add_decomp]
  refine (norm_add_le _ _).trans ?_
  rw [l2_norm_kronecker, l2_norm_kronecker]

end Kronecker

end Qatlib.Concepts.ReferenceError.RefTraceError
