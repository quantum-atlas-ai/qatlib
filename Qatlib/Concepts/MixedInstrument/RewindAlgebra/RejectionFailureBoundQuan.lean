/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundStat
import Qatlib.Concepts.WalkSearch.Spectral.CompleteCSDecomposition
import Qatlib.Concepts.BlockEncoding.Postselection
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding

open Qatlib.Concepts.Execution.WorkspaceCP
open Qatlib.Foundations.InstrumentCore.ProjectiveMeasurement
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.WalkSearch.Spectral

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Matrix Qatlib.Concepts.BlockEncoding
open Qatlib.Concepts.BlockEncoding.Encoding
open Qatlib.Concepts.BlockEncoding.Postselection.Encoding
open scoped Classical BigOperators

theorem rejection_geometric_bound (x : ℝ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (n : ℕ) :
    (1 - x) * x ^ n ≤ 1 / (n + 1) := by
  have hsum : ((n + 1 : ℕ) : ℝ) * x ^ n ≤ ∑ j ∈ Finset.range (n + 1), x ^ j := by
    calc
      _ = ∑ _j ∈ Finset.range (n + 1), x ^ n := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro j hj
        exact pow_le_pow_of_le_one hx0 hx1 (by simpa using Finset.mem_range.mp hj)
  have hm := mul_le_mul_of_nonneg_right hsum (sub_nonneg.mpr hx1)
  rw [geom_sum_mul_neg] at hm
  have hp : 0 ≤ x ^ (n + 1) := pow_nonneg hx0 _
  apply (le_div_iff₀ (by positivity : 0 < (n + 1 : ℝ))).2
  push_cast at hm
  nlinarith only [hm,hp]

theorem rejection_scalar_bound (t : ℝ) (ht : t ∈ Set.Icc 0 1) (n : ℕ) :
    t * (1 - t) * (t ^ 2 + (1 - t) ^ 2) ^ n ≤ 1 / (2 * (n + 1)) := by
  have hx0 : 0 ≤ t ^ 2 + (1 - t) ^ 2 := by positivity
  have hx1 : t ^ 2 + (1 - t) ^ 2 ≤ 1 := by nlinarith [ht.1,ht.2]
  have hh := rejection_geometric_bound _ hx0 hx1 n
  have he : 1 - (t ^ 2 + (1 - t) ^ 2) = 2 * (t * (1 - t)) := by ring
  rw [he] at hh
  have hd : 0 < (n + 1 : ℝ) := by positivity
  have heq : 1 / (2 * (n + 1 : ℝ)) = (1 / (n + 1 : ℝ)) / 2 := by
    field_simp
  rw [heq]
  linarith

def rejectionEigenFactor (t : ℝ) (s : Bool) : ℝ := if s then 1 - t else t

theorem rejection_raw_round {H J : Type} [Fintype H] [DecidableEq H]
    [Fintype J] [DecidableEq J] (P Q : Matrix H H ℂ)
    (hQ : IsOrthogonalProjector Q) (A : Matrix H J ℂ) (t : J → ℝ)
    (hA : IsIsometry A) (hP : A * Aᴴ = P)
    (ht : Aᴴ * Q * A = diagonal (fun i => (t i : ℂ))) (s : Bool) :
    ((1 - P) * (if s then Q else 1 - Q) * (1 - P)) * csCrossRaw Q A t =
      csCrossRaw Q A t * diagonal (fun i => (rejectionEigenFactor (t i) s : ℂ)) := by
  let R := diagonal (fun i => (t i : ℂ))
  let B := csCrossRaw Q A t
  have hdiag : Aᴴ * (Q * A) = R := by simpa only [Matrix.mul_assoc] using ht
  have hAB : Aᴴ * B = 0 := by
    change Aᴴ * (Q*A-A*R) = 0
    rw [Matrix.mul_sub,← Matrix.mul_assoc Aᴴ A R,show Aᴴ*A=1 from hA,
      Matrix.one_mul,hdiag]
    exact sub_self _
  have hPB : P * B = 0 := by rw [← hP,Matrix.mul_assoc,hAB,Matrix.mul_zero]
  have hNB : (1 - P) * B = B := by rw [Matrix.sub_mul,Matrix.one_mul,hPB,sub_zero]
  have hNQA : (1 - P) * (Q * A) = B := by
    rw [Matrix.sub_mul,Matrix.one_mul,← hP,Matrix.mul_assoc,hdiag]
    rfl
  have hNQB : (1 - P) * (Q * B) = B * (1 - R) := by
    change (1-P)*(Q*(Q*A-A*R)) = B*(1-R)
    rw [Matrix.mul_sub,← Matrix.mul_assoc Q Q A,hQ.1,← Matrix.mul_assoc Q A R,
      Matrix.mul_sub,← Matrix.mul_assoc (1-P) (Q*A) R,hNQA,
      Matrix.mul_sub,Matrix.mul_one]
  have hdiag1 : diagonal (fun i => ((1 - t i : ℝ) : ℂ)) = 1 - R := by
    ext i j
    by_cases hij : i=j <;> simp [R,hij]
  cases s with
  | true =>
    change ((1-P)*Q*(1-P))*B = B*diagonal (fun i => ((1-t i : ℝ) : ℂ))
    rw [Matrix.mul_assoc, hNB, Matrix.mul_assoc]
    rw [hNQB,← hdiag1]
  | false =>
    change ((1-P)*(1-Q)*(1-P))*B = B*R
    rw [Matrix.mul_assoc,hNB,Matrix.mul_assoc,Matrix.sub_mul 1 Q B,Matrix.one_mul,
      Matrix.mul_sub,hNB,hNQB,
      Matrix.mul_sub,Matrix.mul_one]
    change B - (B - B * R) = B * R
    abel

theorem rejection_raw_word {D : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (P Q : Operator D) (hQ : IsOrthogonalProjector Q) (A : Matrix (Fin D) J ℂ)
    (t : J → ℝ) (hA : IsIsometry A) (hP : A * Aᴴ = P)
    (ht : Aᴴ * Q * A = diagonal (fun i => (t i : ℂ))) (n : ℕ) (s : Fin n → Bool) :
    rejectWord P Q n s * csCrossRaw Q A t = csCrossRaw Q A t *
      diagonal (fun i => ((∏ j, rejectionEigenFactor (t i) (s j) : ℝ) : ℂ)) := by
  induction n with
  | zero => simp [rejectWord]
  | succ n ih =>
    rw [rejectWord,Fin.foldr_succ]
    change (rejectRound P Q (s 0) * rejectWord P Q n (fun j => s j.succ)) *
      csCrossRaw Q A t = _
    rw [Matrix.mul_assoc,ih,← Matrix.mul_assoc]
    have hr : rejectRound P Q (s 0) * csCrossRaw Q A t = csCrossRaw Q A t *
        diagonal (fun i => (rejectionEigenFactor (t i) (s 0) : ℂ)) :=
      rejection_raw_round P Q hQ A t hA hP ht (s 0)
    rw [hr,Matrix.mul_assoc,Matrix.diagonal_mul_diagonal]
    congr 1
    ext i j
    simp [Fin.prod_univ_succ,Complex.ofReal_mul]

theorem rejection_raw_norm {H J : Type} [Fintype H] [DecidableEq H]
    [Fintype J] [DecidableEq J] (B : Matrix H J ℂ) (t : J → ℝ)
    (hgram : Bᴴ * B = diagonal (fun i => ((t i * (1 - t i) : ℝ) : ℂ)))
    (z : QState J) :
    (Qatlib.Foundations.PureStateMath.Inner (B *ᵥ z) (B *ᵥ z)).re = ∑ i, t i * (1 - t i) * ‖z i‖ ^ 2 := by
  rw [inner_mulVec_left_rect,Matrix.mulVec_mulVec,hgram]
  have he : Qatlib.Foundations.PureStateMath.Inner z ((diagonal (fun i => ((t i * (1 - t i) : ℝ) : ℂ))) *ᵥ z) =
      ∑ i, ((t i * (1 - t i) * ‖z i‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_apply]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Matrix.mulVec_diagonal,Complex.ofReal_mul]
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_eq_conj_mul_self]
    ring
  rw [he,← Complex.ofReal_sum,Complex.ofReal_re]

theorem rejection_word_sum (t : ℝ) (n : ℕ) :
    (∑ s : Fin n → Bool, (∏ j, rejectionEigenFactor t (s j)) ^ 2) =
      (t ^ 2 + (1 - t) ^ 2) ^ n := by
  simp_rw [← Finset.prod_pow]
  rw [← (Fintype.prod_sum (fun _j : Fin n => fun b : Bool => rejectionEigenFactor t b ^ 2))]
  simp [rejectionEigenFactor,add_comm]

theorem rejection_raw_start {D : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (P Q : Operator D) (A : Matrix (Fin D) J ℂ) (t : J → ℝ)
    (hP : A * Aᴴ = P) (ht : Aᴴ * Q * A = diagonal (fun i => (t i : ℂ)))
    (ψ : QState (Fin D)) (hψ : P *ᵥ ψ = ψ) :
    (1 - P) *ᵥ ((1 - Q) *ᵥ ψ) = -(csCrossRaw Q A t *ᵥ (Aᴴ *ᵥ ψ)) := by
  let z := Aᴴ *ᵥ ψ
  have hAz : A *ᵥ z = ψ := by
    change A *ᵥ (Aᴴ *ᵥ ψ) = ψ
    rw [Matrix.mulVec_mulVec,hP,hψ]
  have hNψ : (1-P)*ᵥψ=0 := by simp [Matrix.sub_mulVec,hψ]
  have hNQA : (1-P)*(Q*A)=csCrossRaw Q A t := by
    rw [Matrix.sub_mul,Matrix.one_mul,← hP,Matrix.mul_assoc,← Matrix.mul_assoc Aᴴ Q A,ht]
    rfl
  have hNQψ : (1-P)*ᵥ(Q*ᵥψ)=csCrossRaw Q A t*ᵥz := by
    calc
      _ = (1-P)*ᵥ(Q*ᵥ(A*ᵥz)) := by rw [hAz]
      _ = _ := by rw [Matrix.mulVec_mulVec,Matrix.mulVec_mulVec,Matrix.mul_assoc,hNQA]
  rw [Matrix.sub_mulVec 1 Q ψ,Matrix.one_mulVec,Matrix.mulVec_sub,hNψ,zero_sub,hNQψ]

theorem rejection_failure_spectral_formula {D : ℕ} {J : Type} [Fintype J] [DecidableEq J]
    (P Q : Operator D) (hQ : IsOrthogonalProjector Q) (A : Matrix (Fin D) J ℂ)
    (t : J → ℝ) (hA : IsIsometry A) (hP : A * Aᴴ = P)
    (ht : Aᴴ * Q * A = diagonal (fun i => (t i : ℂ)))
    (ψ : QState (Fin D)) (hψ : P *ᵥ ψ = ψ) (n : ℕ) :
    rejectFailProb P Q ψ n = ∑ i, t i * (1-t i) *
      (t i ^ 2 + (1-t i) ^ 2) ^ n * ‖(Aᴴ *ᵥ ψ) i‖ ^ 2 := by
  let z := Aᴴ *ᵥ ψ
  have hgram : (csCrossRaw Q A t)ᴴ*csCrossRaw Q A t =
      diagonal (fun i => ((t i*(1-t i) : ℝ) : ℂ)) :=
    cs_cross_raw_gram Q hQ A t hA (by change Aᴴ*Q*A=_; exact ht)
  have hstate (s : Fin n → Bool) :
      rejectWord P Q n s *ᵥ ((1-P)*ᵥ((1-Q)*ᵥψ)) =
      -(csCrossRaw Q A t *ᵥ ((diagonal (fun i =>
        ((∏ j, rejectionEigenFactor (t i) (s j) : ℝ) : ℂ))) *ᵥ z)) := by
    rw [rejection_raw_start P Q A t hP ht ψ hψ,Matrix.mulVec_neg,
      Matrix.mulVec_mulVec,rejection_raw_word P Q hQ A t hA hP ht,
      ← Matrix.mulVec_mulVec]
  have hnorm (s : Fin n → Bool) :
      (Qatlib.Foundations.PureStateMath.Inner (-(csCrossRaw Q A t *ᵥ ((diagonal (fun i =>
        ((∏ j, rejectionEigenFactor (t i) (s j) : ℝ) : ℂ))) *ᵥ z)))
        (-(csCrossRaw Q A t *ᵥ ((diagonal (fun i =>
        ((∏ j, rejectionEigenFactor (t i) (s j) : ℝ) : ℂ))) *ᵥ z)))).re =
      ∑ i, t i*(1-t i)*(∏ j, rejectionEigenFactor (t i) (s j)) ^ 2*‖z i‖ ^ 2 := by
    rw [show ∀ x : QState (Fin D), Qatlib.Foundations.PureStateMath.Inner (-x) (-x)=Qatlib.Foundations.PureStateMath.Inner x x from
      fun x => by simp [Qatlib.Foundations.PureStateMath.Inner],rejection_raw_norm _ t hgram]
    apply Finset.sum_congr rfl
    intro i _hi
    simp only [Matrix.mulVec_diagonal,norm_mul,Complex.norm_real,
      Real.norm_eq_abs,mul_pow,sq_abs]
    ring
  unfold rejectFailProb
  simp_rw [hstate,hnorm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [← Finset.sum_mul,← Finset.mul_sum,rejection_word_sum]

theorem rejection_failure_bound_all_rounds (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (ψ : QState (Fin D)) (hnorm : Qatlib.Foundations.PureStateMath.Inner ψ ψ=1) (hψ : P*ᵥψ=ψ) (n : ℕ) :
    rejectFailProb P Q ψ n ≤ 1/(2*(n+1)) := by
  have hP : IsOrthogonalProjector P := ⟨hPi,hPs⟩
  have hQ : IsOrthogonalProjector Q := ⟨hQi,hQs⟩
  obtain ⟨A,t,hb,hA,hAP,ht⟩ := cs_projector_compressed_eigenframe P Q hP hQ
  have ht' : Aᴴ*Q*A=diagonal (fun i => (t i : ℂ)) := by exact ht
  rw [rejection_failure_spectral_formula P Q hQ A t hA hAP ht' ψ hψ n]
  let z := Aᴴ *ᵥ ψ
  have hAz : A *ᵥ z = ψ := by
    change A *ᵥ (Aᴴ *ᵥ ψ) = ψ
    rw [Matrix.mulVec_mulVec,hAP,hψ]
  have hznorm : ∑ i, ‖z i‖ ^ 2 = 1 := by
    have he := Qatlib.Concepts.BlockEncoding.Postselection.Encoding.IsIsometry.inner_mulVec hA z z
    change Qatlib.Foundations.PureStateMath.Inner (A*ᵥz)
        (A*ᵥz)=Qatlib.Foundations.PureStateMath.Inner z z at he
    rw [hAz,hnorm] at he
    have hr := congrArg Complex.re he
    rw [inner_self,← Complex.ofReal_sum,Complex.ofReal_re] at hr
    exact hr.symm
  calc
    _ ≤ ∑ i, (1/(2*(n+1 : ℝ))) * ‖z i‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _hi
      exact mul_le_mul_of_nonneg_right (rejection_scalar_bound (t i) (hb i) n) (sq_nonneg _)
    _ = _ := by rw [← Finset.mul_sum,hznorm,mul_one]

theorem rejectionFailureBound : RejectionFailureBound := by
  intro D P Q hPs hPi hQs hQi ψ hnorm hψ n _hn
  exact rejection_failure_bound_all_rounds D P Q hPs hPi hQs hQi ψ hnorm hψ n

theorem rejectFailProb_nonneg {D : ℕ} (P Q : Operator D) (ψ : QState (Fin D)) (n : ℕ) :
    0 ≤ rejectFailProb P Q ψ n := by
  unfold rejectFailProb
  apply Finset.sum_nonneg
  intro s _hs
  rw [inner_self,← Complex.ofReal_sum,Complex.ofReal_re]
  exact Finset.sum_nonneg (fun _i _hi => sq_nonneg _)

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
