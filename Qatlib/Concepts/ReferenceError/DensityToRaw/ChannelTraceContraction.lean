/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.ChannelTheory.Stinespring.PhyslibChannels
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.ReferenceError.DensityToRaw
namespace HermitianSplit

open Matrix
open scoped ComplexOrder

noncomputable def posPart {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) *
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

noncomputable def negPart {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : Matrix n n ℂ :=
  (hA.eigenvectorUnitary : Matrix n n ℂ) *
      Matrix.diagonal (fun i => ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ)) *
    (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ

theorem hermitian_eq_unitary_diagonal_conjTranspose
    {n : Type*} [Fintype n] [DecidableEq n] {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix n n ℂ) *
        Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
      (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
  exact hA.spectral_theorem

private theorem max_add_max_neg (l : ℝ) : max l 0 + max (-l) 0 = |l| := by
  rcases le_total l 0 with h | h
  · have h1 : max l 0 = 0 := max_eq_right h
    have h2 : max (-l) 0 = -l := max_eq_left (show (0:ℝ) ≤ -l by linarith)
    have h3 : |l| = -l := abs_of_nonpos h
    linarith
  · have h1 : max l 0 = l := max_eq_left h
    have h2 : max (-l) 0 = 0 := max_eq_right (show (-l:ℝ) ≤ 0 by linarith)
    have h3 : |l| = l := abs_of_nonneg h
    linarith

private theorem nonneg_max_right (l : ℝ) : 0 ≤ max l 0 := by
  rcases le_total l 0 with h | h
  · have h1 : max l 0 = 0 := max_eq_right h
    rw [h1]
  · have h1 : max l 0 = l := max_eq_left h
    rw [h1]; exact h

private theorem posPart_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (posPart hA).PosSemidef := by
  refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg.mpr (nonneg_max_right _)

private theorem negPart_posSemidef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : (negPart hA).PosSemidef := by
  refine (Matrix.posSemidef_diagonal_iff.mpr ?_).mul_mul_conjTranspose_same _
  intro i
  exact RCLike.ofReal_nonneg.mpr (nonneg_max_right _)

private theorem diagonal_sub_eq {n : Type*} [Fintype n] [DecidableEq n]
    (f g h : n → ℂ) (hfg : ∀ i, f i - g i = h i) :
    Matrix.diagonal f - Matrix.diagonal g = Matrix.diagonal h := by
  rw [Matrix.diagonal_sub]
  congr 1
  funext i
  exact hfg i

theorem sub_posPart_negPart {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) : posPart hA - negPart hA = A := by
  have hpoint : ∀ i : n,
      (((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) - (((max (-hA.eigenvalues i) 0 : ℝ) : ℂ))
        = (((hA.eigenvalues i : ℝ) : ℂ)) := by
    intro i
    rcases le_total (hA.eigenvalues i) 0 with h | h
    · have h1 : max (hA.eigenvalues i) 0 = 0 := max_eq_right h
      have h2 : max (-hA.eigenvalues i) 0 = -hA.eigenvalues i := max_eq_left (by linarith)
      rw [h1, h2]; push_cast; ring
    · have h1 : max (hA.eigenvalues i) 0 = hA.eigenvalues i := max_eq_left h
      have h2 : max (-hA.eigenvalues i) 0 = 0 := max_eq_right (by linarith)
      rw [h1, h2]; push_cast; ring
  have hstep : posPart hA - negPart hA
      = (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (Matrix.diagonal (fun i => ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) -
            Matrix.diagonal (fun i => ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ))) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    unfold posPart negPart
    refine Eq.trans (Matrix.sub_mul _ _ _).symm ?_
    rw [Matrix.mul_sub]
  have hfac : (hA.eigenvectorUnitary : Matrix n n ℂ) *
          (Matrix.diagonal (fun i => ((max (hA.eigenvalues i) 0 : ℝ) : ℂ)) -
            Matrix.diagonal (fun i => ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ))) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ
      = (hA.eigenvectorUnitary : Matrix n n ℂ) *
          Matrix.diagonal (fun i => ((hA.eigenvalues i : ℝ) : ℂ)) *
        (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ := by
    rw [diagonal_sub_eq _ _ _ hpoint]
  exact hstep.trans hfac |>.trans (hermitian_eq_unitary_diagonal_conjTranspose hA).symm

private theorem trace_unitary_conjTranspose_mul
    {n : Type*} [Fintype n] [DecidableEq n] (U D : Matrix n n ℂ) (hU : Uᴴ * U = 1) :
    Matrix.trace (U * D * Uᴴ) = Matrix.trace D := by
  have h1 : (U * D * Uᴴ).trace = (Uᴴ * U * D).trace := Matrix.trace_mul_cycle U D Uᴴ
  rw [h1, hU, Matrix.one_mul]

private theorem trace_posPart {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Matrix.trace (posPart hA) = ∑ i, ((max (hA.eigenvalues i) 0 : ℝ) : ℂ) := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  have htrace : Matrix.trace (posPart hA) = Matrix.trace
      (Matrix.diagonal (fun i => ((max (hA.eigenvalues i) 0 : ℝ) : ℂ))) := by
    unfold posPart
    exact trace_unitary_conjTranspose_mul _ _ hU
  rw [htrace, Matrix.trace_diagonal]

private theorem trace_negPart {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    Matrix.trace (negPart hA) = ∑ i, ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ) := by
  have hU : (hA.eigenvectorUnitary : Matrix n n ℂ)ᴴ * (hA.eigenvectorUnitary : Matrix n n ℂ) = 1 :=
    Matrix.UnitaryGroup.star_mul_self hA.eigenvectorUnitary
  have htrace : Matrix.trace (negPart hA) = Matrix.trace
      (Matrix.diagonal (fun i => ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ))) := by
    unfold negPart
    exact trace_unitary_conjTranspose_mul _ _ hU
  rw [htrace, Matrix.trace_diagonal]

theorem traceNorm_sub_posPart_negPart {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) :
    A.traceNorm = (posPart hA).traceNorm + (negPart hA).traceNorm := by
  have hP : (posPart hA).traceNorm = ∑ i, max (hA.eigenvalues i) 0 := by
    have hc : ((posPart hA).traceNorm : ℂ)
        = ∑ i, ((max (hA.eigenvalues i) 0 : ℝ) : ℂ) := by
      rw [show ((posPart hA).traceNorm : ℂ) = (posPart hA).trace from
        (posPart_posSemidef hA).traceNorm_eq_trace, trace_posPart hA]
    simpa using congrArg Complex.re hc
  have hN : (negPart hA).traceNorm = ∑ i, max (-hA.eigenvalues i) 0 := by
    have hc : ((negPart hA).traceNorm : ℂ)
        = ∑ i, ((max (-hA.eigenvalues i) 0 : ℝ) : ℂ) := by
      rw [show ((negPart hA).traceNorm : ℂ) = (negPart hA).trace from
        (negPart_posSemidef hA).traceNorm_eq_trace, trace_negPart hA]
    simpa using congrArg Complex.re hc
  have habs' : (∑ i, max (hA.eigenvalues i) 0) + (∑ i, max (-hA.eigenvalues i) 0)
      = ∑ i, |hA.eigenvalues i| := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ => max_add_max_neg (hA.eigenvalues i))
  rw [Matrix.traceNorm_Hermitian_eq_sum_abs_eigenvalues hA, hP, hN]
  exact habs'.symm

end HermitianSplit

open Matrix
open scoped ComplexOrder

variable {D E : ℕ}

private theorem real_of_complex_eq {a b : ℝ} (h : (a : ℂ) = b) : a = b := by
  simpa using congrArg Complex.re h

theorem channel_hermitian_trace_contraction
    {D E : ℕ} (T : QuantumChannel D E) {X : Operator D} (hX : X.IsHermitian) :
    (T.map X).traceNorm ≤ X.traceNorm := by
  have hcp : CompletelyPositive T.map := T.completelyPositive
  have htp : TracePreserving T.map := T.tracePreserving
  have hsplit := HermitianSplit.traceNorm_sub_posPart_negPart hX
  have hsub := HermitianSplit.sub_posPart_negPart hX
  have hpos : (T.map (HermitianSplit.posPart hX)).PosSemidef :=
    hcp.positive (HermitianSplit.posPart_posSemidef hX)
  have hneg : (T.map (HermitianSplit.negPart hX)).PosSemidef :=
    hcp.positive (HermitianSplit.negPart_posSemidef hX)
  have hposP : (HermitianSplit.posPart hX).PosSemidef :=
    HermitianSplit.posPart_posSemidef hX
  have hnegN : (HermitianSplit.negPart hX).PosSemidef :=
    HermitianSplit.negPart_posSemidef hX
  have hnormP : (T.map (HermitianSplit.posPart hX)).traceNorm
      = (HermitianSplit.posPart hX).traceNorm :=
    real_of_complex_eq (hpos.traceNorm_eq_trace.trans
      ((htp (HermitianSplit.posPart hX)).trans hposP.traceNorm_eq_trace.symm))
  have hnormN : (T.map (HermitianSplit.negPart hX)).traceNorm
      = (HermitianSplit.negPart hX).traceNorm :=
    real_of_complex_eq (hneg.traceNorm_eq_trace.trans
      ((htp (HermitianSplit.negPart hX)).trans hnegN.traceNorm_eq_trace.symm))
  have hTS : T.map X = T.map (HermitianSplit.posPart hX)
      - T.map (HermitianSplit.negPart hX) := by
    rw [(congrArg T.map hsub).symm, T.map.map_sub]
  have hsub' : (T.map (HermitianSplit.posPart hX) - T.map (HermitianSplit.negPart hX))
      = T.map (HermitianSplit.posPart hX) + -T.map (HermitianSplit.negPart hX) :=
    sub_eq_add_neg _ _
  have h1 : (T.map (HermitianSplit.posPart hX) - T.map (HermitianSplit.negPart hX)).traceNorm
      ≤ (T.map (HermitianSplit.posPart hX)).traceNorm
        + (T.map (HermitianSplit.negPart hX)).traceNorm := by
    have hh := Matrix.traceNorm_add_le (T.map (HermitianSplit.posPart hX))
      (-T.map (HermitianSplit.negPart hX))
    rw [Matrix.traceNorm_neg, ← hsub'] at hh
    exact hh
  have hle : (T.map X).traceNorm
      ≤ (T.map (HermitianSplit.posPart hX)).traceNorm
        + (T.map (HermitianSplit.negPart hX)).traceNorm := by
    rw [hTS]
    linarith [h1]
  linarith [hle, hnormP, hnormN, hsplit]

theorem amplification_trace {D E : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (htp : TracePreserving T) (r : ℕ) (A : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    Matrix.trace (ChannelAmplification T r A) = Matrix.trace A := by
  have hstep : ∀ a : Fin r,
      (∑ i, T (fun x y => A (a, x) (a, y)) i i) = ∑ i, A (a, i) (a, i) := by
    intro a
    have h := htp (fun x y => A (a, x) (a, y))
    rwa [Matrix.trace] at h
  simp only [Matrix.trace, Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun a _ => hstep a

theorem amplification_sub {D E r : ℕ} (T : Operator D →ₗ[ℂ] Operator E)
    (A B : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ) :
    ChannelAmplification T r (A - B)
      = ChannelAmplification T r A - ChannelAmplification T r B := by
  ext p q
  simp only [ChannelAmplification, Matrix.sub_apply]
  have h := T.map_sub (fun i j => A (p.1, i) (q.1, j)) (fun i j => B (p.1, i) (q.1, j))
  exact congrArg (fun M : Operator E => M p.2 q.2) h

theorem channel_reference_hermitian_trace_contraction
    {D E r : ℕ} (T : QuantumChannel D E)
    {X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ} (hX : X.IsHermitian) :
    (ChannelAmplification T.map r X).traceNorm ≤ X.traceNorm := by
  have hcp : CompletelyPositive T.map := T.completelyPositive
  have htp : TracePreserving T.map := T.tracePreserving
  have hsplit := HermitianSplit.traceNorm_sub_posPart_negPart hX
  have hsub := HermitianSplit.sub_posPart_negPart hX
  have hpos : (ChannelAmplification T.map r (HermitianSplit.posPart hX)).PosSemidef :=
    hcp r _ (HermitianSplit.posPart_posSemidef hX)
  have hneg : (ChannelAmplification T.map r (HermitianSplit.negPart hX)).PosSemidef :=
    hcp r _ (HermitianSplit.negPart_posSemidef hX)
  have hposP : (HermitianSplit.posPart hX).PosSemidef :=
    HermitianSplit.posPart_posSemidef hX
  have hnegN : (HermitianSplit.negPart hX).PosSemidef :=
    HermitianSplit.negPart_posSemidef hX
  have hnormP : (ChannelAmplification T.map r (HermitianSplit.posPart hX)).traceNorm
      = (HermitianSplit.posPart hX).traceNorm :=
    real_of_complex_eq (hpos.traceNorm_eq_trace.trans
      ((amplification_trace T.map htp r _).trans hposP.traceNorm_eq_trace.symm))
  have hnormN : (ChannelAmplification T.map r (HermitianSplit.negPart hX)).traceNorm
      = (HermitianSplit.negPart hX).traceNorm :=
    real_of_complex_eq (hneg.traceNorm_eq_trace.trans
      ((amplification_trace T.map htp r _).trans hnegN.traceNorm_eq_trace.symm))
  have hA : ChannelAmplification T.map r X
      = ChannelAmplification T.map r (HermitianSplit.posPart hX)
        - ChannelAmplification T.map r (HermitianSplit.negPart hX) := by
    rw [(congrArg (ChannelAmplification T.map r) hsub).symm, amplification_sub]
  have hsub' : (ChannelAmplification T.map r (HermitianSplit.posPart hX)
        - ChannelAmplification T.map r (HermitianSplit.negPart hX))
      = ChannelAmplification T.map r (HermitianSplit.posPart hX)
        + -ChannelAmplification T.map r (HermitianSplit.negPart hX) :=
    sub_eq_add_neg _ _
  have h1 : (ChannelAmplification T.map r (HermitianSplit.posPart hX)
        - ChannelAmplification T.map r (HermitianSplit.negPart hX)).traceNorm
      ≤ (ChannelAmplification T.map r (HermitianSplit.posPart hX)).traceNorm
        + (ChannelAmplification T.map r (HermitianSplit.negPart hX)).traceNorm := by
    have hh := Matrix.traceNorm_add_le
      (ChannelAmplification T.map r (HermitianSplit.posPart hX))
      (-ChannelAmplification T.map r (HermitianSplit.negPart hX))
    rw [Matrix.traceNorm_neg, ← hsub'] at hh
    exact hh
  have hle : (ChannelAmplification T.map r X).traceNorm
      ≤ (ChannelAmplification T.map r (HermitianSplit.posPart hX)).traceNorm
        + (ChannelAmplification T.map r (HermitianSplit.negPart hX)).traceNorm := by
    rw [hA]
    linarith [h1]
  linarith [hle, hnormP, hnormN, hsplit]

theorem positive_trace_preserving_hermitian_trace_contraction
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (T : MatrixMap I J ℂ) (hpos : T.IsPositive) (htp : T.IsTracePreserving)
    {X : Matrix I I ℂ} (hX : X.IsHermitian) : (T X).traceNorm ≤ X.traceNorm := by
  have hp := HermitianSplit.posPart_posSemidef hX
  have hn := HermitianSplit.negPart_posSemidef hX
  have hnp : (T (HermitianSplit.posPart hX)).traceNorm =
      (HermitianSplit.posPart hX).traceNorm :=
    real_of_complex_eq ((hpos hp).traceNorm_eq_trace.trans
      ((htp _).trans hp.traceNorm_eq_trace.symm))
  have hnn : (T (HermitianSplit.negPart hX)).traceNorm =
      (HermitianSplit.negPart hX).traceNorm :=
    real_of_complex_eq ((hpos hn).traceNorm_eq_trace.trans
      ((htp _).trans hn.traceNorm_eq_trace.symm))
  conv_lhs => rw [← HermitianSplit.sub_posPart_negPart hX, map_sub]
  calc
    _ ≤ (T (HermitianSplit.posPart hX)).traceNorm +
        (T (HermitianSplit.negPart hX)).traceNorm := by
      simpa only [sub_eq_add_neg, Matrix.traceNorm_neg] using
        Matrix.traceNorm_add_le (T (HermitianSplit.posPart hX))
          (-T (HermitianSplit.negPart hX))
    _ = X.traceNorm := by
      rw [hnp, hnn, ← HermitianSplit.traceNorm_sub_posPart_negPart hX]

theorem channel_reference_hermitian_preserving
    {D E r : ℕ} (T : QuantumChannel D E)
    {X : Matrix (Fin r × Fin D) (Fin r × Fin D) ℂ} (hX : X.IsHermitian) :
    (ChannelAmplification T.map r X).IsHermitian := by
  have hp := T.completelyPositive r _ (HermitianSplit.posPart_posSemidef hX)
  have hn := T.completelyPositive r _ (HermitianSplit.negPart_posSemidef hX)
  have he := congrArg (ChannelAmplification T.map r) (HermitianSplit.sub_posPart_negPart hX)
  rw [amplification_sub] at he
  rw [← he]
  exact hp.isHermitian.sub hn.isHermitian

theorem traceRight_hermitian_trace_contraction
    {I J : Type} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    (X : Matrix (I × J) (I × J) ℂ) (hX : X.IsHermitian) :
    (Matrix.traceRight X).traceNorm ≤ X.traceNorm := by
  have h := positive_trace_preserving_hermitian_trace_contraction
    (CPTPMap.traceRight (d₁ := I) (d₂ := J)).toLinearMap
    (CPTPMap.traceRight (d₁ := I) (d₂ := J)).pos
    (CPTPMap.traceRight (d₁ := I) (d₂ := J)).TP hX
  convert! h using 1
end Qatlib.Concepts.ReferenceError.DensityToRaw
