/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RewindInfiniteStat
import Qatlib.Concepts.MixedInstrument.ClockBridge.MixedInstrumentClock
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.MixedInstrument.ClockBridge
open Qatlib.Concepts.QuantumGibbs.RejectionRewind

namespace Qatlib.Concepts.MixedInstrument.RewindAlgebra
open Matrix Filter
open scoped BigOperators ComplexOrder MatrixOrder Topology Matrix.Norms.L2Operator

theorem rewind_stopped_partial (D n : ℕ) (P Q : Operator D) (X : Operator D) :
    rewindStoppedMap P Q n X=rewindStoppedMap P Q 0 X+
      ∑ k ∈ Finset.range n,rewindSuccessRoundMap P Q k X := by
  simp only [rewindStoppedMap,Finset.range_zero,Finset.sum_empty,add_zero,
    LinearMap.add_apply,LinearMap.sum_apply]

theorem rewind_success_series_bound (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q) :
    MixedClockSeries.TraceSeriesBound (rewindSuccessRoundMap P Q) := by
  intro n X hX
  have hc := (rewindFiniteInstrument D P Q hPs hPi hQs hQi n).2.2.1 X
  have hf := complex_re_nonneg_of_le ((rewindFailureMap_cp D P Q n).positive hX).trace_nonneg
  have hz := complex_re_nonneg_of_le ((rewindStoppedMap_cp D P Q 0).positive hX).trace_nonneg
  simp only [LinearMap.add_apply] at hc
  rw [rewind_stopped_partial D n P Q X] at hc
  have hr := congrArg Complex.re hc
  simp only [Matrix.trace_add,Complex.add_re,
    Matrix.trace_sum,Complex.re_sum] at hr
  linarith

def rewindLimitMap (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q) :
    Operator D →ₗ[ℂ] Operator D :=
  rewindStoppedMap P Q 0+MixedClockSeries.cpSeriesLimit (rewindSuccessRoundMap P Q)
    (rewindSuccessRoundMap_cp D P Q) (rewind_success_series_bound D P Q hPs hPi hQs hQi)

theorem rewind_success_summable (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) : Summable (fun k => rewindSuccessRoundMap P Q k X) := by
  apply Pi.summable.mpr
  intro i
  apply Pi.summable.mpr
  intro j
  exact MixedClockSeries.cpSeries_entry_summable (rewindSuccessRoundMap P Q)
    (rewindSuccessRoundMap_cp D P Q) (rewind_success_series_bound D P Q hPs hPi hQs hQi) X i j

theorem rewind_limit_series (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) : rewindLimitMap D P Q hPs hPi hQs hQi X=
      rewindStoppedMap P Q 0 X+∑' k,rewindSuccessRoundMap P Q k X := by
  ext i j
  simp only [rewindLimitMap,LinearMap.add_apply,Matrix.add_apply,
    MixedClockSeries.cpSeriesLimit_apply]
  have hs := rewind_success_summable D P Q hPs hPi hQs hQi X
  congr 1
  change (∑' k,rewindSuccessRoundMap P Q k X i j)=
    (∑' k,(fun i j => rewindSuccessRoundMap P Q k X i j)) i j
  rw [Pi.tsum_apply hs, Pi.tsum_apply (Pi.summable.mp hs i)]

theorem rewind_stopped_tendsto (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) : Tendsto (fun n => rewindStoppedMap P Q n X) atTop
      (𝓝 (rewindLimitMap D P Q hPs hPi hQs hQi X)) := by
  have he : (fun n => rewindStoppedMap P Q n X)=
      (fun n => rewindStoppedMap P Q 0 X+∑ k ∈ Finset.range n,rewindSuccessRoundMap P Q k X) :=
    funext fun n => rewind_stopped_partial D n P Q X
  rw [he]
  simp only [rewindLimitMap,LinearMap.add_apply]
  exact tendsto_const_nhds.add (MixedClockSeries.cpSeriesLimit_tendsto (rewindSuccessRoundMap P Q)
    (rewindSuccessRoundMap_cp D P Q) (rewind_success_series_bound D P Q hPs hPi hQs hQi) X)

theorem rewind_limit_cp (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q) :
    CompletelyPositive (rewindLimitMap D P Q hPs hPi hQs hQi) :=
  (rewindStoppedMap_cp D P Q 0).add (MixedClockSeries.cpSeriesLimit_completelyPositive
    (rewindSuccessRoundMap P Q) (rewindSuccessRoundMap_cp D P Q)
    (rewind_success_series_bound D P Q hPs hPi hQs hQi))

theorem rewind_limit_sub_stopped (D n : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) :
    rewindLimitMap D P Q hPs hPi hQs hQi X-rewindStoppedMap P Q n X=
      Matrix.of fun i j => ∑' k,rewindSuccessRoundMap P Q (k+n) X i j := by
  rw [rewind_stopped_partial D n P Q X]
  ext i j
  simp only [rewindLimitMap,LinearMap.add_apply,
    Matrix.sub_apply,Matrix.add_apply,MixedClockSeries.cpSeriesLimit_apply,
    Matrix.sum_apply,Matrix.of_apply]
  have hs := Summable.sum_add_tsum_nat_add n
    (MixedClockSeries.cpSeries_entry_summable (rewindSuccessRoundMap P Q)
      (rewindSuccessRoundMap_cp D P Q) (rewind_success_series_bound D P Q hPs hPi hQs hQi) X i j)
  rw [← hs]
  abel

theorem rewind_limit_sub_stopped_psd (D n : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) (hX : X.PosSemidef) :
    (rewindLimitMap D P Q hPs hPi hQs hQi X-rewindStoppedMap P Q n X).PosSemidef := by
  rw [rewind_limit_sub_stopped]
  exact posSemidef_of_tsum_entries (fun k => (rewindSuccessRoundMap_cp D P Q (k+n)).positive hX)
    (fun i j => (summable_nat_add_iff n).mpr (MixedClockSeries.cpSeries_entry_summable
      (rewindSuccessRoundMap P Q) (rewindSuccessRoundMap_cp D P Q)
      (rewind_success_series_bound D P Q hPs hPi hQs hQi) X i j))

theorem rewind_failure_trace_tendsto (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) (hX : X.PosSemidef) :
    Tendsto (fun n => Matrix.trace (rewindFailureMap P Q n X)) atTop (𝓝 0) := by
  have hn : Tendsto (fun n : ℕ => (n:ℝ)+1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  have hd : Tendsto (fun n : ℕ => 2*((n:ℝ)+1)) atTop atTop := hn.const_mul_atTop (by norm_num)
  have hb : Tendsto (fun n : ℕ => (1/(2*((n:ℝ)+1)))*(Matrix.trace X).re) atTop (𝓝 0) := by
    simpa only [one_div,zero_mul] using!
        (tendsto_inv_atTop_zero.comp hd).mul_const (Matrix.trace X).re
  have hr : Tendsto (fun n => (Matrix.trace (rewindFailureMap P Q n X)).re) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun n => complex_re_nonneg_of_le ((rewindFailureMap_cp D P Q n).positive hX).trace_nonneg)
      (fun n => rewind_psd_tail D n P Q hPs hPi hQs hQi X hX)
  have he : (fun n => Matrix.trace (rewindFailureMap P Q n X))=
      (fun n => ((Matrix.trace (rewindFailureMap P Q n X)).re:ℂ)) := by
    funext n
    apply Complex.ext
    · rfl
    · simpa only [Complex.ofReal_im] using!
        (Complex.nonneg_iff.mp ((rewindFailureMap_cp D P Q n).positive hX).trace_nonneg).2.symm
  rw [he]
  simpa only [Complex.ofReal_zero] using! Complex.continuous_ofReal.continuousAt.tendsto.comp hr

theorem rewind_limit_trace_psd (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (X : Operator D) (hX : X.PosSemidef) :
    Matrix.trace (rewindLimitMap D P Q hPs hPi hQs hQi X)=Matrix.trace X := by
  have he : (fun n => Matrix.trace (rewindStoppedMap P Q n X))=
      (fun n => Matrix.trace X-Matrix.trace (rewindFailureMap P Q n X)) := by
    funext n
    have hc := (rewindFiniteInstrument D P Q hPs hPi hQs hQi n).2.2.1 X
    simp only [LinearMap.add_apply,Matrix.trace_add] at hc
    linear_combination hc
  have hl : Tendsto (fun n => Matrix.trace (rewindStoppedMap P Q n X)) atTop (𝓝 (Matrix.trace X)) := by
    rw [he]
    simpa only [sub_zero] using! tendsto_const_nhds.sub
      (rewind_failure_trace_tendsto D P Q hPs hPi hQs hQi X hX)
  exact tendsto_nhds_unique
      (tendsto_matrix_trace (rewind_stopped_tendsto D P Q hPs hPi hQs hQi X)) hl

theorem rewind_limit_tp (D : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q) :
    TracePreserving (rewindLimitMap D P Q hPs hPi hQs hQi) := by
  have he : (Matrix.traceLinearMap (Fin D) ℂ ℂ).comp (rewindLimitMap D P Q hPs hPi hQs hQi)=
      Matrix.traceLinearMap (Fin D) ℂ ℂ := by
    apply LinearMap.ext_on (s := {X : Operator D | 0 ≤ X}) CStarAlgebra.span_nonneg
    intro X hX
    exact rewind_limit_trace_psd D P Q hPs hPi hQs hQi X hX.posSemidef
  intro X
  exact congrArg (fun L : Operator D →ₗ[ℂ] ℂ => L X) he

theorem rewind_limit_tail (D n : ℕ) (P Q : Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (ρ : Operator D) (hρ : ρ.PosSemidef) (htr : Matrix.trace ρ=1) :
    Matrix.traceNorm (rewindLimitMap D P Q hPs hPi hQs hQi ρ-rewindStoppedMap P Q n ρ) ≤
      1/(2*((n:ℝ)+1)) := by
  have hpsd := rewind_limit_sub_stopped_psd D n P Q hPs hPi hQs hQi ρ hρ
  have hnorm : Matrix.traceNorm (rewindLimitMap D P Q hPs hPi hQs hQi ρ-rewindStoppedMap P Q n ρ)=
      (Matrix.trace (rewindLimitMap D P Q hPs hPi hQs hQi ρ-rewindStoppedMap P Q n ρ)).re := by
    simpa only [Complex.ofReal_re] using! congrArg Complex.re hpsd.traceNorm_eq_trace
  rw [hnorm,Matrix.trace_sub,rewind_limit_tp D P Q hPs hPi hQs hQi ρ,Complex.sub_re]
  have hc := (rewindFiniteInstrument D P Q hPs hPi hQs hQi n).2.2.1 ρ
  have hr := congrArg Complex.re hc
  simp only [LinearMap.add_apply,Matrix.trace_add,Complex.add_re] at hr
  have hb := rewindMixedTail D P Q hPs hPi hQs hQi ρ hρ htr n
  linarith

theorem rewindInfiniteCompletion : RewindInfiniteCompletion := by
  intro D P Q hPs hPi hQs hQi
  refine ⟨rewindLimitMap D P Q hPs hPi hQs hQi,?_,?_,
    rewind_limit_cp D P Q hPs hPi hQs hQi,rewind_limit_tp D P Q hPs hPi hQs hQi,?_⟩
  · intro X
    exact ⟨rewind_success_summable D P Q hPs hPi hQs hQi X,
      rewind_limit_series D P Q hPs hPi hQs hQi X⟩
  · exact rewind_stopped_tendsto D P Q hPs hPi hQs hQi
  · intro ρ hρ htr n
    exact rewind_limit_tail D n P Q hPs hPi hQs hQi ρ hρ htr

end Qatlib.Concepts.MixedInstrument.RewindAlgebra
