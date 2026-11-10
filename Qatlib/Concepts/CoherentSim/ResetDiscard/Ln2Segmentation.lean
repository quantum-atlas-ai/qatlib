/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.CoherentSim.ResetDiscard.Ln2Definitions
import Qatlib.Concepts.CoherentSim.ResetDiscard.ResetDiscardSegmentation
import Qatlib.Concepts.CoherentSim.FactorialTaylor.FactorialTaylorSimulation
import Mathlib.Analysis.Complex.ExponentialBounds
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.OperatorErrors.Robustness Qatlib.Concepts.CoherentSim.FactorialTaylor

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.BlockEncoding.StateBlockEncoding

set_option autoImplicit false
namespace Qatlib.Concepts.CoherentSim.ResetDiscard
open Matrix
open scoped Classical BigOperators ComplexOrder Matrix.Norms.L2Operator

theorem truncatedSegment_zero {I : Type*} [Fintype I] [DecidableEq I]
    (H : Matrix I I ℂ) (K : ℕ) : truncatedSegment H 0 K=1 := by
  unfold truncatedSegment
  rw [Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [zero_pow hk]
  · simp

theorem ln2Scale_ge_one (K : ℕ) : 1 ≤ ln2Scale K := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hs := Finset.single_le_sum (s := Finset.range (K+1))
    (f := fun k => Real.log 2^k/(k.factorial : ℝ))
    (fun k _ => div_nonneg (pow_nonneg hl _) (Nat.cast_nonneg _))
    (show 0 ∈ Finset.range (K+1) by simp)
  simpa only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one] using! hs

theorem ln2Scale_gt_three_halves (K : ℕ) (hK : 1 ≤ K) : 3/2 < ln2Scale K := by
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hsub : ({0,1} : Finset ℕ) ⊆ Finset.range (K+1) := by
    intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact Finset.mem_range.mpr (by omega)
    · exact Finset.mem_range.mpr (by omega)
  have hs := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => Real.log 2^k/(k.factorial : ℝ))
    hsub (fun k _ _ => div_nonneg (pow_nonneg hl _) (Nat.cast_nonneg _))
  have he : (∑ k ∈ ({0,1} : Finset ℕ), Real.log 2^k/(k.factorial : ℝ))=1+Real.log 2 := by
    norm_num
  rw [he] at hs
  change 1+Real.log 2 ≤ ln2Scale K at hs
  linarith [Real.log_two_gt_d9]

theorem ln2_raw_zero_time_error (J : Type*) [Fintype J] [DecidableEq J]
    (K : ℕ) (hK : 1 ≤ K) (W : Matrix (J × Unit) (J × Unit) ℂ) (j₀ : J)
    (hW : IsBlockEncoding W j₀ (truncatedSegment (0 : Matrix Unit Unit ℂ) 0 K) (ln2Scale K)) :
    1/4 < Matrix.traceNorm (ResetDiscardStep W j₀ (1 : Matrix Unit Unit ℂ)-1) := by
  let s := ln2Scale K
  have hs : 3/2 < s := ln2Scale_gt_three_halves K hK
  have hspos : 0 < s := by linarith
  rw [truncatedSegment_zero] at hW
  have hi : s⁻¹ ≤ (2/3 : ℝ) := by
    rw [inv_eq_one_div]
    exact (div_le_iff₀ hspos).mpr (by linarith)
  have hi2 : s⁻¹^2 ≤ (4/9 : ℝ) := by
    calc
      _ ≤ (2/3 : ℝ)^2 := pow_le_pow_left₀ (inv_nonneg.mpr hspos.le) hi 2
      _ = _ := by norm_num
  have hstep : ResetDiscardStep W j₀ (1 : Matrix Unit Unit ℂ)=((s⁻¹^2 : ℝ) : ℂ) • 1 := by
    rw [resetDiscardStep_encoding_scalar W j₀ 1 s hW,
      Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one]
  have ht : Matrix.trace (ResetDiscardStep W j₀ (1 : Matrix Unit Unit ℂ)-1)=
      ((s⁻¹^2-1 : ℝ) : ℂ) := by
    rw [hstep, Matrix.trace_sub, Matrix.trace_smul]
    simp [Matrix.trace]
  have hn := Matrix.abs_trace_le_traceNorm
    (ResetDiscardStep W j₀ (1 : Matrix Unit Unit ℂ)-1)
  rw [ht, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith : s⁻¹^2-1 < 0)] at hn
  linarith

theorem ln2_tail_five_le :
    (∑' j : ℕ, Real.log 2^(5+1+j)/((5+1+j).factorial : ℝ)) ≤ (1/4 : ℝ)/69 := by
  have hl0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hl1 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hh := (factorial_taylor_tail_and_coherent_precision.1 (Real.log 2) 5 hl0 hl1).2
  have hp := pow_le_pow_left₀ hl0 hl1 6
  norm_num at hp
  norm_num only [Nat.factorial, Nat.cast_ofNat, Nat.reduceAdd, Nat.reduceMul] at hh
  have hbound : 2*Real.log 2^6/720 ≤ (1/4 : ℝ)/69 := by nlinarith
  exact hh.trans hbound

theorem ln2_identity_encoding_exists (K : ℕ) (_hK : 1 ≤ K) :
    ∃ W : Matrix (Bool × Unit) (Bool × Unit) ℂ,
      IsBlockEncoding W false (1 : Matrix Unit Unit ℂ) (ln2Scale K) :=
  scaled_identity_encoding_exists (ln2Scale K) (ln2Scale_ge_one K)

theorem ln2Segmentation_obstruction : ¬Ln2Segmentation.{0,0} := by
  intro h
  obtain ⟨W,hW⟩ := ln2_identity_encoding_exists 5 (by norm_num)
  have hr : max 1 (Nat.ceil ((1 : ℝ)*0/Real.log 2))=1 := by norm_num
  have hencoding : IsBlockEncoding W false
      (truncatedSegment (0 : Matrix Unit Unit ℂ)
        (0/(max 1 (Nat.ceil ((1 : ℝ)*0/Real.log 2)))) 5) (ln2Scale 5) := by
    simpa only [zero_div, truncatedSegment_zero] using! hW
  have htail : (∑' j : ℕ, Real.log 2^(5+1+j)/((5+1+j).factorial : ℝ)) ≤
      (1/4 : ℝ)/(69*(max 1 (Nat.ceil ((1 : ℝ)*0/Real.log 2)))) := by
    simpa only [hr, Nat.cast_one, mul_one] using! ln2_tail_five_le
  have hh := h Unit (0 : Matrix Unit Unit ℂ) 0 (1/4) 1 5 Bool W false
    Matrix.isHermitian_zero (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) hencoding htail
    (1 : Matrix Unit Unit ℂ) Matrix.PosSemidef.one (by simp [Matrix.trace])
  simp only [hr, Function.iterate_one] at hh
  have he : HamiltonianEvolution (0 : Matrix Unit Unit ℂ) 0=1 := by simp [HamiltonianEvolution]
  rw [he, Matrix.one_mul, Matrix.conjTranspose_one, Matrix.mul_one] at hh
  have hlower := ln2_raw_zero_time_error Bool 5 (by norm_num) W false
    (by simpa only [truncatedSegment_zero] using! hW)
  exact (not_le_of_gt hlower) hh

end Qatlib.Concepts.CoherentSim.ResetDiscard
