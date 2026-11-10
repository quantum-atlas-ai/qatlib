/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.MonteCarloInt20.MainResults.SequentialStore
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
open Qatlib.Concepts.MatrixAccess.RitzPipeline
open scoped BigOperators Classical
open Matrix
open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.AmplitudeCore.PayoffMedian
open Qatlib.Papers.MonteCarloInt20.MainResults.SequentialStore
open Qatlib.Papers.MonteCarloInt20.MainResults.TermCode
open Qatlib.Papers.MonteCarloInt20.MainResults.FlagRotation
open Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel
open Qatlib.Papers.MonteCarloInt20.PrnJump.Lcg
open Qatlib.Concepts.HspRecovery.RecordExtract

namespace Qatlib.Papers.MonteCarloInt20.MainResults.SumCode

def clipped (p : ℕ) (v : Reg (p+1)) : ℕ := min (2^p) (booleanWordLSBValue (p+1) v)

theorem decode_clipped (p : ℕ) (v : Reg (p+1)) : decodeCode p v=(clipped p v:ℝ)/(2^p:ℝ) := by
  have hp : (0:ℝ)<2^p := by positivity
  by_cases h : booleanWordLSBValue (p+1) v≤2^p
  · rw [clipped,Nat.min_eq_right h,decodeCode,min_eq_right]
    exact (div_le_one hp).2 (by exact_mod_cast h)
  · have h' : 2^p≤booleanWordLSBValue (p+1) v := by omega
    rw [clipped,Nat.min_eq_left h',decodeCode,min_eq_left]
    · simpa only [Nat.cast_pow,Nat.cast_ofNat] using! (div_self (ne_of_gt hp)).symm
    · exact (one_le_div hp).2 (by exact_mod_cast h')

def sumCode {d p : ℕ} (v : Codes d p) : ℕ := ∑ i : Reg d,clipped p (v i)

theorem sumCode_bound {d p : ℕ} (v : Codes d p) : sumCode v≤2^(d+p) := by
  calc
    _ ≤ ∑ _i : Reg d,2^p := Finset.sum_le_sum (fun _ _ => min_le_left _ _)
    _ = 2^(d+p) := by simp [Reg,pow_add]

def sumBits {d p : ℕ} (v : Codes d p) : Reg (d+p+1) :=
  Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits.ofNat (d+p+1) (sumCode v)

theorem sumBits_value {d p : ℕ} (v : Codes d p) : booleanWordLSBValue (d+p+1) (sumBits v)=sumCode v := by
  rw [sumBits,Qatlib.Papers.MonteCarloInt20.PrnJump.Kernel.ReductionCore.Bits.ofNat_value]
  apply Nat.mod_eq_of_lt
  have h := sumCode_bound v
  have hp : 0<2^(d+p) := by positivity
  rw [pow_succ]
  omega

def decodeSum (d p : ℕ) (v : Reg (d+p+1)) : ℝ := (booleanWordLSBValue (d+p+1) v:ℝ)/(2^p:ℝ)

theorem decode_sumBits {d p : ℕ} (v : Codes d p) : decodeSum d p (sumBits v)=∑ i : Reg d,decodeCode p (v i) := by
  simp_rw [decodeSum,sumBits_value,decode_clipped]
  rw [← Finset.sum_div]
  norm_cast

def sumUpdate {d p : ℕ} (v : Codes d p × Reg (d+p+1)) : Codes d p × Reg (d+p+1) :=
  (v.1,fun b => v.2 b ^^ sumBits v.1 b)

theorem sumUpdate_involutive (d p : ℕ) : Function.Involutive (sumUpdate (d:=d) (p:=p)) := by
  intro v
  apply Prod.ext
  · rfl
  · funext b
    simp [sumUpdate]

def sumGate (d p : ℕ) : Matrix (Codes d p × Reg (d+p+1)) (Codes d p × Reg (d+p+1)) ℂ :=
    permMatrix sumUpdate

theorem sumGate_unitary (d p : ℕ) : sumGate d p ∈ unitaryGroup (Codes d p × Reg (d+p+1)) ℂ :=
  permMatrix_unitary (sumUpdate_involutive d p)

theorem sumGate_clean {d p : ℕ} (v : Codes d p) :
    ApplyGate (sumGate d p) (Ket (v,ZeroStr (d+p+1)))=Ket (v,sumBits v) := by
  rw [sumGate,applyGate_permMatrix_ket (sumUpdate_involutive d p)]
  simp only [sumUpdate,ZeroStr,Bool.false_xor]

theorem sum_payoff_basis {d p : ℕ} (v : Codes d p) (g : ℝ → ℝ) :
    ApplyGate (TensorGate (sumGate d p).conjTranspose 1*
      payoffRotation (fun q : Codes d p × Reg (d+p+1) => g (decodeSum d p q.2))*TensorGate (sumGate d p) 1)
      (Ket ((v,ZeroStr (d+p+1)),false))=
      TensorState (Ket (v,ZeroStr (d+p+1))) (flagState (g (∑ i : Reg d,decodeCode p (v i)))) := by
  have h := compute_rotate_uncompute_basis (sumGate d p) (sumGate_unitary d p)
    (v,ZeroStr (d+p+1)) (v,sumBits v) (sumGate_clean v)
    (fun q : Codes d p × Reg (d+p+1) => g (decodeSum d p q.2))
  simpa only [decode_sumBits] using! h

theorem sum_payoff_unitary (d p : ℕ) (g : ℝ → ℝ)
    (hg : ∀ q : Reg (d+p+1),g (decodeSum d p q) ∈ Set.Icc (0:ℝ) 1) :
    TensorGate (sumGate d p).conjTranspose 1*
      payoffRotation (fun q : Codes d p × Reg (d+p+1) => g (decodeSum d p q.2))*TensorGate (sumGate d p) 1 ∈
      unitaryGroup ((Codes d p × Reg (d+p+1)) × Bool) ℂ :=
  (unitaryGroup ((Codes d p × Reg (d+p+1)) × Bool) ℂ).mul_mem
    ((unitaryGroup ((Codes d p × Reg (d+p+1)) × Bool) ℂ).mul_mem
      (tensorGate_unitary (conjTranspose_mem_unitaryGroup (sumGate_unitary d p)) (unitaryGroup Bool ℂ).one_mem)
      (payoffRotation_mem_unitaryGroup _ (fun q => hg q.2)))
    (tensorGate_unitary (sumGate_unitary d p) (unitaryGroup Bool ℂ).one_mem)

end Qatlib.Papers.MonteCarloInt20.MainResults.SumCode
