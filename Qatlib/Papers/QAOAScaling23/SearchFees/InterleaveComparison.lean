/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QAOAScaling23.SearchFees.PlainSlot
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical ENNReal
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.FairRandomBits.FiniteCoinExecution
open Qatlib.Concepts.WalkSearch.QuantumAccess
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
namespace Qatlib.Papers.QAOAScaling23.SearchFees
variable {I:Type} [Fintype I] [DecidableEq I]

theorem fail_le_one (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (m:ℕ) : fail U hU seed S valid m≤1 := by
  have h:=event_compl (preparedAASampled U hU seed S (Nat.clog 2 m) m 3) (searchSlotFail valid)
  exact (le_add_right le_rfl).trans h.le

theorem slot_stages (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I) (m:ℕ) :
    slot U hU seed S .stages m=1 := by
  simpa only [slot,increment,Nat.cast_one] using
      expectation_const (preparedAASampled U hU seed S (Nat.clog 2 m) m 3) 1

theorem plain_slot_le_one (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I) (f:Fee) :
    slot U hU seed S f 1≤1 := by
  have h:=plain_five_fees U hU seed S
  cases f with
  | phase=>rw [h.1];exact zero_le
  | bits=>rw [h.2.1];exact zero_le
  | validation=>rw [h.2.2.1]
  | prepare=>rw [h.2.2.2.1]
  | gates=>rw [h.2.2.2.2]
  | stages=>rw [slot_stages]

theorem interleave_expected_le_original (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (f:Fee) (ms:List ℕ) :
    expected U hU seed S valid f (interleavePlain ms)≤
      expected U hU seed S valid f ms+expected U hU seed S valid .stages ms := by
  induction ms with
  | nil=>simp [interleavePlain,expected_nil]
  | cons m ms ih=>
    rw [interleaved_expected_cons,expected_cons,expected_cons,slot_stages]
    calc
      _ ≤ 1+1*(slot U hU seed S f m+fail U hU seed S valid m*
          (expected U hU seed S valid f ms+expected U hU seed S valid .stages ms)) :=
        add_le_add (plain_slot_le_one U hU seed S f)
          (mul_le_mul' (fail_le_one U hU seed S valid 1)
            (add_le_add le_rfl (mul_le_mul_right ih (fail U hU seed S valid m))))
      _ = _ := by ring

theorem slot_prepare_formula (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (m:ℕ) (hm:0<m) :
    slot U hU seed S .prepare m=(1-(coinRejectMass (Nat.clog 2 m) m)^3)*(m:ℝ≥0∞) := by
  have hp:=(prepared_aa_sampled_input_access_ledger U seed S hU (Nat.clog 2 m) m 3 hm
    (Nat.le_pow_clog (by norm_num : 1<2) m)).1
  refine (expectation_congr (fun out:Option (I×ℕ)×ℕ×ℕ=>?_)).trans hp
  rcases out with ⟨a,b,c⟩
  cases a <;>rfl

theorem one_le_twice_slot_prepare (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (m:ℕ) (hm:0<m) : 1≤2*slot U hU seed S .prepare m := by
  let q:=coinRejectMass (Nat.clog 2 m) m
  have hq:q≤1/2 := (finite_coin_effective_cutoff m 3 hm).2.1
  have hq1:q≤1 := hq.trans (by norm_num)
  have hp:q^3≤(1/2:ℝ≥0∞) := by
    calc
      _ = q*q*q := by ring
      _ ≤ (1/2:ℝ≥0∞)*1*1 := mul_le_mul' (mul_le_mul' hq hq1) hq1
      _ = _ := by simp
  have hhalf : (1/2:ℝ≥0∞)=1-(1/2:ℝ≥0∞) :=
    ENNReal.eq_sub_of_add_eq (by finiteness) (by
      calc
        (1/2:ℝ≥0∞)+(1/2:ℝ≥0∞)=2*(2:ℝ≥0∞)⁻¹ := by simp only [div_eq_mul_inv,one_mul];ring
        _ = 1 := ENNReal.mul_inv_cancel (by norm_num) (by finiteness))
  have ha:(1/2:ℝ≥0∞)≤1-q^3 := hhalf.le.trans (tsub_le_tsub_left hp 1)
  rw [slot_prepare_formula U hU seed S m hm]
  have hm1:(1:ℝ≥0∞)≤m := by exact_mod_cast hm
  calc
    (1:ℝ≥0∞) = 2*((1/2:ℝ≥0∞)*1) := by
      simp only [div_eq_mul_inv,one_mul,mul_one]
      exact (ENNReal.mul_inv_cancel (by norm_num) (by finiteness)).symm
    _ ≤ _ := mul_le_mul_right (mul_le_mul' ha hm1) 2

theorem stages_le_twice_prepare (U:Matrix I I ℂ) (hU:U∈Matrix.unitaryGroup I ℂ) (seed:I) (S:Finset I)
    (valid:I→Bool) (ms:List ℕ) (hms:∀m∈ms,0<m) :
    expected U hU seed S valid .stages ms≤2*expected U hU seed S valid .prepare ms := by
  induction ms with
  | nil=>simp [expected_nil]
  | cons m ms ih=>
    have hm:0<m:=hms m (by simp)
    have ht:∀n∈ms,0<n:=fun n hn=>hms n (by simp [hn])
    rw [expected_cons,slot_stages,expected_cons]
    calc
      _ ≤ 2*slot U hU seed S .prepare m+fail U hU seed S valid m*(2*expected U hU seed S valid .prepare ms) :=
        add_le_add (one_le_twice_slot_prepare U hU seed S m hm) (mul_le_mul_right (ih ht) _)
      _ = _ := by ring
end Qatlib.Papers.QAOAScaling23.SearchFees
