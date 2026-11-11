/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.NativeRecords.RawCurrentRecords
import Qatlib.Concepts.SpinorSampling.FiniteExecution.ElementaryReadout

open Qatlib.Foundations.QueryWordCore.Circuit

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.PureStateMath
open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

/-!
# Exact raw current moments for the paid two-copy comparator

The native instrument law supplies each observation. Branch selection, the
full physical trace, and finite rational scaling are separate obligations.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpinorSampling.Model
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.NativeRecords.RawCurrentRecords
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.FiniteExecution.ElementaryReadout

/-- The actual rescaled velocity-branch return on the two observed native current records; branch selection and paid execution are separate obligations. -/
def pairedCurrentRaw {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (l r : S × Bool) : ℝ := 8*residualCollision 1 0 (fun _ : S => 0) l r

/-- The raw return is literally the two native signs times the complete address-collision indicator, including unequal addresses. -/
theorem pairedCurrentRaw_literal {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (l r : S × Bool) :
    pairedCurrentRaw l r = if l.1=r.1 then
      8*(Fintype.card S : ℝ)*recordSign l.2*recordSign r.2 else 0 := by
  unfold pairedCurrentRaw residualCollision
  split_ifs <;> ring

/-- Each observed native sign has square one. -/
theorem recordSign_square (b : Bool) : (recordSign b)^2 = 1 := by
  cases b <;> norm_num [recordSign]

/-- The raw velocity return has its exact squared address-indicator form before any expectation. -/
theorem pairedCurrentRaw_square {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (l r : S × Bool) :
    (pairedCurrentRaw l r)^2 = if r.1=l.1 then 64*(Fintype.card S : ℝ)^2 else 0 := by
  rw [pairedCurrentRaw_literal]
  by_cases h : l.1=r.1
  · rw [ite_eq_left h, ite_eq_left h.symm]
    simp only [mul_pow, recordSign_square, mul_one]
    norm_num
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
    norm_num

/-- Two actual independent signed-record laws give the exact raw velocity mean; the law is the existing native-current consumer, not an assumed moment certificate. -/
theorem pairedCurrentRaw_mean {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) :
    (signedRecordLaw m hm).expect (fun l =>
      (signedRecordLaw m hm).expect (pairedCurrentRaw l)) =
      8*(∑ x, (m x)^2)/(Fintype.card S : ℝ) := by
  let p := signedRecordLaw m hm
  have scale (f : S × Bool → ℝ) (c : ℝ) :
      p.expect (fun x => c*f x) = c*p.expect f := by
    unfold FinDist.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    ring
  change p.expect (fun l => p.expect (pairedCurrentRaw l)) = _
  unfold pairedCurrentRaw
  simp_rw [scale]
  have h := residual_collision_unbiased m (fun _ : S => 0) 1 0 hm
  simp only [one_mul, zero_mul, sub_zero] at h
  rw [h]
  ring

/-- The conditional raw velocity second moment is exactly 64M for every first observed record and every normalized physical current mean. -/
theorem pairedCurrentRaw_conditional_second {S : Type*} [Fintype S] [Nonempty S]
    [DecidableEq S] (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) (l : S × Bool) :
    (signedRecordLaw m hm).expect (fun r => (pairedCurrentRaw l r)^2) =
      64*(Fintype.card S : ℝ) := by
  rw [show (fun r : S × Bool => (pairedCurrentRaw l r)^2) =
      (fun r => if r.1=l.1 then 64*(Fintype.card S : ℝ)^2 else 0) from
        funext (pairedCurrentRaw_square l)]
  change (∑ r : S × Bool, signedRecordWeight m r*
    (if r.1=l.1 then 64*(Fintype.card S : ℝ)^2 else 0)) = _
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_zero, Finset.sum_ite_irrel, Finset.sum_const_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.sum_mul, signed_record_cell_mass]
  have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The complete raw velocity second moment on two independent native-compatible records is exactly 64M, including collision misses. -/
theorem pairedCurrentRaw_second {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (m : S → ℝ) (hm : ∀ x, |m x| ≤ 1) :
    (signedRecordLaw m hm).expect (fun l =>
      (signedRecordLaw m hm).expect (fun r => (pairedCurrentRaw l r)^2)) =
      64*(Fintype.card S : ℝ) := by
  simp_rw [pairedCurrentRaw_conditional_second]
  unfold FinDist.expect
  rw [← Finset.sum_mul, (signedRecordLaw m hm).sum_one, one_mul]

/-- This raw mean is consumed by two actual native current instrument runs on the same supplied field, retaining the full original current contribution. -/
theorem native_pairedCurrentRaw_mean (d r : ℕ) (j : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    (nativeCurrentLaw d r j a b c k hz).expect (fun l =>
      (nativeCurrentLaw d r j a b c k hz).expect (pairedCurrentRaw l)) =
      8*siteMean (fun x => (spinorCurrentMean a b c k (periodicUnitShift d (2^r)) j x)^2) := by
  simp_rw [native_current_law_eq_signed]
  simpa only [siteMean, mul_div_assoc] using pairedCurrentRaw_mean
    (spinorCurrentMean a b c k (periodicUnitShift d (2^r)) j)
    (spinor_current_mean_bound a b c k hz (periodicUnitShift d (2^r)) j)

/-- The exact native velocity second moment is 64M for every point-normalized supplied field; no free copy, transfer or branch-selection cost is inferred from this moment lemma. -/
theorem native_pairedCurrentRaw_second (d r : ℕ) (j : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ)
    (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    (nativeCurrentLaw d r j a b c k hz).expect (fun l =>
      (nativeCurrentLaw d r j a b c k hz).expect (fun out => (pairedCurrentRaw l out)^2)) =
      64*(Fintype.card (Fin d → Fin (2^r)) : ℝ) := by
  simp_rw [native_current_law_eq_signed]
  exact pairedCurrentRaw_second _ _

/-- The current return is computed from exactly two actual complete-register observations of the same original supplied field. -/
def pairedCurrentPhysicalRaw (d r : ℕ)
    (z : (Bool × Qatlib.Foundations.PureStateMath.Reg (registerWidth d r)) ×
      (Bool × Qatlib.Foundations.PureStateMath.Reg (registerWidth d r))) : ℝ :=
  pairedCurrentRaw (velocityRecord d r z.1.1 z.1.2) (velocityRecord d r z.2.1 z.2.2)

/-- The raw physical two-run return has the actual full current mean, without a supplied marginal or moment certificate. -/
theorem pairedCurrentPhysicalRaw_mean (d r : ℕ) (j : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    (independentPairLaw (nativeCurrentRawLaw d r j a b c k hz)
      (nativeCurrentRawLaw d r j a b c k hz)).expect (pairedCurrentPhysicalRaw d r) =
        8*siteMean (fun x => (spinorCurrentMean a b c k (periodicUnitShift d (2^r)) j x)^2) := by
  unfold pairedCurrentPhysicalRaw
  rw [nativeCurrentRawLaw_pair_expect]
  exact native_pairedCurrentRaw_mean d r j a b c k hz

/-- The identical raw physical return has second moment 64M over the same full two-run Born outcomes and neighbor coins. -/
theorem pairedCurrentPhysicalRaw_second (d r : ℕ) (j : Fin d)
    (a b c k : (Fin d → Fin (2^r)) → ℝ) (hz : ∀ x, a x^2+b x^2+c x^2+k x^2=1) :
    (independentPairLaw (nativeCurrentRawLaw d r j a b c k hz)
      (nativeCurrentRawLaw d r j a b c k hz)).expect (fun z => (pairedCurrentPhysicalRaw d r z)^2) =
        64*(Fintype.card (Fin d → Fin (2^r)) : ℝ) := by
  unfold pairedCurrentPhysicalRaw
  rw [nativeCurrentRawLaw_pair_expect d r j a b c k hz (fun l out => (pairedCurrentRaw l out)^2)]
  exact native_pairedCurrentRaw_second d r j a b c k hz

/-- Each observed two-run current branch pays its actual elementary words selected by those same two coins, including the extra T-dagger gates. -/
theorem pairedCurrentPhysicalRaw_gates (d r : ℕ) (j : Fin d) (hr : 2≤r)
    (z : (Bool × Qatlib.Foundations.PureStateMath.Reg (registerWidth d r)) ×
      (Bool × Qatlib.Foundations.PureStateMath.Reg (registerWidth d r))) :
    GateCount (paidNativeProgram (velocityWord d r j z.1.1))+
      GateCount (paidNativeProgram (velocityWord d r j z.2.1)) = 2*(15*(r-1)^2+5) ∧
    QueryCount (paidNativeProgram (velocityWord d r j z.1.1))+
      QueryCount (paidNativeProgram (velocityWord d r j z.2.1))=0 := by
  have h1 := paid_velocity_program_counts d r j z.1.1 hr
  have h2 := paid_velocity_program_counts d r j z.2.1 hr
  rw [h1.1,h2.1,h1.2,h2.2]
  omega

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
