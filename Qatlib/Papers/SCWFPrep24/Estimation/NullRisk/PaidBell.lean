/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell
import Qatlib.Papers.SCWFPrep24.Estimation.NullRisk.Checkerboard
import Qatlib.Concepts.StoppingCore.InterruptBridge.QuerySpaceExtensions

set_option backward.isDefEq.respectTransparency false

open Qatlib.Foundations.QueryWordCore.Circuit

open Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Foundations.PureStateMath.BornBridge

open Qatlib.Foundations.PureStateMath

/-!
# Actual paid pair captures and Bell records

Both physical three-CX captures occur on every branch. The final Bell word
is skipped on an address miss, while all outcomes remain in the normalized
law. Exact moments and expected test gates use that same observation law.
-/

set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators
namespace Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
open Qatlib
open Qatlib.Concepts.SpinorSampling.NativeRecords.ShiftCircuit
open Qatlib.Concepts.SpinorSampling.NativeRecords.NativeBridge
open Qatlib.Concepts.SpinorSampling.Retained.RetainedSpin
open Qatlib.Concepts.SpinorSampling.Retained.NativeCapture
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.SpinorSampling.Model

open Qatlib.Concepts.SpinorSampling.Retained.PhysicalBell

/-- The full normalized native output law after the two captures is retained also on misses; only its numerical return is zero there. -/
def postCaptureLaw (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1)
    (matched : Bool) : FinDist (Reg 2) where
  prob r := BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ)
    (postCaptureProgram matched) (pairInput u v)) r
  nonneg r := sq_nonneg _
  sum_one := by
    cases matched with
    | false =>
      change Normalized (pairInput u v)
      exact pair_input_normalized u v hu hv
    | true =>
      change Normalized (Run (1 : Matrix (Reg 2) (Reg 2) ℂ) bellProgram (pairInput u v))
      exact bell_program_unitary.normalized_run (by simp) (pair_input_normalized u v hu hv)

/-- The actual local spin amplitude after measuring one supplied address retains the original source normalization. -/
def suppliedSpinAt {S : Type*} [Fintype S] (ψ : S → Bool → ℂ) (x : S) (b : Bool) : ℂ :=
  suppliedSpinState (real0 ψ) (imag0 ψ) (real1 ψ) (imag1 ψ) b x

/-- The complete two-capture source state has exactly the original 1/M pair amplitude, including all address outcomes. -/
theorem twoCapturedSpins_source_scale {S : Type*} [Fintype S]
    (ψ : S → Bool → ℂ) (x y : S) :
    twoCapturedSpins (suppliedSpinAt ψ x) (suppliedSpinAt ψ y) =
      (Fintype.card S : ℂ)⁻¹ • pairInput (ψ x) (ψ y) := by
  rw [twoCapturedSpins_eq]
  have hs : (Real.sqrt (Fintype.card S : ℝ) : ℂ)^2=(Fintype.card S : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card S))
  funext r
  simp only [pairInput, suppliedSpinAt, suppliedSpinState, complexSpinor_parts,
    Pi.smul_apply, smul_eq_mul]
  rw [div_mul_div_comm, ← pow_two, hs]
  ring

/-- The joint observed address-and-Born law includes every capture and mismatch, with actual normalized conditional native outcomes. -/
def pairedBellLaw {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (ψ : S → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1) (τ : S → S) :
    FinDist (S × S × Reg 2) where
  prob z := (postCaptureLaw (ψ z.1) (ψ z.2.1) (hψ z.1) (hψ z.2.1)
    (decide (z.2.1=τ z.1))).prob z.2.2/(Fintype.card S : ℝ)^2
  nonneg z := div_nonneg (FinDist.nonneg _ _) (sq_nonneg _)
  sum_one := by
    simp only [Fintype.sum_prod_type, ← Finset.sum_div]
    have he : (∑ x : S, ∑ y : S, ∑ r : Reg 2,
        (postCaptureLaw (ψ x) (ψ y) (hψ x) (hψ y) (decide (y=τ x))).prob r) =
        (Fintype.card S : ℝ)^2 := by
      calc _ = ∑ _ : S, ∑ _ : S, (1 : ℝ) := by
             apply Finset.sum_congr rfl
             intro x _
             apply Finset.sum_congr rfl
             intro y _
             exact (postCaptureLaw (ψ x) (ψ y) (hψ x) (hψ y) (decide (y=τ x))).sum_one
           _ = _ := by simp [nsmul_eq_mul, pow_two]
    rw [he]
    have hM : (Fintype.card S : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact div_self (pow_ne_zero 2 hM)

/-- Every joint probability is literally the Born weight of the two actual sequential three-CX source captures followed by the actual conditional Bell-or-skip word. -/
theorem pairedBellLaw_actual_Born {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (ψ : S → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1) (τ : S → S)
    (z : S × S × Reg 2) :
    (pairedBellLaw ψ hψ τ).prob z =
      BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ)
        (postCaptureProgram (decide (z.2.1=τ z.1)))
        (twoCapturedSpins (suppliedSpinAt ψ z.1) (suppliedSpinAt ψ z.2.1))) z.2.2 := by
  rw [twoCapturedSpins_source_scale,
    Qatlib.Concepts.StoppingCore.InterruptBridge.run_smul]
  simp only [pairedBellLaw, postCaptureLaw, BornProb, Pi.smul_apply, smul_eq_mul,
    Complex.sq_norm, Complex.normSq_mul, map_inv₀, Complex.normSq_natCast]
  ring

/-- The numerical return is an actual native Bell hit multiplied by the public coefficient, and is zero on every mismatch. -/
def postCaptureScore (matched : Bool) (C : ℝ) (r : Reg 2) : ℝ :=
  if matched then if isBellHit r=true then C else 0 else 0

/-- The exact conditional return mean follows from the actual native singlet Born amplitude. -/
theorem postCaptureScore_mean (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1)
    (matched : Bool) (C : ℝ) :
    (postCaptureLaw u v hu hv matched).expect (postCaptureScore matched C) =
      if matched then C*bellProbability u v else 0 := by
  cases matched with
  | false => simp [FinDist.expect, postCaptureScore]
  | true =>
    change (∑ r : Reg 2, BornProb (Run (1 : Matrix (Reg 2) (Reg 2) ℂ)
      bellProgram (pairInput u v)) r*(if isBellHit r=true then C else 0)) = _
    simp_rw [is_bell_hit_iff]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    rw [bell_program_hit_probability]
    ring

/-- The finite native return has its exact squared-value identity, including misses. -/
theorem postCaptureScore_square (matched : Bool) (C : ℝ) (r : Reg 2) :
    (postCaptureScore matched C r)^2=C*postCaptureScore matched C r := by
  unfold postCaptureScore
  split_ifs <;> ring

/-- The conditional second moment uses the same actual outcomes and numerical return as the first moment. -/
theorem postCaptureScore_second (u v : Bool → ℂ) (hu : qubitMass u=1) (hv : qubitMass v=1)
    (matched : Bool) (C : ℝ) :
    (postCaptureLaw u v hu hv matched).expect (fun r => (postCaptureScore matched C r)^2) =
      if matched then C^2*bellProbability u v else 0 := by
  simp_rw [postCaptureScore_square]
  have he : (postCaptureLaw u v hu hv matched).expect
      (fun r => C*postCaptureScore matched C r) =
        C*(postCaptureLaw u v hu hv matched).expect (postCaptureScore matched C) := by
    unfold FinDist.expect
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring
  rw [he, postCaptureScore_mean]
  cases matched with
  | false => simp
  | true =>
    simp only [ite_true]
    ring

/-- The observed two-address return includes every miss and uses the very same post-capture native hit. -/
def pairedBellScore {S : Type*} [DecidableEq S] (τ : S → S) (C : ℝ)
    (z : S × S × Reg 2) : ℝ := postCaptureScore (decide (z.2.1=τ z.1)) C z.2.2

/-- The exact unconditional finite two-capture mean sums only matching contributions without rejecting any physical run. -/
theorem pairedBellScore_mean {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (ψ : S → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1) (τ : S → S) (C : ℝ) :
    (pairedBellLaw ψ hψ τ).expect (pairedBellScore τ C) =
      C*(∑ x, bellProbability (ψ x) (ψ (τ x)))/(Fintype.card S : ℝ)^2 := by
  unfold FinDist.expect pairedBellLaw pairedBellScore
  simp only [Fintype.sum_prod_type]
  have he (x y : S) :
      (∑ r : Reg 2, (postCaptureLaw (ψ x) (ψ y) (hψ x) (hψ y)
        (decide (y=τ x))).prob r/(Fintype.card S : ℝ)^2*
          postCaptureScore (decide (y=τ x)) C r) =
      (if y=τ x then C*bellProbability (ψ x) (ψ y) else 0)/(Fintype.card S : ℝ)^2 := by
    have h := postCaptureScore_mean (ψ x) (ψ y) (hψ x) (hψ y) (decide (y=τ x)) C
    unfold FinDist.expect at h
    simp only [Bool.decide_iff] at h
    calc _ = (∑ r : Reg 2, (postCaptureLaw (ψ x) (ψ y) (hψ x) (hψ y)
            (decide (y=τ x))).prob r*postCaptureScore (decide (y=τ x)) C r)/
            (Fintype.card S : ℝ)^2 := by
              rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro r _; ring
         _ = _ := by rw [h]
  simp_rw [he, ← Finset.sum_div]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← Finset.mul_sum]

/-- The same actual returned value gives the exact unconditional second moment. -/
theorem pairedBellScore_second {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (ψ : S → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1) (τ : S → S) (C : ℝ) :
    (pairedBellLaw ψ hψ τ).expect (fun z => (pairedBellScore τ C z)^2) =
      C^2*(∑ x, bellProbability (ψ x) (ψ (τ x)))/(Fintype.card S : ℝ)^2 := by
  have hs (z : S × S × Reg 2) : (pairedBellScore τ C z)^2=C*pairedBellScore τ C z :=
    postCaptureScore_square _ _ _
  simp_rw [hs]
  have he : (pairedBellLaw ψ hψ τ).expect (fun z => C*pairedBellScore τ C z) =
      C*(pairedBellLaw ψ hψ τ).expect (pairedBellScore τ C) := by
    unfold FinDist.expect
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro z _; ring
  rw [he, pairedBellScore_mean]
  ring

/-- Marginalizing the complete actual post-capture outcomes leaves exactly two independent uniform addresses, even on misses. -/
theorem pairedBellLaw_address_expect {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (ψ : S → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1) (τ : S → S) (f : S → S → ℝ) :
    (pairedBellLaw ψ hψ τ).expect (fun z => f z.1 z.2.1) =
      (∑ x, ∑ y, f x y)/(Fintype.card S : ℝ)^2 := by
  unfold FinDist.expect pairedBellLaw
  simp only [Fintype.sum_prod_type]
  have he (x y : S) :
      (∑ r : Reg 2, (postCaptureLaw (ψ x) (ψ y) (hψ x) (hψ y)
        (decide (y=τ x))).prob r/(Fintype.card S : ℝ)^2*f x y) =
        f x y/(Fintype.card S : ℝ)^2 := by
    calc _ = (∑ r : Reg 2, (postCaptureLaw (ψ x) (ψ y) (hψ x) (hψ y)
          (decide (y=τ x))).prob r)*f x y/(Fintype.card S : ℝ)^2 := by
            rw [Finset.sum_mul, Finset.sum_div]
            apply Finset.sum_congr rfl
            intro r _
            ring
         _ = _ := by rw [(postCaptureLaw (ψ x) (ψ y) (hψ x) (hψ y)
            (decide (y=τ x))).sum_one, one_mul]
  simp_rw [he, ← Finset.sum_div]

/-- The conditional Bell word's expected gate count is exactly 2/M; the six capture CX gates are paid separately on every run. -/
theorem pairedBell_expected_test_gates {S : Type*} [Fintype S] [Nonempty S] [DecidableEq S]
    (ψ : S → Bool → ℂ) (hψ : ∀ x, qubitMass (ψ x)=1) (τ : S → S) :
    (pairedBellLaw ψ hψ τ).expect (fun z =>
      (GateCount (postCaptureProgram (decide (z.2.1=τ z.1))) : ℝ)) =
        2/(Fintype.card S : ℝ) := by
  rw [pairedBellLaw_address_expect ψ hψ τ
    (fun x y => (GateCount (postCaptureProgram (decide (y=τ x))) : ℝ))]
  simp_rw [(postCaptureProgram_counts _).1]
  simp only [Nat.cast_ite, Nat.cast_ofNat, Nat.cast_zero, Bool.decide_iff,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  have hM : (Fintype.card S : ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

/-- The actual bounded output is zero or the same public Bell coefficient on every physical observation. -/
theorem pairedBellScore_abs_le {S : Type*} [DecidableEq S] (τ : S → S) (C : ℝ)
    (z : S × S × Reg 2) : |pairedBellScore τ C z|≤|C| := by
  unfold pairedBellScore postCaptureScore
  split_ifs <;> simp

end Qatlib.Papers.SCWFPrep24.Estimation.NullRisk
