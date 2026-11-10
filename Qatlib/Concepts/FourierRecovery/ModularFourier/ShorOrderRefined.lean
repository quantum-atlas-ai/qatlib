/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrderDefs
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.FourierRecovery.ModularFourier.ShorOrder
open Qatlib.Concepts.PeriodSampling.OrderRecovery

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace Qatlib.Concepts.FourierRecovery.ModularFourier

open Qatlib
open Matrix
open scoped Classical BigOperators ComplexConjugate ENNReal

theorem shorFermatScreen_never_refuses_prime (N : ℕ) [NeZero N] (hp : Nat.Prime N)
    (a : (ZMod N)ˣ) : shorFermatScreen N a = true := by
  have h : a ^ (N - 1) = 1 := primeDirectionWitness_of_prime N hp a
  simp [shorFermatScreen, h]

theorem shorFermatScreen_refuses_composite : shorFermatScreen 4 shorUnitThree = false := by
  decide

private lemma pow_four_le_pow_six (x : ℕ) (hx : 1 ≤ x) : x ^ 4 ≤ x ^ 6 := by
  have h1 : (1 : ℕ) ≤ x ^ 2 := by nlinarith [Nat.zero_le x]
  calc
    x ^ 4 = x ^ 4 * 1 := by ring
    _ ≤ x ^ 4 * x ^ 2 := Nat.mul_le_mul (Nat.le_refl _) h1
    _ = x ^ 6 := by ring

theorem shorFermatScreenBitCost_le_polyLog (N : ℕ) :
    shorFermatScreenBitCost N ≤ polyLogBound 1 6 N := by
  have hb : 1 ≤ orderBitLength N := by
    unfold orderBitLength
    omega
  have hsq : 2 * orderBitLength N + 1 ≤ (orderBitLength N + 1) ^ 2 := by
    have : (orderBitLength N + 1) ^ 2 = orderBitLength N * orderBitLength N
        + 2 * orderBitLength N + 1 := by ring
    omega
  have hfactor : schoolbookMulModCost (orderBitLength N) * (orderBitLength N + 1)
      = orderBitLength N * (2 * orderBitLength N + 1) * (orderBitLength N + 1) := by
    unfold schoolbookMulModCost
    ring
  have hmain : orderBitLength N * (2 * orderBitLength N + 1) * (orderBitLength N + 1)
      ≤ (orderBitLength N + 1) ^ 4 := by
    calc
      orderBitLength N * (2 * orderBitLength N + 1) * (orderBitLength N + 1)
          ≤ (orderBitLength N + 1) * ((orderBitLength N + 1) ^ 2) * (orderBitLength N + 1) := by
            have h1 : orderBitLength N * (2 * orderBitLength N + 1)
                ≤ (orderBitLength N + 1) * ((orderBitLength N + 1) ^ 2) :=
              Nat.mul_le_mul (Nat.le_add_right _ _) hsq
            exact Nat.mul_le_mul h1 (Nat.le_refl _)
      _ = (orderBitLength N + 1) ^ 4 := by ring
  have hfinal : (orderBitLength N + 1) ^ 4 ≤ (orderBitLength N + 1) ^ 6 :=
    pow_four_le_pow_six (orderBitLength N + 1) (by omega)
  unfold shorFermatScreenBitCost polyLogBound
  rw [hfactor, one_mul]
  exact hmain.trans hfinal

theorem shorModExpBitCost_le_polyLog (N : ℕ) :
    shorModExpBitCost N ≤ polyLogBound 1 6 N := by
  have hb : 1 ≤ orderBitLength N := by
    unfold orderBitLength
    omega
  have hsq : 2 * orderBitLength N + 1 ≤ (orderBitLength N + 1) ^ 2 := by
    have : (orderBitLength N + 1) ^ 2 = orderBitLength N * orderBitLength N
        + 2 * orderBitLength N + 1 := by ring
    omega
  have hfactor : (orderBitLength N + 1) * schoolbookMulModCost (orderBitLength N)
      = (orderBitLength N + 1) * orderBitLength N * (2 * orderBitLength N + 1) := by
    unfold schoolbookMulModCost
    ring
  have hmain : (orderBitLength N + 1) * orderBitLength N * (2 * orderBitLength N + 1)
      ≤ (orderBitLength N + 1) ^ 4 := by
    calc
      (orderBitLength N + 1) * orderBitLength N * (2 * orderBitLength N + 1)
          ≤ (orderBitLength N + 1) * (orderBitLength N + 1) * ((orderBitLength N + 1) ^ 2) := by
            have h1 : orderBitLength N ≤ orderBitLength N + 1 := by omega
            exact Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_refl _) h1) hsq
      _ = (orderBitLength N + 1) ^ 4 := by ring
  have hfinal : (orderBitLength N + 1) ^ 4 ≤ (orderBitLength N + 1) ^ 6 :=
    pow_four_le_pow_six (orderBitLength N + 1) (by omega)
  unfold shorModExpBitCost polyLogBound
  rw [hfactor, one_mul]
  exact hmain.trans hfinal

theorem shorCfBitCost_eq (N : ℕ) :
    shorCfBitCost N = (N + 1) * euclidStepBound (orderBitLength N) * orderBitLength N := by
  rfl

theorem shorSuccessReceipt_sound (N M R : ℕ) [NeZero N] (ω : Fin R → AttemptOutcome N M)
    (j : Fin R) (hj : firstSuccessAt (N := N) (M := M) (R := R) ω j) :
    (attemptOutcomeFactor N M (ω j)).isSome ∧
      (shorSuccessReceipt ω j).index = j.val ∧
      (shorSuccessReceipt ω j).attempts = j.val + 1 ∧
      1 < (shorSuccessReceipt ω j).factor ∧ (shorSuccessReceipt ω j).factor < N := by
  obtain ⟨hsome, hfac⟩ := firstSuccessAt_sound N M R ω j hj
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hsome
  have hd' := hfac d hd
  refine ⟨hsome, rfl, rfl, ?_, ?_⟩
  · have : (attemptOutcomeFactor N M (ω j)).getD 0 = d := by
      rw [hd]
      rfl
    rw [shorSuccessReceipt, this]
    exact hd'.1
  · have : (attemptOutcomeFactor N M (ω j)).getD 0 = d := by
      rw [hd]
      rfl
    rw [shorSuccessReceipt, this]
    exact hd'.2.1

theorem hasCompactEncoding_of_fintype (G : Type) [Fintype G] [DecidableEq G] :
    HasCompactEncoding G := by
  have hcard : Fintype.card G ≤ 2 ^ compactRecordWidth (Fintype.card G) := by
    by_cases h0 : Fintype.card G = 0
    · simp [h0]
    · exact compactRecordWidth_bound (Fintype.card G) h0
  refine ⟨fun x => Fin.castLE hcard (Fintype.equivFin G x), ?_⟩
  intro x y hxy
  exact Equiv.injective (Fintype.equivFin G) (Fin.castLE_injective hcard hxy)

theorem clause9_endpoint_holds : clause9_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N _ hp a
    exact shorFermatScreen_never_refuses_prime N hp a
  · exact shorFermatScreen_refuses_composite
  · intro N
    exact shorFermatScreenBitCost_le_polyLog N
  · intro N
    exact preprocessBitCost_le N
  · exact evenDivisor_sound
  · exact perfectPowerDivisor_sound
  · intro N _ hp a
    exact primeDirectionWitness_of_prime N hp a

theorem thresholdGoal_endpoint_holds : thresholdGoal_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact localQft_ledger
  · intro N M _ a hM
    exact modularOrder_ledger N M a hM
  · intro N _ a q
    exact orderVerification_is_power N a q
  · exact euclidCounted_ledger
  · intro N
    exact euclidBitCost_le_polyLog N
  · intro N
    exact shorModExpBitCost_le_polyLog N
  · intro N
    exact shorCfBitCost_eq N
  · intro N M k
    exact attemptLedgerBound_ge_rejected N M k

theorem clause11_endpoint_holds : clause11_endpoint := by
  refine ⟨?_, ?_, ?_⟩
  · intro N M _ t d h
    exact attemptOutcomeFactor_sound N M t d h
  · intro N M R _ ω j hj
    exact shorSuccessReceipt_sound N M R ω j hj
  · intro split n hne
    exact factorTreeOf_complete split n hne

theorem clause12_endpoint_holds : clause12_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G
    exact hasCompactEncoding_of_fintype G
  · intro Ω H _ _ V T hV
    exact compiledMeasurement_matrix_eq V T hV
  · intro Ω H _ _ V T φ
    exact compiledMeasurement_action_eq V T φ
  · intro G
    exact orbitFourier_isometry G
  · intro m hm
    exact compactRecordWidth_bound m hm
  · intro m hm
    rfl

theorem clause13_endpoint_holds : clause13_endpoint := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N hN
    exact originalClockWindow_exists N hN
  · intro N M _ a hM hN hr hsize
    exact orderGoodMass_pos N M a hM hN hr hsize
  · intro N M _ a hM hN hr hsize y
    by_cases hy : OrderGoodEvent N M a y
    · rw [orderConditionalLaw_prob_eq N M a hM _ y hy]
      simp [hy]
    · rw [orderConditionalLaw_prob_eq_zero N M a hM _ y hy]
      simp [hy]
  · intro N M _ a hM hN hr hsize
    exact (orderConditionalLaw N M a hM (orderGoodMass_pos N M a hM hN hr hsize)).sum_one
  · intro m w hw
    exact smallPrimePowers_dvd m w hw
  · intro m
    rfl

end Qatlib.Concepts.FourierRecovery.ModularFourier
