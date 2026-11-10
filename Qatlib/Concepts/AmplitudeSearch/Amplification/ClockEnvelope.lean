/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.Amplification.RunMoment
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

open Qatlib.Concepts.AmplitudeSearch.Amplification.RankedCallLaw

set_option autoImplicit false

namespace Qatlib.Concepts.AmplitudeSearch.Amplification

noncomputable def thresholdEnvelope (D : ℕ → ℝ) (t : ℕ) : ℝ :=
  D t + expectedTraceCost (fun r => D (r - 1)) t

@[simp] theorem thresholdEnvelope_zero (D : ℕ → ℝ) (hD0 : D 0 = 0) :
    thresholdEnvelope D 0 = 0 := by simp [thresholdEnvelope, hD0]

theorem thresholdEnvelope_step (D : ℕ → ℝ) (t : ℕ) :
    thresholdEnvelope D (t + 1) = D (t + 1) +
      (∑ k : Fin (t + 1), thresholdEnvelope D k.val) / (t + 1 : ℝ) := by
  unfold thresholdEnvelope
  rw [expectedTraceCost_succ]
  simp only [Nat.add_sub_cancel]

theorem thresholdEnvelope_monotone (D : ℕ → ℝ)
    (hscaled : ∀ t : ℕ, (t : ℝ) * D t ≤ (t + 1 : ℝ) * D (t + 1)) :
    Monotone (thresholdEnvelope D) := by
  apply monotone_nat_of_le_succ
  intro t
  have ht : (0 : ℝ) < (t + 1 : ℝ) := by positivity
  have hdiv : (t : ℝ) * D t / (t + 1 : ℝ) ≤ D (t + 1) :=
    (div_le_iff₀ ht).mpr (by simpa only [mul_comm] using hscaled t)
  have heq : (t : ℝ) * D t / (t + 1 : ℝ) = D t - D t / (t + 1 : ℝ) := by
    field_simp
    ring
  rw [heq] at hdiv
  simp only [thresholdEnvelope, expectedTraceCost_step, Nat.add_sub_cancel]
  linarith

theorem thresholdEnvelope_skip_step {N : ℕ} (skip : RankSkip N) (D : ℕ → ℝ)
    (hscaled : ∀ t : ℕ, (t : ℝ) * D t ≤ (t + 1 : ℝ) * D (t + 1))
    (t : ℕ) (ht : 0 < t) (htN : t < N) :
    D t + (∑ i : Fin N, if i.val < t then thresholdEnvelope D (skip.next i) else 0) /
      (t : ℝ) ≤ thresholdEnvelope D t := by
  have hmono := thresholdEnvelope_monotone D hscaled
  have hsum : (∑ i : Fin N, if i.val < t then thresholdEnvelope D (skip.next i) else 0) ≤
      ∑ i : Fin N, if i.val < t then thresholdEnvelope D i.val else 0 := by
    apply Finset.sum_le_sum
    intro i _
    split_ifs
    · exact hmono (skip.le_rank i)
    · exact le_rfl
  have hd := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg t)
  rw [RankedCallLaw.sum_lower_ranks t htN.le] at hd
  obtain ⟨u, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt ht)
  rw [thresholdEnvelope_step]
  simpa only [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one] using
    add_le_add (le_refl (D (u + 1))) hd

noncomputable def sourceCallEnvelope (N t : ℕ) : ℝ :=
  if t = 0 then 0 else ((9 / 2 : ℝ) * Real.sqrt N) / Real.sqrt t + binaryLog N

@[simp] theorem sourceCallEnvelope_zero (N : ℕ) : sourceCallEnvelope N 0 = 0 := by
  simp [sourceCallEnvelope]

theorem sourceCallEnvelope_scaled (N t : ℕ) :
    (t : ℝ) * sourceCallEnvelope N t =
      ((9 / 2 : ℝ) * Real.sqrt N) * Real.sqrt t + binaryLog N * t := by
  by_cases ht : t = 0
  · simp [ht, sourceCallEnvelope]
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero ht)
  have hdiv : (t : ℝ) / Real.sqrt t = Real.sqrt t := by
    apply (div_eq_iff hs.ne').2
    exact (Real.mul_self_sqrt (Nat.cast_nonneg t)).symm
  rw [sourceCallEnvelope, if_neg ht]
  calc
    _ = ((9 / 2 : ℝ) * Real.sqrt N) * ((t : ℝ) / Real.sqrt t) + binaryLog N * t := by ring
    _ = _ := by rw [hdiv]

theorem sourceCallEnvelope_scaled_mono (N : ℕ) (hN : 0 < N) :
    ∀ t : ℕ, (t : ℝ) * sourceCallEnvelope N t ≤
      (t + 1 : ℝ) * sourceCallEnvelope N (t + 1) := by
  intro t
  have hL : 0 ≤ binaryLog N := div_nonneg
    (Real.log_nonneg (by exact_mod_cast hN)) (Real.log_pos (by norm_num)).le
  have hroot : Real.sqrt (t : ℝ) ≤ Real.sqrt (t + 1 : ℕ) :=
    Real.sqrt_le_sqrt (by exact_mod_cast Nat.le_succ t)
  have hcast : (t + 1 : ℝ) = ((t + 1 : ℕ) : ℝ) := by norm_cast
  rw [hcast, sourceCallEnvelope_scaled, sourceCallEnvelope_scaled]
  exact add_le_add (mul_le_mul_of_nonneg_left hroot (by positivity))
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_succ t) hL)

theorem sourceEnvelope_nonneg (N t : ℕ) (hN : 0 < N) : 0 ≤ sourceCallEnvelope N t := by
  have hL : 0 ≤ binaryLog N := div_nonneg
    (Real.log_nonneg (by exact_mod_cast hN)) (Real.log_pos (by norm_num)).le
  unfold sourceCallEnvelope
  split_ifs <;> positivity

theorem sourceEnvelope_initial_bound (N : ℕ) (hN : 0 < N) :
    expectedTraceCost (fun r => sourceCallEnvelope N (r - 1)) N ≤ sourceMeanBudget N := by
  apply expectedTraceCost_le_sourceMeanBudget N hN _ (sourceCallEnvelope_zero N)
  intro r hr hrN
  have hr0 : r - 1 ≠ 0 := by omega
  rw [sourceCallEnvelope, if_neg hr0, Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_one]
  rw [Real.sqrt_div (Nat.cast_nonneg N)]
  ring_nf
  exact le_rfl

theorem initialClock_le_sourceMeanBudget {N : ℕ} {Ω : Type}
    (law : RankedCallLaw N Ω) (skip : RankSkip N) (hN : 0 < N)
    (hcall : ∀ t, 0 < t → t < N → ∃ q,
      HasSum (fun x => law.mass t x * law.duration x) q ∧ q ≤ sourceCallEnvelope N t) :
    ∃ q, HasSum (fun x : Fin N × List Ω => law.initialMass skip x * law.runClock x.2) q ∧
      0 ≤ q ∧ q ≤ sourceMeanBudget N := by
  have hscaled := sourceCallEnvelope_scaled_mono N hN
  have hmono := thresholdEnvelope_monotone (sourceCallEnvelope N) hscaled
  obtain ⟨q, hq, hqnn, hqb⟩ := law.initialClock_moment skip (sourceCallEnvelope N)
    (thresholdEnvelope (sourceCallEnvelope N))
    (thresholdEnvelope_zero _ (sourceCallEnvelope_zero N)) hcall
    (thresholdEnvelope_skip_step skip _ hscaled) hN
  refine ⟨q, hq, hqnn, ?_⟩
  have hsum : (∑ i : Fin N, thresholdEnvelope (sourceCallEnvelope N) (skip.next i)) ≤
      ∑ i : Fin N, thresholdEnvelope (sourceCallEnvelope N) i.val :=
    Finset.sum_le_sum (fun i _ => hmono (skip.le_rank i))
  have hd := div_le_div_of_nonneg_right hsum (Nat.cast_nonneg N)
  have heq : (∑ i : Fin N, thresholdEnvelope (sourceCallEnvelope N) i.val) / (N : ℝ) =
      expectedTraceCost (fun r => sourceCallEnvelope N (r - 1)) N := by
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hN)
    rw [expectedTraceCost_succ]
    simp only [thresholdEnvelope, Nat.add_sub_cancel, Nat.cast_succ]
  rw [heq] at hd
  exact hqb.trans (hd.trans (sourceEnvelope_initial_bound N hN))

end Qatlib.Concepts.AmplitudeSearch.Amplification
