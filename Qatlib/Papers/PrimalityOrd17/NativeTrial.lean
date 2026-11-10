/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OrderPrimality.Certificates
import Qatlib.Concepts.OrderPrimality.UniformTrial
import Qatlib.Papers.PrimalityOrd17.TotientBound
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.PrimalityOrd17.NativeTrial
open Qatlib.Foundations.OrderPrimality Qatlib.Concepts.OrderPrimality

theorem order_certificate_sound {N : ℕ} (hN : 2≤N) (a : (ZMod N)ˣ)
    (ha : orderOf a=N-1) : N.Prime := Certificates.orderOf_eq_pred_prime hN a ha

theorem native_trial_probability {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3≤N) :
    UniformTrial.successProb hp hN = (Nat.totient (N-1) : ℝ)/(N-2 : ℕ) :=
  UniformTrial.successProb_eq hp hN

theorem loglog_pos_of_three_le {M : ℕ} (hM : 3≤M) :
    0 < Real.log (Real.log (M : ℝ)) := by
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have h3 : (1:ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<3)]
    exact he
  have hlog : (1:ℝ) < Real.log (M : ℝ) := h3.trans_le
    (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
  exact Real.log_pos hlog

theorem eventual_native_trial_bound :
    ∃ T : ℕ, 4≤T ∧ ∀ (N : ℕ) [NeZero N] (hp : N.Prime) (hN : 3≤N), T≤N →
      0 < Real.log (Real.log ((N-1 : ℕ) : ℝ)) ∧
      1/(3*Real.log (Real.log ((N-1 : ℕ) : ℝ))) < UniformTrial.successProb hp hN := by
  obtain ⟨M₀,hM₀⟩ := TotientBound.totient_ratio_gt_inv_three_loglog
  refine ⟨max M₀ 3 + 1,by omega,?_⟩
  intro N _ hp hN hT
  have hM : M₀≤N-1 := by omega
  have h3 : 3≤N-1 := by omega
  exact ⟨loglog_pos_of_three_le h3,
    (hM₀ (N-1) hM).trans_le (UniformTrial.all_units_fraction_le hp hN)⟩

theorem source_denominator_mismatch :
    UniformTrial.successProb (N:=5) (by norm_num) (by norm_num) = (2:ℝ)/3 ∧
      (Nat.totient 4 : ℝ)/(4:ℕ) = (1:ℝ)/2 := by
  have ht : Nat.totient 4=2 := by decide
  constructor
  · rw [UniformTrial.successProb_eq,ht]
    norm_num
  · rw [ht]
    norm_num

theorem candidates_two_empty : UniformTrial.candidates 2 = ∅ := by
  apply Finset.card_eq_zero.mp
  unfold UniformTrial.candidates
  rw [Finset.card_erase_of_mem (Finset.mem_univ 1),Finset.card_univ,
    ZMod.card_units_eq_totient,Nat.totient_prime (by norm_num : Nat.Prime 2)]

theorem reported_zero_exponent_failure {N : ℕ} (hN : 2≤N) (a : (ZMod N)ˣ) :
    ¬(∀ x : ℕ, x<N-1 → a^x ≠ 1) := by
  intro h
  exact h 0 (by omega) (pow_zero a)

theorem half_screen_fermat_liar :
    (4 : ZMod 15)^7 ≠ 1 ∧ (4 : ZMod 15)^7 ≠ -1 ∧ (4 : ZMod 15)^14 = 1 := by decide

end Qatlib.Papers.PrimalityOrd17.NativeTrial
