/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.OrderPrimality.Certificates
import Qatlib.Concepts.OrderPrimality.UniformTrial
import Qatlib.Papers.PrimalityOrd17.TotientBound

/-!
# Native order certificates and trial probabilities

The module connects maximal multiplicative order to primality and gives the success probability
for the specified uniform trial. It also proves an eventual lower bound and explicit small
examples that distinguish the trial denominator, the positive-exponent condition, and the
half-exponent screen from related formulations [DonisVelaGarciaEscartin2017].

## Main statements

* `order_certificate_sound`: An element of order N - 1 certifies primality for N ≥ 2.
* `eventual_native_trial_bound`: The trial probability eventually exceeds a reciprocal log-log
  bound.
* `half_screen_fermat_liar`: An explicit residue separates the half-exponent screen from the
  Fermat equality.

## References

* [Donis-Vela and Garcia-Escartin, 2017][DonisVelaGarciaEscartin2017]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Papers.PrimalityOrd17.NativeTrial
open Qatlib.Foundations.OrderPrimality Qatlib.Concepts.OrderPrimality

/-- For `N ≥ 2`, a unit modulo `N` of multiplicative order `N - 1` certifies that `N` is prime
[DonisVelaGarciaEscartin2017]. -/
theorem order_certificate_sound {N : ℕ} (hN : 2≤N) (a : (ZMod N)ˣ)
    (ha : orderOf a=N-1) : N.Prime := Certificates.orderOf_eq_pred_prime hN a ha

/-- For a prime `N ≥ 3`, the uniform trial succeeds with probability `totient (N - 1) / (N - 2)`
[DonisVelaGarciaEscartin2017]. -/
theorem native_trial_probability {N : ℕ} [NeZero N] (hp : N.Prime) (hN : 3≤N) :
    UniformTrial.successProb hp hN = (Nat.totient (N-1) : ℝ)/(N-2 : ℕ) :=
  UniformTrial.successProb_eq hp hN

/-- The real number `log (log M)` is positive for every natural number `M ≥ 3`. -/
theorem loglog_pos_of_three_le {M : ℕ} (hM : 3≤M) :
    0 < Real.log (Real.log (M : ℝ)) := by
  have he : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have h3 : (1:ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ)<3)]
    exact he
  have hlog : (1:ℝ) < Real.log (M : ℝ) := h3.trans_le
    (Real.log_le_log (by norm_num) (by exact_mod_cast hM))
  exact Real.log_pos hlog

/-- Beyond some threshold at least four, every prime `N ≥ 3` has positive `log (log (N - 1))`
and trial success probability greater than `1 / (3 * log (log (N - 1)))`
[DonisVelaGarciaEscartin2017]. -/
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

/-- At `N = 5`, the trial probability is `2 / 3`, whereas the ratio `totient 4 / 4` is `1 / 2`
[DonisVelaGarciaEscartin2017]. -/
theorem source_denominator_mismatch :
    UniformTrial.successProb (N:=5) (by norm_num) (by norm_num) = (2:ℝ)/3 ∧
      (Nat.totient 4 : ℝ)/(4:ℕ) = (1:ℝ)/2 := by
  have ht : Nat.totient 4=2 := by decide
  constructor
  · rw [UniformTrial.successProb_eq,ht]
    norm_num
  · rw [ht]
    norm_num

/-- The uniform trial candidate set is empty at `N = 2` [DonisVelaGarciaEscartin2017]. -/
theorem candidates_two_empty : UniformTrial.candidates 2 = ∅ := by
  apply Finset.card_eq_zero.mp
  unfold UniformTrial.candidates
  rw [Finset.card_erase_of_mem (Finset.mem_univ 1),Finset.card_univ,
    ZMod.card_units_eq_totient,Nat.totient_prime (by norm_num : Nat.Prime 2)]

/-- For `N ≥ 2`, no unit modulo `N` can have every power with natural exponent less than `N - 1`
different from one [DonisVelaGarciaEscartin2017]. -/
theorem reported_zero_exponent_failure {N : ℕ} (hN : 2≤N) (a : (ZMod N)ˣ) :
    ¬(∀ x : ℕ, x<N-1 → a^x ≠ 1) := by
  intro h
  exact h 0 (by omega) (pow_zero a)

/-- Modulo fifteen, the seventh power of four is neither one nor minus one, while its fourteenth
power is one [DonisVelaGarciaEscartin2017]. -/
theorem half_screen_fermat_liar :
    (4 : ZMod 15)^7 ≠ 1 ∧ (4 : ZMod 15)^7 ≠ -1 ∧ (4 : ZMod 15)^14 = 1 := by decide

end Qatlib.Papers.PrimalityOrd17.NativeTrial
