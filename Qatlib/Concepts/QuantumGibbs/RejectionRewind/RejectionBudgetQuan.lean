/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.QuantumGibbs.RejectionRewind.RejectionBudgetStat
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionOriginalContracts
import Qatlib.Concepts.MixedInstrument.RewindAlgebra.RejectionFailureBoundQuan
set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.MixedInstrument.RewindAlgebra

namespace Qatlib.Concepts.QuantumGibbs.RejectionRewind
open Matrix

theorem rejection_budget_of_positive_rounds (pfail : ℕ → ℝ)
    (hfail : ∀ n, 1 ≤ n → 0 ≤ pfail n ∧ pfail n ≤ 1 / (2 * (n + 1)))
    (m n : ℕ) (c : ℝ) (hn : 1 ≤ n) (_hc : 0 ≤ c) (_hc1 : c < 1)
    (_hm : 0 < m) (hbudget : (n + 1 : ℝ) * (2 * (1 - c)) ≥ m) :
    (1 - pfail n) ^ m ≥ c := by
  obtain ⟨_h0,h1⟩ := hfail n hn
  have hden : 0 < 2 * (n + 1 : ℝ) := by positivity
  have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hscale := mul_le_mul_of_nonneg_left h1 hmnonneg
  have hbudget' : (m : ℝ) / (2 * (n + 1 : ℝ)) ≤ 1 - c :=
    (div_le_iff₀ hden).2 (by nlinarith only [hbudget])
  have hmx : (m : ℝ) * pfail n ≤ 1 - c := by
    exact hscale.trans (by simpa only [mul_one_div] using hbudget')
  have hx1 : pfail n ≤ 1 := by
    apply h1.trans
    apply (div_le_iff₀ hden).2
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hbern := one_add_mul_sub_le_pow (a := 1 - pfail n) (by linarith : -1 ≤ 1 - pfail n) m
  nlinarith only [hbern,hmx]

theorem rejection_budget_actual (D : ℕ) (P Q : Qatlib.Foundations.PureStateMath.Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (ψ : Qatlib.Foundations.PureStateMath.QState (Fin D)) (hnorm : Qatlib.Foundations.PureStateMath.Inner ψ ψ=1)
    (hψ : P*ᵥψ=ψ) (m n : ℕ) (c : ℝ) (hn : 1 ≤ n) (hc : 0 ≤ c) (hc1 : c < 1)
    (hm : 0 < m) (hbudget : (n+1 : ℝ)*(2*(1-c)) ≥ m) :
    (1-rejectFailProb P Q ψ n)^m ≥ c := by
  apply rejection_budget_of_positive_rounds (rejectFailProb P Q ψ)
    (fun l hl => ⟨rejectFailProb_nonneg P Q ψ l,
      rejectionFailureBound D P Q hPs hPi hQs hQi ψ hnorm hψ l hl⟩) m n c hn hc hc1 hm hbudget

theorem rejectionBudget_false : ¬ RejectionBudgetLegacy := by
  intro h
  let pfail : ℕ → ℝ := fun n => if n = 0 then 2 else 0
  have hf : ∀ n, 1 ≤ n → 0 ≤ pfail n ∧ pfail n ≤ 1 / (2 * (n + 1)) := by
    intro n hn
    have hn0 : n ≠ 0 := by omega
    simp only [pfail,if_neg hn0]
    exact ⟨le_refl _, by positivity⟩
  have bad := h pfail hf 1 0 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  norm_num [pfail] at bad

theorem rejection_budget_of_pointwise_bound (pfail : ℕ → ℝ)
    (m n : ℕ) (c : ℝ)
    (hfail : 0 ≤ pfail n ∧ pfail n ≤ 1 / (2 * (n + 1))) (_hc : 0 ≤ c) (_hc1 : c < 1)
    (_hm : 0 < m) (hbudget : (n + 1 : ℝ) * (2 * (1 - c)) ≥ m) :
    (1 - pfail n) ^ m ≥ c := by
  obtain ⟨_h0,h1⟩ := hfail
  have hden : 0 < 2 * (n + 1 : ℝ) := by positivity
  have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
  have hscale := mul_le_mul_of_nonneg_left h1 hmnonneg
  have hbudget' : (m : ℝ) / (2 * (n + 1 : ℝ)) ≤ 1 - c :=
    (div_le_iff₀ hden).2 (by nlinarith only [hbudget])
  have hmx : (m : ℝ) * pfail n ≤ 1 - c := by
    exact hscale.trans (by simpa only [mul_one_div] using hbudget')
  have hx1 : pfail n ≤ 1 := by
    apply h1.trans
    apply (div_le_iff₀ hden).2
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hbern := one_add_mul_sub_le_pow (a := 1 - pfail n) (by linarith : -1 ≤ 1 - pfail n) m
  nlinarith only [hbern,hmx]

theorem rejectionBudget : RejectionBudget := by
  intro pfail hfail m n c hc hc1 hm hbudget
  exact rejection_budget_of_pointwise_bound pfail m n c (hfail n) hc hc1 hm hbudget

theorem rejection_budget_actual_all_rounds (D : ℕ) (P Q : Qatlib.Foundations.PureStateMath.Operator D)
    (hPs : P.IsHermitian) (hPi : P*P=P) (hQs : Q.IsHermitian) (hQi : Q*Q=Q)
    (ψ : Qatlib.Foundations.PureStateMath.QState (Fin D)) (hnorm : Qatlib.Foundations.PureStateMath.Inner ψ ψ=1)
    (hψ : P*ᵥψ=ψ) (m n : ℕ) (c : ℝ) (hc : 0 ≤ c) (hc1 : c < 1)
    (hm : 0 < m) (hbudget : (n+1 : ℝ)*(2*(1-c)) ≥ m) :
    (1-rejectFailProb P Q ψ n)^m ≥ c := by
  exact rejectionBudget (rejectFailProb P Q ψ)
    (fun l => ⟨rejectFailProb_nonneg P Q ψ l,
      rejection_failure_bound_all_rounds D P Q hPs hPi hQs hQi ψ hnorm hψ l⟩)
    m n c hc hc1 hm hbudget

end Qatlib.Concepts.QuantumGibbs.RejectionRewind
