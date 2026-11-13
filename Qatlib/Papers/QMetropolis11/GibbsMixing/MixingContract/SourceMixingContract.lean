/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.MixedInstrument.Contraction.ContractionMixingDecayQuan
import Qatlib.Concepts.MixedInstrument.Contraction.ContractionFixedPointErrorQuan
import Qatlib.Concepts.QuantumGibbs.RejectionRewind.RejectionBudgetQuan

set_option backward.isDefEq.respectTransparency false

/-!
# Mixing and reject budget (Temme et al. 2011, Sec. 3.2, Eqs. (8)-(10))

Fixed source: arXiv:0911.3635v2, Section 3.2, printed pages 8 and 19.

* Eq. (8) quotes [34]: `‖E^m[ρ] - σ*‖₁ ≤ C_exp (1-Δ)^m` for a map obeying
  quantum detailed balance.  The contraction-side content is the established
  `ContractionMixingDecay` (Eq. (43) contraction with coefficient `η`), which
  this file bridges.  The identification `η = 1-Δ` with the spectral gap and
  the constant `C_exp` scaling are *not* proved by the semantic layer.
* Eq. (10): for `p_fail(n) ≤ 1/(2e(n+1))` one gets
  `(1-p_fail(n*))^{m_mix} ≥ c` whenever `n* > m_mix/(2e(1-c))`.  The established
  `rejectionBudget` proves the same Bernoulli step with the *strict* pointwise
  bound `1/(2(n+1))`; here we also prove the paper's `e`-constant version,
  which the semantic layer explicitly leaves open.

Reused FQNs:
* `Qatlib.Concepts.MixedInstrument.Contraction.contractionMixingDecay`;
* `Qatlib.Concepts.QuantumGibbs.RejectionRewind.rejectionBudget`.
-/

set_option autoImplicit false

namespace Qatlib.Papers.QMetropolis11.GibbsMixing.MixingContract

open Matrix
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.MixedInstrument.Contraction
open Qatlib.Concepts.QuantumGibbs.RejectionRewind

variable {D : ℕ}

/-- **c006, Eq. (8)/(43) contraction decay.**  For a channel `T` with density
fixed point `σ*`, if every pair of densities is contracted in trace norm by
`η < 1`, then `‖E^m[ρ₀] - σ*‖₁ ≤ η^m ‖ρ₀ - σ*‖₁` for every `m`.  This is the
trace-norm content behind the quoted Eq. (8); the spectral-gap identification
`η = 1-Δ` is separate.  Reused FQN:
`...Contraction.contractionMixingDecay`. -/
theorem source_mixingDecay : ContractionMixingDecay :=
  contractionMixingDecay

/-- **c006, Eq. (8), unpacked.**  The geometric decay in the paper's `η^m`
form for every `m`.  Reused FQN: `...Contraction.contractionMixingDecay`. -/
theorem source_mixing_decay (T : QuantumChannel D D) (σs ρ0 : Operator D)
    (hσ : IsDensityOperator σs) (hρ : IsDensityOperator ρ0) (hfix : T.map σs = σs)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hcontr : ∀ X Y : Operator D, IsDensityOperator X → IsDensityOperator Y →
      SchattenOne (T.map X - T.map Y) ≤ η * SchattenOne (X - Y))
    (m : ℕ) :
    SchattenOne ((T.map^[m]) ρ0 - σs) ≤ η ^ m * SchattenOne (ρ0 - σs) :=
  contractionMixingDecay D T σs ρ0 hσ hρ hfix η hη0 hη1 hcontr m

/-- **c006, Eq. (10) budget (strict bound).**  A pointwise failure bound
`p_fail(n) ≤ 1/(2(n+1))` turns into `(1-p_fail(n))^m ≥ c` once
`(n+1)(2(1-c)) ≥ m`.  Reused FQN:
`...RejectionRewind.rejectionBudget`. -/
theorem source_rejectionBudget : RejectionBudget :=
  rejectionBudget

/-- **c006, Eq. (10) budget with the paper's `e` constant.**  For the paper's
pointwise bound `p_fail(n) ≤ 1/(2e(n+1))` and the paper's budget
`n* > m_mix/(2e(1-c))` (written `(n+1)·2e(1-c) ≥ m`), the success probability
after `m` steps is at least `c`.  This is the Bernoulli step of Eq. (10) with
the sharper constant that the `rejectionBudget` does not supply.  New
proof here; the underlying sharp pointwise bound is the asymptotic reading of
Eq. (7) (see `RejectionRecovery.source_rejection_failure_le` for the exact
strict bound actually available in the library). -/
theorem source_rejection_budget_exp (pfail : ℕ → ℝ)
    (hfail : ∀ n, 1 ≤ n → 0 ≤ pfail n ∧ pfail n ≤ 1 / (2 * Real.exp 1 * (n + 1)))
    (m n : ℕ) (c : ℝ) (hn : 1 ≤ n) (_hc : 0 ≤ c) (_hc1 : c < 1)
    (_hm : 0 < m) (hbudget : ((n : ℝ) + 1) * (2 * Real.exp 1 * (1 - c)) ≥ m) :
    (1 - pfail n) ^ m ≥ c := by
  obtain ⟨h0, h1⟩ := hfail n hn
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hden : (0 : ℝ) < 2 * Real.exp 1 * ((n : ℝ) + 1) := by positivity
  have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hscale : (m : ℝ) * pfail n ≤
      (m : ℝ) * (1 / (2 * Real.exp 1 * ((n : ℝ) + 1))) :=
    mul_le_mul_of_nonneg_left h1 hmnonneg
  have hmdiv : (m : ℝ) / (2 * Real.exp 1 * ((n : ℝ) + 1)) ≤ 1 - c := by
    rw [div_le_iff₀ hden]
    nlinarith only [hbudget]
  have hmx : (m : ℝ) * pfail n ≤ 1 - c := by
    refine hscale.trans ?_
    simpa only [mul_one_div] using hmdiv
  have hx1 : pfail n ≤ 1 := by
    refine h1.trans ?_
    rw [div_le_one hden]
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n; linarith
    have he1 : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
    have h2e : (1 : ℝ) ≤ 2 * Real.exp 1 := by linarith
    have hprod : (1 : ℝ) * 1 ≤ (2 * Real.exp 1) * ((n : ℝ) + 1) :=
      mul_le_mul h2e hn1 (by norm_num) (by positivity)
    simpa using hprod
  have hbern := one_add_mul_sub_le_pow (a := 1 - pfail n) (by linarith : -1 ≤ 1 - pfail n) m
  have hbern' : 1 - (m : ℝ) * pfail n ≤ (1 - pfail n) ^ m := by
    nlinarith only [hbern]
  linarith only [hbern', hmx]

end Qatlib.Papers.QMetropolis11.GibbsMixing.MixingContract
