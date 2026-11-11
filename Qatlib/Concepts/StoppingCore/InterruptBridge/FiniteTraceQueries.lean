/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.QueryWordCore.Circuit

/-!
# A first-query bound for finite traces

This module defines finite trace masses from squared norms of actual circuit runs and weights
them by literal query counts in `finiteTraceExpected`. It proves that success on two distinct
outputs forces a lower bound on the first oracle's expected query weight when the second
oracle's total trace mass is at most one.

The argument uses oracle-independence of zero-query circuits, a basic ingredient of quantum
query lower bounds; see [BennettEtAl1997].

## Main statements

* `finiteTraceMass_zero_query`: oracle-independence of zero-query trace masses
* `finite_trace_first_query_lower`: the lower bound `r₀ + r₁ - 1` on expected query weight

## References

* [Bennett et al., 1997][BennettEtAl1997]
-/

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.StoppingCore.InterruptBridge
open Matrix
open Qatlib.Foundations.QueryWordCore.Circuit
open Qatlib.Foundations.PureStateMath
open scoped BigOperators

/-- The squared norm of the state produced by the circuit associated with trace `h`. -/
def finiteTraceMass {I H : Type} [Fintype I] (O : Matrix I I ℂ)
    (code : H → Circuit I) (psi : QState I) (h : H) : ℝ :=
  ∑ i, ‖Run O (code h) psi i‖^2

/-- The sum of trace masses weighted by the literal query counts of their circuits. -/
def finiteTraceExpected {I H : Type} [Fintype I] [Fintype H] (O : Matrix I I ℂ)
    (code : H → Circuit I) (psi : QState I) : ℝ :=
  ∑ h, finiteTraceMass O code psi h*(QueryCount (code h) : ℝ)

/-- The total mass of traces whose decoded output equals the target `t`. -/
def finiteTraceSuccess {I H : Type} [Fintype I] [Fintype H] (O : Matrix I I ℂ)
    (code : H → Circuit I) (psi : QState I) (decode : H → ℕ) (t : ℕ) : ℝ :=
  ∑ h, if decode h = t then finiteTraceMass O code psi h else 0

/-- Every finite trace mass is nonnegative. -/
theorem finiteTraceMass_nonneg {I H : Type} [Fintype I] (O : Matrix I I ℂ)
    (code : H → Circuit I) (psi : QState I) (h : H) : 0 ≤ finiteTraceMass O code psi h :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- A trace circuit containing no queries has the same mass for any two oracle matrices. -/
theorem finiteTraceMass_zero_query {I H : Type} [Fintype I] [DecidableEq I]
    (O₀ O₁ : Matrix I I ℂ) (code : H → Circuit I) (psi : QState I) (h : H)
    (hq : QueryCount (code h) = 0) : finiteTraceMass O₀ code psi h = finiteTraceMass O₁ code psi h := by
  unfold finiteTraceMass
  rw [run_eq_of_queryCount_eq_zero O₀ O₁ (code h) hq psi]

/-- For distinct target outputs, success lower bounds `r₀` and `r₁` force expected query weight
at least `r₀ + r₁ - 1` on the first oracle, provided the second oracle's total trace mass is
at most one. -/
theorem finite_trace_first_query_lower {I H : Type} [Fintype I] [DecidableEq I] [Fintype H]
    (O₀ O₁ : Matrix I I ℂ) (code : H → Circuit I) (psi : QState I) (decode : H → ℕ)
    (t₀ t₁ : ℕ) (hne : t₀ ≠ t₁) (r₀ r₁ : ℝ)
    (htotal : (∑ h, finiteTraceMass O₁ code psi h) ≤ 1)
    (h₀ : r₀ ≤ finiteTraceSuccess O₀ code psi decode t₀)
    (h₁ : r₁ ≤ finiteTraceSuccess O₁ code psi decode t₁) :
    r₀+r₁-1 ≤ finiteTraceExpected O₀ code psi := by
  have hm : finiteTraceSuccess O₀ code psi decode t₀ ≤
      finiteTraceSuccess O₁ code psi decode t₀+finiteTraceExpected O₀ code psi := by
    unfold finiteTraceSuccess finiteTraceExpected
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro h _
    have hp₀ := finiteTraceMass_nonneg O₀ code psi h
    have hp₁ := finiteTraceMass_nonneg O₁ code psi h
    by_cases hd : decode h = t₀
    · simp only [hd,if_true]
      by_cases hq : QueryCount (code h) = 0
      · rw [finiteTraceMass_zero_query O₀ O₁ code psi h hq,hq,Nat.cast_zero,mul_zero,add_zero]
      · have hq1 : (1 : ℝ) ≤ (QueryCount (code h) : ℝ) := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hq)
        have hpaid : finiteTraceMass O₀ code psi h ≤
            finiteTraceMass O₀ code psi h*(QueryCount (code h) : ℝ) := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hq1 hp₀
        linarith
    · simp only [hd,if_false,zero_add]
      exact mul_nonneg hp₀ (Nat.cast_nonneg _)
  have hd : finiteTraceSuccess O₁ code psi decode t₀+finiteTraceSuccess O₁ code psi decode t₁ ≤
      ∑ h, finiteTraceMass O₁ code psi h := by
    unfold finiteTraceSuccess
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro h _
    by_cases h0 : decode h = t₀
    · have h1 : decode h ≠ t₁ := fun e => hne (h0.symm.trans e)
      rw [if_pos h0,if_neg h1,add_zero]
    · by_cases h1 : decode h = t₁
      · rw [if_neg h0,if_pos h1,zero_add]
      · simp only [h0,h1,if_false,add_zero]
        exact finiteTraceMass_nonneg O₁ code psi h
  linarith [hd.trans htotal]

end Qatlib.Concepts.StoppingCore.InterruptBridge
