/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QIntegration00.MainResults.Defs
import Qatlib.Concepts.MonteCarloMean.FinDistBounds.Estimator
import Qatlib.Concepts.AmplitudeCore.InvFreeSampling.BernoulliTail
import Qatlib.Concepts.HspRecovery.BackendAudit.CharacterTableRecoveryProbability

/-!
# Randomized quantum mean estimation bounds

This module combines finite-distribution sampling bounds with an assumed approximation to the
sample mean. It proves a success probability of at least 3/4 and converts the stated cost model
into an `ε⁻¹ * log(ε⁻¹)` bound using explicit logarithmic estimates. See [Novak2001] for the
paper context.

## Main statements

* `section4_accuracy`: Under the sample-size condition, an approximation within `ε/3` of the
  sample mean with probability at least 7/8 is within `ε` of the expectation with probability at
  least 3/4.
* `section4_complexity_bound`: The assumed mean-estimation cost and logarithmic estimates give
  the randomized quantum complexity bound with constant `3 * C * (K + 1)`.
* `sec4_auto`: The stated mean-estimation cost model implies `IsRandomQuantumUpper` with the
  explicit constant obtained from `log_ceil_bound` and `log_log_bound`.

## References

* [Novak, 2001][Novak2001]
-/

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Qatlib.Papers.QIntegration00.MainResults.RandomQuantum

open scoped Classical

open Defs
open Qatlib.Concepts.MonteCarloMean.FinDistBounds
open Qatlib.Concepts.AmplitudeCore.InvFreeSampling
open Qatlib.Concepts.HspRecovery.BackendAudit

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The bound `comp ε ≤ C * ε⁻¹ * log(ε⁻¹)` for every `0 < ε ≤ 1/2`. -/
def IsRandomQuantumUpper (C : ℝ) (comp : ℝ → ℝ) : Prop :=
  ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2), comp ε ≤ C * ε⁻¹ * Real.log ε⁻¹

/-- A real function bounded in absolute value by one has variance at most one under a finite
distribution. -/
theorem variance_le_one (p : FinDist X) (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1) :
    p.variance f ≤ 1 := by
  rw [FinDist.variance_eq_expect_sq_sub]
  have hsq : ∀ x, (f x) ^ 2 ≤ 1 := by
    intro x
    rw [← sq_abs]
    exact pow_le_one₀ (abs_nonneg _) (hf x)
  have hexp : p.expect (fun x => (f x) ^ 2) ≤ 1 := by
    change (∑ x, p.prob x * (f x) ^ 2) ≤ 1
    calc ∑ x, p.prob x * (f x) ^ 2 ≤ ∑ x, p.prob x * 1 :=
          Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (hsq x) (p.nonneg x)
      _ = 1 := by simp [p.sum_one]
  have hμ : 0 ≤ (p.expect f) ^ 2 := sq_nonneg _
  linarith

/-- If `n > 0` and `n * ε² ≥ 72`, a bounded function's sample mean deviates from its expectation
by more than `ε/3` with probability at most 1/8. -/
theorem chebyshev_tail {n : ℕ} (p : FinDist X) (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (hn72 : 72 ≤ (n : ℝ) * ε ^ 2) :
    FinDist.probEvent (L := n) p
        (fun ω : Fin n → X => ε / 3 < |FinDist.avg f ω - p.expect f|) ≤ 1 / 8 := by
  have hε3 : 0 < ε / 3 := by linarith
  have hcheb := FinDist.chebyshev_avg (L := n) p f hn (ε / 3) hε3
  have hvar := variance_le_one p f hf
  have hden : 0 < (n : ℝ) * (ε / 3) ^ 2 := by positivity
  have hstep : p.variance f / ((n : ℝ) * (ε / 3) ^ 2) ≤ 1 / 8 := by
    rw [div_le_iff₀ hden]
    have hkey : (1 : ℝ) ≤ (1 / 8) * ((n : ℝ) * (ε / 3) ^ 2) := by
      have heq : (1 / 8) * ((n : ℝ) * (ε / 3) ^ 2) = ((n : ℝ) * ε ^ 2) / 72 := by ring
      rw [heq, le_div_iff₀ (by norm_num : (0 : ℝ) < 72)]
      linarith
    linarith
  exact hcheb.trans hstep

/-- Under the sample-size condition `n * ε² ≥ 72`, the sample mean of a function bounded by one
is within `ε/3` of its expectation with probability at least 7/8. -/
theorem good_event_mass {n : ℕ} (p : FinDist X) (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (hn72 : 72 ≤ (n : ℝ) * ε ^ 2) :
    7 / 8 ≤ FinDist.probEvent (L := n) p
        (fun ω : Fin n → X => ¬ (ε / 3 < |FinDist.avg f ω - p.expect f|)) := by
  have hbad := chebyshev_tail p f hf hn hε hn72
  have hcompl := probEvent_compl (L := n) p
      (fun ω : Fin n → X => ¬ (ε / 3 < |FinDist.avg f ω - p.expect f|))
  have hcongr : FinDist.probEvent (L := n) p
        (fun ω : Fin n → X => ¬ ¬ (ε / 3 < |FinDist.avg f ω - p.expect f|)) =
      FinDist.probEvent (L := n) p
        (fun ω : Fin n → X => ε / 3 < |FinDist.avg f ω - p.expect f|) :=
    probEvent_congr (L := n) p _ _ (fun ω => by simp)
  rw [hcongr] at hcompl
  linarith

/-- Two successive absolute errors bounded by `ε/3` give a total absolute error at most `2ε/3`. -/
theorem triangle_three {I Q A : ℝ} {ε : ℝ}
    (h1 : |I - Q| ≤ ε / 3) (h2 : |Q - A| ≤ ε / 3) :
    |I - A| ≤ 2 * ε / 3 := by
  calc |I - A| = |(I - Q) + (Q - A)| := by congr 1; ring
    _ ≤ |I - Q| + |Q - A| := abs_add_le _ _
    _ ≤ ε / 3 + ε / 3 := add_le_add h1 h2
    _ = 2 * ε / 3 := by ring

/-- Two events each of probability at least 7/8 have intersection probability at least 3/4. -/
theorem two_good_event_mass {n : ℕ} (p : FinDist X)
    {E F : (Fin n → X) → Prop} [DecidablePred E] [DecidablePred F]
    (hE : 7 / 8 ≤ FinDist.probEvent (L := n) p E)
    (hF : 7 / 8 ≤ FinDist.probEvent (L := n) p F) :
    3 / 4 ≤ FinDist.probEvent (L := n) p (fun ω => E ω ∧ F ω) := by
  have hcomplE := probEvent_compl (L := n) p E
  have hcomplF := probEvent_compl (L := n) p F
  have hcomplG := probEvent_compl (L := n) p (fun ω => E ω ∧ F ω)
  have hunion : FinDist.probEvent (L := n) p (fun ω => ¬ E ω ∨ ¬ F ω) ≤
      FinDist.probEvent (L := n) p (fun ω => ¬ E ω) +
        FinDist.probEvent (L := n) p (fun ω => ¬ F ω) :=
    probEvent_union_le (L := n) p (fun ω => ¬ E ω) (fun ω => ¬ F ω)
  have hG : FinDist.probEvent (L := n) p (fun ω => ¬ (E ω ∧ F ω)) =
      FinDist.probEvent (L := n) p (fun ω => ¬ E ω ∨ ¬ F ω) :=
    probEvent_congr (L := n) p _ _ (fun ω => not_and_or)
  rw [hG] at hcomplG
  linarith

/-- Under the sample-size condition, an approximation within `ε/3` of the sample mean with
probability at least 7/8 is within `ε` of the expectation with probability at least 3/4. See
[Novak2001]. -/
theorem section4_accuracy {n : ℕ} (p : FinDist X) (f : X → ℝ) (hf : ∀ x, |f x| ≤ 1)
    (hn : 0 < n) {ε : ℝ} (hε : 0 < ε) (hn72 : 72 ≤ (n : ℝ) * ε ^ 2)
    {A : (Fin n → X) → ℝ}
    (hquant : 7 / 8 ≤ FinDist.probEvent (L := n) p
      (fun ω : Fin n → X => |A ω - FinDist.avg f ω| ≤ ε / 3)) :
    FinDist.probEvent (L := n) p
        (fun ω : Fin n → X => |A ω - p.expect f| ≤ ε) ≥ 3 / 4 := by
  have hsampling : 7 / 8 ≤ FinDist.probEvent (L := n) p
      (fun ω : Fin n → X => ¬ (ε / 3 < |FinDist.avg f ω - p.expect f|)) :=
    good_event_mass p f hf hn hε hn72
  have hgood : 3 / 4 ≤ FinDist.probEvent (L := n) p
      (fun ω : Fin n → X =>
        ¬ (ε / 3 < |FinDist.avg f ω - p.expect f|) ∧ |A ω - FinDist.avg f ω| ≤ ε / 3) :=
    two_good_event_mass p hsampling hquant
  have hmono : FinDist.probEvent (L := n) p
        (fun ω : Fin n → X =>
          ¬ (ε / 3 < |FinDist.avg f ω - p.expect f|) ∧ |A ω - FinDist.avg f ω| ≤ ε / 3)
      ≤ FinDist.probEvent (L := n) p
          (fun ω : Fin n → X => |A ω - p.expect f| ≤ ε) := by
    refine probEvent_mono p _ _ (fun ω hω => ?_)
    have h1 : |p.expect f - FinDist.avg f ω| ≤ ε / 3 := by
      rw [abs_sub_comm]
      exact le_of_not_gt hω.1
    have h2 : |FinDist.avg f ω - A ω| ≤ ε / 3 := by
      rw [abs_sub_comm]; exact hω.2
    have h3 : |p.expect f - A ω| ≤ 2 * ε / 3 := triangle_three h1 h2
    calc |A ω - p.expect f| = |p.expect f - A ω| := abs_sub_comm _ _
      _ ≤ 2 * ε / 3 := h3
      _ ≤ ε := by linarith
  linarith

/-- The stated sample-size cost estimate and logarithmic bounds imply `IsRandomQuantumUpper`
with constant `3 * C * (K + 1)`. -/
theorem mean_cost_bound {C K : ℝ} (hC : 0 < C)
    {cost : ℝ → ℝ}
    (hcost : ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2),
      cost ε ≤ C * (ε / 3)⁻¹ *
        (Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) + Real.log (Real.log ε⁻¹)))
    (hlogn : ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2),
      Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) ≤ K * Real.log ε⁻¹)
    (hloglog : ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2),
      Real.log (Real.log ε⁻¹) ≤ Real.log ε⁻¹) :
    IsRandomQuantumUpper (C * 3 * (K + 1)) cost := by
  intro ε hεmem
  obtain ⟨hε, hε2⟩ := hεmem
  have h1 := hcost ε ⟨hε, hε2⟩
  have h2 := hlogn ε ⟨hε, hε2⟩
  have h3 := hloglog ε ⟨hε, hε2⟩
  have hinv : (ε / 3)⁻¹ = 3 * ε⁻¹ := by rw [inv_div, div_eq_mul_inv]
  rw [hinv] at h1
  have hsum : Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) + Real.log (Real.log ε⁻¹)
      ≤ (K + 1) * Real.log ε⁻¹ := by linarith
  have hC3 : 0 ≤ C * (3 * ε⁻¹) := by
    have hεinv : 0 < ε⁻¹ := inv_pos.mpr hε
    have hpos : 0 < 3 * ε⁻¹ := by positivity
    exact mul_nonneg (le_of_lt hC) (le_of_lt hpos)
  calc cost ε ≤ C * (3 * ε⁻¹) *
        (Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) + Real.log (Real.log ε⁻¹)) := h1
    _ ≤ C * (3 * ε⁻¹) * ((K + 1) * Real.log ε⁻¹) :=
          mul_le_mul_of_nonneg_left hsum hC3
    _ = C * 3 * (K + 1) * ε⁻¹ * Real.log ε⁻¹ := by ring

/-- The assumed mean-estimation cost and logarithmic estimates give the randomized quantum
complexity bound with constant `3 * C * (K + 1)`. See [Novak2001]. -/
theorem section4_complexity_bound {C K : ℝ} (hC : 0 < C)
    {cost : ℝ → ℝ}
    (hcost : ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2),
      cost ε ≤ C * (ε / 3)⁻¹ *
        (Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) + Real.log (Real.log ε⁻¹)))
    (hlogn : ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2),
      Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) ≤ K * Real.log ε⁻¹)
    (hloglog : ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2),
      Real.log (Real.log ε⁻¹) ≤ Real.log ε⁻¹) :
    IsRandomQuantumUpper (C * 3 * (K + 1)) cost :=
  mean_cost_bound hC hcost hlogn hloglog

/-- For `0 < ε ≤ 1/2`, the iterated logarithm `log(log(ε⁻¹))` is at most `log(ε⁻¹)`. See
[Novak2001]. -/
theorem log_log_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    Real.log (Real.log ε⁻¹) ≤ Real.log ε⁻¹ := by
  have h2 : (2:ℝ) ≤ ε⁻¹ := by
    have h : (1:ℝ)/(1/2) ≤ 1/ε := one_div_le_one_div_of_le hε0 hε
    norm_num at h
    simpa [one_div] using h
  have hy2 : Real.log 2 ≤ Real.log ε⁻¹ := Real.log_le_log (by norm_num) h2
  have hy : 0 < Real.log ε⁻¹ := lt_of_lt_of_le (Real.log_pos (by norm_num)) hy2
  have := Real.log_le_sub_one_of_pos hy
  linarith

/-- For `0 < ε ≤ 1/2`, the logarithm of `ceil(72/ε²)` is at most `(2 + log(289/4)/log 2) *
log(ε⁻¹)`. See [Novak2001]. -/
theorem log_ceil_bound {ε : ℝ} (hε0 : 0 < ε) (hε : ε ≤ 1 / 2) :
    Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) ≤
      (2 + Real.log (289/4) / Real.log 2) * Real.log ε⁻¹ := by
  have hεsq : ε ^ 2 ≤ 1 / 4 := by
    calc ε ^ 2 ≤ (1/2 : ℝ) ^ 2 := pow_le_pow_left₀ (le_of_lt hε0) hε 2
      _ = 1/4 := by norm_num
  have hεsqpos : 0 < ε ^ 2 := by positivity
  have ha : (0:ℝ) < 72 / ε ^ 2 := by positivity
  have h1 : ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) < 72 / ε ^ 2 + 1 :=
    Nat.ceil_lt_add_one (le_of_lt ha)
  have h2 : (1:ℝ) ≤ (1/4) / ε ^ 2 := by
    rw [le_div_iff₀ hεsqpos]; linarith
  have h3 : 72 / ε ^ 2 + 1 ≤ 289/4 / ε ^ 2 := by
    have hsum : 72 / ε ^ 2 + (1/4) / ε ^ 2 = 289/4 / ε ^ 2 := by
      field_simp
      norm_num
    linarith
  have hceil : ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) ≤ 289/4 / ε ^ 2 := le_trans (le_of_lt h1) h3
  have hcpos : (0:ℝ) < ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) := by
    have hpos : 0 < Nat.ceil (72 / ε ^ 2) := Nat.ceil_pos.mpr ha
    exact_mod_cast hpos
  have hlog : Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) ≤ Real.log (289/4 / ε ^ 2) :=
    Real.log_le_log hcpos hceil
  have hsplit : Real.log (289/4 / ε ^ 2) = Real.log (289/4) + 2 * Real.log ε⁻¹ := by
    rw [Real.log_div (by norm_num) (ne_of_gt hεsqpos), Real.log_pow, Real.log_inv]
    ring
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogε2 : Real.log 2 ≤ Real.log ε⁻¹ := by
    have h2' : (2:ℝ) ≤ ε⁻¹ := by
      have h : (1:ℝ)/(1/2) ≤ 1/ε := one_div_le_one_div_of_le hε0 hε
      norm_num at h
      simpa [one_div] using h
    exact Real.log_le_log (by norm_num) h2'
  have hcst : Real.log (289/4) ≤ (Real.log (289/4) / Real.log 2) * Real.log ε⁻¹ := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2pos]
    nlinarith [Real.log_pos (by norm_num : (1:ℝ) < 289/4)]
  rw [hsplit] at hlog
  calc Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ)
      ≤ Real.log (289/4) + 2 * Real.log ε⁻¹ := hlog
    _ ≤ (Real.log (289/4) / Real.log 2) * Real.log ε⁻¹ + 2 * Real.log ε⁻¹ := by linarith
    _ = (2 + Real.log (289/4) / Real.log 2) * Real.log ε⁻¹ := by ring

/-- The stated mean-estimation cost model implies `IsRandomQuantumUpper` with the explicit
constant obtained from `log_ceil_bound` and `log_log_bound`. See [Novak2001]. -/
theorem sec4_auto {C : ℝ} (hC : 0 < C) {cost : ℝ → ℝ}
    (hcost : ∀ ε ∈ Set.Ioc (0 : ℝ) (1 / 2),
      cost ε ≤ C * (ε / 3)⁻¹ *
        (Real.log ((Nat.ceil (72 / ε ^ 2) : ℕ) : ℝ) + Real.log (Real.log ε⁻¹))) :
    IsRandomQuantumUpper (C * 3 * (2 + Real.log (289/4) / Real.log 2 + 1)) cost :=
  mean_cost_bound hC hcost
    (fun _ hε => log_ceil_bound hε.1 hε.2)
    (fun _ hε => log_log_bound hε.1 hε.2)

end Qatlib.Papers.QIntegration00.MainResults.RandomQuantum
