/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.DimConditioning.EventCondition.RecordMixtures.PaidRetryExecution
import Qatlib.Concepts.DimConditioning.EventCondition.RecordMixtures.AcceptedRecordMixture
import Qatlib.Foundations.PureStateMath.BornBridge.PhyslibStates

/-!
# Conditioning after bounded fresh state retries

This module analyzes bounded retries in which a preparation channel replaces each input by a
fresh copy of a fixed density operator. It gives exact accepted and exhausted branch formulas
and geometric terminal probabilities.

`conditional_eq` identifies the accepted retry conditional with the single attempt conditional,
and `posterior_bound` transfers the accepted record error bound to retries. Replacement channels
and conditional states fit the instrument framework of [Watrous2018].

## Main statements

* `terminal_probabilities`: geometric exhaustion and acceptance probabilities.
* `conditional_eq`: accepted retries preserve the single attempt conditional state.
* `posterior_bound`: the posterior trace distance bound for any positive retry count.

## References

* [Watrous, 2018][Watrous2018]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.DimConditioning.EventCondition.PaidRetry

open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Foundations.PureStateMath
open Matrix
open scoped ComplexOrder
open RecordForgottenInstrument

variable {R : Type} [Fintype R] {N D : ℕ}

/-- The preparation channel maps every operator `A` to `trace A • ρ`. -/
def Fresh (P : QuantumChannel D N) (ρ : Operator N) : Prop :=
  ∀ A, P.map A = trace A • ρ

/-- The quantum replacement channel preparing the fixed density operator `ρ` from a nonzero
input dimension. -/
def replacement [NeZero D] (ρ : Operator N) (hρ : IsDensityOperator ρ) :
    QuantumChannel D N :=
  Qatlib.Concepts.ChannelTheory.Stinespring.ofPhyslib
    (CPTPMap.replacement
      (Qatlib.Foundations.PureStateMath.BornBridge.densityOperatorEquivMState N ⟨ρ, hρ⟩))

/-- The replacement channel satisfies `Fresh` for its prepared density operator. -/
theorem replacement_fresh [NeZero D] (ρ : Operator N) (hρ : IsDensityOperator ρ) :
    Fresh (replacement (D := D) ρ hρ) ρ := by
  intro A
  ext i j
  change (∑ k : Fin D, A k k * ρ i j) = (∑ k : Fin D, A k k) * ρ i j
  exact (Finset.sum_mul _ _ _).symm

/-- The finite geometric sum defined by zero initial value and recurrence `retryWeight q (n + 1)
= 1 + q * retryWeight q n`. -/
def retryWeight (q : ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => 1 + q * retryWeight q n

/-- A stopped Boolean branch is the sum of transcript execution maps whose acceptance flag
equals that branch. -/
theorem stopped_branch (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    (n : ℕ) (b : Bool) (A : Operator D) :
    (stopped I P n).branch b A =
      ∑ t : Transcript R n, if accepted t = b then (execute I P t).map A else 0 := by
  classical
  simp only [stopped, run, Instrument.ofBranches, Instrument.coarsen, LinearMap.sum_apply,
    Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t _
  split_ifs <;> rfl

/-- With zero attempts, the accepted branch is zero and the exhausted branch is the input
operator. -/
theorem stopped_zero (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    (b : Bool) (A : Operator D) :
    (stopped I P 0).branch b A = if b then 0 else A := by
  cases b <;> simp [stopped_branch, Transcript, accepted, execute]

/-- A retry step splits into immediate acceptance and the remaining stopped execution applied to
the rejected prepared output. -/
theorem stopped_succ (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    (n : ℕ) (b : Bool) (A : Operator D) :
    (stopped I P (n + 1)).branch b A =
      (if b then (forgetRecord I).branch true (P.map A) else 0) +
        (stopped I P n).branch b ((forgetRecord I).branch false (P.map A)) := by
  classical
  rw [stopped_branch]
  change (∑ t : R ⊕ (R × Transcript R n),
      if accepted (n := n + 1) t = b then (execute I P (n := n + 1) t).map A else 0) = _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [accepted, execute, LinearMap.comp_apply]
  have htail : (∑ r : R, ∑ t : Transcript R n,
      if accepted t = b then (execute I P t).map (I.branch (r, false) (P.map A)) else 0) =
      (stopped I P n).branch b ((forgetRecord I).branch false (P.map A)) := by
    simp_rw [← stopped_branch]
    rw [RecordForgottenInstrument.branch, map_sum]
  rw [htail]
  cases b <;> simp [RecordForgottenInstrument.branch]

/-- With fresh preparation, the accepted branch equals the single attempt accepted output scaled
by the input trace and the geometric retry weight. -/
theorem accepted_branch (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    (ρ : Operator N) (hρ : IsDensityOperator ρ) (hP : Fresh P ρ)
    (n : ℕ) (A : Operator D) :
    (stopped I P n).branch true A =
      (trace A * (retryWeight (instrumentProb (forgetRecord I) ρ false) n : ℂ)) •
        (forgetRecord I).branch true ρ := by
  induction n generalizing A with
  | zero => simp [stopped_zero, retryWeight]
  | succ n ih =>
    rw [stopped_succ, if_pos rfl, ih, hP A, map_smul, map_smul,
      trace_smul, trace_branch_eq (forgetRecord I) hρ.1 false]
    rw [← add_smul]
    congr 1
    simp only [retryWeight, Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_mul]
    ring

/-- With fresh preparation, the exhausted branch trace equals the input trace times the single
attempt rejection probability raised to the retry count. -/
theorem exhausted_trace (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    (ρ : Operator N) (hρ : IsDensityOperator ρ) (hP : Fresh P ρ)
    (n : ℕ) (A : Operator D) :
    trace ((stopped I P n).branch false A) =
      trace A * (instrumentProb (forgetRecord I) ρ false : ℂ) ^ n := by
  induction n generalizing A with
  | zero => simp [stopped_zero]
  | succ n ih =>
    rw [stopped_succ, if_neg Bool.false_ne_true, zero_add, ih, hP A, map_smul,
      trace_smul, trace_branch_eq (forgetRecord I) hρ.1 false, pow_succ]
    ring

/-- For fresh preparation and density input, exhaustion has probability `(1 - p) ^ n` and
acceptance has probability `1 - (1 - p) ^ n`, where `p` is the single attempt acceptance
probability. -/
theorem terminal_probabilities (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    (ρ : Operator N) (hρ : IsDensityOperator ρ) (hP : Fresh P ρ)
    (n : ℕ) (σ : Operator D) (hσ : IsDensityOperator σ) :
    instrumentProb (stopped I P n) σ false =
        (1 - instrumentProb (forgetRecord I) ρ true) ^ n ∧
    instrumentProb (stopped I P n) σ true =
        1 - (1 - instrumentProb (forgetRecord I) ρ true) ^ n := by
  have hsingle := sum_instrumentProb_isDensityOperator (forgetRecord I) hρ
  simp only [Fintype.sum_bool] at hsingle
  have hq : instrumentProb (forgetRecord I) ρ false =
      1 - instrumentProb (forgetRecord I) ρ true := by linarith
  have he : instrumentProb (stopped I P n) σ false =
      instrumentProb (forgetRecord I) ρ false ^ n := by
    change (trace ((stopped I P n).branch false σ)).re = _
    rw [exhausted_trace I P ρ hρ hP, hσ.2, one_mul, ← Complex.ofReal_pow,
      Complex.ofReal_re]
  have htotal := sum_instrumentProb_isDensityOperator (stopped I P n) hσ
  simp only [Fintype.sum_bool] at htotal
  rw [hq] at he
  exact ⟨he, by linarith⟩

/-- If a fresh single attempt has zero acceptance probability, every stopped retry accepted
output and its associated probability are zero. -/
theorem zero_acceptance (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    (ρ : Operator N) (hρ : IsDensityOperator ρ) (hP : Fresh P ρ)
    (hp : instrumentProb (forgetRecord I) ρ true = 0) (n : ℕ) (A : Operator D) :
    (stopped I P n).branch true A = 0 ∧ instrumentProb (stopped I P n) A true = 0 := by
  have hb := (instrumentProb_eq_zero_iff (forgetRecord I) hρ.1 true).mp hp
  have hz : (stopped I P n).branch true A = 0 := by
    rw [accepted_branch I P ρ hρ hP, hb, smul_zero]
  exact ⟨hz, by rw [instrumentProb, hz, trace_zero, Complex.zero_re]⟩

/-- The geometric retry weight is positive for nonnegative `q` and a positive retry count. -/
theorem retryWeight_pos {q : ℝ} (hq : 0 ≤ q) {n : ℕ} (hn : 0 < n) :
    0 < retryWeight q n := by
  have hnonneg : ∀ k, 0 ≤ retryWeight q k := by
    intro k
    induction k with
    | zero => exact le_refl 0
    | succ k ih => exact add_nonneg zero_le_one (mul_nonneg hq ih)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact add_pos_of_pos_of_nonneg zero_lt_one (mul_nonneg hq (hnonneg k))

/-- Positive single attempt acceptance and a positive retry count give positive stopped
acceptance for fresh preparation and density input. -/
theorem accepted_probability_pos (I : Instrument (R × Bool) N D)
    (P : QuantumChannel D N) (ρ : Operator N) (hρ : IsDensityOperator ρ)
    (hP : Fresh P ρ) {n : ℕ} (hn : 0 < n) (σ : Operator D)
    (hσ : IsDensityOperator σ)
    (hp : 0 < instrumentProb (forgetRecord I) ρ true) :
    0 < instrumentProb (stopped I P n) σ true := by
  have hw := retryWeight_pos (instrumentProb_nonneg (forgetRecord I) hρ.1 false) hn
  have he : instrumentProb (stopped I P n) σ true =
      retryWeight (instrumentProb (forgetRecord I) ρ false) n *
        instrumentProb (forgetRecord I) ρ true := by
    change (trace ((stopped I P n).branch true σ)).re = _
    rw [accepted_branch I P ρ hρ hP, hσ.2, one_mul, trace_smul,
      trace_branch_eq (forgetRecord I) hρ.1 true, smul_eq_mul, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [he]
  exact mul_pos hw hp

/-- With fresh preparation and positive single attempt and stopped acceptance probabilities, the
stopped accepted conditional state equals the single attempt accepted conditional state. -/
theorem conditional_eq (I : Instrument (R × Bool) N D) (P : QuantumChannel D N)
    (ρ : Operator N) (hρ : IsDensityOperator ρ) (hP : Fresh P ρ)
    (n : ℕ) (σ : Operator D) (hσ : IsDensityOperator σ)
    (hp : 0 < instrumentProb (forgetRecord I) ρ true)
    (hs : 0 < instrumentProb (stopped I P n) σ true) :
    (stopped I P n).conditionalState σ true hs =
      (forgetRecord I).conditionalState ρ true hp := by
  let w := retryWeight (instrumentProb (forgetRecord I) ρ false) n
  have he : (stopped I P n).branch true σ = (w : ℂ) • (forgetRecord I).branch true ρ := by
    rw [accepted_branch I P ρ hρ hP, hσ.2, one_mul]
  have hm : instrumentProb (stopped I P n) σ true =
      w * instrumentProb (forgetRecord I) ρ true := by
    change (trace ((stopped I P n).branch true σ)).re = _
    rw [he, trace_smul, trace_branch_eq (forgetRecord I) hρ.1 true,
      smul_eq_mul, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hw : w ≠ 0 := by intro hz; rw [hm, hz, zero_mul] at hs; exact (lt_irrefl 0) hs
  have hwC : (w : ℂ) ≠ 0 := by exact_mod_cast hw
  have hpC : (instrumentProb (forgetRecord I) ρ true : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Instrument.conditionalState, Instrument.conditionalState, he, hm,
    Complex.ofReal_mul, smul_smul]
  congr 1
  field_simp

/-- Under fresh preparation and the good record error and mass assumptions, any positive retry
count has acceptance probability `1 - (1 - p) ^ n` and accepted trace distance at most `η +
ζ / (1 - ζ - δ)`. -/
theorem posterior_bound [DecidableEq R] (I : Instrument (R × Bool) N D)
    (P : QuantumChannel D N) (ρ : Operator N) (hρ : IsDensityOperator ρ)
    (hP : Fresh P ρ) (σ : Operator D) (hσ : IsDensityOperator σ)
    {n : ℕ} (hn : 0 < n) (target : Operator D) (ht : IsDensityOperator target)
    (good : Finset R) (η ζ δ : ℝ) (hη : 0 ≤ η) (hζ : 0 ≤ ζ) (hδ : 0 ≤ δ)
    (hsmall : ζ + δ < 1)
    (hgood : ∀ r ∈ good, ∀ hp : 0 < instrumentProb I ρ (r, true),
      traceNorm (I.conditionalState ρ (r, true) hp - target) / 2 ≤ η)
    (hbad : (∑ r : R, if r ∈ good then 0 else
      instrumentProb I ρ (r, true) + instrumentProb I ρ (r, false)) ≤ ζ)
    (hfail : ∀ r ∈ good, instrumentProb I ρ (r, false) ≤
      δ * (instrumentProb I ρ (r, true) + instrumentProb I ρ (r, false))) :
    ∃ hs : 0 < instrumentProb (stopped I P n) σ true,
      instrumentProb (stopped I P n) σ true =
          1 - (1 - instrumentProb (forgetRecord I) ρ true) ^ n ∧
        traceNorm ((stopped I P n).conditionalState σ true hs - target) / 2 ≤
          η + ζ / (1 - ζ - δ) := by
  obtain ⟨hp, _, herr⟩ := AcceptedRecordMixture.output_bound I ρ hρ target ht good η ζ δ
    hη hζ hδ hsmall hgood hbad hfail
  have hs := accepted_probability_pos I P ρ hρ hP hn σ hσ hp
  refine ⟨hs, (terminal_probabilities I P ρ hρ hP n σ hσ).2, ?_⟩
  rw [conditional_eq I P ρ hρ hP n σ hσ hp hs]
  exact herr

end Qatlib.Concepts.DimConditioning.EventCondition.PaidRetry
