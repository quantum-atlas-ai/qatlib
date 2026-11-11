/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.QPowerSimon97.Recovery.NativeRetryConstructionDefs
import Qatlib.Concepts.HspRecovery.Distinguisher.BoundedErrorNearPeriodSimo

/-!
# Amplification bounds for Simon experiments

Analyzes independent decoded Simon runs and the decision rule that rejects if any output differs
from the decoded zero register. Injective functions have a union-bound error estimate, while a
nonzero near-period gives geometric decay of the opposite error, supporting the bounded-error
extension in [Simon1997].

## Main statements

* `amplified_true_le`: For an injective function, the amplified rejection law assigns mass at
  most `r * (1 / 2)^k` to `true`.
* `amplified_false_le`: Under the stated nonzero near-period and sample-count assumptions, the
  amplified rejection law assigns mass at most `(3 / 4)^r` to `false`.

## References

* [Simon, 1997][Simon1997]
-/

set_option warningAsError false
set_option backward.isDefEq.respectTransparency false

open Qatlib.Concepts.ChannelTheory.Stinespring
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Papers.QPowerSimon97.Recovery.SimonQueryTree

open Qatlib.Concepts.HspRecovery.ReductionCore
open Qatlib.Concepts.LinearLearning.ConcisePipeline
open Qatlib.Concepts.PauliClifford.ExactRank

open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.AEMeanReadout.LocalAEBackend.CostedLaw
open Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.HspRecovery.Distinguisher

set_option autoImplicit false

open Qatlib.Concepts.AbelianDecoders.SimonDecoding Qatlib.Concepts.HspRecovery.BackendAudit
open Qatlib.Concepts.WalkFind.UniformThree.FiniteAbelian Qatlib.Concepts.HspRecovery.Distinguisher
open Qatlib.Foundations.StandardDefs.WindowSim
open Qatlib.Concepts.QtmSimulation.Phi3Compilation
open Qatlib.Concepts.UniformBqp.Phi3Compile
open Qatlib.Concepts.CircuitImpl.Phi3Universal
open Matrix
open scoped Classical BigOperators ENNReal

namespace Qatlib.Papers.QPowerSimon97.Recovery
noncomputable section

/-- The first two recorded cost fields of a decoded run with `n + k` samples are `n + k` and `2
* (n + k)`. -/
theorem simonDecodedRun_ledger {n k : ℕ} {R : Type} [AddCommGroup R] [Fintype R]
    [DecidableEq R] (f : BooleanVec n → R) :
    (simonDecodedRun f (n + k)).2.1 = n + k ∧
      (simonDecodedRun f (n + k)).2.2.1 = 2 * (n + k) := by
  have h :=
      (Qatlib.Concepts.HspRecovery.Distinguisher.boundedErrorNearPeriodDistinguisher n k R f).1
  exact ⟨congrArg Prod.fst h, congrArg (Prod.fst ∘ Prod.snd) h⟩
end
noncomputable section

/-- The mass at `true` in a Boolean probability mass function equals the event mass of equality
to `true`. -/
lemma pmf_bool_true (p : PMF Bool) : p true = event p (fun b => b = true) := by
  classical
  unfold event expectation
  rw [tsum_fintype, Fintype.sum_bool]
  simp
end
noncomputable section

/-- The mass at `false` in a Boolean probability mass function equals the event mass of equality
to `false`. -/
lemma pmf_bool_false (p : PMF Bool) : p false = event p (fun b => b = false) := by
  classical
  unfold event expectation
  rw [tsum_fintype, Fintype.sum_bool]
  simp
end
noncomputable section

/-- An event and its complement have masses summing to one. -/
lemma event_partition {α : Type*} (p : PMF α) (E : α → Prop) :
    event p E + event p (fun a => ¬ E a) = 1 := by
  classical
  unfold event expectation
  have hpt : ∀ a, (if E a then (1 : ℝ≥0∞) else 0) + (if ¬ E a then 1 else 0) = 1 := by
    intro a
    by_cases h : E a
    · rw [if_pos h, if_neg (fun hne => hne h)]
      simp [add_zero]
    · rw [if_neg h, if_pos h]
      simp [zero_add]
  rw [← ENNReal.tsum_add]
  dsimp
  have hfun : (fun a => (p a * (if E a then (1 : ℝ≥0∞) else 0)) +
      p a * (if (fun b => ¬ E b) a then 1 else 0)) = fun a => p a := by
    funext a
    rw [← mul_add, hpt a, mul_one]
  convert! (congrArg (fun f => ∑' a, f a) hfun).trans (PMF.tsum_coe p) using 7
end
noncomputable section

/-- Some entry of a vector formed by `Fin.cons` differs from the decoded zero result exactly
when its head does or some tail entry does. -/
lemma cons_reject {n r : ℕ} (a : Option (Reg n)) (v : Fin r → Option (Reg n)) :
    (∃ i : Fin (r + 1), (Fin.cons a v : Fin (r + 1) → Option (Reg n)) i ≠ some (ZeroStr n)) ↔
      a ≠ some (ZeroStr n) ∨ ∃ j : Fin r, v j ≠ some (ZeroStr n) := by
  constructor
  · rintro ⟨i, hi⟩
    cases i using Fin.cases with
    | zero => exact Or.inl (by simpa [Fin.cons_zero] using! hi)
    | succ j => exact Or.inr ⟨j, by simpa [Fin.cons_succ] using! hi⟩
  · rintro (ha | ⟨j, hj⟩)
    · exact ⟨0, by simpa [Fin.cons_zero] using! ha⟩
    · exact ⟨j.succ, by simpa [Fin.cons_succ] using! hj⟩
end
noncomputable section

/-- For `k ≥ 2`, the expression `((k - 1) / k)^k` is at most `(k / (k + 1))^(k + 1)` over the
reals. -/
lemma quarter_step (k : ℕ) (hk : 2 ≤ k) :
    (((k - 1 : ℝ) / k) ^ k) ≤ ((k : ℝ) / (k + 1)) ^ (k + 1) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hk)
  have hk2 : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hden : (0 : ℝ) < (k : ℝ) ^ 2 - 1 := by nlinarith [hk2]
  have ha : (0 : ℝ) ≤ 1 / ((k : ℝ) ^ 2 - 1) := by positivity
  have hber := one_add_mul_le_pow (a := 1 / ((k : ℝ) ^ 2 - 1)) (by linarith) k
  have hlin : (1 : ℝ) + 1 / k ≤ 1 + (k : ℝ) * (1 / ((k : ℝ) ^ 2 - 1)) := by
    have hsame : (k : ℝ) * (1 / ((k : ℝ) ^ 2 - 1)) = (k : ℝ) / ((k : ℝ) ^ 2 - 1) := by
      field_simp
    have hge : (1 : ℝ) / k ≤ (k : ℝ) / ((k : ℝ) ^ 2 - 1) := by
      rw [div_le_div_iff₀ hk0 hden]
      nlinarith
    linarith [hsame, hge]
  have hpow : (1 : ℝ) + 1 / k ≤ (1 + 1 / ((k : ℝ) ^ 2 - 1)) ^ k := le_trans hlin hber
  have hrewrite : (k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1) = 1 + 1 / ((k : ℝ) ^ 2 - 1) := by
    have hnz : (k : ℝ) ^ 2 - 1 ≠ 0 := by linarith
    calc
      (k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)
          = (((k : ℝ) ^ 2 - 1) + 1) / ((k : ℝ) ^ 2 - 1) := by ring
      _ = ((k : ℝ) ^ 2 - 1) / ((k : ℝ) ^ 2 - 1) + 1 / ((k : ℝ) ^ 2 - 1) := by
          rw [add_div]
      _ = 1 + 1 / ((k : ℝ) ^ 2 - 1) := by rw [div_self hnz]
  have hform : ((k : ℝ) + 1) / k = 1 + 1 / (k : ℝ) := by
    have hnz : (k : ℝ) ≠ 0 := by linarith
    calc
      ((k : ℝ) + 1) / k = (k : ℝ) / k + 1 / k := by rw [add_div]
      _ = 1 + 1 / k := by rw [div_self hnz]
  rw [← hrewrite, ← hform, div_pow, div_le_div_iff₀ (by positivity) (by positivity)] at hpow
  rw [div_pow, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have hmul : ((k : ℝ) - 1) * ((k : ℝ) + 1) = (k : ℝ) ^ 2 - 1 := by ring
  rw [pow_succ' ((k : ℝ) + 1), mul_comm (((k : ℝ) - 1) ^ k), mul_assoc,
    mul_comm (((k : ℝ) + 1) ^ k) (((k : ℝ) - 1) ^ k), ← mul_pow, hmul]
  refine le_trans hpow ?_
  apply le_of_eq
  rw [← pow_mul, mul_comm, ← pow_succ']
  have hexp : 2 * k + 1 = k + (k + 1) := by omega
  rw [hexp, pow_add, mul_comm]
end
noncomputable section

/-- For an integer `m ≥ 2`, the real expression `(1 - 1 / m)^m` is at least `1 / 4`. -/
lemma one_sub_inv_pow_ge_quarter (m : ℕ) (hm : 2 ≤ m) :
    (1 / 4 : ℝ) ≤ (1 - 1 / (m : ℝ)) ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num
  | succ m hm ih =>
    have hstep := quarter_step m hm
    have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
    have hm1 : ((m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
    have hsub : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (le_trans (by decide : (1 : ℕ) ≤ 2) hm)]
      simp
    have hold : (1 - 1 / (m : ℝ)) ^ m = (((m - 1 : ℕ) : ℝ) / m) ^ m := by
      rw [hsub]
      field_simp
    have hnew : (1 - 1 / ((m + 1 : ℕ) : ℝ)) ^ (m + 1) =
        ((m : ℝ) / (m + 1)) ^ (m + 1) := by
      have hbase : (1 : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) = (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
        have hnz : ((m + 1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : m + 1 ≠ 0)
        calc
          (1 : ℝ) - 1 / ((m + 1 : ℕ) : ℝ)
              = (((m + 1 : ℕ) : ℝ) - 1) / ((m + 1 : ℕ) : ℝ) := by
                rw [sub_div, div_self hnz]
          _ = (m : ℝ) / ((m + 1 : ℕ) : ℝ) := by
                congr 1
                rw [Nat.cast_add]
                ring
      rw [hbase, Nat.cast_add, Nat.cast_one]
    rw [hnew]
    have hprev : (((m - 1 : ℕ) : ℝ) / m) ^ m ≤ ((m : ℝ) / (m + 1)) ^ (m + 1) := by
      simpa [hsub] using! hstep
    exact le_trans (by rwa [← hold]) hprev
end
noncomputable section

/-- For an injective function, a decoded Simon run with `n + k` samples differs from the decoded
zero result with mass at most `(1 / 2)^k`. -/
lemma single_reject_le {n k : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    {f : BooleanVec n → R} (hf : Function.Injective f) :
    event (simonDecodedRun f (n + k)).1 (fun out => out ≠ some (ZeroStr n)) ≤
      ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
  (Qatlib.Concepts.HspRecovery.Distinguisher.boundedErrorNearPeriodDistinguisher n k R f).2.1 hf
end
noncomputable section

/-- For an injective function, the mass that any of `r` fresh decoded runs differs from the zero
result is at most `r * (1 / 2)^k`. -/
lemma fresh_reject_le {n k : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    {f : BooleanVec n → R} (hf : Function.Injective f) (r : ℕ) :
    event (simonFreshRuns f (n + k) r) (fun v => ∃ i, v i ≠ some (ZeroStr n)) ≤
      ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) := by
  induction r with
  | zero =>
    classical
    simp [simonFreshRuns, event, expectation, PMF.pure_apply, IsEmpty.exists_iff]
  | succ r ih =>
    have hρ : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
    have hadd : ENNReal.ofReal (((r + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ k) =
        ENNReal.ofReal ((1 / 2 : ℝ) ^ k) +
          ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) := by
      rw [← ENNReal.ofReal_add hρ (mul_nonneg (Nat.cast_nonneg _) hρ)]
      congr 1
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
    rw [hadd]
    let Z : Option (Reg n) := some (ZeroStr n)
    let single := (simonDecodedRun f (n + k)).1
    have hsingle : event single (fun a => a ≠ Z) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ k) :=
      single_reject_le hf
    have hrest : event (simonFreshRuns f (n + k) r) (fun w => ∃ j, w j ≠ Z) ≤
        ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) := ih

    have hstep : event (simonFreshRuns f (n + k) (r + 1)) (fun v => ∃ i, v i ≠ Z) ≤
        event single (fun a => a ≠ Z) +
          event (simonFreshRuns f (n + k) r) (fun w => ∃ j, w j ≠ Z) := by
      classical
      let tail := simonFreshRuns f (n + k) r
      let c : ℝ≥0∞ := event tail (fun w => ∃ j, w j ≠ Z)
      have hrec : simonFreshRuns f (n + k) (r + 1) =
          PMF.bind single fun a => PMF.map (Fin.cons a) tail := by
        simp [simonFreshRuns, tail, single]
      rw [hrec, event, expectation_bind]
      have hcont : ∀ a, event (PMF.map (Fin.cons a) tail) (fun v => ∃ i, v i ≠ Z) =
          if a ≠ Z then (1 : ℝ≥0∞) else c := by
        intro a
        rw [PMF.map, event, expectation_bind]
        simp only [expectation_pure, Function.comp_def]
        by_cases ha : a ≠ Z
        · rw [if_pos ha]
          have hpred : ∀ w : Fin r → Option (Reg n),
              (∃ i, (Fin.cons a w : Fin (r + 1) → Option (Reg n)) i ≠ Z) := by
            intro w
            exact (cons_reject a w).mpr (Or.inl ha)
          simp only [hpred, if_true, expectation, PMF.tsum_coe, mul_one]
        · rw [if_neg ha]
          have hpred : ∀ w : Fin r → Option (Reg n),
              (∃ i, (Fin.cons a w : Fin (r + 1) → Option (Reg n)) i ≠ Z) ↔ (∃ j, w j ≠ Z) := by
            intro w
            have haeq : a = Z := by simpa using! ha
            rw [cons_reject, haeq]
            constructor
            · rintro (hZ | h)
              · exact absurd rfl hZ
              · exact h
            · intro h
              exact Or.inr h
          simp only [event, expectation, c]
          refine congrArg
              (fun (indicator : (Fin r → Option (Reg n)) → ℝ≥0∞) =>
                ∑' (w : Fin r → Option (Reg n)), tail w * indicator w) ?_
          funext w
          by_cases hw : ∃ j, w j ≠ Z
          · rw [if_pos ((hpred w).mpr hw), if_pos hw]
          · have hn : ¬ ∃ i, (Fin.cons a w : Fin (r + 1) → Option (Reg n)) i ≠ Z :=
              (hpred w).not.mpr hw
            rw [if_neg hn, if_neg hw]
      simp only [event] at hcont
      simp_rw [hcont]
      unfold event expectation
      have hle : ∀ a, (if a ≠ Z then (1 : ℝ≥0∞) else c) ≤
          (if a ≠ Z then 1 else 0) + c := by
        intro a
        by_cases ha : a ≠ Z
        · rw [if_pos ha, if_pos ha]
          exact le_add_of_nonneg_right bot_le
        · rw [if_neg ha, if_neg ha, zero_add]
      calc
        ∑' a, single a * (if a ≠ Z then (1 : ℝ≥0∞) else c)
            ≤ ∑' a, single a * ((if a ≠ Z then 1 else 0) + c) := by
              refine ENNReal.tsum_le_tsum fun a =>
                mul_le_mul_of_nonneg_left (hle a) bot_le
        _ = (∑' a, single a * (if a ≠ Z then 1 else 0)) + ∑' a, single a * c := by
              simp_rw [mul_add, ENNReal.tsum_add]
        _ = event single (fun a => a ≠ Z) + c := by
              unfold event expectation
              rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
              apply congrArg (· + c)
              refine tsum_congr ?_
              intro a
              beta_reduce
              by_cases ha : a ≠ Z
              · rw [if_pos ha, if_pos ha]
              · rw [if_neg ha, if_neg ha]
    exact le_trans hstep (add_le_add hsingle hrest)
end
noncomputable section

/-- For an injective function, the amplified rejection law assigns mass at most `r * (1 / 2)^k`
to `true`. -/
lemma amplified_true_le {n k : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    {f : BooleanVec n → R} (hf : Function.Injective f) (r : ℕ) :
    (simonAmplifiedReject f (n + k) r) true ≤
      ENNReal.ofReal ((r : ℝ) * (1 / 2 : ℝ) ^ k) := by
  rw [simonAmplifiedReject, pmf_bool_true, event_map]
  refine le_trans (le_of_eq (event_congr ?_)) (fresh_reject_le hf r)
  intro v
  simp [simonAnyRejectBits, decide_eq_true_eq]
end
noncomputable section

/-- If a nonzero shift violates periodicity on at most the stated fraction of inputs and `n + k
≥ 2`, the decoded zero result has mass at most `3 / 4` in one run. -/
lemma single_accept_le {n k : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    {f : BooleanVec n → R} (hm : 2 ≤ n + k) {s : BooleanVec n} (hs : s ≠ 0)
    (hcard : Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n) :
    event (simonDecodedRun f (n + k)).1 (fun out => out = some (ZeroStr n)) ≤
      ENNReal.ofReal (3 / 4 : ℝ) := by
  let p := (simonDecodedRun f (n + k)).1
  have hlow : ENNReal.ofReal ((1 - 1 / ((n : ℝ) + k)) ^ (n + k)) ≤
      event p (fun out => out ≠ some (ZeroStr n)) :=
    (Qatlib.Concepts.HspRecovery.Distinguisher.boundedErrorNearPeriodDistinguisher n k R f).2.2 s hs hcard
  have hquarter : ENNReal.ofReal (1 / 4 : ℝ) ≤
      ENNReal.ofReal ((1 - 1 / ((n : ℝ) + k)) ^ (n + k)) := by
    refine ENNReal.ofReal_le_ofReal ?_
    have hreal := one_sub_inv_pow_ge_quarter (n + k) hm
    rwa [Nat.cast_add] at hreal
  have hge : ENNReal.ofReal (1 / 4 : ℝ) ≤ event p (fun out => out ≠ some (ZeroStr n)) :=
    le_trans hquarter hlow
  have hpart := event_partition p (fun out => out ≠ some (ZeroStr n))
  have hfin : event p (fun out => out ≠ some (ZeroStr n)) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (event_le_one p _)
  have hcomp : event p (fun out => ¬ out ≠ some (ZeroStr n)) =
      1 - event p (fun out => out ≠ some (ZeroStr n)) := by
    have hcancel := ENNReal.add_sub_cancel_left
      (a := event p (fun out => out ≠ some (ZeroStr n)))
      (b := event p (fun out => ¬ out ≠ some (ZeroStr n))) hfin
    rw [hpart] at hcancel
    exact hcancel.symm
  have hle : event p (fun out => ¬ out ≠ some (ZeroStr n)) ≤
      1 - ENNReal.ofReal (1 / 4 : ℝ) := by
    rw [hcomp]
    exact tsub_le_tsub_left hge 1
  have hthree : (1 : ℝ≥0∞) - ENNReal.ofReal (1 / 4 : ℝ) = ENNReal.ofReal (3 / 4 : ℝ) := by
    have hsub : ENNReal.ofReal ((1 : ℝ) - 1 / 4) =
        ENNReal.ofReal 1 - ENNReal.ofReal (1 / 4) :=
      ENNReal.ofReal_sub (1 : ℝ) (q := (1 : ℝ) / 4) (by norm_num)
    rw [← ENNReal.ofReal_one, ← hsub]
    norm_num
  rw [hthree] at hle
  exact le_trans (le_of_eq (event_congr fun out => by simp)) hle
end
noncomputable section

/-- If each single-run decoded zero event has mass at most `3 / 4`, the mass that all `r` fresh
runs return the zero result is at most `(3 / 4)^r`. -/
lemma fresh_accept_le {n k : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    (f : BooleanVec n → R)
    (hacc : event (simonDecodedRun f (n + k)).1 (fun out => out = some (ZeroStr n)) ≤
      ENNReal.ofReal (3 / 4 : ℝ))
    (r : ℕ) :
    event (simonFreshRuns f (n + k) r) (fun v => ∀ i, v i = some (ZeroStr n)) ≤
      ENNReal.ofReal ((3 / 4 : ℝ) ^ r) := by
  induction r with
  | zero =>
    have hpred : ∀ v : Fin 0 → Option (Reg n), ∀ i, v i = some (ZeroStr n) := fun v i => i.elim0
    have hone : event (simonFreshRuns f (n + k) 0)
        (fun v => ∀ i, v i = some (ZeroStr n)) = 1 := by
      have hpart := event_partition (simonFreshRuns f (n + k) 0)
        (fun v => ∀ i, v i = some (ZeroStr n))
      have hzero : event (simonFreshRuns f (n + k) 0)
          (fun v => ¬ ∀ i, v i = some (ZeroStr n)) = 0 :=
        event_zero _ _ fun v hv => hv (hpred v)
      rw [hzero, add_zero] at hpart
      exact hpart
    rw [hone, pow_zero, ENNReal.ofReal_one]
  | succ r ih =>
    classical
    let single := (simonDecodedRun f (n + k)).1
    let tail := simonFreshRuns f (n + k) r
    let c : ℝ≥0∞ := event tail (fun w => ∀ j, w j = some (ZeroStr n))
    have htail : c ≤ ENNReal.ofReal ((3 / 4 : ℝ) ^ r) := ih
    have hrec : simonFreshRuns f (n + k) (r + 1) =
        PMF.bind single fun a => PMF.map (Fin.cons a) tail := by
      simp [simonFreshRuns, tail, single]
    have hcont : ∀ a, event (PMF.map (Fin.cons a) tail)
        (fun v => ∀ i, v i = some (ZeroStr n)) =
        if a = some (ZeroStr n) then c else 0 := by
      intro a
      rw [event_map]
      by_cases ha : a = some (ZeroStr n)
      · rw [if_pos ha]
        refine event_congr ?_
        intro w
        constructor
        · intro h j
          simpa [ha, Fin.cons_succ] using! h j.succ
        · intro h i
          cases i using Fin.cases with
          | zero => simpa [Fin.cons_zero] using! ha
          | succ j => simpa [Fin.cons_succ] using! h j
      · rw [if_neg ha]
        refine event_zero _ _ ?_
        intro w hw
        have hex := (cons_reject a w).mpr (Or.inl ha)
        rcases hex with ⟨i, hi⟩
        exact hi (hw i)
    rw [hrec, event, expectation_bind]
    unfold event at hcont
    beta_reduce at hcont
    simp_rw [hcont]
    have hprod : expectation single (fun a => if a = some (ZeroStr n) then c else 0) =
        c * event single (fun a => a = some (ZeroStr n)) := by
      unfold event expectation
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr ?_
      intro a
      beta_reduce
      by_cases ha : a = some (ZeroStr n)
      · rw [if_pos ha, if_pos ha, mul_one, mul_comm]
      · rw [if_neg ha, if_neg ha, mul_zero, mul_zero]
    rw [hprod]
    calc
      c * event single (fun a => a = some (ZeroStr n)) ≤
          ENNReal.ofReal ((3 / 4 : ℝ) ^ r) * ENNReal.ofReal (3 / 4 : ℝ) :=
        mul_le_mul htail hacc bot_le bot_le
      _ = ENNReal.ofReal ((3 / 4 : ℝ) ^ (r + 1)) := by
        rw [← ENNReal.ofReal_mul (by positivity), pow_succ, mul_comm]
end
noncomputable section

/-- Under the stated nonzero near-period and sample-count assumptions, the amplified rejection
law assigns mass at most `(3 / 4)^r` to `false`. -/
lemma amplified_false_le {n k : ℕ} {R : Type} [AddCommGroup R] [Fintype R] [DecidableEq R]
    {f : BooleanVec n → R} (hm : 2 ≤ n + k) {s : BooleanVec n} (hs : s ≠ 0)
    (hcard : Nat.card {x : BooleanVec n | f x ≠ f (x + s)} * (n + k) ≤ 2 ^ n)
    (r : ℕ) :
    (simonAmplifiedReject f (n + k) r) false ≤ ENNReal.ofReal ((3 / 4 : ℝ) ^ r) := by
  rw [simonAmplifiedReject, pmf_bool_false, event_map]
  refine le_trans (le_of_eq (event_congr ?_)) (fresh_accept_le f (single_accept_le hm hs hcard) r)
  intro v
  simp [simonAnyRejectBits, decide_eq_false_iff_not, not_exists]
end
end Qatlib.Papers.QPowerSimon97.Recovery
