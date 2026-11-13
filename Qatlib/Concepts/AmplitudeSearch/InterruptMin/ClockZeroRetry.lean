/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmplitudeSearch.InterruptMin.SearchTerminal
import Qatlib.Concepts.AmplitudeSearch.InterruptMin.InterruptedCallBudget

/-!
# Escaping zero-cost retry sequences

This module collapses sequences of distinguished retry outcomes into a probability law on the
first different outcome. The products `reach` have geometric tails under the half-mass
condition, giving normalization of `escapePMF`.

The specialization `sourceEscapePMF` handles zero-iteration failures in exponential search
schedules [BoyerEtAl1998].

## Main statements

* `escapeMass_hasSum`: Normalized nonnegative rows with the half-mass tail condition give
  escape-token masses summing to one.
* `escapeSum_head`: Splits an escape payoff sum into the nondistinguished outcomes at stage zero
  and continuation weighted by its distinguished mass.
* `sourceEscapePMF`: The probability law of the first source attempt outcome differing from
  zero-iteration failure.

## References

* [Boyer et al., 1998][BoyerEtAl1998]
-/

set_option backward.isDefEq.respectTransparency false
open Qatlib.Concepts.SearchStopping.UnknownCount
open Qatlib.Concepts.AmplitudeSearch.InterruptMin

set_option autoImplicit false
noncomputable section
namespace Qatlib.Concepts.AmplitudeSearch.InterruptMin
open Qatlib
open scoped BigOperators Classical ENNReal
open Filter Topology

variable {Ω : ℕ → Type} [∀ n, Fintype (Ω n)] [∀ n, DecidableEq (Ω n)]

/-- The product of continuation factors `q k` over stages `k < n`. -/
def reach (q : ℕ → ℝ) (n : ℕ) : ℝ := ∏ i ∈ Finset.range n, q i

/-- Extending the reach product by one stage multiplies it by `q n`. -/
theorem reach_succ (q : ℕ → ℝ) (n : ℕ) : reach q (n+1) = reach q n * q n := by
  exact Finset.prod_range_succ _ _

/-- A reach product of nonnegative factors is nonnegative. -/
theorem reach_nonneg (q : ℕ → ℝ) (hq : ∀ n, 0 ≤ q n) (n : ℕ) : 0 ≤ reach q n :=
  Finset.prod_nonneg fun i _ => hq i

/-- A reach product whose factors lie in `[0, 1]` is at most one. -/
theorem reach_le_one (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, q n ≤ 1)
    (n : ℕ) : reach q n ≤ 1 := by
  induction n with
  | zero => simp [reach]
  | succ n ih =>
    rw [reach_succ]
    exact (mul_le_mul_of_nonneg_right ih (hq0 n)).trans (by simpa using hq1 n)

/-- If all factors after stage zero are at most one half, `reach q (n + 1)` is at most `(1 /
2)^n`. -/
theorem reach_tail (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, q n ≤ 1)
    (hqhalf : ∀ n, 1 ≤ n → q n ≤ 1/2) (n : ℕ) :
    reach q (n+1) ≤ (1/2 : ℝ)^n := by
  induction n with
  | zero => simpa using reach_le_one q hq0 hq1 1
  | succ n ih =>
    rw [reach_succ,pow_succ]
    exact mul_le_mul ih (hqhalf (n+1) (by omega)) (hq0 _) (by positivity)

/-- Under the half-mass tail condition, the reach products tend to zero. -/
theorem reach_tendsto_zero (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, q n ≤ 1)
    (hqhalf : ∀ n, 1 ≤ n → q n ≤ 1/2) : Tendsto (reach q) atTop (nhds 0) := by
  apply (tendsto_add_atTop_iff_nat 1).mp
  exact squeeze_zero (fun n => reach_nonneg q hq0 (n+1)) (reach_tail q hq0 hq1 hqhalf)
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))

/-- Under the half-mass tail condition, the masses `reach q n * (1 - q n)` sum to one. -/
theorem escape_rows_hasSum (q : ℕ → ℝ) (hq0 : ∀ n, 0 ≤ q n) (hq1 : ∀ n, q n ≤ 1)
    (hqhalf : ∀ n, 1 ≤ n → q n ≤ 1/2) :
    HasSum (fun n => reach q n * (1-q n)) 1 := by
  have hsum (n : ℕ) : (∑ i ∈ Finset.range n, reach q i * (1-q i)) = 1-reach q n := by
    induction n with
    | zero => simp [reach]
    | succ n ih =>
      rw [Finset.sum_range_succ,ih,reach_succ]
      ring
  apply (hasSum_iff_tendsto_nat_of_nonneg
    (fun n => mul_nonneg (reach_nonneg q hq0 n) (sub_nonneg.mpr (hq1 n))) 1).2
  simp_rw [hsum]
  simpa using tendsto_const_nhds.sub (reach_tendsto_zero q hq0 hq1 hqhalf)

/-- For a row of total mass one, the sum over outcomes other than `dead n` is one minus its
distinguished mass. -/
theorem escape_row_sum (w : (n : ℕ) → Ω n → ℝ) (dead : (n : ℕ) → Ω n)
    (hw : ∀ n, ∑ x, w n x = 1) (n : ℕ) :
    (∑ x : {x : Ω n // x ≠ dead n}, w n x) = 1-w n (dead n) := by
  have hsplit : (∑ x : {x : Ω n // x ≠ dead n}, w n x) + w n (dead n) = ∑ x, w n x := by
    have he : (Finset.univ.filter fun x : Ω n => x ≠ dead n) = Finset.univ.erase (dead n) := by
      ext x
      simp
    have hs := Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Ω n)))
      (p := fun x => x ≠ dead n) (w n)
    rw [he] at hs
    have hs' : (∑ x : {x : Ω n // x ≠ dead n}, w n x) =
        ∑ x ∈ Finset.univ.erase (dead n), w n x := by simpa using hs
    rw [hs']
    exact Finset.sum_erase_add _ _ (Finset.mem_univ _)
  rw [hw] at hsplit
  linarith

/-- A stage paired with an outcome different from that stage's distinguished retry outcome. -/
abbrev EscapeToken (dead : (n : ℕ) → Ω n) := Σ n, {x : Ω n // x ≠ dead n}

/-- The mass of reaching the token's stage through distinguished outcomes and then selecting its
nondistinguished outcome. -/
def escapeMass (w : (n : ℕ) → Ω n → ℝ) (dead : (n : ℕ) → Ω n)
    (x : EscapeToken dead) : ℝ := reach (fun n => w n (dead n)) x.1 * w x.1 x.2

omit [∀ n, Fintype (Ω n)] [∀ n, DecidableEq (Ω n)] in

/-- Nonnegative row masses give nonnegative escape-token masses. -/
theorem escapeMass_nonneg (w : (n : ℕ) → Ω n → ℝ) (dead : (n : ℕ) → Ω n)
    (hw0 : ∀ n x, 0 ≤ w n x) (x : EscapeToken dead) : 0 ≤ escapeMass w dead x :=
  mul_nonneg (reach_nonneg _ (fun n => hw0 n (dead n)) x.1) (hw0 _ _)

/-- Normalized nonnegative rows with the half-mass tail condition give escape-token masses
summing to one. -/
theorem escapeMass_hasSum (w : (n : ℕ) → Ω n → ℝ) (dead : (n : ℕ) → Ω n)
    (hw0 : ∀ n x, 0 ≤ w n x) (hw1 : ∀ n, ∑ x, w n x = 1)
    (hhalf : ∀ n, 1 ≤ n → w n (dead n) ≤ 1/2) : HasSum (escapeMass w dead) 1 := by
  have hq1 (n : ℕ) : w n (dead n) ≤ 1 := by
    rw [← hw1 n]
    exact Finset.single_le_sum (fun x _ => hw0 n x) (Finset.mem_univ _)
  apply search_nonnegative_trace_sum _ (escapeMass_nonneg w dead hw0) 1
  simp only [escapeMass,← Finset.mul_sum,escape_row_sum w dead hw1]
  exact escape_rows_hasSum _ (fun n => hw0 n (dead n)) hq1 hhalf

/-- The probability law on the first nondistinguished outcome, constructed from the normalized
escape masses. -/
def escapePMF (w : (n : ℕ) → Ω n → ℝ) (dead : (n : ℕ) → Ω n)
    (hw0 : ∀ n x, 0 ≤ w n x) (hw1 : ∀ n, ∑ x, w n x = 1)
    (hhalf : ∀ n, 1 ≤ n → w n (dead n) ≤ 1/2) : PMF (EscapeToken dead) :=
  pmfOfRealMass (escapeMass w dead) (escapeMass_nonneg w dead hw0)
    (escapeMass_hasSum w dead hw0 hw1 hhalf)

/-- The real mass of an escape token under `escapePMF` equals `escapeMass`. -/
theorem escapePMF_toReal (w : (n : ℕ) → Ω n → ℝ) (dead : (n : ℕ) → Ω n)
    (hw0 : ∀ n x, 0 ≤ w n x) (hw1 : ∀ n, ∑ x, w n x = 1)
    (hhalf : ∀ n, 1 ≤ n → w n (dead n) ≤ 1/2) (x : EscapeToken dead) :
    (escapePMF w dead hw0 hw1 hhalf x).toReal = escapeMass w dead x :=
  pmfOfRealMass_toReal _ _ _ _

/-- Splits the first factor from a reach product and shifts the remaining sequence. -/
theorem reach_head (q : ℕ → ℝ) (n : ℕ) :
    reach q (n+1) = q 0 * reach (fun i => q (i+1)) n := by
  simpa only [reach,mul_comm] using Finset.prod_range_succ' q n

/-- The extended nonnegative sum of payoffs weighted by escape-token masses. -/
def escapeSum (w : (n : ℕ) → Ω n → ℝ) (dead : (n : ℕ) → Ω n)
    (v : (n : ℕ) → {x : Ω n // x ≠ dead n} → ℝ≥0∞) : ℝ≥0∞ :=
  ∑' n, ∑' x : {x : Ω n // x ≠ dead n},
    ENNReal.ofReal (escapeMass w dead ⟨n,x⟩) * v n x

/-- Expectation over escape tokens equals the stagewise sum `escapeSum`. -/
theorem escapePMF_sum (w : (n : ℕ) → Ω n → ℝ) (dead : (n : ℕ) → Ω n)
    (hw0 : ∀ n x, 0 ≤ w n x) (hw1 : ∀ n, ∑ x, w n x = 1)
    (hhalf : ∀ n, 1 ≤ n → w n (dead n) ≤ 1/2)
    (v : (n : ℕ) → {x : Ω n // x ≠ dead n} → ℝ≥0∞) :
    (∑' x : EscapeToken dead, escapePMF w dead hw0 hw1 hhalf x * v x.1 x.2) =
      escapeSum w dead v := by
  unfold escapePMF
  simp only [pmfOfRealMass_apply]
  unfold escapeMass
  exact ENNReal.tsum_sigma (fun n (x : {x : Ω n // x ≠ dead n}) =>
    ENNReal.ofReal (reach (fun n => w n (dead n)) n * w n x) * v n x)

omit [∀ n, Fintype (Ω n)] [∀ n, DecidableEq (Ω n)] in

/-- Splits an escape payoff sum into the nondistinguished outcomes at stage zero and
continuation weighted by its distinguished mass. -/
theorem escapeSum_head (w : (n : ℕ) → Ω n → ℝ) (dead : (n : ℕ) → Ω n)
    (hw0 : ∀ n x, 0 ≤ w n x)
    (v : (n : ℕ) → {x : Ω n // x ≠ dead n} → ℝ≥0∞) :
    escapeSum w dead v =
      (∑' x : {x : Ω 0 // x ≠ dead 0}, ENNReal.ofReal (w 0 x) * v 0 x) +
      ENNReal.ofReal (w 0 (dead 0)) *
        escapeSum (Ω := fun n => Ω (n+1)) (fun n => w (n+1)) (fun n => dead (n+1))
          (fun n x => v (n+1) x) := by
  unfold escapeSum
  rw [tsum_eq_zero_add' ENNReal.summable]
  have hr0 : reach (fun n => w n (dead n)) 0 = 1 := by simp [reach]
  simp only [escapeMass,hr0,one_mul]
  congr 1
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro n
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro x
  rw [reach_head]
  simp only [mul_assoc,ENNReal.ofReal_mul (hw0 0 (dead 0))]

/-- Adding the distinguished outcome to the sum over all other outcomes recovers the full finite
sum. -/
theorem sum_nondead_add (n : ℕ) (dead : Ω n) (f : Ω n → ℝ≥0∞) :
    (∑ x : {x : Ω n // x ≠ dead}, f x) + f dead = ∑ x, f x := by
  have he : (Finset.univ.filter fun x : Ω n => x ≠ dead) = Finset.univ.erase dead := by
    ext x
    simp
  have hs := Finset.sum_subtype_eq_sum_filter (s := (Finset.univ : Finset (Ω n)))
    (p := fun x => x ≠ dead) f
  rw [he] at hs
  have hs' : (∑ x : {x : Ω n // x ≠ dead}, f x) = ∑ x ∈ Finset.univ.erase dead, f x := by
    simpa using hs
  rw [hs']
  exact Finset.sum_erase_add _ _ (Finset.mem_univ _)

/-- For `N > 1`, each positive-stage exponential attempt size is at least two. -/
theorem sizes_ge_two_succ (N k : ℕ) (hN : 1 < N) : 2 ≤ ExponentialSizes N (k+1) := by
  have hn : (1:ℝ) < N := by exact_mod_cast hN
  have hs : (1:ℝ) < Real.sqrt N := by
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N), Real.sqrt_nonneg (N:ℝ)]
  have hp : (1:ℝ) < (6/5:ℝ)^(k+1) := one_lt_pow₀ (by norm_num) (by omega)
  have hw : (1:ℝ) < ExponentialWidth N (k+1) := by
    rw [(search_exponential_schedule N (by omega)).1]
    exact lt_min hp hs
  have hc : (1:ℝ) < (ExponentialSizes N (k+1) : ℝ) := hw.trans_le (Nat.le_ceil _)
  exact_mod_cast hc

/-- For attempt size at least two, the mass of a zero-iteration rejected attempt is at most one
half. -/
theorem zero_reject_le_half {I : Type} [Fintype I] [DecidableEq I]
    (hN : 0 < Fintype.card I) (A : Finset I) (m : ℕ) (hm : 2 ≤ m) :
    AttemptMass A m (⟨0,by omega⟩,none) ≤ (1/2:ℝ) := by
  have hp := search_joint_attempt_law hN A m (by omega)
  have hle : AttemptMass A m (⟨0,by omega⟩,none) ≤ 1/(m:ℝ) := by
    rw [← search_joint_attempt_slice hN A m ⟨0,by omega⟩]
    exact Finset.single_le_sum (fun o _ => hp.1 (⟨0,by omega⟩,o)) (Finset.mem_univ none)
  apply hle.trans
  have hmr : (2:ℝ) ≤ m := by exact_mod_cast hm
  exact one_div_le_one_div_of_le (by norm_num) hmr

/-- Advances a stage by recursively applying `n` successor steps. -/
def advance : ℕ → ℕ → ℕ
  | stage,0 => stage
  | stage,n+1 => advance (stage+1) n

/-- Advancing `stage` by `n` steps equals `stage + n`. -/
theorem advance_eq (stage n : ℕ) : advance stage n = stage+n := by
  induction n generalizing stage with
  | zero => rfl
  | succ n ih => rw [advance,ih]; omega

/-- An iteration count and optional search output at the exponential stage reached after `n`
advances. -/
abbrev SourceOutcome (N stage n : ℕ) := Fin (ExponentialSizes N (advance stage n)) × Option (Fin N)

/-- The distinguished zero-iteration failure outcome at the specified source stage. -/
def sourceDead (N : ℕ) (hN : 1 < N) (stage n : ℕ) : SourceOutcome N stage n :=
  (⟨0,(search_exponential_schedule N (by omega)).2.1 _⟩,none)

/-- The joint attempt mass at the exponential stage reached after `n` advances. -/
def sourceRow (N : ℕ) (A : Finset (Fin N)) (stage n : ℕ)
    (x : SourceOutcome N stage n) : ℝ := AttemptMass A (ExponentialSizes N (advance stage n)) x

/-- Source attempt-row masses are nonnegative for `N > 1`. -/
theorem sourceRow_nonneg (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage n : ℕ) (x : SourceOutcome N stage n) : 0 ≤ sourceRow N A stage n x :=
  (search_joint_attempt_law (by simpa using (show 0 < N by omega)) A _
    ((search_exponential_schedule N (by omega)).2.1 _)).1 x

/-- Each source attempt row has total mass one for `N > 1`. -/
theorem sourceRow_sum (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage n : ℕ) : (∑ x, sourceRow N A stage n x) = 1 :=
  (search_joint_attempt_law (by simpa using (show 0 < N by omega)) A _
    ((search_exponential_schedule N (by omega)).2.1 _)).2.1

/-- After at least one advance, the distinguished source failure has mass at most one half. -/
theorem sourceDead_half (N : ℕ) (hN : 1 < N) (A : Finset (Fin N)) (stage n : ℕ)
    (hn : 1 ≤ n) : sourceRow N A stage n (sourceDead N hN stage n) ≤ 1/2 := by
  have hm : 2 ≤ ExponentialSizes N (advance stage n) := by
    rw [advance_eq]
    obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero (show stage+n ≠ 0 by omega)
    rw [hk]
    exact sizes_ge_two_succ N k hN
  exact zero_reject_le_half (by simpa using (show 0 < N by omega)) A _ hm

/-- A source stage offset paired with an attempt outcome other than zero-iteration failure. -/
abbrev SourceToken (N : ℕ) (hN : 1 < N) (stage : ℕ) := EscapeToken (sourceDead N hN stage)

/-- The probability law of the first source attempt outcome differing from zero-iteration
failure. -/
def sourceEscapePMF (N : ℕ) (hN : 1 < N) (A : Finset (Fin N)) (stage : ℕ) :
    PMF (SourceToken N hN stage) :=
  escapePMF (sourceRow N A stage) (sourceDead N hN stage)
    (sourceRow_nonneg N hN A stage) (sourceRow_sum N hN A stage) (sourceDead_half N hN A stage)

/-- The real source escape-token mass is the reach product of earlier distinguished masses times
the selected row mass. -/
theorem sourceEscapePMF_toReal (N : ℕ) (hN : 1 < N) (A : Finset (Fin N))
    (stage : ℕ) (x : SourceToken N hN stage) :
    (sourceEscapePMF N hN A stage x).toReal =
      reach (fun n => sourceRow N A stage n (sourceDead N hN stage n)) x.1 *
        sourceRow N A stage x.1 x.2 :=
  escapePMF_toReal (sourceRow N A stage) (sourceDead N hN stage)
    (sourceRow_nonneg N hN A stage) (sourceRow_sum N hN A stage)
    (sourceDead_half N hN A stage) x

end Qatlib.Concepts.AmplitudeSearch.InterruptMin
