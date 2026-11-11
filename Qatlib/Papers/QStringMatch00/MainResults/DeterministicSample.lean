/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Algebra.Group.Semigroup
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Group.Defs
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.Order.GroupWithZero.Defs
import Mathlib.Algebra.Order.Monoid.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Ring.Unbundled.Rat
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Order.ZeroLEOne
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Star.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Empty
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.NNRat.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Data.Nat.Init
import Mathlib.Data.Nat.Log
import Mathlib.Data.Rat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Order.RelClasses
import Mathlib.Tactic
import Mathlib.Tactic.CancelDenoms.Core
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.NormNum.Basic
import Mathlib.Tactic.NormNum.Ineq
import Mathlib.Tactic.NormNum.Inv
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.NormNum.Result
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.Common

/-!
# Deterministic samples by successive filtering

This module formalizes the finite-set sampling argument used in [RameshVinay2000]. `StageKeep`
selects candidates with a specified value at a chosen column, and `runK` iterates these filters.
Nonempty filters that halve the candidate count isolate a candidate once the number of stages is
sufficient.

The separation hypothesis in `deterministic_sample_exists_auto` supplies the stages
existentially. `stageCount` and `stageCost` provide a scalar bound for the product of the number
of stages and the cost assigned to each stage.

## Main statements

* `deterministic_sample_exists`: prescribed nonempty halving stages determine a unique candidate
  using at most `n` columns.
* `deterministic_sample_exists_auto`: pairwise distinguishable candidates in a nonempty set of
  size at most `2 ^ n` possess such a sample.
* `deterministic_sample_cost`: the stage-count product satisfies an explicit square-root and
  logarithmic bound.

## References

* [Ramesh and Vinay, 2000][RameshVinay2000]
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.QStringMatch00.MainResults.DeterministicSample

variable {ι : Type*}

/-- The candidates in `S` whose value at column `c` equals the selected character `χ`. -/
def StageKeep (val : ι → ℕ → ℕ) (c χ : ℕ) (S : Finset ι) : Finset ι :=
  S.filter (fun i => val i c = χ)

/-- The candidate set obtained by applying the first `k` column-character filters specified by
`stage` to the initial set. -/
def runK (val : ι → ℕ → ℕ) (stage : ℕ → ℕ × ℕ) : ℕ → Finset ι → Finset ι
  | 0, S => S
  | k + 1, S => StageKeep val (stage k).1 (stage k).2 (runK val stage k S)

/-- Every candidate surviving any number of filtering stages belongs to the initial candidate
set `S0`. -/
lemma runK_subset (val : ι → ℕ → ℕ) (stage : ℕ → ℕ × ℕ) (S0 : Finset ι) :
    ∀ n : ℕ, runK val stage n S0 ⊆ S0 := by
  intro n
  induction n with
  | zero => intro i hi; simpa [runK] using hi
  | succ n ih =>
    intro i hi
    have hi' : i ∈ (runK val stage n S0).filter
        (fun j => val j (stage n).1 = (stage n).2) := by
      rwa [show runK val stage (n + 1) S0 =
        (runK val stage n S0).filter
          (fun j => val j (stage n).1 = (stage n).2) from rfl] at hi
    exact ih (Finset.mem_filter.mp hi').1

/-- If each of the first `n` stages retains at most half the candidates, the final cardinality
multiplied by `2 ^ n` is at most the initial cardinality. -/
lemma runK_card (val : ι → ℕ → ℕ) (stage : ℕ → ℕ × ℕ) (S0 : Finset ι) :
    ∀ n : ℕ,
      (∀ k < n, 2 * (runK val stage (k + 1) S0).card ≤
        (runK val stage k S0).card) →
      (runK val stage n S0).card * 2 ^ n ≤ S0.card := by
  intro n
  induction n with
  | zero => intro _; simp [runK]
  | succ n ih =>
    intro hstep
    have hprev : (runK val stage n S0).card * 2 ^ n ≤ S0.card :=
      ih (fun k hk => hstep k (Nat.lt_trans hk (Nat.lt_succ_self n)))
    have hstepn : 2 * (runK val stage (n + 1) S0).card ≤
        (runK val stage n S0).card := hstep n (Nat.lt_succ_self n)
    calc (runK val stage (n + 1) S0).card * 2 ^ (n + 1)
        = ((runK val stage (n + 1) S0).card * 2) * 2 ^ n := by
          rw [pow_succ]; ring
      _ ≤ (runK val stage n S0).card * 2 ^ n := by
          apply Nat.mul_le_mul_right
          omega
      _ ≤ S0.card := hprev

/-- A candidate in `S0` that agrees with a surviving candidate on all columns used in the first
`n` stages also survives those stages. -/
lemma mem_runK_of_agree (val : ι → ℕ → ℕ) (stage : ℕ → ℕ × ℕ) (S0 : Finset ι)
    (f g : ι) :
    ∀ n : ℕ, f ∈ runK val stage n S0 →
      (∀ k < n, val g (stage k).1 = val f (stage k).1) →
      g ∈ S0 → g ∈ runK val stage n S0 := by
  intro n
  induction n with
  | zero => intro _ _ hg; simpa [runK] using hg
  | succ n ih =>
    intro hf hagree hg
    have hdef : runK val stage (n + 1) S0 =
        (runK val stage n S0).filter
          (fun j => val j (stage n).1 = (stage n).2) := rfl
    have hmem : f ∈ (runK val stage n S0).filter
        (fun j => val j (stage n).1 = (stage n).2) := by
      rw [hdef] at hf
      exact hf
    have hf' : f ∈ runK val stage n S0 := (Finset.mem_filter.mp hmem).1
    have hcharf : val f (stage n).1 = (stage n).2 := (Finset.mem_filter.mp hmem).2
    have hchary : val g (stage n).1 = (stage n).2 := by
      rw [hagree n (Nat.lt_succ_self n), hcharf]
    have hgn : g ∈ runK val stage n S0 :=
      ih hf' (fun k hk => hagree k (Nat.lt_trans hk (Nat.lt_succ_self n))) hg
    rw [hdef]
    exact Finset.mem_filter.mpr ⟨hgn, hchary⟩

/-- Nonempty halving stages on a nonempty candidate set of size at most `2 ^ n` isolate a
candidate determined uniquely within that set by at most `n` sampled columns. -/
theorem deterministic_sample_exists
    (val : ι → ℕ → ℕ) (stage : ℕ → ℕ × ℕ) (S0 : Finset ι) (n : ℕ)
    (hne : S0.Nonempty)
    (hstep_ne : ∀ k < n, (runK val stage (k + 1) S0).Nonempty)
    (hstep_card : ∀ k < n,
      2 * (runK val stage (k + 1) S0).card ≤ (runK val stage k S0).card)
    (hsize : S0.card ≤ 2 ^ n) :
    ∃ f ∈ S0,
      (∀ g ∈ S0,
        (∀ k < n, val g (stage k).1 = val f (stage k).1) → g = f) ∧
      ((List.range n).map (fun k => (stage k).1)).toFinset.card ≤ n := by

  have hFne : (runK val stage n S0).Nonempty := by
    cases n with
    | zero => simpa [runK] using hne
    | succ k => exact hstep_ne k (Nat.lt_succ_self k)

  have hcard_le : (runK val stage n S0).card ≤ 1 := by
    have hc := runK_card val stage S0 n hstep_card
    have hpow : 0 < 2 ^ n := pow_pos (by norm_num) n

    have hle : (runK val stage n S0).card * 2 ^ n ≤ 1 * 2 ^ n := by
      calc (runK val stage n S0).card * 2 ^ n ≤ S0.card := hc
        _ ≤ 2 ^ n := hsize
        _ = 1 * 2 ^ n := by ring
    exact Nat.le_of_mul_le_mul_right hle hpow
  have hcard_pos : 0 < (runK val stage n S0).card :=
    Finset.card_pos.mpr hFne
  have hcard_one : (runK val stage n S0).card = 1 := by omega
  obtain ⟨f, hF⟩ := Finset.card_eq_one.mp hcard_one
  have hfF : f ∈ runK val stage n S0 := by rw [hF]; exact Finset.mem_singleton_self f
  have hfS0 : f ∈ S0 := runK_subset val stage S0 n hfF
  refine ⟨f, hfS0, ?_, ?_⟩
  · intro g hgS0 hagree
    have hgF : g ∈ runK val stage n S0 :=
      mem_runK_of_agree val stage S0 f g n hfF hagree hgS0
    rw [hF] at hgF
    exact Finset.mem_singleton.mp hgF
  · calc ((List.range n).map (fun k => (stage k).1)).toFinset.card
        ≤ ((List.range n).map (fun k => (stage k).1)).length :=
          (List.toFinset_card_le _)
      _ = n := by simp

/-- The ceiling base-two logarithm `Nat.clog 2 m` used as the sampling stage count. -/
def stageCount (m : ℕ) : ℕ := Nat.clog 2 m

/-- The scalar cost `C * Real.sqrt m * (Real.log m + 1)` assigned to a sampling stage. -/
def stageCost (m : ℕ) (C : ℝ) : ℝ := C * Real.sqrt m * (Real.log m + 1)

/-- For `m ≥ 2`, the sampling stage count is at most `2 * Real.log (m + 2) + 2` after coercion
to the reals. -/
lemma stageCount_le_log (m : ℕ) (hm : 2 ≤ m) :
    (stageCount m : ℝ) ≤ 2 * Real.log (m + 2) + 2 := by

  have hlt : 2 ^ (Nat.clog 2 m - 1) < m :=
    Nat.pow_pred_clog_lt_self (by norm_num) (by omega)
  have hcast : ((2 : ℝ) ^ (Nat.clog 2 m - 1)) < (m : ℝ) := by exact_mod_cast hlt
  have hmlog : Real.log ((2 : ℝ) ^ (Nat.clog 2 m - 1)) < Real.log ((m : ℝ) + 2) := by
    apply Real.log_lt_log (by positivity)
    linarith
  rw [Real.log_pow] at hmlog

  have hclogpos : 0 < Nat.clog 2 m := Nat.clog_pos (by norm_num) (by omega)
  have hcast_sub : ((Nat.clog 2 m - 1 : ℕ) : ℝ) = (Nat.clog 2 m : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ Nat.clog 2 m)]
    norm_num
  rw [hcast_sub] at hmlog

  have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hnonneg : (0 : ℝ) ≤ (Nat.clog 2 m : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (Nat.clog 2 m : ℝ) := by exact_mod_cast hclogpos
    linarith
  have hmul : ((Nat.clog 2 m : ℝ) - 1) * (1 / 2) ≤
      ((Nat.clog 2 m : ℝ) - 1) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlog2.le hnonneg
  have : ((Nat.clog 2 m : ℝ) - 1) * (1 / 2) < Real.log ((m : ℝ) + 2) :=
    lt_of_le_of_lt hmul hmlog
  unfold stageCount
  linarith

/-- For `m ≥ 2` and nonnegative `C`, the stage-count product is at most `C * (2 * Real.log (m +
2) + 2) * Real.sqrt m * (Real.log m + 1)`. This is the scalar sampling-cost estimate
associated with Section 5 of [RameshVinay2000]. -/
theorem deterministic_sample_cost
    (m : ℕ) (hm : 2 ≤ m) (C : ℝ) (hC : 0 ≤ C) :
    (stageCount m : ℝ) * stageCost m C ≤
      C * (2 * Real.log (m + 2) + 2) * Real.sqrt m * (Real.log m + 1) := by
  unfold stageCost
  have hcount := stageCount_le_log m hm
  have hcost : (0 : ℝ) ≤ C * Real.sqrt m * (Real.log m + 1) := by
    have hs : (0 : ℝ) ≤ Real.sqrt m := Real.sqrt_nonneg _
    have hl : (0 : ℝ) ≤ Real.log m + 1 := by
      have : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m))
      linarith
    positivity
  calc (stageCount m : ℝ) * (C * Real.sqrt m * (Real.log m + 1))
      ≤ (2 * Real.log (m + 2) + 2) * (C * Real.sqrt m * (Real.log m + 1)) :=
        mul_le_mul_of_nonneg_right hcount hcost
    _ = C * (2 * Real.log (m + 2) + 2) * Real.sqrt m * (Real.log m + 1) := by
        ring

/-- If two candidates in `S` differ at column `c`, some character at that column selects a
nonempty subset containing at most half of `S`. -/
lemma exists_nonmajority_char (val : ι → ℕ → ℕ) (S : Finset ι) (c : ℕ)
    (i j : ι) (hi : i ∈ S) (hj : j ∈ S) (hij : val i c ≠ val j c) :
    ∃ χ, 2 * (StageKeep val c χ S).card ≤ S.card ∧
      (StageKeep val c χ S).Nonempty := by
  classical
  set χ0 : ℕ := val i c with hχ0
  have hsum : (StageKeep val c χ0 S).card +
      (S.filter (fun x => ¬ val x c = χ0)).card = S.card := by
    show (S.filter (fun x => val x c = χ0)).card +
      (S.filter (fun x => ¬ val x c = χ0)).card = S.card
    exact Finset.card_filter_add_card_filter_not (s := S) (fun x => val x c = χ0)
  have hjB : j ∈ S.filter (fun x => ¬ val x c = χ0) := by
    refine Finset.mem_filter.mpr ⟨hj, ?_⟩
    rw [hχ0]
    exact fun h => hij h.symm
  have hiA : i ∈ StageKeep val c χ0 S := by
    show i ∈ S.filter (fun x => val x c = χ0)
    exact Finset.mem_filter.mpr ⟨hi, by rw [hχ0]⟩
  by_cases hle : (StageKeep val c χ0 S).card ≤
      (S.filter (fun x => ¬ val x c = χ0)).card
  · refine ⟨χ0, ?_, ⟨i, hiA⟩⟩
    omega
  · push Not at hle
    have hBcard : (S.filter (fun x => ¬ val x c = χ0)).card <
        (StageKeep val c χ0 S).card := hle
    refine ⟨val j c, ?_, ⟨j, ?_⟩⟩
    · have hsub : StageKeep val c (val j c) S ⊆
          S.filter (fun x => ¬ val x c = χ0) := by
        intro x hx
        simp only [StageKeep, Finset.mem_filter] at hx ⊢
        exact ⟨hx.1, by rw [hx.2, hχ0]; exact fun h => hij h.symm⟩
      have hcard := Finset.card_le_card hsub
      omega
    · show j ∈ S.filter (fun x => val x c = val j c)
      exact Finset.mem_filter.mpr ⟨hj, rfl⟩

/-- A pairwise distinguishable candidate set with at least two elements possesses a
column-character filter selecting a nonempty subset of at most half its cardinality. -/
lemma exists_split_column (val : ι → ℕ → ℕ) (S : Finset ι)
    (hsep : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ∃ c, val i c ≠ val j c)
    (h2 : 2 ≤ S.card) :
    ∃ c χ, 2 * (StageKeep val c χ S).card ≤ S.card ∧
      (StageKeep val c χ S).Nonempty := by
  classical
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (by omega : 1 < S.card)
  obtain ⟨c, hc⟩ := hsep i hi j hj hij
  exact ⟨c, exists_nonmajority_char val S c i j hi hj hc⟩

/-- A nonempty pairwise distinguishable candidate set of size at most `2 ^ n` possesses a
sequence of stages and a candidate uniquely determined within the set by at most `n` sampled
columns. This formalizes the sample-existence argument associated with Section 5 of
[RameshVinay2000]. -/
theorem deterministic_sample_exists_auto
    (val : ι → ℕ → ℕ) (n : ℕ) (S0 : Finset ι)
    (hne : S0.Nonempty)
    (hsep : ∀ i ∈ S0, ∀ j ∈ S0, i ≠ j → ∃ c, val i c ≠ val j c)
    (hsize : S0.card ≤ 2 ^ n) :
    ∃ stage : ℕ → ℕ × ℕ, ∃ f ∈ S0,
      (∀ g ∈ S0, (∀ k < n, val g (stage k).1 = val f (stage k).1) → g = f) ∧
      ((List.range n).map (fun k => (stage k).1)).toFinset.card ≤ n := by
  classical
  induction n generalizing S0 with
  | zero =>
      have hcard1 : S0.card = 1 := by
        have := Finset.card_pos.mpr hne
        omega
      obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard1
      refine ⟨fun _ => (0, 0), f, by rw [hf]; simp, ?_, ?_⟩
      · intro g hg _
        rw [hf] at hg
        simpa using hg
      · exact le_trans (List.toFinset_card_le _) (by simp)
  | succ n ih =>
      by_cases hcard1 : S0.card = 1
      · obtain ⟨f, hf⟩ := Finset.card_eq_one.mp hcard1
        refine ⟨fun _ => (0, 0), f, by rw [hf]; simp, ?_, ?_⟩
        · intro g hg _
          rw [hf] at hg
          simpa using hg
        · exact le_trans (List.toFinset_card_le _) (by simp)
      · have h2 : 2 ≤ S0.card := by
          have := Finset.card_pos.mpr hne
          omega
        obtain ⟨c, χ, hhalf, hne1⟩ := exists_split_column val S0 hsep h2
        set S1 : Finset ι := StageKeep val c χ S0 with hS1
        have hsub1 : S1 ⊆ S0 := by
          intro x hx
          simp only [hS1, StageKeep, Finset.mem_filter] at hx
          exact hx.1
        have hsep1 : ∀ i ∈ S1, ∀ j ∈ S1, i ≠ j → ∃ c', val i c' ≠ val j c' :=
          fun i hi j hj hne => hsep i (hsub1 hi) j (hsub1 hj) hne
        have hsize1 : S1.card ≤ 2 ^ n := by
          have hpow : 2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ]; ring
          omega
        obtain ⟨stage', f, hf1, huniq, hcount⟩ := ih S1 hne1 hsep1 hsize1
        refine ⟨fun k => if k = 0 then (c, χ) else stage' (k - 1), f, hsub1 hf1,
          ?_, ?_⟩
        · intro g hgS0 hagree
          have hfc : val f c = χ := by
            have hmem := hf1
            simp only [hS1, StageKeep, Finset.mem_filter] at hmem
            exact hmem.2
          have hgc : val g c = χ := by
            rw [← hfc]
            exact hagree 0 (Nat.succ_pos n)
          have hgS1 : g ∈ S1 := by
            simp only [hS1, StageKeep, Finset.mem_filter]
            exact ⟨hgS0, hgc⟩
          exact huniq g hgS1 (fun k hk => by
            have hk' : k + 1 < n + 1 := Nat.succ_lt_succ hk
            have h := hagree (k + 1) hk'
            simp only [if_neg (by omega : ¬ (k + 1 = 0)), Nat.add_sub_cancel] at h
            exact h)
        · exact le_trans (List.toFinset_card_le _) (by simp)

end Qatlib.Papers.QStringMatch00.MainResults.DeterministicSample
