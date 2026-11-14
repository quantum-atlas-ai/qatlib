/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.CharZero.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Group.Semigroup
public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Algebra.GroupWithZero.Defs
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Algebra.GroupWithZero.NeZero
public import Mathlib.Algebra.GroupWithZero.Units.Basic
public import Mathlib.Algebra.NeZero
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Algebra.Order.Group.Defs
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.GroupWithZero.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Defs
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
public import Mathlib.Algebra.Order.Monoid.Unbundled.Defs
public import Mathlib.Algebra.Order.Ring.Abs
public import Mathlib.Algebra.Order.Ring.Defs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Ring.Unbundled.Basic
public import Mathlib.Algebra.Order.Star.Basic
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Star.Basic
public import Mathlib.Analysis.Asymptotics.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Group.Real
public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.Real.Star
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Int.Cast.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.Data.Nat.Init
public import Mathlib.Data.Set.Defs
public import Mathlib.Logic.Function.Defs
public import Mathlib.Order.Basic
public import Mathlib.Order.Defs.Lattice
public import Mathlib.Order.Defs.LinearOrder
public import Mathlib.Order.Defs.PartialOrder
public import Mathlib.Order.Filter.AtTopBot.Archimedean
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.Order.Filter.Tendsto
public import Mathlib.Order.Lattice
public import Mathlib.Order.RelClasses
public import Mathlib.Tactic
public import Mathlib.Tactic.CancelDenoms.Core
public import Mathlib.Tactic.FieldSimp.Lemmas
public import Mathlib.Tactic.Linarith.Lemmas
public import Mathlib.Tactic.Linarith.Preprocessing
public import Mathlib.Tactic.NormNum.Basic
public import Mathlib.Tactic.NormNum.Eq
public import Mathlib.Tactic.NormNum.Ineq
public import Mathlib.Tactic.NormNum.Inv
public import Mathlib.Tactic.NormNum.Result
public import Mathlib.Tactic.Positivity.Core
public import Mathlib.Tactic.Ring.Basic
public import Mathlib.Tactic.Ring.Common
public import Mathlib.Tactic.Ring.RingNF
public import Qatlib.Papers.QSearchAdvice09.MainResults.Basic
public import Qatlib.Papers.QSearchAdvice09.MainResults.PowSums

@[expose] public section

/-!
# Power-law advice bounds by probability branches

This module splits the advice cost bound into probabilities above and below 1/n and compares
both contributions with `crudeSqrtSum`. Power-sum estimates then give constant, logarithmic, and
square-root big-O bounds and transfer them to eventually dominated nonnegative cost functions.

The source paper is [Montanaro2011].

## Main statements

* `powerLawTstarBound_le_crude`: For n ≥ 1, the power-law cost bound is at most 136 times
  sumPow(k/2, n)/√(powerLawMass k n), plus 4/3.
* `prop_3_4_case_sqrt`: For −1 ≤ k < 0, an eventually nonnegative function eventually dominated
  by the stated nonnegative power-law bound is O(√n).
* `prop_3_4_case_const`: For k < −2, an eventually nonnegative function eventually dominated by
  the stated nonnegative power-law bound is O(1).

## References

* [Montanaro, 2011][Montanaro2011]
-/

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

noncomputable section

open Finset

open scoped BigOperators

namespace Qatlib.Papers.QSearchAdvice09.MainResults

/-- The sum of square roots of power-law probabilities strictly greater than 1/n. -/
def sqrtBranchSum (k : ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n,
    if (1 : ℝ) / (n : ℝ) < powerLawProb k n x then Real.sqrt (powerLawProb k n x) else 0

/-- The sum of power-law probabilities at most 1/n. -/
def smallBranchSum (k : ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n,
    if powerLawProb k n x ≤ (1 : ℝ) / (n : ℝ) then powerLawProb k n x else 0

/-- The sum of square roots of all power-law probabilities. -/
def crudeSqrtSum (k : ℝ) (n : ℕ) : ℝ :=
  ∑ x : Fin n, Real.sqrt (powerLawProb k n x)

/-- The power-law normalizing mass equals `sumPow k n`. -/
theorem powerLawMass_eq_sumPow (k : ℝ) (n : ℕ) :
    powerLawMass k n = sumPow k n := by
  unfold powerLawMass
  exact sum_Icc_one_eq_sumPow k n

/-- For n ≥ 1, every power-law probability is nonnegative. -/
theorem powerLawProb_nonneg (k : ℝ) (n : ℕ) (hn : 1 ≤ n) (x : Fin n) :
    0 ≤ powerLawProb k n x := by
  unfold powerLawProb
  apply div_nonneg
  · exact Real.rpow_nonneg (by positivity) k
  · exact (powerLawMass_pos k n hn).le

/-- The power-law cost bound is 83 times the square-root branch sum plus 53√n times the
small-probability mass, plus 4/3. -/
theorem powerLawTstarBound_eq (k : ℝ) (n : ℕ) :
    powerLawTstarBound k n
      = 83 * sqrtBranchSum k n + 53 * Real.sqrt (n : ℝ) * smallBranchSum k n + 4 / 3 := by
  unfold powerLawTstarBound sqrtBranchSum smallBranchSum
  rfl

/-- Replacing √p by zero under any condition cannot increase it for nonnegative p. -/
theorem if_sqrt_le_sqrt (c : Prop) [Decidable c] (p : ℝ) (_hp : 0 ≤ p) :
    (if c then Real.sqrt p else 0) ≤ Real.sqrt p := by
  by_cases h : c
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact Real.sqrt_nonneg p

/-- For n ≥ 1, the square-root branch sum is at most the sum over all probabilities. -/
theorem sqrtBranchSum_le_crude (k : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    sqrtBranchSum k n ≤ crudeSqrtSum k n := by
  unfold sqrtBranchSum crudeSqrtSum
  apply sum_le_sum
  intro x _
  exact if_sqrt_le_sqrt _ _ (powerLawProb_nonneg k n hn x)

/-- For n ≥ 1 and 0 ≤ p ≤ 1/n, √n·p ≤ √p. -/
theorem sqrtN_mul_le_sqrt {n : ℕ} (hn : 1 ≤ n) {p : ℝ} (hp0 : 0 ≤ p)
    (hp : p ≤ (1 : ℝ) / (n : ℝ)) : Real.sqrt (n : ℝ) * p ≤ Real.sqrt p := by
  rcases eq_or_lt_of_le hp0 with hzero | hpos
  · rw [← hzero]; simp
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hn)
  have hnp : (n : ℝ) * p ≤ 1 := by
    have := (le_div_iff₀ hnpos).mp hp
    linarith
  have hle : (n : ℝ) * p ^ 2 ≤ p := by
    have h1 : p * ((n : ℝ) * p) ≤ p * 1 := mul_le_mul_of_nonneg_left hnp hp0
    nlinarith [h1]
  have hEq : Real.sqrt ((n : ℝ) * p ^ 2) = Real.sqrt (n : ℝ) * p := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ (n : ℝ)), Real.sqrt_sq hp0]
  rw [← hEq]
  exact Real.sqrt_le_sqrt hle

/-- For n ≥ 1, √n times the small-probability mass is at most the full square-root probability
sum. -/
theorem sqrtN_smallBranch_le_crude (k : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    Real.sqrt (n : ℝ) * smallBranchSum k n ≤ crudeSqrtSum k n := by
  unfold smallBranchSum crudeSqrtSum
  rw [Finset.mul_sum]
  apply sum_le_sum
  intro x _
  by_cases h : powerLawProb k n x ≤ (1 : ℝ) / (n : ℝ)
  · rw [ite_eq_left h]
    exact sqrtN_mul_le_sqrt hn (powerLawProb_nonneg k n hn x) h
  · rw [ite_eq_right h]
    simp only [mul_zero]
    exact Real.sqrt_nonneg _

/-- For n ≥ 1, the full square-root probability sum equals sumPow(k/2, n)/√(powerLawMass k n). -/
theorem crudeSqrtSum_eq (k : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    crudeSqrtSum k n = sumPow (k / 2) n / Real.sqrt (powerLawMass k n) := by
  have hMpos : 0 < powerLawMass k n := powerLawMass_pos k n hn
  have hterm : ∀ x : Fin n,
      Real.sqrt (powerLawProb k n x)
        = ((((x : ℕ) + 1 : ℝ) ^ (k / 2)) / Real.sqrt (powerLawMass k n)) := by
    intro x
    unfold powerLawProb
    have hbase : (0 : ℝ) ≤ (((x : ℕ) + 1 : ℝ)) := by positivity
    rw [Real.sqrt_div' _ hMpos.le]
    have hsq : Real.sqrt ((((x : ℕ) + 1 : ℝ)) ^ k) = ((((x : ℕ) + 1 : ℝ)) ^ (k / 2)) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hbase]
      ring_nf
    rw [hsq]
  unfold crudeSqrtSum
  rw [Finset.sum_congr rfl (fun x _ => hterm x)]
  rw [← Finset.sum_div]
  congr 1
  have hsum : ∑ x : Fin n, ((((x : ℕ) + 1 : ℝ)) ^ (k / 2)) = sumPow (k / 2) n := by
    simpa [sumPow] using! (Fin.sum_univ_eq_sum_range
      (fun i : ℕ => (((i : ℝ) + 1) ^ (k / 2))) n)
  rw [hsum]

/-- For n ≥ 1, the power-law cost bound is at most 136 times sumPow(k/2, n)/√(powerLawMass k n),
plus 4/3 [Montanaro2011]. -/
theorem powerLawTstarBound_le_crude (k : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    powerLawTstarBound k n
      ≤ 136 * (sumPow (k / 2) n / Real.sqrt (powerLawMass k n)) + 4 / 3 := by
  have h1 := sqrtBranchSum_le_crude k n hn
  have h2 := sqrtN_smallBranch_le_crude k n hn
  have hc := crudeSqrtSum_eq k n hn
  have hnpos : (0 : ℝ) ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  rw [powerLawTstarBound_eq]
  have hA : 83 * sqrtBranchSum k n ≤ 83 * crudeSqrtSum k n := by
    gcongr
  have hB : 53 * (Real.sqrt (n : ℝ) * smallBranchSum k n) ≤ 53 * crudeSqrtSum k n := by
    gcongr
  have hcrude : 0 ≤ crudeSqrtSum k n := by
    unfold crudeSqrtSum
    apply sum_nonneg
    intro x _
    exact Real.sqrt_nonneg _
  calc 83 * sqrtBranchSum k n + 53 * Real.sqrt (n : ℝ) * smallBranchSum k n + 4 / 3
      = 83 * sqrtBranchSum k n + 53 * (Real.sqrt (n : ℝ) * smallBranchSum k n) + 4 / 3 := by
        ring
    _ ≤ 83 * crudeSqrtSum k n + 53 * crudeSqrtSum k n + 4 / 3 := by linarith
    _ = 136 * crudeSqrtSum k n + 4 / 3 := by ring
    _ = 136 * (sumPow (k / 2) n / Real.sqrt (powerLawMass k n)) + 4 / 3 := by rw [hc]

/-- For n ≥ 1, the power-law cost bound is nonnegative. -/
theorem powerLawTstarBound_nonneg (k : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ powerLawTstarBound k n := by
  rw [powerLawTstarBound_eq]
  have h1 : 0 ≤ sqrtBranchSum k n := by
    unfold sqrtBranchSum
    apply sum_nonneg
    intro x _
    by_cases h : (1 : ℝ) / (n : ℝ) < powerLawProb k n x
    · rw [ite_eq_left h]; exact Real.sqrt_nonneg _
    · rw [ite_eq_right h]
  have h2 : 0 ≤ smallBranchSum k n := by
    unfold smallBranchSum
    apply sum_nonneg
    intro x _
    by_cases h : powerLawProb k n x ≤ (1 : ℝ) / (n : ℝ)
    · rw [ite_eq_left h]; exact powerLawProb_nonneg k n hn x
    · rw [ite_eq_right h]
  have h3 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  nlinarith [h1, h2, h3]

/-- For a negative exponent and n ≥ 1, the power sum is at least one. -/
theorem one_le_sumPow_of_neg {k : ℝ} (_hk : k < 0) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ sumPow k n := by
  have hmem : 0 ∈ Finset.range n := by rw [Finset.mem_range]; omega
  have hnonneg : ∀ i ∈ Finset.range n, (0 : ℝ) ≤ ((i : ℝ) + 1) ^ k := by
    intro i _; positivity
  have := Finset.single_le_sum hnonneg hmem
  unfold sumPow
  simpa using! this

/-- For k < −2, the ratio sumPow(k/2, n)/√(powerLawMass k n) is O(1) [Montanaro2011]. -/
theorem crude_isBigO_one {k : ℝ} (hk : k < -2) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => sumPow (k / 2) n / Real.sqrt (powerLawMass k n))
      (fun _ : ℕ => (1 : ℝ)) := by
  have hk2 : k / 2 < -1 := by linarith
  have hC : (0 : ℝ) < 1 / (-(k / 2 + 1) * 2 ^ (k / 2)) := by
    apply div_pos (by norm_num)
    exact mul_pos (by linarith) (Real.rpow_pos_of_pos (by norm_num) _)
  refine Asymptotics.IsBigO.of_bound (1 / (-(k / 2 + 1) * 2 ^ (k / 2))) ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn1
  have hMge : (1 : ℝ) ≤ powerLawMass k n := by
    rw [powerLawMass_eq_sumPow]
    exact one_le_sumPow_of_neg (by linarith : k < 0) hn1
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (powerLawMass k n) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hMge
  have hnum : sumPow (k / 2) n ≤ 1 / (-(k / 2 + 1) * 2 ^ (k / 2)) := sumPow_upper_lt hk2 n
  have hAnneg : (0 : ℝ) ≤ sumPow (k / 2) n := sumPow_nonneg _ _
  have hq_nneg : (0 : ℝ) ≤ sumPow (k / 2) n / Real.sqrt (powerLawMass k n) :=
    div_nonneg hAnneg (Real.sqrt_nonneg _)
  have hstep : sumPow (k / 2) n / Real.sqrt (powerLawMass k n) ≤ sumPow (k / 2) n / 1 :=
    div_le_div_of_nonneg_left hAnneg (by norm_num : (0 : ℝ) < 1) hsqrt1
  rw [Real.norm_of_nonneg hq_nneg, Real.norm_eq_abs, abs_one, mul_one]
  calc sumPow (k / 2) n / Real.sqrt (powerLawMass k n)
      ≤ sumPow (k / 2) n / 1 := hstep
    _ = sumPow (k / 2) n := by rw [div_one]
    _ ≤ 1 / (-(k / 2 + 1) * 2 ^ (k / 2)) := hnum

/-- For k < −2, the power-law cost bound is O(1). -/
theorem tstarBound_isBigO_one {k : ℝ} (hk : k < -2) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => powerLawTstarBound k n)
      (fun _ : ℕ => (1 : ℝ)) := by
  have hcrude := crude_isBigO_one hk
  rw [Asymptotics.isBigO_iff_isBigOWith] at hcrude
  obtain ⟨c, hc⟩ := hcrude
  have hcb : ∀ᶠ n : ℕ in Filter.atTop,
      sumPow (k / 2) n / Real.sqrt (powerLawMass k n) ≤ c := by
    filter_upwards [hc.bound] with n hn
    have hnn : (0 : ℝ) ≤ sumPow (k / 2) n / Real.sqrt (powerLawMass k n) :=
      div_nonneg (sumPow_nonneg _ _) (Real.sqrt_nonneg _)
    simpa [Real.norm_of_nonneg hnn] using! hn
  refine Asymptotics.IsBigO.of_bound (136 * c + 4 / 3) ?_
  filter_upwards [hcb, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hb hn1
  have hbnneg := powerLawTstarBound_nonneg k n hn1
  have hle := powerLawTstarBound_le_crude k n hn1
  rw [Real.norm_of_nonneg hbnneg, Real.norm_eq_abs, abs_one, mul_one]
  calc powerLawTstarBound k n
      ≤ 136 * (sumPow (k / 2) n / Real.sqrt (powerLawMass k n)) + 4 / 3 := hle
    _ ≤ 136 * c + 4 / 3 := by nlinarith [hb]

/-- At k = −2, the ratio sumPow(k/2, n)/√(powerLawMass k n) is O(log n) [Montanaro2011]. -/
theorem crude_isBigO_log :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => sumPow ((-2 : ℝ) / 2) n / Real.sqrt (powerLawMass (-2) n))
      (fun n : ℕ => Real.log (n : ℝ)) := by
  have hk : (-2 : ℝ) < 0 := by norm_num
  refine Asymptotics.IsBigO.of_bound 2 ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (1 : ℝ))] with n hn1 hlog1
  have hMge : (1 : ℝ) ≤ powerLawMass (-2) n := by
    rw [powerLawMass_eq_sumPow]; exact one_le_sumPow_of_neg hk hn1
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (powerLawMass (-2) n) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hMge
  have hnum : sumPow ((-2 : ℝ) / 2) n ≤ 1 + Real.log (n : ℝ) := by
    have hsp : sumPow ((-2 : ℝ) / 2) n = harmSum n := by
      rw [show ((-2 : ℝ) / 2) = -1 by norm_num]; exact sumPow_neg_one n
    rw [hsp]; exact harm_le_one_add_log n
  have hAnneg : (0 : ℝ) ≤ sumPow ((-2 : ℝ) / 2) n := sumPow_nonneg _ _
  have hq_nneg : (0 : ℝ) ≤ sumPow ((-2 : ℝ) / 2) n / Real.sqrt (powerLawMass (-2) n) :=
    div_nonneg hAnneg (Real.sqrt_nonneg _)
  have hstep : sumPow ((-2 : ℝ) / 2) n / Real.sqrt (powerLawMass (-2) n) ≤
      sumPow ((-2 : ℝ) / 2) n / 1 :=
    div_le_div_of_nonneg_left hAnneg (by norm_num : (0 : ℝ) < 1) hsqrt1
  have hlog1' : (1 : ℝ) ≤ Real.log (n : ℝ) := hlog1
  have hlognneg : (0 : ℝ) ≤ Real.log (n : ℝ) := le_trans (by norm_num) hlog1'
  rw [Real.norm_of_nonneg hq_nneg, Real.norm_of_nonneg hlognneg]
  calc sumPow ((-2 : ℝ) / 2) n / Real.sqrt (powerLawMass (-2) n)
      ≤ sumPow ((-2 : ℝ) / 2) n / 1 := hstep
    _ = sumPow ((-2 : ℝ) / 2) n := by rw [div_one]
    _ ≤ 1 + Real.log (n : ℝ) := hnum
    _ ≤ 2 * Real.log (n : ℝ) := by linarith

/-- At k = −2, the power-law cost bound is O(log n). -/
theorem tstarBound_isBigO_log :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => powerLawTstarBound (-2) n)
      (fun n : ℕ => Real.log (n : ℝ)) := by
  have hcrude := crude_isBigO_log
  rw [Asymptotics.isBigO_iff_isBigOWith] at hcrude
  obtain ⟨c, hc⟩ := hcrude
  have hcb : ∀ᶠ n : ℕ in Filter.atTop,
      sumPow ((-2 : ℝ) / 2) n / Real.sqrt (powerLawMass (-2) n) ≤ c * Real.log (n : ℝ) := by
    filter_upwards [hc.bound] with n hn
    have hnn : (0 : ℝ) ≤ sumPow ((-2 : ℝ) / 2) n / Real.sqrt (powerLawMass (-2) n) :=
      div_nonneg (sumPow_nonneg _ _) (Real.sqrt_nonneg _)
    rw [Real.norm_of_nonneg hnn] at hn
    have : ‖Real.log (n : ℝ)‖ = Real.log (n : ℝ) := by
      rw [Real.norm_eq_abs, abs_of_nonneg]
      exact Real.log_natCast_nonneg n
    rw [this] at hn
    exact hn
  refine Asymptotics.IsBigO.of_bound (136 * c + 4 / 3) ?_
  filter_upwards [hcb, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩,
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop (1 : ℝ))] with n hb hn1 hlog1
  have hbnneg := powerLawTstarBound_nonneg (-2) n hn1
  have hle := powerLawTstarBound_le_crude (-2) n hn1
  have hlog1' : (1 : ℝ) ≤ Real.log (n : ℝ) := hlog1
  have hlognneg : (0 : ℝ) ≤ Real.log (n : ℝ) := le_trans (by norm_num) hlog1'
  rw [Real.norm_of_nonneg hbnneg, Real.norm_of_nonneg hlognneg]
  calc powerLawTstarBound (-2) n
      ≤ 136 * (sumPow ((-2 : ℝ) / 2) n / Real.sqrt (powerLawMass (-2) n)) + 4 / 3 := hle
    _ ≤ 136 * (c * Real.log (n : ℝ)) + 4 / 3 := by nlinarith [hb]
    _ ≤ (136 * c + 4 / 3) * Real.log (n : ℝ) := by nlinarith [hlog1']

/-- For −1 < k < 0, the ratio sumPow(k/2, n)/√(powerLawMass k n) is O(√n) [Montanaro2011]. -/
theorem crude_isBigO_sqrt_of_gt {k : ℝ} (hk1 : -1 < k) (hk0 : k < 0) :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => sumPow (k / 2) n / Real.sqrt (powerLawMass k n))
      (fun n : ℕ => Real.sqrt (n : ℝ)) := by
  have hk2a : -1 < k / 2 := by linarith
  have hk2b : k / 2 < 0 := by linarith
  have hspos : 0 < k / 2 + 1 := by linarith
  have hk1pos : 0 < k + 1 := by linarith
  have hC1 : (0 : ℝ) ≤ 2 ^ (k / 2 + 1) / ((k / 2 + 1) * 2 ^ (k / 2)) := by positivity
  have hrpow_tendsto : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ (k + 1)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hk1pos).comp tendsto_natCast_atTop_atTop
  have hge : ∀ᶠ n : ℕ in Filter.atTop, (2 : ℝ) ≤ (n : ℝ) ^ (k + 1) :=
    hrpow_tendsto.eventually (Filter.eventually_ge_atTop (2 : ℝ))
  refine Asymptotics.IsBigO.of_bound
    ((2 ^ (k / 2 + 1) / ((k / 2 + 1) * 2 ^ (k / 2))) * Real.sqrt (2 * (k + 1))) ?_
  filter_upwards [hge, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n h2 hn1
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)

  have hnum : sumPow (k / 2) n ≤
      (2 ^ (k / 2 + 1) / ((k / 2 + 1) * 2 ^ (k / 2))) * (n : ℝ) ^ (k / 2 + 1) := by
    have hb := sumPow_upper_neg hk2a hk2b n
    have hmono : ((n : ℝ) + 1) ^ (k / 2 + 1) ≤ 2 ^ (k / 2 + 1) * (n : ℝ) ^ (k / 2 + 1) :=
      rpow_succ_le_two_mul hspos.le (by exact_mod_cast hn1)
    have hden : (0 : ℝ) < (k / 2 + 1) * 2 ^ (k / 2) :=
      mul_pos hspos (Real.rpow_pos_of_pos (by norm_num) _)
    calc sumPow (k / 2) n ≤ ((n : ℝ) + 1) ^ (k / 2 + 1) / ((k / 2 + 1) * 2 ^ (k / 2)) := hb
      _ ≤ (2 ^ (k / 2 + 1) * (n : ℝ) ^ (k / 2 + 1)) / ((k / 2 + 1) * 2 ^ (k / 2)) :=
          div_le_div_of_nonneg_right hmono hden.le
      _ = (2 ^ (k / 2 + 1) / ((k / 2 + 1) * 2 ^ (k / 2))) * (n : ℝ) ^ (k / 2 + 1) := by
          ring

  have hMlow : (n : ℝ) ^ (k + 1) / (2 * (k + 1)) ≤ powerLawMass k n := by
    rw [powerLawMass_eq_sumPow]
    have hbase := sumPow_lower_neg hk1 hk0 n
    have hden : (0 : ℝ) < k + 1 := hk1pos
    have h1 : (n : ℝ) ^ (k + 1) ≤ ((n : ℝ) + 1) ^ (k + 1) :=
      Real.rpow_le_rpow (le_of_lt hnpos) (by linarith) hk1pos.le
    have h2 : (n : ℝ) ^ (k + 1) - 1 ≥ (n : ℝ) ^ (k + 1) / 2 := by linarith
    have hnum2 : (n : ℝ) ^ (k + 1) / (2 * (k + 1)) ≤
        (((n : ℝ) + 1) ^ (k + 1) - 1) / (k + 1) := by
      have heq : (n : ℝ) ^ (k + 1) / (2 * (k + 1)) = ((n : ℝ) ^ (k + 1) / 2) / (k + 1) := by
        field_simp
      rw [heq, div_le_div_iff_of_pos_right hden]
      nlinarith [h1, h2]
    exact le_trans hnum2 hbase
  have hsqrtM : (n : ℝ) ^ ((k + 1) / 2) / Real.sqrt (2 * (k + 1)) ≤
      Real.sqrt (powerLawMass k n) := by
    have hpos : (0 : ℝ) ≤ (n : ℝ) ^ (k + 1) := Real.rpow_nonneg hnpos.le _
    have hsarg : Real.sqrt ((n : ℝ) ^ (k + 1) / (2 * (k + 1))) =
        (n : ℝ) ^ ((k + 1) / 2) / Real.sqrt (2 * (k + 1)) := by
      rw [Real.sqrt_div' _ (by positivity)]
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hnpos.le]
      ring_nf
    rw [← hsarg]
    exact Real.sqrt_le_sqrt hMlow
  have hsqrtden : (0 : ℝ) < (n : ℝ) ^ ((k + 1) / 2) / Real.sqrt (2 * (k + 1)) := by
    apply div_pos
    · exact Real.rpow_pos_of_pos hnpos _
    · exact Real.sqrt_pos.2 (by positivity)
  have hq_nneg : (0 : ℝ) ≤ sumPow (k / 2) n / Real.sqrt (powerLawMass k n) :=
    div_nonneg (sumPow_nonneg _ _) (Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg hq_nneg, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  set C := 2 ^ (k / 2 + 1) / ((k / 2 + 1) * 2 ^ (k / 2)) with hCdef
  have hCnn : 0 ≤ C := hC1
  have hstep1 : sumPow (k / 2) n / Real.sqrt (powerLawMass k n)
      ≤ (C * (n : ℝ) ^ (k / 2 + 1)) / Real.sqrt (powerLawMass k n) :=
    div_le_div_of_nonneg_right hnum (Real.sqrt_nonneg _)
  have hstep2 : (C * (n : ℝ) ^ (k / 2 + 1)) / Real.sqrt (powerLawMass k n)
      ≤ (C * (n : ℝ) ^ (k / 2 + 1)) / ((n : ℝ) ^ ((k + 1) / 2) / Real.sqrt (2 * (k + 1))) :=
    div_le_div_of_nonneg_left (mul_nonneg hCnn (Real.rpow_nonneg hnpos.le _)) hsqrtden hsqrtM
  have hstep : sumPow (k / 2) n / Real.sqrt (powerLawMass k n)
      ≤ (C * (n : ℝ) ^ (k / 2 + 1)) / ((n : ℝ) ^ ((k + 1) / 2) / Real.sqrt (2 * (k + 1))) :=
    le_trans hstep1 hstep2
  have hexp : (n : ℝ) ^ (k / 2 + 1) / (n : ℝ) ^ ((k + 1) / 2) = Real.sqrt (n : ℝ) := by
    rw [← Real.rpow_sub hnpos, Real.sqrt_eq_rpow]
    congr 1
    ring
  calc sumPow (k / 2) n / Real.sqrt (powerLawMass k n)
      ≤ (C * (n : ℝ) ^ (k / 2 + 1)) / ((n : ℝ) ^ ((k + 1) / 2) / Real.sqrt (2 * (k + 1))) := hstep
    _ = C * Real.sqrt (2 * (k + 1)) *
          ((n : ℝ) ^ (k / 2 + 1) / (n : ℝ) ^ ((k + 1) / 2)) := by
          field_simp
    _ = C * Real.sqrt (2 * (k + 1)) * Real.sqrt (n : ℝ) := by rw [hexp]

/-- For −1 < k < 0, the power-law cost bound is O(√n). -/
theorem tstarBound_isBigO_sqrt_of_gt {k : ℝ} (hk1 : -1 < k) (hk0 : k < 0) :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => powerLawTstarBound k n)
      (fun n : ℕ => Real.sqrt (n : ℝ)) := by
  have hcrude := crude_isBigO_sqrt_of_gt hk1 hk0
  rw [Asymptotics.isBigO_iff_isBigOWith] at hcrude
  obtain ⟨c, hc⟩ := hcrude
  have hcb : ∀ᶠ n : ℕ in Filter.atTop,
      sumPow (k / 2) n / Real.sqrt (powerLawMass k n) ≤ c * Real.sqrt (n : ℝ) := by
    filter_upwards [hc.bound] with n hn
    have hnn : (0 : ℝ) ≤ sumPow (k / 2) n / Real.sqrt (powerLawMass k n) :=
      div_nonneg (sumPow_nonneg _ _) (Real.sqrt_nonneg _)
    rw [Real.norm_of_nonneg hnn] at hn
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hn
    exact hn
  refine Asymptotics.IsBigO.of_bound (136 * c + 4 / 3) ?_
  filter_upwards [hcb, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hb hn1
  have hbnneg := powerLawTstarBound_nonneg k n hn1
  have hle := powerLawTstarBound_le_crude k n hn1
  rw [Real.norm_of_nonneg hbnneg, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hn1)
  calc powerLawTstarBound k n
      ≤ 136 * (sumPow (k / 2) n / Real.sqrt (powerLawMass k n)) + 4 / 3 := hle
    _ ≤ 136 * (c * Real.sqrt (n : ℝ)) + 4 / 3 := by nlinarith [hb]
    _ ≤ (136 * c + 4 / 3) * Real.sqrt (n : ℝ) := by nlinarith [hs1]

/-- At k = −1, the ratio sumPow(k/2, n)/√(powerLawMass k n) is O(√n) [Montanaro2011]. -/
theorem crude_isBigO_sqrt_neg_one :
    Asymptotics.IsBigO Filter.atTop
      (fun n : ℕ => sumPow ((-1 : ℝ) / 2) n / Real.sqrt (powerLawMass (-1) n))
      (fun n : ℕ => Real.sqrt (n : ℝ)) := by
  have hk2a : (-1 : ℝ) < (-1 : ℝ) / 2 := by norm_num
  have hk2b : (-1 : ℝ) / 2 < 0 := by norm_num
  have hspos : 0 < (-1 : ℝ) / 2 + 1 := by norm_num
  refine Asymptotics.IsBigO.of_bound
    (2 ^ ((-1 : ℝ) / 2 + 1) / (((-1 : ℝ) / 2 + 1) * 2 ^ ((-1 : ℝ) / 2))) ?_
  filter_upwards [Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hn1
  have hMge : (1 : ℝ) ≤ powerLawMass (-1) n := by
    rw [powerLawMass_eq_sumPow]
    exact one_le_sumPow_of_neg (by norm_num : (-1 : ℝ) < 0) hn1
  have hsqrt1 : (1 : ℝ) ≤ Real.sqrt (powerLawMass (-1) n) := by
    have h := Real.sqrt_le_sqrt hMge
    rwa [Real.sqrt_one] at h
  have hnum : sumPow ((-1 : ℝ) / 2) n ≤
      (2 ^ ((-1 : ℝ) / 2 + 1) / (((-1 : ℝ) / 2 + 1) * 2 ^ ((-1 : ℝ) / 2))) *
        Real.sqrt (n : ℝ) := by
    have hb := sumPow_upper_neg hk2a hk2b n
    have hmono : ((n : ℝ) + 1) ^ ((-1 : ℝ) / 2 + 1) ≤
        2 ^ ((-1 : ℝ) / 2 + 1) * (n : ℝ) ^ ((-1 : ℝ) / 2 + 1) :=
      rpow_succ_le_two_mul hspos.le (by exact_mod_cast hn1)
    have hpow : (n : ℝ) ^ ((-1 : ℝ) / 2 + 1) = Real.sqrt (n : ℝ) := by
      have h12 : (-1 : ℝ) / 2 + 1 = 1 / 2 := by norm_num
      rw [h12, ← Real.sqrt_eq_rpow]
    calc sumPow ((-1 : ℝ) / 2) n
        ≤ ((n : ℝ) + 1) ^ ((-1 : ℝ) / 2 + 1) / (((-1 : ℝ) / 2 + 1) * 2 ^ ((-1 : ℝ) / 2)) := hb
      _ ≤ (2 ^ ((-1 : ℝ) / 2 + 1) * (n : ℝ) ^ ((-1 : ℝ) / 2 + 1)) /
            (((-1 : ℝ) / 2 + 1) * 2 ^ ((-1 : ℝ) / 2)) :=
          div_le_div_of_nonneg_right hmono (by positivity)
      _ = (2 ^ ((-1 : ℝ) / 2 + 1) / (((-1 : ℝ) / 2 + 1) * 2 ^ ((-1 : ℝ) / 2))) *
            Real.sqrt (n : ℝ) := by
          rw [hpow]; ring
  have hq_nneg : (0 : ℝ) ≤ sumPow ((-1 : ℝ) / 2) n / Real.sqrt (powerLawMass (-1) n) :=
    div_nonneg (sumPow_nonneg _ _) (Real.sqrt_nonneg _)
  rw [Real.norm_of_nonneg hq_nneg, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hstep : sumPow ((-1 : ℝ) / 2) n / Real.sqrt (powerLawMass (-1) n) ≤
      sumPow ((-1 : ℝ) / 2) n / 1 :=
    div_le_div_of_nonneg_left (sumPow_nonneg _ _) (by norm_num : (0 : ℝ) < 1) hsqrt1
  calc sumPow ((-1 : ℝ) / 2) n / Real.sqrt (powerLawMass (-1) n)
      ≤ sumPow ((-1 : ℝ) / 2) n / 1 := hstep
    _ = sumPow ((-1 : ℝ) / 2) n := by rw [div_one]
    _ ≤ (2 ^ ((-1 : ℝ) / 2 + 1) / (((-1 : ℝ) / 2 + 1) * 2 ^ ((-1 : ℝ) / 2))) *
          Real.sqrt (n : ℝ) := hnum

/-- At k = −1, the power-law cost bound is O(√n). -/
theorem tstarBound_isBigO_sqrt_neg_one :
    Asymptotics.IsBigO Filter.atTop (fun n : ℕ => powerLawTstarBound (-1) n)
      (fun n : ℕ => Real.sqrt (n : ℝ)) := by
  have hcrude := crude_isBigO_sqrt_neg_one
  rw [Asymptotics.isBigO_iff_isBigOWith] at hcrude
  obtain ⟨c, hc⟩ := hcrude
  have hcb : ∀ᶠ n : ℕ in Filter.atTop,
      sumPow ((-1 : ℝ) / 2) n / Real.sqrt (powerLawMass (-1) n) ≤ c * Real.sqrt (n : ℝ) := by
    filter_upwards [hc.bound] with n hn
    have hnn : (0 : ℝ) ≤ sumPow ((-1 : ℝ) / 2) n / Real.sqrt (powerLawMass (-1) n) :=
      div_nonneg (sumPow_nonneg _ _) (Real.sqrt_nonneg _)
    rw [Real.norm_of_nonneg hnn] at hn
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)] at hn
    exact hn
  refine Asymptotics.IsBigO.of_bound (136 * c + 4 / 3) ?_
  filter_upwards [hcb, Filter.eventually_atTop.2 ⟨1, fun n hn => hn⟩] with n hb hn1
  have hbnneg := powerLawTstarBound_nonneg (-1) n hn1
  have hle := powerLawTstarBound_le_crude (-1) n hn1
  rw [Real.norm_of_nonneg hbnneg, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  have hs1 : (1 : ℝ) ≤ Real.sqrt (n : ℝ) := by
    have h := Real.sqrt_le_sqrt (by exact_mod_cast hn1 : (1 : ℝ) ≤ (n : ℝ))
    rwa [Real.sqrt_one] at h
  calc powerLawTstarBound (-1) n
      ≤ 136 * (sumPow ((-1 : ℝ) / 2) n / Real.sqrt (powerLawMass (-1) n)) + 4 / 3 := hle
    _ ≤ 136 * (c * Real.sqrt (n : ℝ)) + 4 / 3 := by nlinarith [hb]
    _ ≤ (136 * c + 4 / 3) * Real.sqrt (n : ℝ) := by nlinarith [hs1]

/-- For −1 ≤ k < 0, an eventually nonnegative function eventually dominated by the stated
nonnegative power-law bound is O(√n) [Montanaro2011]. -/
theorem prop_3_4_case_sqrt (k : ℝ) (hk1 : -1 ≤ k) (hk0 : k < 0) (Tstar : ℕ → ℝ)
    (h_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ Tstar n)
    (h_bound_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ powerLawTstarBound k n)
    (h_bound : ∀ᶠ n : ℕ in Filter.atTop, Tstar n ≤ powerLawTstarBound k n) :
    Asymptotics.IsBigO Filter.atTop Tstar (fun n => Real.sqrt (n : ℝ)) := by
  have hbase : Asymptotics.IsBigO Filter.atTop Tstar (fun n => powerLawTstarBound k n) :=
    isBigO_of_eventually_le h_nonneg h_bound_nonneg h_bound
  rcases eq_or_lt_of_le hk1 with hk | hk
  · subst hk
    exact hbase.trans tstarBound_isBigO_sqrt_neg_one
  · exact hbase.trans (tstarBound_isBigO_sqrt_of_gt hk hk0)

/-- An eventually nonnegative function eventually dominated by the stated nonnegative power-law
bound at k = −2 is O(log n) [Montanaro2011]. -/
theorem prop_3_4_case_log (Tstar : ℕ → ℝ)
    (h_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ Tstar n)
    (h_bound_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ powerLawTstarBound (-2) n)
    (h_bound : ∀ᶠ n : ℕ in Filter.atTop, Tstar n ≤ powerLawTstarBound (-2) n) :
    Asymptotics.IsBigO Filter.atTop Tstar (fun n => Real.log (n : ℝ)) :=
  (isBigO_of_eventually_le h_nonneg h_bound_nonneg h_bound).trans tstarBound_isBigO_log

/-- For k < −2, an eventually nonnegative function eventually dominated by the stated
nonnegative power-law bound is O(1) [Montanaro2011]. -/
theorem prop_3_4_case_const {k : ℝ} (hk : k < -2) (Tstar : ℕ → ℝ)
    (h_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ Tstar n)
    (h_bound_nonneg : ∀ᶠ n : ℕ in Filter.atTop, 0 ≤ powerLawTstarBound k n)
    (h_bound : ∀ᶠ n : ℕ in Filter.atTop, Tstar n ≤ powerLawTstarBound k n) :
    Asymptotics.IsBigO Filter.atTop Tstar (fun _ => (1 : ℝ)) :=
  (isBigO_of_eventually_le h_nonneg h_bound_nonneg h_bound).trans (tstarBound_isBigO_one hk)

end Qatlib.Papers.QSearchAdvice09.MainResults
