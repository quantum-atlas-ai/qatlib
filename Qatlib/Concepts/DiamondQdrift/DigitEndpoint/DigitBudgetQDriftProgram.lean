/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.EffectiveInput.EffectiveQuantizerExactScaleCamp
import Qatlib.Concepts.RandCompile.EffectiveInput.QuantizedCoefficientQDrift

/-!
# Digit budgets for qDRIFT compilation

This module constructs `digitBudgetQDriftData` from rational lower approximations to coefficient
magnitudes and sign flags. It bounds the number of digit reads, the coefficient table error, and
the simulation step count.

`digitBudgetQDrift_reference_error` bounds the actual finite coin implementation uniformly over
reference systems, giving an effective input version of the qDRIFT setting of [Campbell2019].

## Main statements

* `digitBudgetQDriftData_spec`: digit access, precision, and step count guarantees.
* `digitBudgetQDrift_reference_error`: trace norm error at most `ε` times the input trace norm.

## References

* [Campbell, 2019][Campbell2019]
-/

set_option backward.isDefEq.respectTransparency false
set_option warningAsError false

set_option autoImplicit false
set_option maxHeartbeats 600000
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.PureStateMath

open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.DiamondQdrift.QuantizerCert
open Qatlib.Concepts.TrotterFormula.LieStrang
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.EffectiveInput
open Qatlib.Concepts.RandCompile.FairBitSampling

namespace Qatlib.Concepts.DiamondQdrift.DigitEndpoint
open Matrix
open scoped BigOperators Matrix.Norms.L2Operator

/-- Finite compilation data containing coefficient precision, stored digits, a signed table,
integer weights, digit reads, steps, rejection fuel, and base time. -/
structure DigitBudgetQDriftData (L : ℕ) where
  precision : ℕ
  digits : List ℚ
  table : Fin L → ℚ
  weights : Fin L → ℕ
  digitReads : ℕ
  steps : ℕ
  fuel : ℕ
  baseTime : ℚ

/-- Construct qDRIFT compilation data from one rational digit column, sign flags, rational time,
and rational error tolerance. -/
def digitBudgetQDriftData {L : ℕ} (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool)
    (t ε : ℚ) : DigitBudgetQDriftData L :=
  let k := Nat.clog 2 (Nat.ceil (16 * (L : ℚ) * |t| / ε))
  let digits := List.ofFn (fun j => q j k)
  let table : Fin L → ℚ := fun j =>
    let x := digits[j.val]'(by simp only [digits, List.length_ofFn]; exact j.isLt)
    if sgn j then -x else x
  let w := dyadicWeights k table
  let lam : ℚ := (weightTotal w : ℚ) / (2 : ℚ) ^ k
  let n := max 1 (Nat.ceil (16 * lam ^ 2 * t ^ 2 / ε))
  let s := Nat.clog 2 (Nat.ceil (8 / ε))
  { precision := k
    digits := digits
    table := table
    weights := w
    digitReads := digits.length
    steps := n
    fuel := fairQdriftFuel n s
    baseTime := t / (2 : ℚ) ^ k }

/-- The branch evolution time obtained by multiplying the stored base time by total weight and
dividing by the step count. -/
def digitBudgetQDriftBranchTime {L : ℕ} (r : DigitBudgetQDriftData L) : ℚ :=
  r.baseTime * (weightTotal r.weights : ℚ) / (r.steps : ℚ)

/-- The natural ceiling of a rational number is unchanged when the rational is cast to the
reals. -/
private theorem natCeilRatCast (x : ℚ) : Nat.ceil (x : ℝ) = Nat.ceil x := by
  rw [← Int.ceil_toNat, ← Int.ceil_toNat, Rat.ceil_cast]

/-- For positive `ε`, the selected binary precision satisfies `16 * L * |t| ≤ ε * 2 ^ k` over
the rationals. -/
private theorem precision_pow_bound (L : ℕ) (t ε : ℚ) (hε : 0 < ε) :
    16 * (L : ℚ) * |t| ≤ ε * (2 : ℚ) ^
      (Nat.clog 2 (Nat.ceil (16 * (L : ℚ) * |t| / ε))) := by
  have hc : 16 * (L : ℚ) * |t| / ε ≤ (2 : ℚ) ^
      (Nat.clog 2 (Nat.ceil (16 * (L : ℚ) * |t| / ε))) := by
    calc 16 * (L : ℚ) * |t| / ε ≤ ((Nat.ceil (16 * (L : ℚ) * |t| / ε) : ℕ) : ℚ) :=
          Nat.le_ceil _
    _ ≤ _ := by
        exact_mod_cast Nat.le_pow_clog (by norm_num : (1 : ℕ) < 2) _
  rw [div_le_iff₀ hε] at hc
  exact hc.trans_eq (mul_comm _ _)

/-- The selected binary precision satisfies the corresponding real inequality `16 * L * |t| ≤ ε
* 2 ^ k`. -/
private theorem precision_pow_bound_real (L : ℕ) (t ε : ℚ) (hε : 0 < ε) :
    (16 : ℝ) * (L : ℝ) * |(t : ℝ)| ≤ (ε : ℝ) * (2 : ℝ) ^
      (Nat.clog 2 (Nat.ceil (16 * (L : ℚ) * |t| / ε))) := by
  have h := precision_pow_bound L t ε hε
  exact_mod_cast h

/-- Each stored table entry is the oracle value at the selected precision with its specified
sign. -/
private theorem tableEntry {L : ℕ} (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool)
    (t ε : ℚ) (j : Fin L) :
    (digitBudgetQDriftData q sgn t ε).table j =
      if sgn j then -(q j (digitBudgetQDriftData q sgn t ε).precision)
        else q j (digitBudgetQDriftData q sgn t ε).precision := by
  simp only [digitBudgetQDriftData]
  rw [List.getElem_ofFn]

/-- For a correct sign flag and a lower magnitude approximation, the signed absolute coefficient
error equals the magnitude approximation deficit. -/
private theorem signed_entry_deficit {L : ℕ} (a : Fin L → ℝ) (q : Fin L → ℕ → ℚ)
    (sgn : Fin L → Bool) (k : ℕ)
    (hor : ∀ j, RatLowerOracle |a j| (q j))
    (hp : ∀ j, (if sgn j then -(a j) else a j) = |a j|) (j : Fin L) :
    |a j - ((if sgn j then -(q j k) else q j k : ℚ) : ℝ)| = |a j| - (q j k : ℝ) := by
  obtain ⟨hq0, hqle, hqdef⟩ := hor j k
  cases hsgn : sgn j with
  | false =>
    have hpj : a j = |a j| := by
      have h := hp j
      rw [hsgn] at h
      simpa using h
    have hc : ¬(false = true) := by simp
    rw [if_neg hc, abs_of_nonneg (by linarith)]
    linarith
  | true =>
    have hpj : -a j = |a j| := by
      have h := hp j
      rw [hsgn] at h
      simpa using h
    have hc : (true = true) := rfl
    rw [if_pos hc]
    have he : a j - ((-(q j k) : ℚ) : ℝ) = -(|a j| - (q j k : ℝ)) := by
      rw [Rat.cast_neg]; linarith
    rw [he, abs_neg, abs_of_nonneg (by linarith)]

/-- The total absolute coefficient error of a correctly signed precision `k` table is at most `L
/ 2 ^ k`. -/
private theorem table_l1_error {L : ℕ} (a : Fin L → ℝ) (q : Fin L → ℕ → ℚ)
    (sgn : Fin L → Bool) (k : ℕ)
    (hor : ∀ j, RatLowerOracle |a j| (q j))
    (hp : ∀ j, (if sgn j then -(a j) else a j) = |a j|) :
    (∑ j, |a j - ((if sgn j then -(q j k) else q j k : ℚ) : ℝ)|) ≤
      (L : ℝ) / (2 : ℝ) ^ k := by
  have hkey : ∀ j, |a j - ((if sgn j then -(q j k) else q j k : ℚ) : ℝ)| ≤
      ((2 : ℝ) ⁻¹) ^ k := fun j =>
    ((signed_entry_deficit a q sgn k hor hp j).trans_le (hor j k).2.2)
  refine (Finset.sum_le_sum (fun j _ => hkey j)).trans_eq ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    inv_pow, inv_eq_one_div, mul_one_div]

/-- The dyadic weight mass divided by `2 ^ k` is at most the table magnitude sum plus `L / 2 ^
(k + 1)`. -/
private theorem weight_mass_bound {L : ℕ} (k : ℕ) (table : Fin L → ℚ) :
    ((weightTotal (dyadicWeights k table) : ℝ) / (2 : ℝ) ^ k) ≤
      (∑ j, |(table j : ℝ)|) + (L : ℝ) / (2 : ℝ) ^ (k + 1) := by
  have hper (j : Fin L) : ((dyadicWeights k table j : ℤ)) =
      |(dyadicCoefficient k (table j) : ℤ)| := by
    simp [dyadicWeights]
  have abs_le_add (x y : ℝ) : |x| ≤ |x - y| + |y| := by
    simpa using abs_sub_le x y 0
  have htri (j : Fin L) : ((dyadicWeights k table j : ℝ)) / (2 : ℝ) ^ k ≤
      |(table j : ℝ)| + 1 / (2 : ℝ) ^ (k + 1) := by
    have hcast : ((dyadicWeights k table j : ℝ)) =
        |(dyadicCoefficient k (table j) : ℝ)| := by exact_mod_cast hper j
    calc ((dyadicWeights k table j : ℝ)) / (2 : ℝ) ^ k
        = |(dyadicCoefficient k (table j) : ℝ) / (2 : ℝ) ^ k| := by
          rw [hcast, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ k)]
      _ ≤ |(dyadicCoefficient k (table j) : ℝ) / (2 : ℝ) ^ k - (table j : ℝ)|
          + |(table j : ℝ)| := abs_le_add _ _
      _ ≤ 1 / (2 : ℝ) ^ (k + 1) + |(table j : ℝ)| :=
          add_le_add (dyadicCoefficient_error k (table j)) le_rfl
      _ = |(table j : ℝ)| + 1 / (2 : ℝ) ^ (k + 1) := add_comm _ _
  have hsum : ((weightTotal (dyadicWeights k table) : ℝ)) =
      (∑ j, ((dyadicWeights k table j : ℝ))) := by
    simp [weightTotal]
  rw [hsum, Finset.sum_div]
  refine (Finset.sum_le_sum (fun j _ => htri j)).trans_eq ?_
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one_div]

/-- Valid lower oracles and sign flags give exactly `L` digit reads, table error at most `L / 2
^ precision`, positive step count, the precision budget, and at most `ceil (32 * λ² * t² /
ε) + 3` steps, where `λ` is the coefficient magnitude sum. This supplies digit and step
budgets for the qDRIFT setting of [Campbell2019]. -/
theorem digitBudgetQDriftData_spec :
    ∀ (L : ℕ) (a : Fin L → ℝ) (t ε : ℚ)
      (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool),
    0 < ε → ε ≤ 1 →
    (∀ j, RatLowerOracle |a j| (q j)) →
    (∀ j, (if sgn j then -(a j) else a j) = |a j|) →
    let r := digitBudgetQDriftData q sgn t ε
    r.digitReads = L ∧ r.digits = List.ofFn (fun j => q j r.precision) ∧
    (∑ j, |a j - (r.table j : ℝ)|) ≤ (L : ℝ) / (2 : ℝ) ^ r.precision ∧
    1 ≤ r.steps ∧
    (16 : ℝ) * L * |(t : ℝ)| ≤ (ε : ℝ) * (2 : ℝ) ^ r.precision ∧
    r.steps ≤ Nat.ceil (32 * (∑ j, |a j|) ^ 2 * (t : ℝ) ^ 2 / (ε : ℝ)) + 3 := by
  intro L a t ε q sgn hε hε1 hor hp
  (try dsimp only)
  have hreads : (digitBudgetQDriftData q sgn t ε).digitReads = L := by
    simp [digitBudgetQDriftData, List.length_ofFn]
  set k := (digitBudgetQDriftData q sgn t ε).precision with hk
  have htable (j : Fin L) : (digitBudgetQDriftData q sgn t ε).table j =
      if sgn j then -(q j k) else q j k := tableEntry q sgn t ε j
  have hl1 : (∑ j, |a j - ((digitBudgetQDriftData q sgn t ε).table j : ℝ)|) ≤
      (L : ℝ) / (2 : ℝ) ^ k := by
    have hsumeq : (∑ j, |a j - ((if sgn j then -(q j k) else q j k : ℚ) : ℝ)|) =
        (∑ j, |a j - ((digitBudgetQDriftData q sgn t ε).table j : ℝ)|) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [htable j]
    rw [← hsumeq]
    exact table_l1_error a q sgn k hor hp
  have hpow : (16 : ℝ) * L * |(t : ℝ)| ≤ (ε : ℝ) * (2 : ℝ) ^ k :=
    precision_pow_bound_real L t ε hε
  have hmass := weight_mass_bound k (digitBudgetQDriftData q sgn t ε).table
  have hper (j : Fin L) : |(((digitBudgetQDriftData q sgn t ε).table j : ℝ))| ≤
      |a j| := by
    have hq0 : (0 : ℝ) ≤ (q j k : ℝ) := by exact_mod_cast (hor j k).1
    have hqle : (q j k : ℝ) ≤ |a j| := (hor j k).2.1
    rw [htable j]
    cases hsgn : sgn j with
    | false => rw [if_neg (by simp), abs_of_nonneg hq0]; exact hqle
    | true => rw [if_pos rfl, Rat.cast_neg, abs_neg, abs_of_nonneg hq0]; exact hqle
  have htabs : (∑ j, |(((digitBudgetQDriftData q sgn t ε).table j : ℝ))|) ≤
      (∑ j, |a j|) := Finset.sum_le_sum (fun j _ => hper j)
  have hlamw : (((weightTotal (dyadicWeights k
      (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k)) ≤
      (∑ j, |a j|) + (L : ℝ) / (2 : ℝ) ^ (k + 1) :=
    hmass.trans (add_le_add htabs le_rfl)
  have hlamw' : (0 : ℝ) ≤ ((weightTotal (dyadicWeights k
      (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k) := by positivity
  have hlam2 : ((weightTotal (dyadicWeights k
      (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k) ^ 2 ≤
      2 * (∑ j, |a j|) ^ 2 + 2 * ((L : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 := by
    have hkey : ((∑ j, |a j|) + (L : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 ≤
        2 * (∑ j, |a j|) ^ 2 + 2 * ((L : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 := by
      nlinarith [sq_nonneg ((∑ j, |a j|) - (L : ℝ) / (2 : ℝ) ^ (k + 1))]
    exact (pow_le_pow_left₀ hlamw' hlamw 2).trans hkey
  have hLtk : (L : ℝ) * |(t : ℝ)| / (2 : ℝ) ^ k ≤ (ε : ℝ) / 16 := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    exact (div_le_iff₀ h2).mpr (by nlinarith [hpow])
  have hsteps : (digitBudgetQDriftData q sgn t ε).steps = max 1 (Nat.ceil (16 *
      ((weightTotal (dyadicWeights k (digitBudgetQDriftData q sgn t ε).table) : ℚ) /
        (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε)) := rfl
  set WQ : ℚ := (weightTotal (dyadicWeights k (digitBudgetQDriftData q sgn t ε).table) : ℚ)
    with hWQ
  have hcast : ((16 * (WQ / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε : ℚ) : ℝ) =
      16 * ((weightTotal (dyadicWeights k
      (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k) ^ 2 * (t : ℝ) ^ 2 /
      (ε : ℝ) := by
    rw [hWQ]
    push_cast
    ring
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hct : ((L : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 * (t : ℝ) ^ 2 ≤ ((ε : ℝ) / 32) ^ 2 := by
    have hc2 : (L : ℝ) * |(t : ℝ)| / (2 : ℝ) ^ (k + 1) ≤ (ε : ℝ) / 32 := by
      have h2 : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
      have hkp : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
      refine (div_le_iff₀ h2).mpr ?_
      rw [hkp]
      nlinarith [hpow]
    have ht : |(t : ℝ)| ^ 2 = (t : ℝ) ^ 2 := sq_abs _
    have heq : ((L : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 * (t : ℝ) ^ 2 =
        ((L : ℝ) * |(t : ℝ)| / (2 : ℝ) ^ (k + 1)) ^ 2 := by
      rw [div_pow, div_pow, mul_pow, ht]
      ring
    rw [heq]
    exact pow_le_pow_left₀ (by positivity) hc2 2
  have hmain : 16 * ((weightTotal (dyadicWeights k
      (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k) ^ 2 * (t : ℝ) ^ 2 /
      (ε : ℝ) ≤ 32 * (∑ j, |a j|) ^ 2 * (t : ℝ) ^ 2 / (ε : ℝ) + (ε : ℝ) / 32 := by
    have hsq1 : 16 * ((weightTotal (dyadicWeights k
        (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k) ^ 2 * (t : ℝ) ^ 2 ≤
        32 * (∑ j, |a j|) ^ 2 * (t : ℝ) ^ 2 +
        32 * ((L : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 * (t : ℝ) ^ 2 := by
      nlinarith [hlam2]
    have hc32 : 32 * ((L : ℝ) / (2 : ℝ) ^ (k + 1)) ^ 2 * (t : ℝ) ^ 2 / (ε : ℝ) ≤
        (ε : ℝ) / 32 := by
      refine (div_le_iff₀ hεR).mpr ?_
      nlinarith [hct]
    have hd := div_le_div_of_nonneg_right hsq1 hεR.le
    rw [add_div] at hd
    linarith
  have hceil : Nat.ceil (16 * (WQ / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε) ≤
      Nat.ceil (32 * (∑ j, |a j|) ^ 2 * (t : ℝ) ^ 2 / (ε : ℝ)) + 1 := by
    have hr : Nat.ceil (16 * (WQ / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε) =
        Nat.ceil (((16 * (WQ / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε : ℚ) : ℝ)) :=
      (natCeilRatCast _).symm
    rw [hr, hcast]
    have hc1 := Nat.ceil_le_ceil hmain
    have hc2 := Nat.ceil_add_le (32 * (∑ j, |a j|) ^ 2 * (t : ℝ) ^ 2 / (ε : ℝ))
      ((ε : ℝ) / 32)
    have hε1R : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
    have hc3 : Nat.ceil ((ε : ℝ) / 32) ≤ 1 :=
      Nat.ceil_le.2 (by nlinarith [hε1R])
    omega
  have hfinal : (digitBudgetQDriftData q sgn t ε).steps ≤
      Nat.ceil (32 * (∑ j, |a j|) ^ 2 * (t : ℝ) ^ 2 / (ε : ℝ)) + 3 := by
    rw [hsteps]
    omega
  exact ⟨hreads, rfl, hl1, by rw [hsteps]; exact Nat.le_max_left 1 _, hpow, hfinal⟩

/-- The precision budget bounds `L * |t| / 2 ^ k` by `ε / 16` and its next precision counterpart
by `ε / 32`. -/
private theorem L_abs_over_pow (L : ℕ) (t ε : ℚ) (_hε : 0 < ε) (k : ℕ)
    (hpow : (16 : ℝ) * L * |(t : ℝ)| ≤ (ε : ℝ) * (2 : ℝ) ^ k) :
    (L : ℝ) * |(t : ℝ)| / (2 : ℝ) ^ k ≤ (ε : ℝ) / 16 ∧
    (L : ℝ) * |(t : ℝ)| / (2 : ℝ) ^ (k + 1) ≤ (ε : ℝ) / 32 := by
  have h1 : (L : ℝ) * |(t : ℝ)| / (2 : ℝ) ^ k ≤ (ε : ℝ) / 16 := by
    have h2 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
    exact (div_le_iff₀ h2).mpr (by nlinarith [hpow])
  have h2 : (L : ℝ) * |(t : ℝ)| / (2 : ℝ) ^ (k + 1) ≤ (ε : ℝ) / 32 := by
    have hk : (0 : ℝ) < (2 : ℝ) ^ (k + 1) := by positivity
    have hkp : (2 : ℝ) ^ (k + 1) = 2 * (2 : ℝ) ^ k := by ring
    refine (div_le_iff₀ hk).mpr ?_
    rw [hkp]
    nlinarith [hpow]
  exact ⟨h1, h2⟩

/-- The combined coefficient and weight rounding contribution is at most `3 * ε / 16` under the
precision budget. -/
private theorem rounding_term_bound (L : ℕ) (t ε : ℚ) (_hε : 0 < ε) (k : ℕ)
    (hpow : (16 : ℝ) * L * |(t : ℝ)| ≤ (ε : ℝ) * (2 : ℝ) ^ k) :
    2 * |(t : ℝ)| * ((L : ℝ) / (2 : ℝ) ^ k + (L : ℝ) / (2 : ℝ) ^ (k + 1)) ≤
    3 * (ε : ℝ) / 16 := by
  obtain ⟨h1, h2⟩ := L_abs_over_pow L t ε _hε k hpow
  have e1 : 2 * |(t : ℝ)| * ((L : ℝ) / (2 : ℝ) ^ k + (L : ℝ) / (2 : ℝ) ^ (k + 1)) =
      2 * ((L : ℝ) * |(t : ℝ)| / (2 : ℝ) ^ k) +
      2 * ((L : ℝ) * |(t : ℝ)| / (2 : ℝ) ^ (k + 1)) := by
    ring
  rw [e1]
  linarith

/-- The selected fair coin rejection fuel bounds `2 * n * (1 / 2) ^ fuel` by `ε / 16` under the
stated binary precision bound. -/
private theorem fuel_inverse_budget (n s : ℕ) (_t ε : ℚ) (hε : 0 < ε)
    (hs : (8 : ℝ) / (ε : ℝ) ≤ (2 : ℝ) ^ s) :
    2 * (n : ℝ) * ((1 / 2 : ℝ) ^ (fairQdriftFuel n s)) ≤ (ε : ℝ) / 16 := by
  have hc : (n : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 (max 1 n)) := by
    exact_mod_cast ((Nat.le_max_right 1 n).trans
      (Nat.le_pow_clog (by norm_num : (1 : ℕ) < 2) _))
  have honediv : ((1 / 2 : ℝ) ^ (Nat.clog 2 (max 1 n))) =
      1 / ((2 : ℝ) ^ (Nat.clog 2 (max 1 n))) := by
    rw [one_div, inv_pow, inv_eq_one_div]
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have h8 : (8 : ℝ) ≤ (ε : ℝ) * (2 : ℝ) ^ s :=
    ((div_le_iff₀ hεR).mp hs).trans_eq (mul_comm _ _)
  have h2s : ((1 / 2 : ℝ) ^ s) ≤ (ε : ℝ) / 8 := by
    have he : ((1 / 2 : ℝ) ^ s) = 1 / ((2 : ℝ) ^ s) := by
      rw [one_div, inv_pow, inv_eq_one_div]
    have hp : (0 : ℝ) < (2 : ℝ) ^ s := by positivity
    rw [he]
    field_simp
    linarith [h8]
  have hR : fairQdriftFuel n s = s + Nat.clog 2 (max 1 n) + 2 := rfl
  have hnc' : (n : ℝ) * (1 / ((2 : ℝ) ^ (Nat.clog 2 (max 1 n)))) ≤ 1 := by
    have hp : (0 : ℝ) < (2 : ℝ) ^ (Nat.clog 2 (max 1 n)) := by positivity
    have hpre : (n : ℝ) ≤ 1 * ((2 : ℝ) ^ (Nat.clog 2 (max 1 n))) := by
      rw [one_mul]; exact hc
    have hdiv : (n : ℝ) / ((2 : ℝ) ^ (Nat.clog 2 (max 1 n))) ≤ 1 :=
      (div_le_iff₀ hp).mpr hpre
    rwa [← mul_one_div] at hdiv
  have key : (n : ℝ) * (1 / ((2 : ℝ) ^ (Nat.clog 2 (max 1 n)))) * ((1 / 2 : ℝ) ^ s) ≤
      (ε : ℝ) / 8 :=
    (mul_le_mul hnc' h2s (by positivity) (by positivity)).trans_eq (by ring)
  calc 2 * (n : ℝ) * ((1 / 2 : ℝ) ^ (fairQdriftFuel n s))
      = 2 * (1 / 4) * ((n : ℝ) * (1 / ((2 : ℝ) ^ (Nat.clog 2 (max 1 n)))) *
          ((1 / 2 : ℝ) ^ s)) := by
        rw [hR, pow_add, pow_add, honediv]
        ring
    _ ≤ 2 * (1 / 4) * ((ε : ℝ) / 8) := mul_le_mul_of_nonneg_left key (by positivity)
    _ = (ε : ℝ) / 16 := by ring

/-- For Hermitian contraction terms, valid lower oracles, correct sign flags, and `0 < ε ≤ 1`,
the actual compiled map has trace norm error at most `ε * traceNorm X` for every reference
size and input matrix `X`. This is a finite coin implementation bound in the qDRIFT setting
of [Campbell2019]. -/
theorem digitBudgetQDrift_reference_error :
    ∀ (L D : ℕ) (a : Fin L → ℝ) (K : Fin L → Operator D)
    (t ε : ℚ) (j0 : Fin L) (q : Fin L → ℕ → ℚ) (sgn : Fin L → Bool),
    (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) → 0 < ε → ε ≤ 1 →
    (∀ j, RatLowerOracle |a j| (q j)) →
    (∀ j, (if sgn j then -(a j) else a j) = |a j|) →
    let r := digitBudgetQDriftData q sgn t ε
    let terms := dyadicSignedTerms r.precision r.table K
    ∀ ref : ℕ, ∀ X : Matrix (Fin D × Fin ref) (Fin D × Fin ref) ℂ,
      Matrix.traceNorm (
        tensorLeft (fairQdriftActualMap r.weights j0 r.steps r.fuel terms r.baseTime) X -
        tensorLeft (conjBranch (HamiltonianEvolution (∑ j, (a j : ℂ) • K j) t)) X)
      ≤ (ε : ℝ) * Matrix.traceNorm X := by
  intro L D a K t ε j0 q sgn hK hε hε1 hor hp r terms ref X
  set k := (digitBudgetQDriftData q sgn t ε).precision with hk
  have hsteps : (digitBudgetQDriftData q sgn t ε).steps = max 1 (Nat.ceil (16 *
      ((weightTotal (dyadicWeights k (digitBudgetQDriftData q sgn t ε).table) : ℚ) /
        (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε)) := rfl
  have hfuel : (digitBudgetQDriftData q sgn t ε).fuel = fairQdriftFuel
      (digitBudgetQDriftData q sgn t ε).steps (Nat.clog 2 (Nat.ceil (8 / ε))) := rfl
  have hn : 0 < (digitBudgetQDriftData q sgn t ε).steps := by
    rw [hsteps]; exact Nat.le_max_left 1 _
  have hpow : (16 : ℝ) * L * |(t : ℝ)| ≤ (ε : ℝ) * (2 : ℝ) ^ k :=
    precision_pow_bound_real L t ε hε
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hε1R : (ε : ℝ) ≤ 1 := by exact_mod_cast hε1
  have htable (j : Fin L) : (digitBudgetQDriftData q sgn t ε).table j =
      if sgn j then -(q j k) else q j k := tableEntry q sgn t ε j
  have hl1 : (∑ j, |a j - ((digitBudgetQDriftData q sgn t ε).table j : ℝ)|) ≤
      (L : ℝ) / (2 : ℝ) ^ k := by
    have hsumeq : (∑ j, |a j - ((if sgn j then -(q j k) else q j k : ℚ) : ℝ)|) =
        (∑ j, |a j - ((digitBudgetQDriftData q sgn t ε).table j : ℝ)|) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [htable j]
    rw [← hsumeq]
    exact table_l1_error a q sgn k hor hp
  have hbaseR : ((digitBudgetQDriftData q sgn t ε).baseTime : ℝ) =
      (t : ℝ) / (2 : ℝ) ^ k := by
    simp only [digitBudgetQDriftData]
    rw [Rat.cast_div]
    push_cast
    rfl
  have hs : (8 : ℝ) / (ε : ℝ) ≤ (2 : ℝ) ^ (Nat.clog 2 (Nat.ceil (8 / ε))) := by
    have h1 : (8 : ℚ) / ε ≤ ((Nat.ceil ((8 : ℚ) / ε) : ℕ) : ℚ) := Nat.le_ceil _
    have h2 : ((Nat.ceil ((8 : ℚ) / ε) : ℕ) : ℚ) ≤
        ((2 : ℚ) ^ (Nat.clog 2 (Nat.ceil ((8 : ℚ) / ε)))) := by
      exact_mod_cast Nat.le_pow_clog (by norm_num : (1 : ℕ) < 2) _
    exact_mod_cast h1.trans h2
  have hterm2 : 2 * ((digitBudgetQDriftData q sgn t ε).steps : ℝ) *
      ((1 / 2 : ℝ) ^ (digitBudgetQDriftData q sgn t ε).fuel) ≤ (ε : ℝ) / 16 := by
    rw [hfuel]
    exact fuel_inverse_budget _ _ t ε hε hs
  have hterm3 := rounding_term_bound L t ε hε k hpow
  have hWcase : weightTotal (dyadicWeights k (digitBudgetQDriftData q sgn t ε).table) = 0 ∨
      0 < weightTotal (dyadicWeights k (digitBudgetQDriftData q sgn t ε).table) := by
    rcases Nat.eq_zero_or_pos (weightTotal (dyadicWeights k
      (digitBudgetQDriftData q sgn t ε).table)) with h | h
    · exact Or.inl h
    · exact Or.inr h
  rcases hWcase with hW | hW
  · have hwmap : fairQdriftActualMap (digitBudgetQDriftData q sgn t ε).weights j0
        (digitBudgetQDriftData q sgn t ε).steps (digitBudgetQDriftData q sgn t ε).fuel
        (dyadicSignedTerms k (digitBudgetQDriftData q sgn t ε).table K)
        ((digitBudgetQDriftData q sgn t ε).baseTime : ℝ) = LinearMap.id := by
      refine (fairQdriftActualMap_zero (digitBudgetQDriftData q sgn t ε).weights j0
        (digitBudgetQDriftData q sgn t ε).steps (digitBudgetQDriftData q sgn t ε).fuel
        (dyadicSignedTerms k (digitBudgetQDriftData q sgn t ε).table K)
        ((digitBudgetQDriftData q sgn t ε).baseTime : ℝ) ?_).1
      have hw : (digitBudgetQDriftData q sgn t ε).weights =
          dyadicWeights k (digitBudgetQDriftData q sgn t ε).table := rfl
      rw [hw]
      exact hW
    rw [hwmap, tensorLeft_id, tensorLeft_conjBranch]
    have hH : (∑ j, (a j : ℂ) • K j).IsHermitian :=
      quantized_real_generator_hermitian a K (fun j => (hK j).1)
    have hz (j : Fin L) : dyadicCoefficient k ((digitBudgetQDriftData q sgn t ε).table j) = 0 := by
      have hw0 : dyadicWeights k (digitBudgetQDriftData q sgn t ε).table j = 0 :=
        Finset.sum_eq_zero_iff.mp hW j (Finset.mem_univ j)
      have hconv : (dyadicWeights k (digitBudgetQDriftData q sgn t ε).table j) =
          (dyadicCoefficient k ((digitBudgetQDriftData q sgn t ε).table j)).natAbs := rfl
      exact Int.natAbs_eq_zero.mp (by rw [← hconv]; exact hw0)
    have hgen := dyadic_target_generator_error L D k
      (digitBudgetQDriftData q sgn t ε).table a K ((L : ℝ) / (2 : ℝ) ^ k) hK hl1
    have hsum0 : (∑ j, (((dyadicCoefficient k
        ((digitBudgetQDriftData q sgn t ε).table j) : ℂ)/(2 : ℂ)^k) • K j)) = 0 := by
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [hz j]
      simp
    rw [hsum0, sub_zero] at hgen
    have hstab := hermitian_evolution_reference_stability D ref 0
      (∑ j, (a j : ℂ) • K j) (t : ℝ) X (by simp) hH
    have hU : HamiltonianEvolution (0 : Operator D) (t : ℝ) = 1 := by
      simp [HamiltonianEvolution]
    simp only [hU, tensorGate_one, Matrix.conjTranspose_one, Matrix.one_mul,
      Matrix.mul_one] at hstab
    rw [show ((0 : Operator D) - ∑ j, (a j : ℂ) • K j) = -(∑ j, (a j : ℂ) • K j) from
      (zero_sub _)] at hstab
    rw [norm_neg] at hstab
    refine hstab.trans (mul_le_mul_of_nonneg_right ?_ (Matrix.traceNorm_nonneg X))
    have hcomb : 2 * |(t : ℝ)| * ‖∑ j, (a j : ℂ) • K j‖ ≤
        2 * |(t : ℝ)| * ((L : ℝ) / (2 : ℝ) ^ k + (L : ℝ) / (2 : ℝ) ^ (k + 1)) :=
      mul_le_mul_of_nonneg_left hgen (by positivity)
    have := rounding_term_bound L t ε hε k hpow
    linarith
  · have hmain := quantized_qdrift_actual_reference_error L D k
      (digitBudgetQDriftData q sgn t ε).steps (digitBudgetQDriftData q sgn t ε).fuel ref
      (digitBudgetQDriftData q sgn t ε).table a j0 K (t : ℝ) ((L : ℝ) / (2 : ℝ) ^ k) X hn hW hK hl1
    have hnR : (0 : ℝ) < ((digitBudgetQDriftData q sgn t ε).steps : ℝ) := by
      exact_mod_cast hn
    have hnlamQ : (16 * ((weightTotal (dyadicWeights k
        (digitBudgetQDriftData q sgn t ε).table) : ℚ) / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε : ℚ) ≤
        ((digitBudgetQDriftData q sgn t ε).steps : ℚ) := by
      have h1 : (16 * ((weightTotal (dyadicWeights k
          (digitBudgetQDriftData q sgn t ε).table) : ℚ) / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε : ℚ) ≤
          ((Nat.ceil (16 * ((weightTotal (dyadicWeights k
          (digitBudgetQDriftData q sgn t ε).table) : ℚ) / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε) : ℕ) : ℚ) :=
        Nat.le_ceil _
      have h2 : ((Nat.ceil (16 * ((weightTotal (dyadicWeights k
          (digitBudgetQDriftData q sgn t ε).table) : ℚ) / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε) : ℕ) : ℚ) ≤
          ((max 1 (Nat.ceil (16 * ((weightTotal (dyadicWeights k
          (digitBudgetQDriftData q sgn t ε).table) : ℚ) / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε)) : ℕ) : ℚ) := by
        exact_mod_cast Nat.le_max_right 1 _
      rw [← hsteps] at h2
      exact h1.trans h2
    have hcast2 : ((16 * ((weightTotal (dyadicWeights k
        (digitBudgetQDriftData q sgn t ε).table) : ℚ) / (2 : ℚ) ^ k) ^ 2 * t ^ 2 / ε : ℚ) : ℝ) =
        16 * ((weightTotal (dyadicWeights k
        (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k) ^ 2 * (t : ℝ) ^ 2 /
        (ε : ℝ) := by
      push_cast
      ring
    have hnlamR : 16 * ((weightTotal (dyadicWeights k
        (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k) ^ 2 * (t : ℝ) ^ 2 /
        (ε : ℝ) ≤ ((digitBudgetQDriftData q sgn t ε).steps : ℝ) := by
      rw [← hcast2]
      exact_mod_cast hnlamQ
    have hmul : 16 * ((weightTotal (dyadicWeights k
        (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k) ^ 2 * (t : ℝ) ^ 2 ≤
        ((digitBudgetQDriftData q sgn t ε).steps : ℝ) * (ε : ℝ) :=
      (div_le_iff₀ hεR).mp hnlamR
    have hterm1 : 4 * ((weightTotal (dyadicWeights k
        (digitBudgetQDriftData q sgn t ε).table) : ℝ) / (2 : ℝ) ^ k) ^ 2 * (t : ℝ) ^ 2 /
        ((digitBudgetQDriftData q sgn t ε).steps : ℝ) ≤ (ε : ℝ) / 4 := by
      refine (div_le_iff₀ hnR).mpr ?_
      nlinarith [hmul]
    rw [fairQdriftActualMap_reference, tensorLeft_conjBranch]
    have hbaseR' : ((r.baseTime : ℚ) : ℝ) = (t : ℝ) / (2 : ℝ) ^ k := hbaseR
    have hqo : quantizedQdriftOutput k r.table j0 r.steps r.fuel K (t : ℝ) ref X =
        fairQdriftReferenceOutput r.weights j0 r.steps r.fuel terms
        ((r.baseTime : ℚ) : ℝ) ref X := by
      rw [hbaseR']
      rfl
    rw [← hqo]
    refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (Matrix.traceNorm_nonneg X))
    have hsum3 := add_le_add (add_le_add hterm1 hterm2) hterm3
    have heq : (ε : ℝ) / 4 + (ε : ℝ) / 16 + 3 * (ε : ℝ) / 16 = (ε : ℝ) / 2 := by ring
    rw [heq] at hsum3
    linarith
end Qatlib.Concepts.DiamondQdrift.DigitEndpoint
