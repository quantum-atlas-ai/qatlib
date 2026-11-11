/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs

/-!
# Certified qDRIFT budgets and postselection

This module derives executable qDRIFT budgets from certified rational parameter reads and
bracket streams, proves allocation bounds, and compares capped sampling with postselected
importance sampling. It also establishes projection and conditional-output estimates,
phase-estimation repetition bounds, and exact synthesis of Hermitian evolutions by two-level
instructions and reflection-gate circuits.

The mathematical background is described in [Campbell2019].

## Main statements

* `clause19_endpoint`: certified input reads yield simulation budgets and path ledgers.
* `tight_allocation_endpoint`: allocation bounds imply finite diamond-distance bounds.
* `clause21_endpoint`: coherence obstruction and postselection guarantees.
* `synthesis_registers_agree`: two exact synthesis forms on qubit registers.

## References

* [Campbell, 2019][Campbell2019]
-/

open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.AdaptiveCP.BranchTrace
open Qatlib.Concepts.FairRandomBits.RationalReject
open Qatlib.Foundations.QueryWordCore.Circuit Qatlib.Concepts.ReferenceError.MixturePaths
open Qatlib.Concepts.ReferenceError.RefTraceError
open Qatlib.Concepts.LchsSimulation.StaticLchs Qatlib.Foundations.PureStateMath.Reflection
open Qatlib.Concepts.MatrixAccess.KnownFrameSynth
open Qatlib.Foundations.PureStateMath
open Qatlib.Concepts.NativeNumerics.PhaseSynthesis
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.GateVocabulary.LocalReflectionGates
open Qatlib.Concepts.LinearLearning.ConcisePipeline.CostedLaw
open Qatlib.Concepts.BlockEncoding.LCU Qatlib.Foundations.PureStateMath.BornBridge Qatlib.Concepts.CopyEvolution.Discriminate
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.SchattenDiamond.DiamondNorm Qatlib.Concepts.RandCompile.ChannelBudget
open Qatlib.Concepts.RandCompile.FairBitSampling
open Qatlib.Concepts.RandCompile.ReferenceModel
open Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftDefs

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

/-- If a list contains an element satisfying a Boolean predicate, `List.find?` returns some
element. -/
theorem exists_find?_of_mem_true : ∀ (p : ℕ → Bool) (l : List ℕ),
    (∃ a ∈ l, p a = true) → ∃ a, l.find? p = some a := by
  intro p l
  induction l with
  | nil =>
      intro h
      obtain ⟨a, ha, _⟩ := h
      exact absurd ha (by simp)
  | cons b l ih =>
      intro h
      by_cases hb : p b = true
      · exact ⟨b, by simp [hb]⟩
      · obtain ⟨a, ha, hpa⟩ := h
        simp only [List.mem_cons] at ha
        rcases ha with rfl | ha
        · exact absurd hpa hb
        · obtain ⟨a, ha'⟩ := ih ⟨a, ha, hpa⟩
          exact ⟨a, by simp [hb, ha']⟩

/-- The selected scan precision is at most the available fuel. -/
theorem scanPrecision_le : ∀ (fuel : ℕ) (cert : ℕ → Bool),
    scanPrecision fuel cert ≤ fuel := by
  intro fuel cert
  unfold scanPrecision
  cases h : precScan cert fuel with
  | some j =>
    have hj : j ≤ fuel := by
      have := List.mem_of_find?_eq_some h
      simpa [precScan] using! this
    simp only [h, Option.getD_some]
    exact hj
  | none => simp [precScan]

/-- If a certified precision exists within the fuel bound, the precision returned by
`scanPrecision` is certified. -/
theorem scanPrecision_certified : ∀ (fuel : ℕ) (cert : ℕ → Bool),
    (∃ k, k ≤ fuel ∧ cert k = true) →
    cert (scanPrecision fuel cert) = true := by
  intro fuel cert hex
  obtain ⟨k, hk, hc⟩ := hex
  obtain ⟨j, hj⟩ := exists_find?_of_mem_true cert (List.range (fuel + 1))
    ⟨k, List.mem_range.mpr (by omega), hc⟩
  have hjmem : j ≤ fuel := by
    have := List.mem_of_find?_eq_some hj
    simpa [precScan] using! this
  unfold scanPrecision
  rw [precScan, hj]
  exact List.find?_some hj

/-- Casting a rational dyadic power to the reals preserves its value. -/
theorem dyadic_cast (k : ℕ) : ((1 / 2 : ℚ) ^ k : ℝ) = (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, pow_succ]
    push_cast
    ring

/-- A reliable lower-parameter read produces an error budget no greater than the represented
real value. -/
theorem epsBudget_le (x : ℝ) (q : ℕ → ℚ) (hq : RelLowerParamRead x q) (k : ℕ) :
    (epsBudget q k : ℝ) ≤ x := by
  have h1 : (q k : ℝ) ≤ x := (hq k).1
  have h2 : (0 : ℝ) ≤ ((1 / 2 : ℚ) ^ k : ℝ) := by
    exact_mod_cast (show (0 : ℚ) ≤ (1 / 2 : ℚ) ^ k by positivity)
  have h3 : (epsBudget q k : ℝ) ≤ (q k : ℝ) := by
    have hpos : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ k := by positivity
    have h4 : ((q k - (1 / 2 : ℚ) ^ k : ℚ) : ℝ) ≤ (q k : ℝ) := by
      exact_mod_cast (show q k - (1 / 2 : ℚ) ^ k ≤ q k by linarith)
    exact h4
  exact h3.trans h1

/-- A certified error budget is strictly positive as a real number. -/
theorem epsBudget_pos (q : ℕ → ℚ) (k : ℕ) (h : epsCertified q k = true) :
    0 < (epsBudget q k : ℝ) := by
  have hq : (0 : ℚ) < epsBudget q k := by
    simp only [epsCertified, decide_eq_true_eq] at h
    exact h
  exact_mod_cast hq

/-- The integer time bound computed from a reliable parameter read bounds the absolute real
time. -/
theorem timeBound_ge (t : ℝ) (tq : ℕ → ℚ) (htq : RelParamRead t tq) (k : ℕ) :
    |t| ≤ (timeBound (tq k) k : ℝ) := by
  have h1 : |t| ≤ |(tq k : ℝ)| + |t - (tq k : ℝ)| := by
    calc |t| = |(tq k : ℝ) + (t - (tq k : ℝ))| := by rw [add_sub_cancel]
      _ ≤ |(tq k : ℝ)| + |t - (tq k : ℝ)| := abs_add_le _ _
  have h2 : |t - (tq k : ℝ)| ≤ (1 / 2 : ℝ) ^ k := htq k
  have hceil : ((max (tq k) (-(tq k)) + (1 / 2 : ℚ) ^ k : ℚ) : ℝ)
      ≤ (timeBound (tq k) k : ℝ) := by
    have h := Nat.le_ceil (max (tq k) (-(tq k)) + (1 / 2 : ℚ) ^ k)
    unfold timeBound
    exact_mod_cast h
  have habs : |tq k| ≤ max (tq k) (-(tq k)) := by
    by_cases h : 0 ≤ (tq k : ℚ)
    · rw [abs_of_nonneg h]
      exact le_max_left _ _
    · have h' : (tq k : ℚ) ≤ 0 := le_of_not_ge h
      rw [abs_of_nonpos h']
      exact le_max_right _ _
  have hD : (tq k : ℝ) ≤ (timeBound (tq k) k : ℝ) := by
    have hle : (tq k : ℚ) ≤ max (tq k) (-(tq k)) + (1 / 2 : ℚ) ^ k := by
      exact (le_max_left _ _).trans
        (le_add_of_nonneg_right (by positivity : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ k))
    have hcast : (tq k : ℝ) ≤ ((max (tq k) (-(tq k)) + (1 / 2 : ℚ) ^ k : ℚ) : ℝ) := by
      exact_mod_cast hle
    exact hcast.trans hceil
  have hE : -(tq k : ℝ) ≤ (timeBound (tq k) k : ℝ) := by
    have hle : -(tq k) ≤ max (tq k) (-(tq k)) + (1 / 2 : ℚ) ^ k := by
      exact (le_max_right _ _).trans
        (le_add_of_nonneg_right (by positivity : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ k))
    have hcast : (-(tq k) : ℝ)
        ≤ ((max (tq k) (-(tq k)) + (1 / 2 : ℚ) ^ k : ℚ) : ℝ) := by
      exact_mod_cast hle
    exact hcast.trans hceil
  have h3 : |(tq k : ℝ)| ≤ (timeBound (tq k) k : ℝ) := by
    rw [abs_le]
    exact ⟨by simpa using! neg_le_neg hE, hD⟩
  have h4 : |t - (tq k : ℝ)| ≤ ((1 / 2 : ℚ) ^ k : ℝ) := by
    rw [dyadic_cast]
    exact h2
  have h5 : |(tq k : ℝ)| + ((1 / 2 : ℚ) ^ k : ℝ) ≤ (timeBound (tq k) k : ℝ) := by
    have habs' : |(tq k : ℝ)| ≤ ((max (tq k) (-(tq k)) : ℚ) : ℝ) := by
      rw [← Rat.cast_abs]
      exact_mod_cast habs
    have hcast : ((max (tq k) (-(tq k)) + (1 / 2 : ℚ) ^ k : ℚ) : ℝ)
        = ((max (tq k) (-(tq k)) : ℚ) : ℝ) + ((1 / 2 : ℚ) ^ k : ℝ) := by
      push_cast
      ring
    rw [hcast] at hceil
    linarith
  linarith

/-- A successful precision certificate ensures `2⁻ˢ / 2` is at most the rational error budget,
viewed as a real number. -/
theorem successCertified_ge (eQ : ℚ) (s : ℕ) (h : successCertified eQ s = true) :
    (2 : ℝ)⁻¹ ^ s / 2 ≤ (eQ : ℝ) := by
  have hq : (1 : ℚ) ≤ (2 : ℚ) ^ (s + 1) * eQ := by
    simp only [successCertified, decide_eq_true_eq] at h
    exact h
  have hr : (1 : ℝ) ≤ (2 : ℝ) ^ (s + 1) * (eQ : ℝ) := by
    exact_mod_cast hq
  have hpos : (0 : ℝ) < (2 : ℝ) ^ (s + 1) := by positivity
  have hdiv : (1 : ℝ) / (2 : ℝ) ^ (s + 1) ≤ (eQ : ℝ) := by
    have h : (1 : ℝ) ≤ (eQ : ℝ) * (2 : ℝ) ^ (s + 1) := by
      rw [mul_comm]
      exact hr
    exact (div_le_iff₀ hpos).mpr h
  have hid : (1 : ℝ) / (2 : ℝ) ^ (s + 1) = (2 : ℝ)⁻¹ ^ (s + 1) := by
    rw [one_div, inv_pow]
  have h2 : (2 : ℝ)⁻¹ ^ s / 2 = (2 : ℝ)⁻¹ ^ (s + 1) := by
    rw [pow_succ, div_eq_mul_inv]
  have hfin : (2 : ℝ)⁻¹ ^ (s + 1) ≤ (eQ : ℝ) := by
    rw [← hid]
    exact hdiv
  rw [h2]
  exact hfin

/-- For a positive rational error budget, the computed success fuel satisfies its precision
certificate. -/
theorem successFuel_certified (eQ : ℚ) (he : 0 < eQ) :
    successCertified eQ (successFuel eQ) = true := by
  have hne : eQ ≠ 0 := ne_of_gt he
  have htwo : ∀ n : ℕ, 2 ^ n ≥ n + 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
        _ ≥ (n + 1) * 2 := Nat.mul_le_mul_right 2 ih
        _ ≥ n + 2 := by omega
  have hceil : (1 / eQ : ℚ) ≤ (successFuel eQ : ℚ) := by
    unfold successFuel
    have h := Nat.le_ceil (1 / eQ)
    exact_mod_cast h
  have hge : (2 : ℚ) ^ (successFuel eQ + 1) ≥ (1 / eQ : ℚ) := by
    have h := htwo (successFuel eQ + 1)
    have h2 : (successFuel eQ + 1 : ℕ) ≤ 2 ^ (successFuel eQ + 1) := by omega
    have h2' : ((successFuel eQ + 1 : ℕ) : ℚ) ≤ (2 : ℚ) ^ (successFuel eQ + 1) := by
      exact_mod_cast h2
    have h3 : (1 / eQ : ℚ) ≤ (successFuel eQ : ℚ) + 1 := by linarith
    have h2'' : (successFuel eQ : ℚ) + 1 ≤ (2 : ℚ) ^ (successFuel eQ + 1) := by
      simpa using! h2'
    exact h3.trans h2''
  have hmul : (2 : ℚ) ^ (successFuel eQ + 1) * eQ ≥ (1 / eQ) * eQ := by
    have h1 := mul_le_mul_of_nonneg_right hge (le_of_lt he)
    exact h1
  simp only [successCertified, decide_eq_true_eq]
  simpa [div_eq_mul_inv, inv_mul_cancel₀ hne] using! hmul

/-- For a positive rational error budget, the selected success level satisfies its precision
certificate. -/
theorem successLevel_certified (eQ : ℚ) (he : 0 < eQ) :
    successCertified eQ (successLevel eQ) = true := by
  have hex : ∃ k, k ≤ successFuel eQ ∧ successCertified eQ k = true :=
    ⟨successFuel eQ, le_rfl, successFuel_certified eQ he⟩
  exact scanPrecision_certified (successFuel eQ) (successCertified eQ) hex

/-- The qDRIFT input run satisfies the stated exact formulas for parameter reads, digit reads,
arithmetic, ceiling and logarithm operations, bit time, and bit space. -/
theorem qdriftInputRun_cost (fuel L : ℕ) (tq eq : ℕ → ℚ) :
    let run := qdriftInputRun fuel L tq eq
    run.cost.paramReads = 2 * (run.precision + 1) ∧
    run.cost.digitReads = L * (run.precision + 1) + L ∧
    run.cost.ringOps = 4 * (run.precision + 1) + 2 + 2 * (run.successLevel + 1) ∧
    run.cost.ceilOps = 2 ∧
    run.cost.logOps = run.successLevel + 1 ∧
    run.cost.bitTime =
      (run.cost.ringOps + run.cost.ceilOps + run.cost.logOps) *
        (run.cost.bitLength + 2) * (run.cost.bitLength + 2) ∧
    run.cost.bitSpace = run.cost.bitLength + run.cost.digitReads * run.cost.bitLength + 16 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The run bit-length bound controls the rational bit sizes of both parameter streams at every
precision up to `k`. -/
theorem runBitLength_bounds (k s : ℕ) (L : ℕ) (tq eq : ℕ → ℚ) :
    ∀ k' ≤ k, qdRatBits (tq k') ≤ runBitLength k s L tq eq ∧
      qdRatBits (eq k') ≤ runBitLength k s L tq eq := by
  intro k' hk'
  have hmem : k' ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
  have hsup : max (qdRatBits (tq k')) (qdRatBits (eq k')) ≤
      (Finset.range (k + 1)).sup (fun k' => max (qdRatBits (tq k')) (qdRatBits (eq k'))) :=
    Finset.le_sup (f := fun k' => max (qdRatBits (tq k')) (qdRatBits (eq k'))) hmem
  have hnonneg : 0 ≤ (Finset.range (k + 1)).sup
      (fun k' => max (qdRatBits (tq k')) (qdRatBits (eq k'))) := by
    have hmem0 : 0 ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
    have h1 : max (qdRatBits (tq 0)) (qdRatBits (eq 0))
        ≤ (Finset.range (k + 1)).sup
            (fun k' => max (qdRatBits (tq k')) (qdRatBits (eq k'))) :=
      Finset.le_sup (f := fun k' => max (qdRatBits (tq k')) (qdRatBits (eq k'))) hmem0
    exact le_trans (Nat.zero_le _) h1
  have hbound : (Finset.range (k + 1)).sup
      (fun k' => max (qdRatBits (tq k')) (qdRatBits (eq k'))) ≤ runBitLength k s L tq eq := by
    unfold runBitLength
    omega
  constructor
  · exact le_trans (le_max_left _ _) (le_trans hsup hbound)
  · exact le_trans (le_max_right _ _) (le_trans hsup hbound)

/-- The rational dyadic truncation of a number is no greater than that number. -/
theorem ratTrunc_le (c : ℚ) (k : ℕ) : ratTrunc c k ≤ c := by
  have h1 : ((Rat.floor (c * ((2 : ℚ) ^ k)) : ℤ) : ℚ) ≤ c * ((2 : ℚ) ^ k) := by
    have := Int.floor_le (c * ((2 : ℚ) ^ k))
    exact_mod_cast this
  have h3 : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  rw [ratTrunc]
  exact (div_le_iff₀ h3).mpr h1

/-- The difference between a rational number and its level-`k` truncation is strictly less than
`2⁻ᵏ`. -/
theorem ratTrunc_lt (c : ℚ) (k : ℕ) :
    c - ratTrunc c k < (1 / 2 : ℚ) ^ k := by
  have h1 : c * ((2 : ℚ) ^ k) < ((Rat.floor (c * ((2 : ℚ) ^ k)) : ℤ) : ℚ) + 1 := by
    have := Int.lt_floor_add_one (c * ((2 : ℚ) ^ k))
    exact_mod_cast this
  have h3 : (0 : ℚ) < (2 : ℚ) ^ k := by positivity
  have h4 : (1 / 2 : ℚ) ^ k = 1 / (2 : ℚ) ^ k := by
    rw [div_pow, one_pow]
  have h5 : c - ((Rat.floor (c * ((2 : ℚ) ^ k)) : ℤ) : ℚ) / ((2 : ℚ) ^ k)
      = (c * ((2 : ℚ) ^ k) - ((Rat.floor (c * ((2 : ℚ) ^ k)) : ℤ) : ℚ)) / ((2 : ℚ) ^ k) := by
    field_simp
  rw [ratTrunc, h5, h4, div_lt_div_iff_of_pos_right h3]
  linarith

/-- A rational power of one half casts to the same power in the reals. -/
theorem dyadic_cast_rat (k : ℕ) : ((1 / 2 : ℚ) ^ k : ℝ) = (1 / 2 : ℝ) ^ k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [pow_succ, pow_succ, ih]
    norm_num

/-- The real absolute error of level-`k` rational truncation is at most `2⁻ᵏ`. -/
theorem ratTrunc_err (c : ℚ) (k : ℕ) :
    |(c : ℝ) - (ratTrunc c k : ℝ)| ≤ (1 / 2 : ℝ) ^ k := by
  have h1 : (ratTrunc c k : ℝ) ≤ (c : ℝ) := by
    exact_mod_cast (ratTrunc_le c k)
  have h2 : (c : ℝ) - (ratTrunc c k : ℝ) < ((1 / 2 : ℚ) ^ k : ℝ) := by
    exact_mod_cast (ratTrunc_lt c k)
  have h3 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
  rw [dyadic_cast_rat k] at h2
  rw [abs_le]
  constructor <;> linarith

/-- The real value returned by `bracketRead lo k` is no greater than the lower endpoint `lo`. -/
theorem bracketRead_le (lo : ℚ) (k : ℕ) :
    (bracketRead lo k : ℝ) ≤ (lo : ℝ) := by
  have h1 : ratTrunc lo (k + 1) ≤ lo := ratTrunc_le lo (k + 1)
  have h2 : ((ratTrunc lo (k + 1) : ℚ) : ℝ) ≤ (lo : ℝ) := by exact_mod_cast h1
  unfold bracketRead
  exact h2

/-- The real absolute difference between `lo` and its level-`k` bracket read is at most
`2⁻⁽ᵏ⁺¹⁾`. -/
theorem bracketRead_err (lo : ℚ) (k : ℕ) :
    |(lo : ℝ) - (bracketRead lo k : ℝ)| ≤ (1 / 2 : ℝ) ^ (k + 1) := by
  have h := ratTrunc_err lo (k + 1)
  unfold bracketRead
  exact h

/-- A valid rational bracket yields a read below the represented real value with absolute error
at most `bracketError lo hi k`. -/
theorem bracketRead_reliable (x : ℝ) (lo hi : ℚ) (h : RelBracket x lo hi) (k : ℕ) :
    (bracketRead lo k : ℝ) ≤ x ∧
    |x - (bracketRead lo k : ℝ)| ≤ bracketError lo hi k := by
  have h1 : (bracketRead lo k : ℝ) ≤ (lo : ℝ) := bracketRead_le lo k
  have h2 : (lo : ℝ) ≤ x := h.1
  have h3 : x ≤ (hi : ℝ) := h.2
  have h5 : |x - (lo : ℝ)| ≤ (hi : ℝ) - (lo : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  have h6 : |(lo : ℝ) - (bracketRead lo k : ℝ)| ≤ (1 / 2 : ℝ) ^ (k + 1) :=
    bracketRead_err lo k
  have h7 : |x - (bracketRead lo k : ℝ)|
      ≤ |x - (lo : ℝ)| + |(lo : ℝ) - (bracketRead lo k : ℝ)| := by
    have heq : x - (bracketRead lo k : ℝ)
        = (x - (lo : ℝ)) + ((lo : ℝ) - (bracketRead lo k : ℝ)) := by ring
    rw [heq]
    exact abs_add_le _ _
  constructor
  · exact h1.trans h2
  · rw [bracketError]
    linarith [h7]

/-- The error budget computed from a valid rational bracket is no greater than the bracketed
real value. -/
theorem epsBudgetBracket_le (x : ℝ) (lo hi : ℚ) (h : RelBracket x lo hi) (k : ℕ) :
    (epsBudgetBracket lo hi k : ℝ) ≤ x := by
  have hq1 : bracketRead lo k ≤ lo := by
    unfold bracketRead
    exact ratTrunc_le lo (k + 1)
  have hq2 : 0 ≤ hi - lo := by
    exact_mod_cast (sub_nonneg.mpr (h.1.trans h.2))
  have hq3 : epsBudgetBracket lo hi k ≤ lo := by
    rw [epsBudgetBracket]
    have h4 : (0 : ℚ) ≤ (1 / 2 : ℚ) ^ (k + 1) := by positivity
    linarith
  have hq4 : (epsBudgetBracket lo hi k : ℝ) ≤ (lo : ℝ) := by exact_mod_cast hq3
  exact hq4.trans h.1

/-- A certified bracket-based error budget is strictly positive as a real number. -/
theorem epsBudgetBracket_pos (lo hi : ℚ) (k : ℕ)
    (h : epsCertifiedBracket lo hi k = true) :
    0 < (epsBudgetBracket lo hi k : ℝ) := by
  have hq : (0 : ℚ) < epsBudgetBracket lo hi k := by
    simp only [epsCertifiedBracket, decide_eq_true_eq] at h
    exact h
  exact_mod_cast hq

/-- The integer time bound computed from a valid rational bracket bounds the absolute bracketed
real value. -/
theorem bracketTimeBound_ge (x : ℝ) (lo hi : ℚ) (h : RelBracket x lo hi) :
    |x| ≤ (bracketTimeBound lo hi : ℝ) := by
  have h1 : |x| ≤ max |(lo : ℝ)| |(hi : ℝ)| := by
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      have h2 : (hi : ℝ) ≤ max |(lo : ℝ)| |(hi : ℝ)| := by
        calc (hi : ℝ) ≤ |(hi : ℝ)| := le_abs_self _
          _ ≤ max |(lo : ℝ)| |(hi : ℝ)| := le_max_right _ _
      linarith [h.2]
    · have hx' : x < 0 := lt_of_not_ge hx
      rw [abs_of_neg hx']
      have h2 : -x ≤ -(lo : ℝ) := by linarith [h.1]
      have h3 : -(lo : ℝ) ≤ max |(lo : ℝ)| |(hi : ℝ)| := by
        calc -(lo : ℝ) ≤ |(lo : ℝ)| := neg_le_abs _
          _ ≤ max |(lo : ℝ)| |(hi : ℝ)| := le_max_left _ _
      linarith
  have h2 : max |(lo : ℝ)| |(hi : ℝ)| ≤ (Nat.ceil (max |(lo : ℝ)| |(hi : ℝ)|) : ℝ) := by
    exact_mod_cast (Nat.le_ceil (max |(lo : ℝ)| |(hi : ℝ)|))
  have h3 : (bracketTimeBound lo hi : ℝ)
      = (Nat.ceil (max |(lo : ℝ)| |(hi : ℝ)|) : ℝ) := by
    rw [bracketTimeBound]
  rw [h3]
  exact h1.trans h2

/-- Reliable parameter reads with a certified positive error budget yield bounded time and
precision parameters, a fair-bit qDRIFT map within error `ε` in finite diamond distance, and
the stated pathwise resource ledgers. See [Campbell2019]. -/
theorem clause19_endpoint : ∀ (L D : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (K : Fin L → Operator D) (t ε : ℝ) (tq eq : ℕ → ℚ) (fuel : ℕ),
    RelParamRead t tq → RelLowerParamRead ε eq →
    0 < weightTotal w → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    (∃ k, k ≤ fuel ∧ epsCertified eq k = true) →
    ∃ (T s : ℕ),
      |t| ≤ T ∧
      (2 : ℝ)⁻¹ ^ s / 2 ≤ ε ∧
      finiteDiamondDistance
          (fairQdriftActualMap w j0 (fairQdriftSteps (weightTotal w) T s)
            (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t)
          (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
        ≤ ENNReal.ofReal ε ∧
      (∀ ω : Fin (fairQdriftSteps (weightTotal w) T s) →
          Fin (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) →
          Reg (Nat.clog 2 (weightTotal w)),
        IsUnitaryCircuit (fairQdriftCircuit w j0
          (fairQdriftSteps (weightTotal w) T s)
          (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t ω) ∧
        QueryCount (fairQdriftCircuit w j0
          (fairQdriftSteps (weightTotal w) T s)
          (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t ω) = 0 ∧
        GateCount (fairQdriftCircuit w j0
          (fairQdriftSteps (weightTotal w) T s)
          (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t ω) =
          fairQdriftSteps (weightTotal w) T s ∧
        (∑ m, (fairQdriftPick w j0
          (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) (ω m)).2.1) ≤
          fairQdriftSteps (weightTotal w) T s * Nat.clog 2 (weightTotal w) *
            fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s ∧
        (∑ m, (fairQdriftPick w j0
          (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) (ω m)).2.2) ≤
          fairQdriftSteps (weightTotal w) T s * L *
            fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) := by
  intro L D w j0 K t ε tq eq fuel htq heq hW hK hex
  set k0 : ℕ := scanPrecision fuel (epsCertified eq) with hk0
  have hk0cert : epsCertified eq k0 = true :=
    scanPrecision_certified fuel (epsCertified eq) hex
  have hpos : 0 < (epsBudget eq k0 : ℝ) := epsBudget_pos eq k0 hk0cert
  have hle : (epsBudget eq k0 : ℝ) ≤ ε := epsBudget_le ε eq heq k0
  have hscert : successCertified (epsBudget eq k0) (successLevel (epsBudget eq k0)) = true :=
    successLevel_certified (epsBudget eq k0) (by exact_mod_cast hpos)
  have hpay : (2 : ℝ)⁻¹ ^ successLevel (epsBudget eq k0) / 2 ≤ (epsBudget eq k0 : ℝ) :=
    successCertified_ge (epsBudget eq k0) _ hscert
  have hmain := fair_qdrift_computed_finite_diamond_and_ledgers L D
    (timeBound (tq k0) k0) (successLevel (epsBudget eq k0)) w j0 K t hW
    (timeBound_ge t tq htq k0) hK
  (try dsimp only at hmain)
  have hd := hmain.1
  have hled := hmain.2
  refine ⟨timeBound (tq k0) k0, successLevel (epsBudget eq k0), ?_, ?_, ?_, ?_⟩
  · exact timeBound_ge t tq htq k0
  · exact hpay.trans hle
  · refine ?_
    have h1 : ENNReal.ofReal ((2 : ℝ)⁻¹ ^ successLevel (epsBudget eq k0) / 2)
        ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (hpay.trans hle)
    exact hd.trans h1
  · intro ω
    exact hled ω

/-- Reliable bracket streams with a certified error budget yield time and precision bounds
giving fair-bit qDRIFT finite diamond distance at most `ε`. -/
theorem clause19_bracket_endpoint : ∀ (L D : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (K : Fin L → Operator D) (t ε : ℝ) (tlo thi elo ehi : ℕ → ℚ) (fuel : ℕ),
    RelBracketStream t tlo thi → RelBracketStream ε elo ehi →
    0 < weightTotal w → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    (∃ k, k ≤ fuel ∧ epsCertifiedBracket (elo k) (ehi k) k = true) →
    ∃ (T s : ℕ),
      |t| ≤ T ∧
      (2 : ℝ)⁻¹ ^ s / 2 ≤ ε ∧
      finiteDiamondDistance
          (fairQdriftActualMap w j0 (fairQdriftSteps (weightTotal w) T s)
            (fairQdriftFuel (fairQdriftSteps (weightTotal w) T s) s) K t)
          (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
        ≤ ENNReal.ofReal ε := by
  intro L D w j0 K t ε tlo thi elo ehi fuel ht heq hW hK hex
  set k0 : ℕ := scanPrecision fuel (fun k => epsCertifiedBracket (elo k) (ehi k) k) with hk0
  have hk0cert : epsCertifiedBracket (elo k0) (ehi k0) k0 = true :=
    scanPrecision_certified fuel (fun k => epsCertifiedBracket (elo k) (ehi k) k) hex
  have hpos : 0 < (epsBudgetBracket (elo k0) (ehi k0) k0 : ℝ) :=
    epsBudgetBracket_pos (elo k0) (ehi k0) k0 hk0cert
  have hle : (epsBudgetBracket (elo k0) (ehi k0) k0 : ℝ) ≤ ε := by
    obtain ⟨hbracket, _⟩ := heq k0
    exact epsBudgetBracket_le ε (elo k0) (ehi k0) hbracket k0
  have hscert : successCertified (epsBudgetBracket (elo k0) (ehi k0) k0)
      (successLevel (epsBudgetBracket (elo k0) (ehi k0) k0)) = true :=
    successLevel_certified (epsBudgetBracket (elo k0) (ehi k0) k0) (by exact_mod_cast hpos)
  have hpay : (2 : ℝ)⁻¹ ^ successLevel (epsBudgetBracket (elo k0) (ehi k0) k0) / 2
      ≤ (epsBudgetBracket (elo k0) (ehi k0) k0 : ℝ) :=
    successCertified_ge (epsBudgetBracket (elo k0) (ehi k0) k0) _ hscert
  have hT : |t| ≤ (bracketTimeBound (tlo k0) (thi k0) : ℕ) := by
    obtain ⟨hbracket, _⟩ := ht k0
    exact bracketTimeBound_ge t (tlo k0) (thi k0) hbracket
  have hmain := fair_qdrift_computed_finite_diamond_and_ledgers L D
    (bracketTimeBound (tlo k0) (thi k0))
    (successLevel (epsBudgetBracket (elo k0) (ehi k0) k0))
    w j0 K t hW hT hK
  (try dsimp only at hmain)
  have hd := hmain.1
  have hε : (2 : ℝ)⁻¹ ^ successLevel (epsBudgetBracket (elo k0) (ehi k0) k0) / 2 ≤ ε := by
    linarith
  refine ⟨bracketTimeBound (tlo k0) (thi k0),
    successLevel (epsBudgetBracket (elo k0) (ehi k0) k0), hT, hε, ?_⟩
  exact hd.trans (ENNReal.ofReal_le_ofReal hε)

/-- A certified allocation for a positive rational error budget uses at least `sourceTightCount
W T eQ` steps. -/
theorem tightCount_lower_bound (W T : ℕ) (eQ : ℚ) (R n : ℕ)
    (he : 0 < eQ) (h : tightCountCertified W T eQ R n = true) :
    sourceTightCount W T eQ ≤ n := by
  have hq : (0 : ℕ) < n ∧
      2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 * ((2 : ℚ) ^ R) + (n : ℚ) ^ 2
        ≤ eQ * (n : ℚ) * ((2 : ℚ) ^ R) := by
    simp only [tightCountCertified, decide_eq_true_eq] at h
    exact h
  have hn : (0 : ℚ) < (n : ℚ) := by exact_mod_cast hq.1
  have hposR : (0 : ℚ) < ((2 : ℚ) ^ R) := by positivity
  have h1 : 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 * ((2 : ℚ) ^ R)
      ≤ eQ * (n : ℚ) * ((2 : ℚ) ^ R) := by
    have h := le_trans (le_add_of_nonneg_right (by positivity :
      (0 : ℚ) ≤ (n : ℚ) ^ 2)) hq.2
    linarith
  have h2 : 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 ≤ eQ * (n : ℚ) := by
    have h' := (div_le_div_iff_of_pos_right hposR).mpr h1
    simpa using! h'
  have h3 : 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ ≤ (n : ℚ) := by
    apply (div_le_iff₀ he).mpr
    have : 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 ≤ (n : ℚ) * eQ := by
      linarith [h2]
    exact this
  unfold sourceTightCount
  exact Nat.ceil_le.mpr h3

/-- Every positive rational error budget has a certified allocation between `sourceTightCount W
T eQ` and `max 1 (ceil (4 * W² * T² / eQ))` steps. -/
theorem tightCount_achievable (W T : ℕ) (eQ : ℚ) (he : 0 < eQ) :
    ∃ (R n : ℕ),
      tightCountCertified W T eQ R n = true ∧
      sourceTightCount W T eQ ≤ n ∧
      n ≤ max 1 (Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ)) := by
  have htwo : ∀ n : ℕ, 2 ^ n ≥ n + 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc 2 ^ (n + 1) = 2 ^ n * 2 := by rw [pow_succ]
        _ ≥ (n + 1) * 2 := Nat.mul_le_mul_right 2 ih
        _ ≥ n + 2 := by omega
  set n0 : ℕ := max 1 (Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ)) with hn0
  set R : ℕ := Nat.ceil (2 * (n0 : ℚ) / eQ) with hR
  refine ⟨R, n0, ?_, ?_, ?_⟩
  · have hne : eQ ≠ 0 := ne_of_gt he
    have hn0N : (0 : ℕ) < n0 := by
      rw [hn0]
      exact lt_of_lt_of_le (Nat.zero_lt_succ 0) (le_max_left _ _)
    have hn0pos : (0 : ℚ) < (n0 : ℚ) := by exact_mod_cast hn0N
    have hceil : (2 * (n0 : ℚ) / eQ : ℚ) ≤ (R : ℚ) := by
      have h := Nat.le_ceil (2 * (n0 : ℚ) / eQ)
      rw [hR]
      exact_mod_cast h
    have hge : (2 : ℚ) ^ R ≥ 2 * (n0 : ℚ) / eQ := by
      have h := htwo R
      have hR' : (R : ℚ) + 1 ≤ (2 : ℚ) ^ R := by exact_mod_cast h
      linarith
    have hle : (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ : ℚ) ≤ (n0 : ℚ) := by
      have hceil : (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ : ℚ)
          ≤ ((Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) : ℕ) : ℚ) := by
        exact_mod_cast (Nat.le_ceil _)
      have hmax : ((Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) : ℕ) : ℚ)
          ≤ (n0 : ℚ) := by
        rw [hn0]
        exact_mod_cast (le_max_right _ _)
      exact hceil.trans hmax
    have hP : (0 : ℚ) ≤ ((2 : ℚ) ^ R) := by positivity
    have hN : (0 : ℚ) ≤ (n0 : ℚ) := by positivity
    have hmul : 4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 ≤ (n0 : ℚ) * eQ := by
      have h1 := mul_le_mul_of_nonneg_right hle (le_of_lt he)
      have h1' : (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) * eQ ≤ (n0 : ℚ) * eQ := h1
      have h2 : (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) * eQ
          = 4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 := by field_simp
      rw [h2] at h1'
      exact h1'
    have hmul' : 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 ≤ ((n0 : ℚ) * eQ) / 2 := by
      have h := (div_le_div_iff_of_pos_right (by norm_num : (0 : ℚ) < 2)).mpr hmul
      convert! h using 1 <;> ring
    have hfuel : eQ * ((2 : ℚ) ^ R) ≥ 2 * (n0 : ℚ) := by
      have hmul := mul_le_mul_of_nonneg_right hge (le_of_lt he)
      have hmul' : (2 * (n0 : ℚ) / eQ) * eQ = 2 * (n0 : ℚ) := by field_simp
      rw [hmul'] at hmul
      linarith
    have hA : 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 * ((2 : ℚ) ^ R)
        ≤ (eQ * (n0 : ℚ) * ((2 : ℚ) ^ R)) / 2 := by
      have h := mul_le_mul_of_nonneg_right hmul' hP
      convert! h using 1 <;> ring
    have hB : (n0 : ℚ) ^ 2 ≤ (eQ * ((2 : ℚ) ^ R) * (n0 : ℚ)) / 2 := by
      have h := mul_le_mul_of_nonneg_right hfuel hN
      have h3 : (0 : ℚ) ≤ (n0 : ℚ) ^ 2 := by positivity
      linarith
    simp only [tightCountCertified, decide_eq_true_eq]
    refine ⟨hn0N, ?_⟩
    linarith
  · have hmono : (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ : ℚ)
        ≤ (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ : ℚ) := by
      have h1 : 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 ≤ 4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 := by
        nlinarith [show (0 : ℚ) ≤ 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 by positivity]
      have h2 := mul_le_mul_of_nonneg_right h1 (le_of_lt he)
      have h2' : 2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 ≤ 4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 :=
        le_of_mul_le_mul_right h2 (by positivity : (0 : ℚ) < eQ)
      exact (div_le_div_iff_of_pos_right he).mpr h2'
    unfold sourceTightCount
    have h1 : (Nat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) : ℕ)
        ≤ Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) := by
      apply Nat.ceil_le.mpr
      exact hmono.trans (Nat.le_ceil _)
    have h2 : (Nat.ceil (2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ) : ℕ)
        ≤ max 1 (Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ)) :=
      h1.trans (le_max_right _ _)
    rw [hn0]
    exact h2
  · exact le_rfl

/-- A certified allocation satisfies the real combined-error bound `2 * W² * T² / n + n * 2⁻ᴿ ≤
eQ`. -/
theorem tightCount_real_budget (W T : ℕ) (eQ : ℚ) (R n : ℕ)
    (h : tightCountCertified W T eQ R n = true) :
    2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) + (n : ℝ) * ((2 : ℝ)⁻¹) ^ R ≤ (eQ : ℝ) := by
  have hq : (0 : ℕ) < n ∧
      2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 * ((2 : ℚ) ^ R) + (n : ℚ) ^ 2
        ≤ eQ * (n : ℚ) * ((2 : ℚ) ^ R) := by
    simp only [tightCountCertified, decide_eq_true_eq] at h
    exact h
  have hnN : (0 : ℕ) < n := hq.1
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hnN
  have h1 : 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((2 : ℝ) ^ R) + (n : ℝ) ^ 2
      ≤ (eQ : ℝ) * (n : ℝ) * ((2 : ℝ) ^ R) := by
    have h2 : ((2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 * ((2 : ℚ) ^ R) + (n : ℚ) ^ 2 : ℚ) : ℝ)
        ≤ ((eQ * (n : ℚ) * ((2 : ℚ) ^ R) : ℚ) : ℝ) := by
      exact_mod_cast hq.2
    have h3 : ((2 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 * ((2 : ℚ) ^ R) + (n : ℚ) ^ 2 : ℚ) : ℝ)
        = 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((2 : ℝ) ^ R) + (n : ℝ) ^ 2 := by
      push_cast
      ring
    have h4 : ((eQ * (n : ℚ) * ((2 : ℚ) ^ R) : ℚ) : ℝ)
        = (eQ : ℝ) * (n : ℝ) * ((2 : ℝ) ^ R) := by
      push_cast
      ring
    rw [h3, h4] at h2
    exact h2
  have hsum : 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) + (n : ℝ) / ((2 : ℝ) ^ R)
      ≤ (eQ : ℝ) := by
    have hNP : (0 : ℝ) < (n : ℝ) * ((2 : ℝ) ^ R) := by positivity
    have h1' : 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((2 : ℝ) ^ R) + (n : ℝ) ^ 2
        ≤ (eQ : ℝ) * ((n : ℝ) * ((2 : ℝ) ^ R)) := by
      convert! h1 using 1 <;> ring
    have h2 := (div_le_iff₀ hNP).mpr h1'
    have heq : (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 * ((2 : ℝ) ^ R) + (n : ℝ) ^ 2)
        / ((n : ℝ) * ((2 : ℝ) ^ R))
        = 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) + (n : ℝ) / ((2 : ℝ) ^ R) := by
      field_simp
    rw [heq] at h2
    exact h2
  have h8 : (n : ℝ) / ((2 : ℝ) ^ R) = (n : ℝ) * ((2 : ℝ)⁻¹) ^ R := by
    rw [div_eq_mul_inv, ← inv_pow]
  rw [h8] at hsum
  exact hsum

/-- An allocation whose combined simulation and sampling bound is at most `eQ` gives fair-bit
qDRIFT finite diamond distance at most `eQ` for weighted Hermitian contractions and bounded
time. -/
theorem tight_allocation_endpoint : ∀ (L D : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (K : Fin L → Operator D) (t : ℝ) (T : ℕ) (eQ : ℝ) (R n : ℕ),
    0 < weightTotal w → |t| ≤ T → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    0 < n →
    2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) + (n : ℝ) * ((2 : ℝ)⁻¹) ^ R ≤ eQ →
    finiteDiamondDistance (fairQdriftActualMap w j0 n R K t)
      (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
      ≤ ENNReal.ofReal eQ := by
  intro L D w j0 K t T eQ R n hW ht hK hn hbudget
  have hmain := fair_qdrift_actual_finite_diamond_output L D n R w j0 K t hn hK
  obtain ⟨hraw, hdist, _⟩ := hmain
  have hbound : 2 * (weightTotal w : ℝ) ^ 2 * t ^ 2 / (n : ℝ)
      + (n : ℝ) * ((2 : ℝ)⁻¹) ^ R ≤ eQ := by
    have hT : t ^ 2 ≤ (T : ℝ) ^ 2 := by
      have := abs_le.1 (by simpa using! ht)
      nlinarith
    have hmono : 2 * (weightTotal w : ℝ) ^ 2 * t ^ 2 / (n : ℝ)
        ≤ 2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) := by
      have hc : (0 : ℝ) ≤ 2 * (weightTotal w : ℝ) ^ 2 * (1 / (n : ℝ)) := by
        have h1 : (0 : ℝ) ≤ (weightTotal w : ℝ) ^ 2 := by positivity
        have h2 : (0 : ℝ) ≤ 1 / (n : ℝ) := by positivity
        exact mul_nonneg (mul_nonneg (by norm_num) h1) h2
      have h3 := mul_le_mul_of_nonneg_left hT hc
      convert! h3 using 1 <;> ring
    linarith
  refine ?_
  have h1 : ENNReal.ofReal (2 * (weightTotal w : ℝ) ^ 2 * t ^ 2 / (n : ℝ)
      + (n : ℝ) * ((2 : ℝ)⁻¹) ^ R) ≤ ENNReal.ofReal eQ :=
    ENNReal.ofReal_le_ofReal hbound
  exact hdist.trans h1

/-- The indexed control-block map has zero cross block for every input matrix. -/
theorem ctrlBlockMapIdx_cross_zero {D : ℕ} (Λ : Operator D →ₗ[ℂ] Operator D)
    (M : Matrix (Fin 2 × Fin D) (Fin 2 × Fin D) ℂ) :
    ctrlCrossBlock (ctrlBlockMapIdx Λ M) = 0 := by
  ext i j
  simp [ctrlCrossBlock, ctrlBlockMapIdx]

/-- The coherent witness has the constant cross block with entry equal to the fourth power of `1
/ sqrt 2`, viewed in the complexes. -/
theorem ctrlCrossBlock_coherent :
    ctrlCrossBlock coherentWitness
      = Matrix.of fun _ _ => (Complex.ofReal ((Real.sqrt 2)⁻¹)) ^ 4 := by
  ext i j
  simp [ctrlCrossBlock, coherentWitness]

/-- The indexed control-block map annihilates the coherent witness's cross block, although that
witness's original cross block is nonzero. -/
theorem no_free_lunch_endpoint (Λ : Operator 2 →ₗ[ℂ] Operator 2) :
    ctrlCrossBlock (ctrlBlockMapIdx Λ coherentWitness) = 0 ∧
    ctrlCrossBlock coherentWitness ≠ 0 := by
  refine ⟨ctrlBlockMapIdx_cross_zero Λ coherentWitness, ?_⟩
  intro h
  have hh := congrFun (congrFun h 0) 0
  simp [ctrlCrossBlock, coherentWitness] at hh

/-- For positive step count and error, the qDRIFT error inequality is equivalent to the
corresponding natural-number ceiling lower bound on the step count. -/
theorem tableQdriftCount_minimal (lam t eps : ℝ) (n : ℕ) (hn : 0 < n) (heps : 0 < eps) :
    (2 * lam ^ 2 * t ^ 2 / (n : ℝ) ≤ eps) ↔
      Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps) ≤ n := by
  have hne : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hceil : (Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps) : ℝ) ≥ 2 * lam ^ 2 * t ^ 2 / eps := by
    exact Nat.le_ceil _
  constructor
  · intro h
    have h2 : 2 * lam ^ 2 * t ^ 2 ≤ eps * (n : ℝ) := by
      exact (div_le_iff₀ hne).mp h
    have h3 : 2 * lam ^ 2 * t ^ 2 / eps ≤ (n : ℝ) := by
      apply (div_le_iff₀ heps).mpr
      linarith [h2]
    exact Nat.ceil_le.mpr h3
  · intro h
    have h2 : 2 * lam ^ 2 * t ^ 2 / eps ≤ (n : ℝ) := by
      have h' := Nat.ceil_le.mp h
      exact_mod_cast h'
    have h3 : 2 * lam ^ 2 * t ^ 2 ≤ eps * (n : ℝ) := by
      have h' := (div_le_iff₀ heps).mp h2
      simpa [mul_comm] using! h'
    exact (div_le_iff₀ hne).mpr h3

/-- The phase-estimation query-step budget makes `2 * lam² * peTimes j²` at most the allocated
error share times the step count. -/
theorem pe_query_accuracy (lam deltaE pf : ℝ) (j : ℕ)
    (hshare : 0 < peErrorShare deltaE pf j) :
    2 * lam ^ 2 * (peTimes j) ^ 2
      ≤ peErrorShare deltaE pf j * (peQuerySteps lam deltaE pf j : ℝ) := by
  have hceil : 2 * lam ^ 2 * (peTimes j) ^ 2 / peErrorShare deltaE pf j
      ≤ (Nat.ceil (2 * lam ^ 2 * (peTimes j) ^ 2 / peErrorShare deltaE pf j) : ℝ) := by
    exact Nat.le_ceil (2 * lam ^ 2 * (peTimes j) ^ 2 / peErrorShare deltaE pf j : ℝ)
  have hstep : (peQuerySteps lam deltaE pf j : ℝ)
      ≥ Nat.ceil (2 * lam ^ 2 * (peTimes j) ^ 2 / peErrorShare deltaE pf j) := by
    unfold peQuerySteps
    have h : Nat.ceil (2 * lam ^ 2 * (peTimes j) ^ 2 / peErrorShare deltaE pf j)
        ≤ max 1 (Nat.ceil (2 * lam ^ 2 * (peTimes j) ^ 2 / peErrorShare deltaE pf j)) :=
      le_max_right _ _
    exact_mod_cast h
  have hdiv : 2 * lam ^ 2 * (peTimes j) ^ 2
      ≤ peErrorShare deltaE pf j
        * (Nat.ceil (2 * lam ^ 2 * (peTimes j) ^ 2 / peErrorShare deltaE pf j) : ℝ) := by
    have h := (div_le_iff₀ hshare).mp hceil
    simpa [mul_comm] using! h
  exact hdiv.trans (mul_le_mul_of_nonneg_left hstep (le_of_lt hshare))

/-- The sampler's exhaustion report is true exactly when its raw run ends in an exhaustion
state. -/
theorem fairQdriftPickReport_exhausted {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (hW : 0 < weightTotal w) (ω : Fin R → Reg (Nat.clog 2 (weightTotal w))) :
    fairQdriftPickReport w j0 R ω = true ↔
      ∃ BD : ℕ × ℕ,
        (fairQdriftRawRun w (Nat.clog 2 (weightTotal w)) R ω (.inr (0, 0))).1 = .inr BD := by
  unfold fairQdriftPickReport
  rw [if_neg (ne_of_gt hW)]
  cases hcfg : (fairQdriftRawRun w (Nat.clog 2 (weightTotal w)) R ω (.inr (0, 0))).1 with
  | inl out => simp [fairQdriftExhausted, hcfg]
  | inr BD => simp [fairQdriftExhausted, hcfg]

/-- When the fair-bit sampler reports exhaustion, its selected label is the fallback label. -/
theorem fairQdriftPick_exhausted_is_fallback {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (hW : 0 < weightTotal w) (ω : Fin R → Reg (Nat.clog 2 (weightTotal w)))
    (hex : fairQdriftPickReport w j0 R ω = true) :
    (fairQdriftPick w j0 R ω).1 = j0 := by
  rw [fairQdriftPick, if_neg (ne_of_gt hW)]
  cases hcfg : (fairQdriftRawRun w (Nat.clog 2 (weightTotal w)) R ω (.inr (0, 0))).1 with
  | inl out =>
    have hfalse : fairQdriftPickReport w j0 R ω = false := by
      simp [fairQdriftPickReport, fairQdriftExhausted, hcfg, ne_of_gt hW]
    rw [hfalse] at hex
    simp at hex
  | inr BD =>
    simp [fairQdriftFallback, hcfg]

/-- The capped sampling law decomposes into the clean probability times the importance law plus
the exhaustion probability concentrated at the fallback label. -/
theorem fairQdriftLaw_exhaust_split {L : ℕ} (w : Fin L → ℕ) (j0 : Fin L) (R : ℕ)
    (hW : 0 < weightTotal w) (j : Fin L) :
    (fairQdriftLaw w j0 R).prob j =
      fairBitCleanProb w R * (fairQdriftImportanceLaw w hW).prob j +
      fairBitExhaustProb w R * (if j = j0 then 1 else 0) := by
  have h := fair_bit_qdrift_actual_sampler_law L R w j0 hW j
  dsimp only [fairBitCleanProb, fairBitExhaustProb, fairQdriftImportanceLaw]
  rw [h]
  ring

/-- With positive total weight and at least one rejection round, the clean sampling probability
lies between one half and one. -/
theorem fairBitCleanProb_bounds {L : ℕ} (w : Fin L → ℕ) (hW : 0 < weightTotal w)
    (R : ℕ) (hR : 1 ≤ R) :
    1 / 2 ≤ fairBitCleanProb w R ∧ fairBitCleanProb w R ≤ 1 := by
  have hq := fairQdriftReject_real w hW
  have hq0 : 0 ≤ 1 - (weightTotal w : ℝ) / (2 ^ (Nat.clog 2 (weightTotal w)) : ℝ) := hq.2.1
  have hq1 : 1 - (weightTotal w : ℝ) / (2 ^ (Nat.clog 2 (weightTotal w)) : ℝ) ≤ 1 / 2 := hq.2.2
  have hp : (1 - (weightTotal w : ℝ) / (2 ^ (Nat.clog 2 (weightTotal w)) : ℝ)) ^ R
      ≤ (1 / 2 : ℝ) ^ R := pow_le_pow_left₀ hq0 hq1 R
  have hp1 : (1 / 2 : ℝ) ^ R ≤ 1 / 2 := by
    have hsucc : (1 / 2 : ℝ) ^ (R - 1 + 1) = (1 / 2) ^ (R - 1) * (1 / 2) := pow_succ _ _
    calc (1 / 2 : ℝ) ^ R = (1 / 2) ^ (R - 1 + 1) := by congr 1; omega
      _ = (1 / 2) ^ (R - 1) * (1 / 2) := hsucc
      _ ≤ 1 * (1 / 2) := by
        exact mul_le_mul_of_nonneg_right (pow_le_one₀ (by norm_num) (by norm_num)) (by norm_num)
      _ = 1 / 2 := by ring
  have hclean : fairBitCleanProb w R
      = 1 - (1 - (weightTotal w : ℝ) / (2 ^ (Nat.clog 2 (weightTotal w)) : ℝ)) ^ R := rfl
  have hexh : (1 - (weightTotal w : ℝ) / (2 ^ (Nat.clog 2 (weightTotal w)) : ℝ)) ^ R ≤ 1 / 2 :=
    hp.trans hp1
  have hexn : 0 ≤ (1 - (weightTotal w : ℝ) / (2 ^ (Nat.clog 2 (weightTotal w)) : ℝ)) ^ R :=
    pow_nonneg hq0 R
  refine ⟨?_, ?_⟩
  · rw [hclean]
    have h := sub_le_sub_left hexh 1
    linarith
  · rw [hclean]
    have h := sub_le_sub_left hexn 0
    simpa using! h

/-- With at least one rejection round, the `n`-step postselection success mass lies between
`2⁻ⁿ` and one. -/
theorem postSelect_success_mass_bounds {L : ℕ} (w : Fin L → ℕ) (hW : 0 < weightTotal w)
    (R n : ℕ) (hR : 1 ≤ R) :
    (1 / 2) ^ n ≤ postSelectSuccessMass w R n ∧ postSelectSuccessMass w R n ≤ 1 := by
  have h := fairBitCleanProb_bounds w hW R hR
  unfold postSelectSuccessMass
  refine ⟨?_, ?_⟩
  · exact pow_le_pow_left₀ (by norm_num) h.1 n
  · exact pow_le_one₀ (le_trans (by norm_num) h.1) h.2

/-- The Hamiltonian associated with the weight-based importance law and total-weight scale
equals the weighted sum of its terms. -/
theorem importance_hamiltonian {L D : ℕ} (w : Fin L → ℕ) (hW : 0 < weightTotal w)
    (K : Fin L → Operator D) :
    qdriftHamiltonian (fairQdriftImportanceLaw w hW) K (weightTotal w : ℝ) =
      ∑ j, (w j : ℂ) • K j := by
  unfold qdriftHamiltonian
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_smul, fairQdriftImportanceLaw, Complex.ofReal_div, Complex.ofReal_natCast]
  rw [mul_div_cancel₀ _ (by exact_mod_cast (ne_of_gt hW))]

/-- For weighted Hermitian contractions and a positive step count, the postselected qDRIFT map
is within `postSelectDiamondBudget w n t` of the target in finite diamond distance. -/
theorem postSelected_diamond_budget {L D : ℕ} (w : Fin L → ℕ) (n : ℕ)
    (K : Fin L → Operator D) (t : ℝ) (hW : 0 < weightTotal w) (hn : 0 < n)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    finiteDiamondDistance (postSelectedQdriftMap w hW n K t)
      (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
      ≤ ENNReal.ofReal (postSelectDiamondBudget w n t) := by
  have h := (exact_qdrift_actual_finite_diamond_budget L D (fairQdriftImportanceLaw w hW) K
    (weightTotal w : ℝ) t n (by positivity) hn hK).1
  rw [importance_hamiltonian] at h
  unfold postSelectedQdriftMap
  simpa [postSelectDiamondBudget] using! h

/-- The capped and exact-importance one-step reference mixtures differ in trace norm by at most
`2 * 2⁻ᴿ * traceNorm X`. -/
private theorem postSelect_one_step_sampling_error {L D : ℕ} (w : Fin L → ℕ)
    (j0 : Fin L) (R : ℕ) (hW : 0 < weightTotal w) (U : Fin L → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (r : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixture (fairQdriftLaw w j0 R) U r X -
      referenceMixture (fairQdriftImportanceLaw w hW) U r X) ≤
      2 * ((2 : ℝ)⁻¹)^R * Matrix.traceNorm X := by
  let q := 1 - (weightTotal w : ℝ)/(2^Nat.clog 2 (weightTotal w) : ℝ)
  let a := q^R
  let d := fairQdriftImportanceLaw w hW
  let A := TensorGate (U j0) (1 : Operator r) * X * (TensorGate (U j0) (1 : Operator r))ᴴ
  let B := referenceMixture d U r X
  have hq := fairQdriftReject_real w hW
  have ha : 0 ≤ a := pow_nonneg hq.2.1 R
  have hab : a ≤ ((2 : ℝ)⁻¹)^R := by
    exact pow_le_pow_left₀ hq.2.1 (by simpa using! hq.2.2) R
  have hl (j : Fin L) : (fairQdriftLaw w j0 R).prob j =
      (1-a)*d.prob j + (if j=j0 then a else 0) := by
    rw [fair_bit_qdrift_actual_sampler_law L R w j0 hW j]
    dsimp [d, fairQdriftImportanceLaw, a, q]
    split_ifs <;> ring
  have hm : referenceMixture (fairQdriftLaw w j0 R) U r X =
      ((1-a : ℝ) : ℂ) • B + (a : ℂ) • A := by
    rw [referenceMixture_apply]
    simp_rw [hl, Complex.ofReal_add, Complex.ofReal_mul, add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum]
    congr 1
    simp [A]
  have hs : referenceMixture (fairQdriftLaw w j0 R) U r X - B = (a : ℂ) • (A-B) := by
    rw [hm, Complex.ofReal_sub, Complex.ofReal_one, sub_smul, one_smul, smul_sub]
    abel
  rw [hs, Matrix.traceNorm_smul]
  simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have hA : Matrix.traceNorm A = Matrix.traceNorm X :=
      finite_reference_unitary_traceNorm _ r X (hU j0)
  have hB : Matrix.traceNorm B ≤ Matrix.traceNorm X :=
      finite_reference_mixture_contraction d U r X hU
  have ht : Matrix.traceNorm (A-B) ≤ 2*Matrix.traceNorm X := by
    calc
      Matrix.traceNorm (A-B) ≤ Matrix.traceNorm A + Matrix.traceNorm B := by
        simpa only [sub_eq_add_neg, Matrix.traceNorm_neg] using! Matrix.traceNorm_add_le A (-B)
      _ ≤ _ := by rw [hA]; linarith
  calc a * Matrix.traceNorm (A-B) ≤ a*(2*Matrix.traceNorm X) := mul_le_mul_of_nonneg_left ht ha
    _ ≤ ((2 : ℝ)⁻¹)^R*(2*Matrix.traceNorm X) :=
      mul_le_mul_of_nonneg_right hab (mul_nonneg (by norm_num) (Matrix.traceNorm_nonneg X))
    _ = _ := by ring

/-- The capped and exact-importance `n`-step reference mixtures differ in trace norm by at most
`2 * n * 2⁻ᴿ * traceNorm X`. -/
private theorem postSelect_iterated_sampling_error {L D : ℕ} (w : Fin L → ℕ)
    (j0 : Fin L) (R : ℕ) (hW : 0 < weightTotal w) (U : Fin L → Operator D)
    (hU : ∀ j, U j ∈ Matrix.unitaryGroup (Fin D) ℂ) (r n : ℕ)
    (X : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ) :
    Matrix.traceNorm (referenceMixturePower (fairQdriftLaw w j0 R) U r n X -
      referenceMixturePower (fairQdriftImportanceLaw w hW) U r n X) ≤
      2*n*((2 : ℝ)⁻¹)^R*Matrix.traceNorm X := by
  let e := fairQdriftLaw w j0 R
  let d := fairQdriftImportanceLaw w hW
  induction n with
  | zero => simp [referenceMixturePower]
  | succ n ih =>
    let A := referenceMixturePower e U r n X
    let B := referenceMixturePower d U r n X
    have he : referenceMixturePower e U r (n+1) X = referenceMixture e U r A :=
      Function.iterate_succ_apply' _ n X
    have hd : referenceMixturePower d U r (n+1) X = referenceMixture d U r B :=
      Function.iterate_succ_apply' _ n X
    have hs : referenceMixture e U r A - referenceMixture d U r B =
        referenceMixture e U r (A-B) + (referenceMixture e U r B - referenceMixture d U r B) := by
      rw [referenceMixture_sub]
      abel
    change Matrix.traceNorm
        (referenceMixturePower e U r (n+1) X - referenceMixturePower d U r (n+1) X) ≤ _
    rw [he, hd, hs]
    have h1 := (finite_reference_mixture_contraction e U r (A-B) hU).trans ih
    have h2 := postSelect_one_step_sampling_error w j0 R hW U hU r B
    have hB := referenceMixturePower_contraction d U r n X hU
    have h2' := h2.trans (mul_le_mul_of_nonneg_left hB (by positivity))
    exact ((Matrix.traceNorm_add_le _ _).trans (add_le_add h1 h2')).trans_eq (by push_cast; ring)

/-- The capped fair-bit qDRIFT map and the postselected importance-sampling map have finite
diamond distance at most `n * 2⁻ᴿ`. -/
theorem postSelect_vs_capped_sampling_bound {L D : ℕ} (w : Fin L → ℕ) (j0 : Fin L)
    (n R : ℕ) (K : Fin L → Operator D) (t : ℝ) (hW : 0 < weightTotal w) (hn : 0 < n)
    (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) :
    finiteDiamondDistance (fairQdriftActualMap w j0 n R K t)
      (postSelectedQdriftMap w hW n K t) ≤ ENNReal.ofReal (n * ((2 : ℝ)⁻¹)^R) := by
  have h := finiteDiamondDistance_le_of_uniform
    (fairQdriftActualMap w j0 n R K t) (postSelectedQdriftMap w hW n K t)
    (2 * (n : ℝ) * ((2 : ℝ)⁻¹)^R) (by positivity) (by
      intro r X
      rw [fairQdriftActualMap, if_neg (ne_of_gt hW), postSelectedQdriftMap, exactQdriftMap,
        tensorLeft_mixturePowerMap, tensorLeft_mixturePowerMap]
      exact postSelect_iterated_sampling_error w j0 R hW
        (fun j => HamiltonianEvolution (K j) (t*(weightTotal w : ℝ)/(n : ℝ)))
        (fun j => hamiltonianEvolution_unitary (hK j).1 _) r n X)
  have h2 : ENNReal.ofReal ((2 * (n : ℝ) * ((2 : ℝ)⁻¹)^R) / 2)
      = ENNReal.ofReal (n * ((2 : ℝ)⁻¹)^R) := by
    congr 1
    ring
  rw [h2] at h
  exact h

/-- The stated ceiling lower bound on a positive step count ensures postselected qDRIFT finite
diamond distance at most `eQ` for bounded time and weighted Hermitian contractions. -/
theorem postSelected_source_tight_count {L D : ℕ} (w : Fin L → ℕ)
    (K : Fin L → Operator D) (t : ℝ) (T : ℕ) (eQ : ℝ) (n : ℕ)
    (hW : 0 < weightTotal w) (ht : |t| ≤ T) (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (hn : 0 < n) (he : 0 < eQ)
    (hceil : Nat.ceil (2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ) ≤ n) :
    finiteDiamondDistance (postSelectedQdriftMap w hW n K t)
      (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
      ≤ ENNReal.ofReal eQ := by
  have hbud := postSelected_diamond_budget w n K t hW hn hK
  have hT : t ^ 2 ≤ (T : ℝ) ^ 2 := by
    have := mul_self_le_mul_self (abs_nonneg t) ht
    simpa only [← sq, sq_abs] using! this
  have hX : 2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ ≤ (n : ℝ) := by
    have h1 : 2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ
        ≤ (Nat.ceil (2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hceil
    linarith
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmain : 2 * (weightTotal w : ℝ) ^ 2 * t ^ 2 / (n : ℝ) ≤ eQ := by
    rw [div_le_iff₀ hnR]
    have h1 : 2 * (weightTotal w : ℝ) ^ 2 * t ^ 2 ≤ 2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 := by
      have hc : (0 : ℝ) ≤ 2 * (weightTotal w : ℝ) ^ 2 := by positivity
      have h3 := mul_le_mul_of_nonneg_left hT hc
      convert! h3 using 1
    have h2 : 2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 ≤ (n : ℝ) * eQ := by
      have h3 := (div_le_iff₀ he).mp hX
      linarith
    linarith
  have h1 : ENNReal.ofReal (postSelectDiamondBudget w n t) ≤ ENNReal.ofReal eQ :=
    ENNReal.ofReal_le_ofReal hmain
  exact hbud.trans h1

/-- For positive time bound and error budget, some positive step count gives postselected qDRIFT
finite diamond distance at most the requested error. -/
theorem postSelected_source_tight_count_achievable {L D : ℕ} (w : Fin L → ℕ)
    (K : Fin L → Operator D) (t : ℝ) (T : ℕ) (eQ : ℝ)
    (hW : 0 < weightTotal w) (ht : |t| ≤ T) (hK : ∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1)
    (hT : 0 < T) (he : 0 < eQ) :
    ∃ n : ℕ, 0 < n ∧
      finiteDiamondDistance (postSelectedQdriftMap w hW n K t)
        (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
        ≤ ENNReal.ofReal eQ := by
  have hX : 0 < 2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ := by positivity
  have hceil := Nat.le_ceil (2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ)
  have hpos : 0 < Nat.ceil (2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ) := by
    exact_mod_cast (lt_of_lt_of_le hX hceil)
  refine ⟨Nat.ceil (2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ), hpos, ?_⟩
  exact postSelected_source_tight_count w K t T eQ
    (Nat.ceil (2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ)) hW ht hK hpos he le_rfl

/-- A self-adjoint idempotent matrix has operator norm at most one. -/
theorem projection_opNorm_le_one {D : ℕ} (P : Operator D)
    (hP : Pᴴ = P) (hPP : P * P = P) : ‖P‖ ≤ 1 := by
  have h := Matrix.l2_opNorm_conjTranspose_mul_self (𝕜 := ℂ) P
  rw [hP, hPP] at h
  have hfac : ‖P‖ * (‖P‖ - 1) = 0 := by linarith
  rcases mul_eq_zero.mp hfac with hz | hz
  · have hz' : ‖P‖ = 0 := by linarith
    simp [hz']
  · have hz' : ‖P‖ = 1 := by linarith
    simp [hz']

/-- Sandwiching a matrix between a self-adjoint projection cannot increase its trace norm. -/
theorem projection_sandwich_traceNorm_le {D : ℕ} (P M : Operator D)
    (hP : Pᴴ = P) (hPP : P * P = P) :
    Matrix.traceNorm (P * M * P) ≤ Matrix.traceNorm M :=
  Matrix.traceNorm_sandwich_le (hS := projection_opNorm_le_one P hP hPP)
    (hT := projection_opNorm_le_one P hP hPP)

/-- The difference of selective masses for a common projection and input is bounded by the trace
norm of the two maps' output difference. -/
theorem selectiveMass_diff_le {D : ℕ} (Φ Ψ : Operator D →ₗ[ℂ] Operator D)
    (P X : Operator D) (hP : Pᴴ = P) (hPP : P * P = P) :
    |selectiveMass Φ P X - selectiveMass Ψ P X| ≤ Matrix.traceNorm ((Φ - Ψ) X) := by
  have hsub : (Φ - Ψ) X = Φ X - Ψ X := rfl
  have hmat : P * Φ X * P - P * Ψ X * P = P * (Φ - Ψ) X * P := by
    rw [hsub, Matrix.mul_sub, Matrix.sub_mul]
  have htr : Matrix.trace (selectiveOutput Φ P X) - Matrix.trace (selectiveOutput Ψ P X)
      = Matrix.trace (P * (Φ - Ψ) X * P) := by
    unfold selectiveOutput
    rw [← Matrix.trace_sub, hmat]
  have hre : (Matrix.trace (selectiveOutput Φ P X)).re
      - (Matrix.trace (selectiveOutput Ψ P X)).re
      = (Matrix.trace (P * (Φ - Ψ) X * P)).re := by
    have h := congrArg Complex.re htr
    simpa only [Complex.sub_re] using! h
  unfold selectiveMass
  rw [hre]
  calc |(Matrix.trace (P * (Φ - Ψ) X * P)).re|
      ≤ ‖Matrix.trace (P * (Φ - Ψ) X * P)‖ := Complex.abs_re_le_norm _
    _ ≤ Matrix.traceNorm (P * (Φ - Ψ) X * P) := Matrix.abs_trace_le_traceNorm _
    _ ≤ Matrix.traceNorm ((Φ - Ψ) X) :=
      projection_sandwich_traceNorm_le P _ hP hPP

/-- Every element of `Fin D × Fin 1` equals its first coordinate paired with zero. -/
theorem finProdOne_eta (D : ℕ) (p : Fin D × Fin 1) : p = (p.1, 0) := by
  have h2 : p.2 = 0 := Subsingleton.elim p.2 0
  exact Prod.ext rfl h2

/-- Two elements of `Fin D × Fin 1` are equal exactly when their first coordinates are equal. -/
theorem finProdOne_ext_iff (D : ℕ) (p q : Fin D × Fin 1) : p = q ↔ p.1 = q.1 := by
  constructor
  · intro h
    exact congrArg Prod.fst h
  · intro h
    have h2 : p.2 = q.2 := Subsingleton.elim p.2 q.2
    exact Prod.ext h h2

/-- The matrix identifying a system basis with its product with the one-element basis, with
entry one when the system labels coincide and zero otherwise. -/
noncomputable def prodOneEmbedding (D : ℕ) : Matrix (Fin D) (Fin D × Fin 1) ℂ :=
  Matrix.of fun i p => if i = p.1 then 1 else 0

/-- An entry of `prodOneEmbedding` is one exactly when the system label matches the first
product coordinate. -/
theorem prodOneEmbedding_apply (D : ℕ) (i : Fin D) (p : Fin D × Fin 1) :
    prodOneEmbedding D i p = if i = p.1 then 1 else 0 := by
  rw [prodOneEmbedding, Matrix.of_apply]

/-- The conjugate-transpose entries of `prodOneEmbedding` are the same zero-one label-matching
indicators. -/
theorem prodOneEmbedding_conjTranspose_apply (D : ℕ) (p : Fin D × Fin 1) (i : Fin D) :
    (prodOneEmbedding D)ᴴ p i = if i = p.1 then 1 else 0 := by
  rw [Matrix.conjTranspose_apply]
  by_cases h : i = p.1
  · simp [h, prodOneEmbedding_apply]
  · simp [h, prodOneEmbedding_apply]

/-- The singleton-reference identification matrix is an isometry. -/
theorem prodOneEmbedding_isometry (D : ℕ) : (prodOneEmbedding D).Isometry := by
  rw [Matrix.Isometry]
  ext p q
  rw [Matrix.mul_apply]
  simp only [prodOneEmbedding_apply, prodOneEmbedding_conjTranspose_apply, Matrix.one_apply]
  by_cases h : p.1 = q.1
  · have hpq : p = q := (finProdOne_ext_iff D p q).mpr h
    subst hpq
    rw [Finset.sum_eq_single p.1]
    · simp [h]
    · intro i _ hi
      have hne : i ≠ p.1 := fun hc => hi hc
      simp [hne]
    · simp
  · have hpq : ¬(p = q) := fun hc => h ((finProdOne_ext_iff D p q).mp hc)
    have h' : ¬(q = p) := fun hc => h ((finProdOne_ext_iff D p q).mp hc.symm)
    rw [Finset.sum_eq_single p.1]
    · simp [h, hpq]
    · intro i _ hi
      have hne : i ≠ p.1 := fun hc => hi hc
      simp [hne]
    · simp

/-- Multiplying the singleton-reference identification matrix by its conjugate transpose gives
the system identity. -/
theorem prodOneEmbedding_mul_conjTranspose (D : ℕ) :
    prodOneEmbedding D * (prodOneEmbedding D)ᴴ = 1 := by
  ext x y
  rw [Matrix.mul_apply]
  simp only [prodOneEmbedding_apply, prodOneEmbedding_conjTranspose_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (x, 0)]
  · by_cases h : y = x
    · simp [h]
    · have h' : ¬(x = y) := fun hc => h hc.symm
      simp [h, h']
  · intro p _ hp
    have hne : x ≠ p.1 := by
      intro hc
      apply hp
      calc p = (p.1, 0) := finProdOne_eta D p
        _ = (x, 0) := by rw [hc]
    simp [hne]
  · simp

/-- Summing a function against the singleton-reference label-matching indicator selects its
value at the matched label. -/
theorem sum_prodOne_embedding {D : ℕ} (y : Fin D) (g : Fin D → ℂ) :
    (∑ v : Fin D, g v * (if v = y then 1 else 0)) = g y := by
  rw [Finset.sum_eq_single y]
  · simp
  · intro v _ hv
    simp [hv]
  · simp

/-- Sandwiching a system operator by the singleton-reference identification gives its submatrix
lifted by first-coordinate projection. -/
theorem prodOneEmbedding_sandwich (D : ℕ) (A : Operator D) :
    (prodOneEmbedding D)ᴴ * A * (prodOneEmbedding D)
      = A.submatrix (fun p : Fin D × Fin 1 => p.1) (fun q : Fin D × Fin 1 => q.1) := by
  ext x y
  simp only [Matrix.mul_apply, prodOneEmbedding_apply, prodOneEmbedding_conjTranspose_apply]
  calc (∑ v : Fin D, (∑ u : Fin D, (if u = x.1 then 1 else 0) * A u v)
          * (if v = y.1 then 1 else 0))
      = ∑ v : Fin D, ∑ u : Fin D,
          ((if u = x.1 then 1 else 0) * A u v) * (if v = y.1 then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro v _
            rw [Finset.sum_mul]
    _ = ∑ u : Fin D, ∑ v : Fin D,
          ((if u = x.1 then 1 else 0) * A u v) * (if v = y.1 then 1 else 0) :=
          Finset.sum_comm
    _ = ∑ u : Fin D, (if u = x.1 then 1 else 0)
          * (∑ v : Fin D, A u v * (if v = y.1 then 1 else 0)) := by
            apply Finset.sum_congr rfl
            intro u _
            calc ∑ v : Fin D, ((if u = x.1 then 1 else 0) * A u v) * (if v = y.1 then 1 else 0)
                = ∑ v : Fin D, (if u = x.1 then 1 else 0)
                    * (A u v * (if v = y.1 then 1 else 0)) := by
                      apply Finset.sum_congr rfl
                      intro v _
                      exact mul_assoc _ _ _
              _ = (if u = x.1 then 1 else 0)
                    * (∑ v : Fin D, A u v * (if v = y.1 then 1 else 0)) := by
                      rw [Finset.mul_sum]
    _ = ∑ u : Fin D, (if u = x.1 then 1 else 0) * A u y.1 := by
          apply Finset.sum_congr rfl
          intro u _
          rw [sum_prodOne_embedding]
    _ = A x.1 y.1 := by
          rw [Finset.sum_eq_single x.1]
          · simp
          · intro u _ hu
            have hne : u ≠ x.1 := fun hc => hu hc
            simp [hne]
          · simp
    _ = A.submatrix (fun p : Fin D × Fin 1 => p.1) (fun q : Fin D × Fin 1 => q.1) x y := by
      rw [Matrix.submatrix_apply]

/-- Lifting a system operator to a singleton reference by first-coordinate projection preserves
its trace norm. -/
theorem traceNorm_prodOne_submatrix {D : ℕ} (A : Operator D) :
    Matrix.traceNorm (A.submatrix (fun p : Fin D × Fin 1 => p.1)
        (fun q : Fin D × Fin 1 => q.1))
      = Matrix.traceNorm A := by
  rw [← prodOneEmbedding_sandwich]
  calc Matrix.traceNorm ((prodOneEmbedding D)ᴴ * A * (prodOneEmbedding D))
      = Matrix.traceNorm ((prodOneEmbedding D)ᴴ * A) := by
        have hι'' : (prodOneEmbedding D)ᴴ * A * (prodOneEmbedding D)
            = (prodOneEmbedding D)ᴴ * A * (prodOneEmbedding D)ᴴᴴ := by
          rw [Matrix.conjTranspose_conjTranspose]
        rw [hι'', Matrix.traceNorm_isometry_right (u := (prodOneEmbedding D)ᴴ) (by
          have h := prodOneEmbedding_mul_conjTranspose D
          ext a b
          by_cases hab : a = b <;>
            simpa [Matrix.one_apply, hab, Matrix.conjTranspose_conjTranspose] using!
              congrFun (congrFun h a) b)]
    _ = Matrix.traceNorm A := by
        rw [Matrix.traceNorm_isometry_left (u := (prodOneEmbedding D)ᴴ) (by
          have h := prodOneEmbedding_mul_conjTranspose D
          ext a b
          by_cases hab : a = b <;>
            simpa [Matrix.one_apply, hab, Matrix.conjTranspose_conjTranspose] using!
              congrFun (congrFun h a) b)]

/-- A finite diamond-distance bound `δ` gives system-output trace-norm error at most `2 * δ *
traceNorm X` for every input operator. -/
theorem diamondSystemFactor_transfer {D E : ℕ} (Φ Ψ : Operator D →ₗ[ℂ] Operator E)
    (X : Operator D) {δ : ℝ} (hδ : 0 ≤ δ)
    (hd : (finiteDiamondDistance Φ Ψ : ℝ≥0∞) ≤ ENNReal.ofReal δ) :
    Matrix.traceNorm ((Φ - Ψ) X) ≤ 2 * δ * Matrix.traceNorm X := by
  have hh : (1/2 : ℝ≥0∞) * ENNReal.ofReal (2 * δ) = ENNReal.ofReal ((2 * δ)/2) := by
    rw [show (1/2 : ℝ≥0∞) = ENNReal.ofReal (1/2 : ℝ) by
      rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1/2)]
    congr 1
    ring
  have hd' : finiteDiamondDistance Φ Ψ ≤ ENNReal.ofReal ((2 * δ)/2) := by
    have hdiv : (2 * δ)/2 = δ := by ring
    rw [hdiv]
    exact hd
  have hnorm : finiteDiamondNorm (Φ - Ψ) ≤ ENNReal.ofReal (2 * δ) := by
    calc
      _ = 2 * finiteDiamondDistance Φ Ψ := by
        unfold finiteDiamondDistance
        rw [← mul_assoc]
        rw [one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
      _ ≤ 2 * ENNReal.ofReal ((2 * δ)/2) := mul_le_mul le_rfl hd' bot_le bot_le
      _ = ENNReal.ofReal (2 * δ) := by
        rw [← hh, ← mul_assoc, one_div, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  have huniform : ∀ (r : ℕ) (X' : Matrix (Fin D × Fin r) (Fin D × Fin r) ℂ),
      Matrix.traceNorm (tensorLeft (Φ - Ψ) X') ≤ (2 * δ) * Matrix.traceNorm X' :=
    (finiteDiamondNorm_le_iff_uniform D E (Φ - Ψ) (2 * δ)
      (mul_nonneg (by norm_num) hδ)).mp hnorm
  have hρ : tensorLeft (Φ - Ψ)
        (X.submatrix (fun p : Fin D × Fin 1 => p.1) (fun q : Fin D × Fin 1 => q.1))
      = ((Φ - Ψ) X).submatrix (fun p : Fin E × Fin 1 => p.1) (fun q : Fin E × Fin 1 => q.1) := by
    ext x y
    simp only [tensorLeft, Matrix.submatrix_apply]
  have h := huniform 1 (X.submatrix (fun p : Fin D × Fin 1 => p.1)
    (fun q : Fin D × Fin 1 => q.1))
  rw [hρ, traceNorm_prodOne_submatrix, traceNorm_prodOne_submatrix] at h
  exact h

/-- Taking a power of the controlled operator block equals forming the controlled block of that
power. -/
theorem ctrlOperatorBlk_pow (D : ℕ) (U : Operator D) (n : ℕ) :
    ctrlOperatorBlk U ^ n = ctrlOperatorBlk (U ^ n) := by
  unfold ctrlOperatorBlk
  rw [← Matrix.blockDiagonal_pow]
  refine congrArg (fun M : Fin 2 → Operator D => Matrix.blockDiagonal M) ?_
  show (fun b : Fin 2 => (if b = 0 then (1 : Operator D) else U) ^ n)
      = (fun b : Fin 2 => if b = 0 then (1 : Operator D) else U ^ n)
  funext b
  by_cases hb : b = 0 <;> simp [hb]

/-- A positive power of the zero-and-term block dilation equals the dilation of the
corresponding term power. -/
theorem dilatedTermBlk_pow (D : ℕ) (K : Operator D) (n : ℕ) (hn : 0 < n) :
    dilatedTermBlk K ^ n = dilatedTermBlk (K ^ n) := by
  unfold dilatedTermBlk
  rw [← Matrix.blockDiagonal_pow]
  refine congrArg (fun M : Fin 2 → Operator D => Matrix.blockDiagonal M) ?_
  show (fun b : Fin 2 => (if b = 0 then (0 : Operator D) else K) ^ n)
      = (fun b : Fin 2 => if b = 0 then (0 : Operator D) else K ^ n)
  funext b
  by_cases hb : b = 0
  · simp only [hb, if_pos, zero_pow (Nat.ne_of_gt hn)]
  · simp [hb]

/-- Gives the controlled operator's entries: identity in the zero-control block, `U` in the
other diagonal block, and zero across blocks. -/
theorem ctrlOperatorBlk_apply (D : ℕ) (U : Operator D) (d d' : Fin D) (b b' : Fin 2) :
    ctrlOperatorBlk U (d, b) (d', b') =
      if b = b' then (if b = 0 then (if d = d' then 1 else 0) else U d d') else 0 := by
  rw [ctrlOperatorBlk, Matrix.blockDiagonal_apply]
  by_cases hb : b = b'
  · by_cases hb' : b' = 0
    · simp [hb, hb', Matrix.one_apply]
    · simp [hb, hb']
  · simp [hb]

/-- The binomial sum with coefficients `R.choose i` equals `(x + y)^R`. -/
theorem binomial_sum_choose (R : ℕ) (x y : ℝ) :
    (∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ i * y ^ (R - i)))
      = (x + y) ^ R := by
  induction R with
  | zero =>
    simp
  | succ R ih =>
    have hsplit := Finset.sum_choose_succ_mul (fun i j => x ^ i * y ^ j) R
    have hfirst :
        (∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ i * y ^ (R + 1 - i)))
          = y * (∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ i * y ^ (R - i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ R := by simpa using! (Finset.mem_range.mp hi)
      rw [show R + 1 - i = (R - i) + 1 by omega, pow_succ]
      ring
    have hsecond :
        (∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ (i + 1) * y ^ (R - i)))
          = x * (∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ i * y ^ (R - i))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i ≤ R := by simpa using! (Finset.mem_range.mp hi)
      rw [pow_succ]
      ring
    calc (∑ i ∈ Finset.range (R + 1 + 1),
          ((R + 1).choose i : ℝ) * (x ^ i * y ^ (R + 1 - i)))
        = (∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ i * y ^ (R + 1 - i)))
          + ∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ (i + 1) * y ^ (R - i)) := by
            exact hsplit
      _ = y * (∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ i * y ^ (R - i)))
          + x * (∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ i * y ^ (R - i))) := by
            rw [hfirst, hsecond]
      _ = (x + y) * (∑ i ∈ Finset.range (R + 1), (R.choose i : ℝ) * (x ^ i * y ^ (R - i))) := by
            ring
      _ = (x + y) * (x + y) ^ R := by rw [ih]
      _ = (x + y) ^ (R + 1) := by rw [pow_succ]; ring

/-- For `0 < q < 1` and `t ≥ 1`, the failure probability of an odd-sized majority is bounded by
`t⁻¹^(m + 1) * (t * q + (1 - q))^(2 * m + 1)`. -/
theorem majorityFailure_tilt (m : ℕ) (q t : ℝ) (hq0 : 0 < q) (hq1 : q < 1)
    (ht0 : 0 < t) (ht1 : 1 ≤ t) :
    majorityFailure q (2 * m + 1)
      ≤ t⁻¹ ^ (m + 1) * (t * q + (1 - q)) ^ (2 * m + 1) := by
  have hdiv : (2 * m + 1) / 2 = m := by omega
  have hpoint : ∀ i ∈ Finset.range (2 * m + 1 + 1),
      (if m < i then (Nat.choose (2 * m + 1) i : ℝ) * q ^ i * (1 - q) ^ ((2 * m + 1) - i)
        else 0)
        ≤ t⁻¹ ^ (m + 1) * ((Nat.choose (2 * m + 1) i : ℝ) *
          ((t * q) ^ i * (1 - q) ^ ((2 * m + 1) - i))) := by
    intro i hi
    by_cases hmi : m < i
    · have hi' : i ≤ 2 * m + 1 := by
        have := Finset.mem_range.mp hi
        omega
      have hti : t⁻¹ ^ (m + 1) * t ^ i = t ^ (i - (m + 1)) := by
        have h1 : t ^ i = t ^ (m + 1) * t ^ (i - (m + 1)) := by
          rw [← pow_add]
          congr 1
          omega
        rw [h1, inv_pow, ← mul_assoc, inv_mul_cancel₀ (a := t ^ (m + 1)) (by positivity),
          one_mul]
      have hone : ∀ k : ℕ, 1 ≤ t ^ k := by
        intro k
        induction k with
        | zero => simp
        | succ k ih =>
          rw [pow_succ]
          have h1 : 1 * t ≤ t ^ k * t := mul_le_mul_of_nonneg_right ih (by positivity)
          linarith
      have hge : 1 ≤ t ^ (i - (m + 1)) := hone (i - (m + 1))
      have hqpow : q ^ i ≤ t⁻¹ ^ (m + 1) * (t * q) ^ i := by
        rw [mul_pow, ← mul_assoc, hti]
        simpa using!
          (mul_le_mul_of_nonneg_right hge (show (0 : ℝ) ≤ q ^ i by positivity))
      have hc : 0 ≤ (Nat.choose (2 * m + 1) i : ℝ) := by positivity
      have hcp : 0 ≤ (1 - q) ^ ((2 * m + 1) - i) := by positivity
      simp only [if_pos hmi]
      calc (Nat.choose (2 * m + 1) i : ℝ) * q ^ i * (1 - q) ^ ((2 * m + 1) - i)
          = (Nat.choose (2 * m + 1) i : ℝ) * (q ^ i * (1 - q) ^ ((2 * m + 1) - i)) := by ring
        _ ≤ (Nat.choose (2 * m + 1) i : ℝ) *
            ((t⁻¹ ^ (m + 1) * (t * q) ^ i) * (1 - q) ^ ((2 * m + 1) - i)) := by
              exact mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_right hqpow hcp) hc
        _ = t⁻¹ ^ (m + 1) * ((Nat.choose (2 * m + 1) i : ℝ) *
              ((t * q) ^ i * (1 - q) ^ ((2 * m + 1) - i))) := by ring
    · simp only [if_neg hmi]
      positivity
  unfold majorityFailure
  rw [hdiv]
  calc (∑ i ∈ Finset.range (2 * m + 1 + 1),
        if m < i then (Nat.choose (2 * m + 1) i : ℝ) * q ^ i * (1 - q) ^ ((2 * m + 1) - i)
          else 0)
      ≤ ∑ i ∈ Finset.range (2 * m + 1 + 1),
        t⁻¹ ^ (m + 1) * ((Nat.choose (2 * m + 1) i : ℝ) *
          ((t * q) ^ i * (1 - q) ^ ((2 * m + 1) - i))) := by
            exact Finset.sum_le_sum hpoint
      _ = t⁻¹ ^ (m + 1) * (∑ i ∈ Finset.range (2 * m + 1 + 1),
          (Nat.choose (2 * m + 1) i : ℝ) * ((t * q) ^ i * (1 - q) ^ ((2 * m + 1) - i))) := by
            rw [Finset.mul_sum]
      _ = t⁻¹ ^ (m + 1) * ((t * q + (1 - q)) ^ (2 * m + 1)) := by
            rw [binomial_sum_choose]

/-- For `0 ≤ x < 1`, the product `(1 - x)^m * (1 + m * x)` is at most one. -/
theorem bernoulli_pow_le (x : ℝ) (m : ℕ) (hx0 : 0 ≤ x) (hx1 : x < 1) :
    (1 - x) ^ m * (1 + m * x) ≤ 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hcast : (m.succ : ℝ) = (m : ℝ) + 1 := by
      rw [Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one]
    have hsq : 0 ≤ ((m : ℝ) + 1) * x ^ 2 :=
      mul_nonneg (by linarith) (sq_nonneg x)
    have hmul : (1 - x) * (1 + ((m : ℝ) + 1) * x) ≤ 1 + (m : ℝ) * x := by
      nlinarith [sq_nonneg x, hsq]
    have hnonneg : 0 ≤ (1 - x) ^ m := by positivity
    calc (1 - x) ^ m.succ * (1 + (m.succ : ℝ) * x)
        = (1 - x) ^ m * ((1 - x) * (1 + (m.succ : ℝ) * x)) := by rw [pow_succ]; ring
      _ ≤ (1 - x) ^ m * (1 + (m : ℝ) * x) := by
            rw [hcast]
            exact mul_le_mul_of_nonneg_left hmul hnonneg
      _ ≤ 1 := ih

/-- Regroups `a^(m + 1) * b^(2 * m + 1)` as `(a * b²)^m * (a * b)`. -/
theorem pow_pair (a b : ℝ) (m : ℕ) :
    a ^ (m + 1) * b ^ (2 * m + 1) = (a * b ^ 2) ^ m * (a * b) := by
  rw [pow_succ, pow_succ]
  rw [show b ^ (2 * m) = (b ^ 2) ^ m by
    rw [show 2 * m = m + m by omega, pow_add, ← mul_pow, pow_two]]
  rw [mul_pow]
  ring

/-- The chosen number of phase-estimation repetitions makes majority failure at single-run error
`2 / 5` at most `pf / 2`. -/
theorem majorityFailure_pe (pf : ℝ) (hpf : 0 < pf) :
    majorityFailure (2 / 5) (peRounds pf) ≤ pf / 2 := by
  set m : ℕ := Nat.ceil (70 / pf) with hm
  have hmpf : (70 : ℝ) ≤ m * pf := by
    have h2 := Nat.le_ceil (70 / pf)
    have h3 : pf * (70 / pf) = 70 := by field_simp
    have h1 : (70 : ℝ) ≤ pf * (Nat.ceil (70 / pf) : ℝ) := by
      calc (70 : ℝ) = pf * (70 / pf) := h3.symm
        _ ≤ pf * (Nat.ceil (70 / pf) : ℝ) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast h2) (le_of_lt hpf)
    linarith [h1]
  have hchern := majorityFailure_tilt m (2 / 5) (3 / 2) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  have hgeom : ((3 / 2 : ℝ)⁻¹ ^ (m + 1)
      * ((3 / 2 : ℝ) * (2 / 5) + (1 - 2 / 5)) ^ (2 * m + 1))
      = (4 / 5 : ℝ) * ((24 / 25 : ℝ) ^ m) := by
    rw [show (3 / 2 : ℝ)⁻¹ = 2 / 3 by norm_num,
      show (3 / 2 : ℝ) * (2 / 5) + (1 - 2 / 5) = 6 / 5 by norm_num]
    rw [pow_pair]
    have hb : (2 / 3 : ℝ) * (6 / 5) ^ 2 = 24 / 25 := by norm_num
    rw [hb]
    ring
  have hbern : (24 / 25 : ℝ) ^ m ≤ 1 / (1 + m / 25) := by
    have hb := bernoulli_pow_le (1 / 25 : ℝ) m (by norm_num) (by norm_num)
    have hconv : (1 - 1 / 25 : ℝ) ^ m = (24 / 25) ^ m := by ring
    have hconv2 : 1 + m * (1 / 25 : ℝ) = 1 + m / 25 := by ring
    rw [hconv, hconv2] at hb
    exact (le_div_iff₀ (by positivity : (0 : ℝ) < 1 + m / 25)).mpr hb
  have hfrac : 1 / (1 + m / 25) ≤ 25 * pf / (25 * pf + 70) := by
    have hconv : 1 / (1 + m / 25) = 25 / (25 + (m : ℝ)) := by field_simp
    rw [hconv]
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 25 + m)
      (by positivity : (0 : ℝ) < 25 * pf + 70)).2
    nlinarith [hmpf]
  have hfinal : (4 / 5 : ℝ) * ((24 / 25 : ℝ) ^ m) ≤ pf / 2 := by
    calc ((4 / 5 : ℝ) * ((24 / 25 : ℝ) ^ m)) ≤ (4 / 5 : ℝ) * (1 / (1 + m / 25)) := by
          exact mul_le_mul_of_nonneg_left hbern (by norm_num)
      _ ≤ (4 / 5 : ℝ) * (25 * pf / (25 * pf + 70)) := by
          exact mul_le_mul_of_nonneg_left hfrac (by norm_num)
      _ = (20 : ℝ) * pf / (25 * pf + 70) := by ring
      _ ≤ pf / 2 := by
          apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 25 * pf + 70)
            (by norm_num : (0 : ℝ) < 2)).2
          nlinarith [hmpf, sq_nonneg pf]
  have hrounds : peRounds pf = 2 * m + 1 := by simp only [peRounds, hm]
  rw [hrounds]
  have hchern' : majorityFailure (2 / 5) (2 * m + 1) ≤ pf / 2 := by
    rw [hgeom] at hchern
    exact hchern.trans hfinal
  exact hchern'

/-- Combines the coherent cross-block obstruction with minimal qDRIFT step counts,
phase-estimation accuracy and repetition bounds, postselection guarantees, and
selective-mass stability. -/
theorem clause21_endpoint : ∀ (Λ : Operator 2 →ₗ[ℂ] Operator 2),
    ctrlCrossBlock (ctrlBlockMapIdx Λ coherentWitness) = 0 ∧
    ctrlCrossBlock coherentWitness ≠ 0 ∧
    (∀ (lam t eps : ℝ) (n : ℕ), 0 < n → 0 < eps →
      ((2 * lam ^ 2 * t ^ 2 / (n : ℝ) ≤ eps) ↔
        Nat.ceil (2 * lam ^ 2 * t ^ 2 / eps) ≤ n)) ∧
    (∀ (lam deltaE pf : ℝ) (j : ℕ), 0 < peErrorShare deltaE pf j →
      2 * lam ^ 2 * (peTimes j) ^ 2
        ≤ peErrorShare deltaE pf j * (peQuerySteps lam deltaE pf j : ℝ)) ∧
    (∀ (pf : ℝ), 0 < pf →
      majorityFailure (2 / 5) (peRounds pf) ≤ pf / 2) ∧
    (∀ (L D : ℕ) (w : Fin L → ℕ) (j0 : Fin L) (n R : ℕ)
      (K : Fin L → Operator D) (t : ℝ) (T : ℕ) (eQ : ℝ) (hW : 0 < weightTotal w),
      (1 ≤ R → (1 / 2) ^ n ≤ postSelectSuccessMass w R n ∧
        postSelectSuccessMass w R n ≤ 1) ∧
      (0 < n → 1 ≤ R → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
        finiteDiamondDistance (postSelectedQdriftMap w hW n K t)
          (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
          ≤ ENNReal.ofReal (postSelectDiamondBudget w n t)) ∧
      (0 < n → 1 ≤ R → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
        finiteDiamondDistance (fairQdriftActualMap w j0 n R K t)
          (postSelectedQdriftMap w hW n K t) ≤ ENNReal.ofReal (n * ((2 : ℝ)⁻¹)^R)) ∧
      (Nat.ceil (2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / eQ) ≤ n →
        0 < n → 1 ≤ R → |t| ≤ T → 0 < eQ →
        (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
        finiteDiamondDistance (postSelectedQdriftMap w hW n K t)
          (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
          ≤ ENNReal.ofReal eQ)) ∧
    (∀ (D : ℕ) (Φ Ψ : Operator D →ₗ[ℂ] Operator D) (P X : Operator D),
      Pᴴ = P → P * P = P →
        |selectiveMass Φ P X - selectiveMass Ψ P X| ≤ Matrix.traceNorm ((Φ - Ψ) X)) := by
  intro Λ
  have hnfl := no_free_lunch_endpoint Λ
  refine ⟨hnfl.1, hnfl.2, ?_, ?_, ?_, ?_, ?_⟩
  · intro lam t eps n hn heps
    exact tableQdriftCount_minimal lam t eps n hn heps
  · intro lam deltaE pf j hshare
    exact pe_query_accuracy lam deltaE pf j hshare
  · intro pf hpf
    exact majorityFailure_pe pf hpf
  · intro L D w j0 n R K t T eQ hW
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hR
      exact postSelect_success_mass_bounds w hW R n hR
    · intro hn hR hK
      exact postSelected_diamond_budget w n K t hW hn hK
    · intro hn hR hK
      exact postSelect_vs_capped_sampling_bound w j0 n R K t hW hn hK
    · intro hceil hn hR ht he hK
      exact postSelected_source_tight_count w K t T eQ n hW ht hK hn he hceil
  · intro D Φ Ψ P X hP hPP
    exact selectiveMass_diff_le Φ Ψ P X hP hPP

/-- Every finite Hermitian evolution has an exact legal two-level program of length at most `D *
(D + 1) / 2`. -/
theorem nonPauli_exponential_two_level_synthesis : ∀ (D : ℕ) (K : Operator D) (θ : ℝ),
    K.IsHermitian →
    ∃ ts : List (TwoLevelInstruction (Fin D)),
      (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ Fintype.card (Fin D) * (Fintype.card (Fin D) + 1) / 2 ∧
      twoLevelProgram ts = HamiltonianEvolution K θ := by
  intro D K θ hK
  obtain ⟨ts, hts, hlen, hprog⟩ :=
    known_unitary_two_level_factorization (Fin D) (HamiltonianEvolution K θ)
      (hamiltonianEvolution_unitary hK θ)
  exact ⟨ts, hts, hlen, hprog⟩

/-- Every Hermitian evolution on an `m`-qubit register has a legal reflection-gate
implementation on `m + (m + 1)` qubits with zero queries, at most `synthGateBudget m` gates,
and exact action on the known-frame embedding. -/
theorem hermitian_exponential_circuit_synthesis : ∀ (m : ℕ)
    (K : Matrix (Reg m) (Reg m) ℂ) (θ : ℝ),
    K.IsHermitian →
    ∃ gs : List (ReflectionGate (m + (m + 1))),
      reflectionLegal gs ∧
      gs.length ≤ synthGateBudget m ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg m),
        Run 1 (reflectionCompile gs) (knownFrameEmbed m ψ) =
          knownFrameEmbed m (HamiltonianEvolution K θ *ᵥ ψ) := by
  intro m K θ hK
  obtain ⟨gs, hgs, hlen, hq, hg, hsem⟩ :=
    known_unitary_actual_clean_local_synthesis m (HamiltonianEvolution K θ)
      (hamiltonianEvolution_unitary hK θ)
  have hbudget : gs.length ≤ synthGateBudget m := by
    unfold synthGateBudget
    exact hlen
  exact ⟨gs, hgs, hbudget, hq, hg, hsem⟩

/-- Combines the allocated fair-bit qDRIFT error bound with certified step-count bounds, exact
Hermitian-evolution synthesis, and existence of accurate postselected simulations. -/
theorem clause20_endpoint : ∀ (L D : ℕ) (w : Fin L → ℕ) (j0 : Fin L)
    (K : Fin L → Operator D) (t : ℝ) (T : ℕ) (eQ : ℝ) (R n : ℕ),
    0 < weightTotal w → |t| ≤ T → (∀ j, (K j).IsHermitian ∧ ‖K j‖ ≤ 1) →
    0 < n →
    2 * (weightTotal w : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) + (n : ℝ) * ((2 : ℝ)⁻¹) ^ R ≤ eQ →
    (finiteDiamondDistance (fairQdriftActualMap w j0 n R K t)
      (conjBranch (HamiltonianEvolution (∑ j, (w j : ℂ) • K j) t))
      ≤ ENNReal.ofReal eQ) ∧
    (∀ (W T : ℕ) (eQ' : ℚ) (R' n' : ℕ),
      0 < eQ' → tightCountCertified W T eQ' R' n' = true →
        sourceTightCount W T eQ' ≤ n') ∧
    (∀ (W T : ℕ) (eQ' : ℚ), 0 < eQ' →
      ∃ (R' n' : ℕ),
        tightCountCertified W T eQ' R' n' = true ∧
        sourceTightCount W T eQ' ≤ n' ∧
        n' ≤ max 1 (Nat.ceil (4 * (W : ℚ) ^ 2 * (T : ℚ) ^ 2 / eQ'))) ∧
    (∀ (D' : ℕ) (K' : Operator D') (θ : ℝ), K'.IsHermitian →
      (∃ ts : List (TwoLevelInstruction (Fin D')),
        (∀ g ∈ ts, twoLevelLegal g) ∧
        ts.length ≤ Fintype.card (Fin D') * (Fintype.card (Fin D') + 1) / 2 ∧
        twoLevelProgram ts = HamiltonianEvolution K' θ) ∧
      (∀ (m : ℕ) (K'' : Matrix (Reg m) (Reg m) ℂ) (θ' : ℝ), K''.IsHermitian →
        ∃ gs : List (ReflectionGate (m + (m + 1))),
          reflectionLegal gs ∧
          gs.length ≤ synthGateBudget m ∧
          QueryCount (reflectionCompile gs) = 0 ∧
          GateCount (reflectionCompile gs) = gs.length ∧
          ∀ ψ : QState (Reg m),
            Run 1 (reflectionCompile gs) (knownFrameEmbed m ψ) =
              knownFrameEmbed m (HamiltonianEvolution K'' θ' *ᵥ ψ))) ∧
    (∀ (L' D' : ℕ) (w' : Fin L' → ℕ) (K' : Fin L' → Operator D')
      (t' : ℝ) (T' : ℕ) (eQ' : ℝ) (hW' : 0 < weightTotal w'),
      (|t'| ≤ T' → (∀ j, (K' j).IsHermitian ∧ ‖K' j‖ ≤ 1) →
        0 < T' → 0 < eQ' →
        ∃ n' : ℕ, 0 < n' ∧
          finiteDiamondDistance (postSelectedQdriftMap w' hW' n' K' t')
            (conjBranch (HamiltonianEvolution (∑ j, (w' j : ℂ) • K' j) t'))
            ≤ ENNReal.ofReal eQ')) := by
  intro L D w j0 K t T eQ R n hW ht hK hn hbudget
  refine ⟨tight_allocation_endpoint L D w j0 K t T eQ R n hW ht hK hn hbudget, ?_, ?_, ?_, ?_⟩
  · intro W T eQ' R' n' he' hc'
    exact tightCount_lower_bound W T eQ' R' n' he' hc'
  · intro W T eQ' he'
    exact tightCount_achievable W T eQ' he'
  · intro D' K' θ' hK'
    refine ⟨nonPauli_exponential_two_level_synthesis D' K' θ' hK', ?_⟩
    intro m K'' θ' hK''
    exact hermitian_exponential_circuit_synthesis m K'' θ' hK''
  · intro L' D' w' K' t' T' eQ' hW' ht' hK' hT' he'
    exact postSelected_source_tight_count_achievable w' K' t' T' eQ' hW' ht' hK' hT' he'

/-- Every Hermitian evolution on a qubit register has an exact legal two-level program of length
at most the register cardinality times its successor divided by two. -/
theorem nonPauli_exponential_two_level_synthesis_reg : ∀ (m : ℕ)
    (K : Matrix (Reg m) (Reg m) ℂ) (θ : ℝ),
    K.IsHermitian →
    ∃ ts : List (TwoLevelInstruction (Reg m)),
      (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ Fintype.card (Reg m) * (Fintype.card (Reg m) + 1) / 2 ∧
      twoLevelProgram ts = HamiltonianEvolution K θ := by
  intro m K θ hK
  obtain ⟨ts, hts, hlen, hprog⟩ :=
    known_unitary_two_level_factorization (Reg m) (HamiltonianEvolution K θ)
      (hamiltonianEvolution_unitary hK θ)
  exact ⟨ts, hts, hlen, hprog⟩

/-- A Hermitian evolution on a qubit register possesses both an exact bounded-length two-level
program and an exact zero-query reflection circuit acting on its known-frame embedding. -/
theorem synthesis_registers_agree : ∀ (m : ℕ)
    (K : Matrix (Reg m) (Reg m) ℂ) (θ : ℝ),
    K.IsHermitian →
    (∃ ts : List (TwoLevelInstruction (Reg m)),
      (∀ g ∈ ts, twoLevelLegal g) ∧
      ts.length ≤ Fintype.card (Reg m) * (Fintype.card (Reg m) + 1) / 2 ∧
      twoLevelProgram ts = HamiltonianEvolution K θ) ∧
    (∃ gs : List (ReflectionGate (m + (m + 1))),
      reflectionLegal gs ∧
      gs.length ≤ synthGateBudget m ∧
      QueryCount (reflectionCompile gs) = 0 ∧
      GateCount (reflectionCompile gs) = gs.length ∧
      ∀ ψ : QState (Reg m),
        Run 1 (reflectionCompile gs) (knownFrameEmbed m ψ) =
          knownFrameEmbed m (HamiltonianEvolution K θ *ᵥ ψ)) := by
  intro m K θ hK
  exact ⟨nonPauli_exponential_two_level_synthesis_reg m K θ hK,
    hermitian_exponential_circuit_synthesis m K θ hK⟩

section

variable {D : ℕ} [DecidableEq (Fin D)]

/-- The outer product of a basis ket has entry one only at the pair of its basis label with
itself. -/
theorem outerProduct_ket_apply (i j k : Fin D) :
    Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i) j k
      = if j = i ∧ k = i then 1 else 0 := by
  rw [Qatlib.Foundations.PureStateMath.Reflection.outerProduct_apply]
  by_cases hj : j = i
  · by_cases hk : k = i
    · subst hj
      subst hk
      simp [Qatlib.Foundations.PureStateMath.Ket]
    · simp [Qatlib.Foundations.PureStateMath.Ket, hj, hk]
  · simp [Qatlib.Foundations.PureStateMath.Ket, hj]

/-- The diagonal of a basis-ket outer product is the indicator of its basis label. -/
theorem outerProduct_ket_diag (i j : Fin D) :
    Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i) j j = if j = i then 1 else 0 := by
  rw [outerProduct_ket_apply]
  by_cases h : j = i
  · rw [if_pos h, if_pos ⟨h, h⟩]
  · rw [if_neg h, if_neg (fun h2 => h h2.1)]

/-- The diagonal of a matrix times a basis-ket outer product is zero away from that basis label
and equals the selected matrix entry there. -/
theorem mul_outerProduct_ket_apply (U : Matrix (Fin D) (Fin D) ℂ) (i j : Fin D) :
    (U * Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i)) j j
      = if j = i then U j i else 0 := by
  rw [Matrix.mul_apply]
  by_cases hji : j = i
  · rw [Finset.sum_eq_single i]
    · simp [outerProduct_ket_apply, hji]
    · intro l _ hl
      simp [outerProduct_ket_apply, hji, hl]
    · simp
  · simp [outerProduct_ket_apply, hji]

/-- The outer product of a basis ket has trace norm one. -/
theorem traceNorm_outerProduct_ket (i : Fin D) :
    Matrix.traceNorm (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i)) = 1 := by
  have hG := Matrix.traceNorm_eq_max_re_tr_U
    (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i))

  have hhi : Matrix.traceNorm
      (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i)) ≤ 1 := by
    rcases hG.1 with ⟨U₀, hU₀⟩
    rw [← hU₀]
    have htr : (U₀.val * Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i)).trace
        = U₀.val i i := by
      simp only [Matrix.trace, Matrix.diag_apply]
      have h2 : ∀ j : Fin D,
          (U₀.val * Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i)) j j
            = if j = i then U₀.val j i else 0 := fun j => mul_outerProduct_ket_apply U₀.val i j
      simp [h2]
    rw [htr]
    have habs : Complex.re (U₀.val i i) ≤ ‖U₀.val i i‖ :=
      le_trans (le_abs_self _) (Complex.abs_re_le_norm _)
    have hbn : ‖U₀.val i i‖ ≤ 1 :=
      @entry_norm_bound_of_unitary ℂ (Fin D) _ _ (fun a b => Classical.propDecidable (a = b))
        U₀.val U₀.property i i
    linarith

  have hlo : 1 ≤ Matrix.traceNorm
      (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i)) := by
    have hsum : ∑ j : Fin D, (if j = i then (1 : ℂ) else 0) = 1 := by
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl]
      · intro l _ hl
        rw [if_neg hl]
      · simp
    have htr : (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i)).trace = 1 := by
      simp only [Matrix.trace, Matrix.diag_apply]
      calc (∑ j : Fin D, (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i)) j j)
          = ∑ j : Fin D, (if j = i then (1 : ℂ) else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            exact outerProduct_ket_diag i j
        _ = 1 := hsum
    have habs := Matrix.abs_trace_le_traceNorm
      (Qatlib.Foundations.PureStateMath.Reflection.outerProduct (Qatlib.Foundations.PureStateMath.Ket i))
    rw [htr] at habs
    have hone : ‖(1 : ℂ)‖ = 1 := by simp
    rw [hone] at habs
    exact habs
  exact le_antisymm hhi hlo

end

section

variable {D : ℕ}

/-- The complex norm of the difference of two real casts equals the real absolute difference. -/
theorem norm_ofReal_sub (a b : ℝ) : ‖(Complex.ofReal a - Complex.ofReal b : ℂ)‖ = |a - b| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- A conditional output is its selective output scaled by the inverse selective mass, cast to
the complexes. -/
theorem conditionalOutput_eq (Φ : Operator D →ₗ[ℂ] Operator D) (P X : Operator D) :
    conditionalOutput Φ P X
      = Complex.ofReal ((selectiveMass Φ P X)⁻¹) • selectiveOutput Φ P X := by
  rw [conditionalOutput, Complex.ofReal_inv]

/-- Splits the difference of conditional outputs into a scaled selective-output difference and a
correction for the inverse selective masses. -/
theorem conditionalOutput_sub (Φ Ψ : Operator D →ₗ[ℂ] Operator D) (P X : Operator D) :
    conditionalOutput Φ P X - conditionalOutput Ψ P X
      = Complex.ofReal ((selectiveMass Φ P X)⁻¹)
          • (selectiveOutput Φ P X - selectiveOutput Ψ P X)
        + (Complex.ofReal ((selectiveMass Φ P X)⁻¹)
            - Complex.ofReal ((selectiveMass Ψ P X)⁻¹))
          • selectiveOutput Ψ P X := by
  rw [conditionalOutput_eq, conditionalOutput_eq]
  have h : ∀ (a b : ℂ) (S T : Operator D),
      a • S - b • T = a • (S - T) + (a - b) • T := by
    intro a b S T
    calc a • S - b • T = (a • S - a • T) + (a • T - b • T) := by abel
      _ = a • (S - T) + (a - b) • T := by rw [smul_sub, sub_smul]
  exact h _ _ _ _

/-- Bounds conditional-output trace-norm difference by the output error weighted by the first
inverse mass and the second output norm weighted by the inverse-mass difference. -/
theorem conditionalOutput_traceNorm_sub_le
    (Φ Ψ : Operator D →ₗ[ℂ] Operator D) (P X : Operator D)
    (hP : Pᴴ = P) (hPP : P * P = P) :
    Matrix.traceNorm (conditionalOutput Φ P X - conditionalOutput Ψ P X)
      ≤ ‖Complex.ofReal ((selectiveMass Φ P X)⁻¹)‖
          * Matrix.traceNorm ((Φ - Ψ) X)
        + ‖Complex.ofReal ((selectiveMass Φ P X)⁻¹)
            - Complex.ofReal ((selectiveMass Ψ P X)⁻¹)‖
          * Matrix.traceNorm (Ψ X) := by
  rw [conditionalOutput_sub]
  calc Matrix.traceNorm
        (Complex.ofReal ((selectiveMass Φ P X)⁻¹)
            • (selectiveOutput Φ P X - selectiveOutput Ψ P X)
          + (Complex.ofReal ((selectiveMass Φ P X)⁻¹)
            - Complex.ofReal ((selectiveMass Ψ P X)⁻¹))
            • selectiveOutput Ψ P X)
      ≤ ‖Complex.ofReal ((selectiveMass Φ P X)⁻¹)‖
          * Matrix.traceNorm (selectiveOutput Φ P X - selectiveOutput Ψ P X)
        + ‖Complex.ofReal ((selectiveMass Φ P X)⁻¹)
            - Complex.ofReal ((selectiveMass Ψ P X)⁻¹)‖
          * Matrix.traceNorm (selectiveOutput Ψ P X) := by
        exact le_trans (Matrix.traceNorm_add_le _ _)
          (add_le_add (le_of_eq (Matrix.traceNorm_smul _ _))
            (le_of_eq (Matrix.traceNorm_smul _ _)))
    _ ≤ ‖Complex.ofReal ((selectiveMass Φ P X)⁻¹)‖
          * Matrix.traceNorm ((Φ - Ψ) X)
        + ‖Complex.ofReal ((selectiveMass Φ P X)⁻¹)
            - Complex.ofReal ((selectiveMass Ψ P X)⁻¹)‖
          * Matrix.traceNorm (Ψ X) := by
      have hA : Matrix.traceNorm (selectiveOutput Φ P X - selectiveOutput Ψ P X)
          ≤ Matrix.traceNorm ((Φ - Ψ) X) := by
        have hmat : selectiveOutput Φ P X - selectiveOutput Ψ P X
            = P * ((Φ - Ψ) X) * P := by
          unfold selectiveOutput
          have hsub : (Φ - Ψ) X = Φ X - Ψ X := rfl
          rw [hsub, Matrix.mul_sub, Matrix.sub_mul]
        rw [hmat]
        exact projection_sandwich_traceNorm_le P _ hP hPP
      have hB : Matrix.traceNorm (selectiveOutput Ψ P X) ≤ Matrix.traceNorm (Ψ X) := by
        unfold selectiveOutput
        exact projection_sandwich_traceNorm_le P (Ψ X) hP hPP
      exact add_le_add (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
        (mul_le_mul_of_nonneg_left hB (norm_nonneg _))

/-- Expresses the conditional-output trace-norm bound using real absolute values of the inverse
selective masses and their difference. -/
theorem conditionalOutput_traceNorm_sub_le_real
    (Φ Ψ : Operator D →ₗ[ℂ] Operator D) (P X : Operator D)
    (hP : Pᴴ = P) (hPP : P * P = P) :
    Matrix.traceNorm (conditionalOutput Φ P X - conditionalOutput Ψ P X)
      ≤ |(selectiveMass Φ P X)⁻¹| * Matrix.traceNorm ((Φ - Ψ) X)
        + |(selectiveMass Φ P X)⁻¹ - (selectiveMass Ψ P X)⁻¹|
          * Matrix.traceNorm (Ψ X) := by
  have h1 : ‖Complex.ofReal ((selectiveMass Φ P X)⁻¹)‖ = |(selectiveMass Φ P X)⁻¹| := by
    rw [Complex.norm_real, Real.norm_eq_abs]
  have h2 : ‖(Complex.ofReal ((selectiveMass Φ P X)⁻¹)
      - Complex.ofReal ((selectiveMass Ψ P X)⁻¹) : ℂ)‖
      = |(selectiveMass Φ P X)⁻¹ - (selectiveMass Ψ P X)⁻¹| :=
    norm_ofReal_sub _ _
  have h := conditionalOutput_traceNorm_sub_le Φ Ψ P X hP hPP
  rw [h1, h2] at h
  exact h

end

end Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdrift
