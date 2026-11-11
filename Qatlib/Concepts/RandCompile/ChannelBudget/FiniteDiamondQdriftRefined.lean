/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs

/-!
# Refined qDRIFT precision and resource bounds

This module proves evaluation and cost identities for `RatProgram`, certifies finite precision
scans of dyadic lower reads, and bounds the combined simulation and fair-bit error expression.
These estimates refine the resource bookkeeping used with qDRIFT [Campbell2019].

The endpoint theorems collect the scan and storage guarantees, the error-budget balancing
inequalities, and a conditional comparison of simulation and phase-estimation count expressions.

## Main statements

* `scanPrecision_bounds`: a successful scan gives a positive corrected tolerance and a bounded
  stored time.
* `fairBitBudget_at_tight_count`: upward rounding of the balancing value incurs at most `2⁻ᴿ`
  extra budget.
* `clause19_endpoint`, `clause20_endpoint`, `clause21_endpoint`: collect the refined guarantees.

## References

* [Campbell, 2019][Campbell2019]
-/

open Qatlib.Concepts.SchattenDiamond.DiamondNorm
set_option backward.isDefEq.respectTransparency false
set_option warningAsError false
open Qatlib.Concepts.QspSimulation.Achievability.WellFormedAdjointCircuit
open Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefinedDefs

set_option autoImplicit false

namespace Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined

open Matrix Qatlib
open scoped BigOperators Classical ENNReal Matrix.Norms.L2Operator

/-- Evaluating an addition node gives the sum of the evaluations of its two subprograms. -/
theorem ratProgram_eval_add (a b : RatProgram) :
    RatProgram.eval (RatProgram.add a b) = RatProgram.eval a + RatProgram.eval b := rfl

/-- Evaluating a multiplication node gives the product of the evaluations of its two
subprograms. -/
theorem ratProgram_eval_mul (a b : RatProgram) :
    RatProgram.eval (RatProgram.mul a b) = RatProgram.eval a * RatProgram.eval b := rfl

/-- Evaluating a division node gives the quotient of the evaluations of its two subprograms. -/
theorem ratProgram_eval_div (a b : RatProgram) :
    RatProgram.eval (RatProgram.div a b) = RatProgram.eval a / RatProgram.eval b := rfl

/-- Evaluating a ceiling node gives the integer ceiling of the subprogram value, cast to a
rational. -/
theorem ratProgram_eval_ceil (a : RatProgram) :
    RatProgram.eval (RatProgram.ceil a) = Rat.ceil (RatProgram.eval a) := rfl

/-- Evaluating a binary logarithm node gives the binary ceiling logarithm of the absolute
numerator of the subprogram value. -/
theorem ratProgram_eval_log2 (a : RatProgram) :
    RatProgram.eval (RatProgram.log2 a) =
      (Nat.clog 2 (RatProgram.eval a).num.natAbs : ℚ) := rfl

/-- Evaluating a digit node rounds the subprogram value downward to the dyadic grid of precision
`k`. -/
theorem ratProgram_eval_digits (a : RatProgram) (k : ℕ) :
    RatProgram.eval (RatProgram.digits a k) =
      ((⌊RatProgram.eval a * (2 : ℚ) ^ k⌋ : ℤ) : ℚ) / (2 : ℚ) ^ k := rfl

/-- The number of operation nodes in a rational program equals the total of its operation cost
ledger. -/
theorem ratProgram_nodes_cost (p : RatProgram) :
    RatProgram.nodes p = (RatProgram.cost p).total := by
  induction p with
  | lit q => rfl
  | add a b iha ihb =>
      simp only [RatProgram.nodes, RatProgram.cost, RatCost.total, iha, ihb]
      omega
  | mul a b iha ihb =>
      simp only [RatProgram.nodes, RatProgram.cost, RatCost.total, iha, ihb]
      omega
  | div a b iha ihb =>
      simp only [RatProgram.nodes, RatProgram.cost, RatCost.total, iha, ihb]
      omega
  | ceil a ih =>
      simp only [RatProgram.nodes, RatProgram.cost, RatCost.total, ih]
      omega
  | log2 a ih =>
      simp only [RatProgram.nodes, RatProgram.cost, RatCost.total, ih]
      omega
  | digits a k ih =>
      simp only [RatProgram.nodes, RatProgram.cost, RatCost.total, ih]
      omega

/-- The bit-time allowance equals the total operation count multiplied by `(B + 2)²`. -/
theorem ratCost_bitTime (c : RatCost) (B : ℕ) :
    c.bitTime B = c.total * (B + 2) * (B + 2) := rfl

/-- The bit-space allowance equals `3 * (B + 2)`. -/
theorem ratCost_bitSpace (c : RatCost) (B : ℕ) : c.bitSpace B = 3 * (B + 2) := rfl

/-- The scan bit-length allowance bounds the dyadic-read space allowance. -/
theorem scanRunBitLength_read {L : ℕ} {x : ℝ} {k : ℕ} :
    dyadicReadSpace x k ≤ scanRunBitLength L x k := by
  have hstep : dyadicReadSpace x k ≤
      dyadicReadSpace x k + digitTableSpace L x k + 2 * (Nat.clog 2 (L + 1)) + 64 := by
    omega
  exact hstep

/-- The scan bit-length allowance bounds the digit-table space allowance. -/
theorem scanRunBitLength_table {L : ℕ} {x : ℝ} {k : ℕ} :
    digitTableSpace L x k ≤ scanRunBitLength L x k := by
  have hstep : digitTableSpace L x k ≤
      dyadicReadSpace x k + digitTableSpace L x k + 2 * (Nat.clog 2 (L + 1)) + 64 := by
    omega
  exact hstep

/-- A dyadic read's numerator magnitude plus `k + 1` is bounded by `dyadicReadSpace x k`. -/
theorem dyadicRead_space {x : ℝ} {q : ℕ → ℚ} (h : DyadicRead x q) (k : ℕ)
    (m : ℤ) (hm : q k = m / ((2 : ℚ) ^ k)) :
    |m| + k + 1 ≤ dyadicReadSpace x k := by
  have hb : |m| ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1) := h.numerator_bound k m hm
  have hstep : |m| + k + 1 ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1) + k + 1 := by
    omega
  exact hstep

/-- A dyadic lower read's numerator magnitude plus `k + 1` is bounded by `dyadicReadSpace x k`. -/
theorem dyadicLowerRead_space {x : ℝ} {q : ℕ → ℚ} (h : DyadicLowerRead x q) (k : ℕ)
    (m : ℤ) (hm : q k = m / ((2 : ℚ) ^ k)) :
    |m| + k + 1 ≤ dyadicReadSpace x k := by
  have hb : |m| ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1) := h.numerator_bound k m hm
  have hstep : |m| + k + 1 ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1) + k + 1 := by
    omega
  exact hstep

/-- Casting the rational reciprocal of `2^k` to the reals gives `(1 / 2)^k`. -/
theorem one_div_pow_two_cast (k : ℕ) :
    ((1 / ((2 : ℚ) ^ k) : ℚ) : ℝ) = (1 / 2 : ℝ) ^ k := by
  have h : (1 / ((2 : ℚ) ^ k) : ℚ) = (1 / 2 : ℚ) ^ k := by
    rw [div_pow, one_pow]
  rw [h, Rat.cast_pow]
  norm_num

/-- Casting the corrected rational budget to the reals subtracts `(1 / 2)^k` from the read
value. -/
theorem correctedBudget_cast (eq : ℚ) (k : ℕ) :
    (correctedBudget eq k : ℝ) = (eq : ℝ) - (1 / 2 : ℝ) ^ k := by
  have h := one_div_pow_two_cast k
  simp only [correctedBudget]
  rw [Rat.cast_sub, h]

/-- The corrected budget from a dyadic lower read is at most the underlying real parameter. -/
theorem correctedBudget_lower_bound {x : ℝ} {q : ℕ → ℚ} (h : DyadicLowerRead x q)
    (k : ℕ) : (correctedBudget (q k) k : ℝ) ≤ x := by
  have h1 : (q k : ℝ) ≤ x := h.lower k
  have h2 : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ k := by positivity
  have h3 : x - (q k : ℝ) ≤ (1 / 2 : ℝ) ^ k := h.deficit k
  rw [correctedBudget_cast]
  linarith

/-- The scan certificate is true exactly when the corrected tolerance is positive and the
rational time magnitude is at most `T`. -/
theorem scanCert_iff {tq eq : ℚ} {T k : ℕ} :
    scanCert tq eq T k = true ↔
      0 < eq - 1 / ((2 : ℚ) ^ k) ∧ |tq| ≤ (T : ℚ) := by
  simp [scanCert]

/-- If a list contains an element passing a Boolean test, then `List.find?` returns some
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

/-- If some level within the fuel passes `scanCert`, the selected precision also passes it. -/
theorem scanPrecision_certified : ∀ (fuel : ℕ) (tq eq : ℕ → ℚ) (T : ℕ),
    (∃ k, k ≤ fuel ∧ scanCert (tq k) (eq k) T k = true) →
    scanCert (tq (scanPrecision fuel tq eq T)) (eq (scanPrecision fuel tq eq T)) T
      (scanPrecision fuel tq eq T) = true := by
  intro fuel tq eq T hex
  obtain ⟨k, hk, hc⟩ := hex
  obtain ⟨j, hj⟩ := exists_find?_of_mem_true (fun k => scanCert (tq k) (eq k) T k)
    (List.range (fuel + 1)) ⟨k, List.mem_range.mpr (by omega), hc⟩
  have hjmem : j ≤ fuel := by
    have h := List.mem_of_find?_eq_some hj
    simpa using! h
  unfold scanPrecision
  simp only [hj, Option.getD_some]
  have hp : (fun k => scanCert (tq k) (eq k) T k) j = true :=
    List.find?_some (p := fun k => scanCert (tq k) (eq k) T k) hj
  exact hp

/-- The selected scan precision is bounded by `max 1 fuel`. -/
theorem scanPrecision_le : ∀ (fuel : ℕ) (tq eq : ℕ → ℚ) (T : ℕ),
    scanPrecision fuel tq eq T ≤ max 1 fuel := by
  intro fuel tq eq T
  unfold scanPrecision
  cases h : (List.range (fuel + 1)).find? (fun k => scanCert (tq k) (eq k) T k) with
  | some j =>
      have hjmem : j ≤ fuel := by
        have h' := List.mem_of_find?_eq_some h
        simpa using! h'
      simp only [Option.getD_some]
      exact Nat.le_trans hjmem (Nat.le_max_right _ _)
  | none =>
      simp only [Option.getD_none]
      exact Nat.le_refl _

/-- A successful scan of a dyadic lower tolerance stream gives a positive corrected budget below
the true tolerance and a stored time magnitude at most `T`. -/
theorem scanPrecision_bounds {eps : ℝ} {qeps qt : ℕ → ℚ}
    (heps : DyadicLowerRead eps qeps) (fuel : ℕ) (T : ℕ)
    (hex : ∃ k, k ≤ fuel ∧ scanCert (qt k) (qeps k) T k = true) :
    0 < correctedBudget (qeps (scanPrecision fuel qt qeps T))
        (scanPrecision fuel qt qeps T) ∧
      (correctedBudget (qeps (scanPrecision fuel qt qeps T))
        (scanPrecision fuel qt qeps T) : ℝ) ≤ eps ∧
      |(qt (scanPrecision fuel qt qeps T) : ℝ)| ≤ (T : ℝ) := by
  have hc := scanPrecision_certified fuel qt qeps T hex
  have hc' := (scanCert_iff).mp hc
  have hp := correctedBudget_lower_bound heps (scanPrecision fuel qt qeps T)
  refine ⟨hc'.1, hp, ?_⟩
  have h1 : |(qt (scanPrecision fuel qt qeps T) : ℚ)| ≤ (T : ℚ) := hc'.2
  exact_mod_cast h1

/-- For every positive step count, the combined fair-bit budget is at least `fairBitBudgetMin`. -/
theorem fairBitBudget_min : ∀ (W T R : ℕ) (n : ℕ), 0 < n →
    fairBitBudgetMin W T R ≤ fairBitBudget W T R n := by
  intro W T R n hn
  have hs0 : (0 : ℝ) ≤ (2 : ℝ) ^ R := by positivity
  have hAM : (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) + (n : ℝ) / ((2 : ℝ) ^ R)) ^ 2
      ≥ 4 * (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ)) * ((n : ℝ) / ((2 : ℝ) ^ R)) := by
    nlinarith [sq_nonneg (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ) -
      (n : ℝ) / ((2 : ℝ) ^ R))]
  have hkey : 4 * (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (n : ℝ)) * ((n : ℝ) / ((2 : ℝ) ^ R))
      = 8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ R) := by
    field_simp
    ring
  have hmin : (fairBitBudgetMin W T R) ^ 2
      = 8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ R) := by
    unfold fairBitBudgetMin
    have h2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    calc (2 * Real.sqrt 2 * (W : ℝ) * (T : ℝ) / Real.sqrt ((2 : ℝ) ^ R)) ^ 2
        = (2 : ℝ) ^ 2 * (Real.sqrt 2) ^ 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 /
            (Real.sqrt ((2 : ℝ) ^ R)) ^ 2 := by ring
      _ = 4 * 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ R) := by
        rw [h2, Real.sq_sqrt hs0]
        ring
      _ = 8 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / ((2 : ℝ) ^ R) := by ring
  have hsq : (fairBitBudgetMin W T R) ^ 2 ≤ (fairBitBudget W T R n) ^ 2 := by
    rw [fairBitBudget]
    have h := hAM
    rw [hkey] at h
    rw [hmin]
    exact h
  have hmin0 : (0 : ℝ) ≤ fairBitBudgetMin W T R := by
    unfold fairBitBudgetMin
    positivity
  have hbud0 : (0 : ℝ) ≤ fairBitBudget W T R n := by
    unfold fairBitBudget
    positivity
  have h3 : Real.sqrt ((fairBitBudgetMin W T R) ^ 2) ≤
      Real.sqrt ((fairBitBudget W T R n) ^ 2) := Real.sqrt_le_sqrt hsq
  rw [Real.sqrt_sq hmin0, Real.sqrt_sq hbud0] at h3
  exact h3

/-- For positive `W` and `T`, the budget at `tightFairBitCount` is at most `fairBitBudgetMin +
2⁻ᴿ`. -/
theorem fairBitBudget_at_tight_count : ∀ (W T R : ℕ) (_hW : 0 < W) (_hT : 0 < T),
    fairBitBudget W T R (tightFairBitCount W T R) ≤
      fairBitBudgetMin W T R + 1 / ((2 : ℝ) ^ R) := by
  intro W T R hW hT
  have hs0 : (0 : ℝ) ≤ (2 : ℝ) ^ R := by positivity
  set s : ℝ := Real.sqrt ((2 : ℝ) ^ R) with hs
  have hsp : (0 : ℝ) < s := by
    rw [hs]
    exact Real.sqrt_pos.2 (by positivity)
  have hsq : s ^ 2 = (2 : ℝ) ^ R := by
    rw [hs]
    exact Real.sq_sqrt hs0
  have hsqrt2 : (1 : ℝ) ≤ Real.sqrt 2 := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) := by norm_num
    have h3 : Real.sqrt 1 ≤ Real.sqrt 2 := Real.sqrt_le_sqrt h2
    simpa only [Real.sqrt_one] using! h3
  have hsp1 : (1 : ℝ) ≤ s := by
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ R := by
      exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
    have h3 : Real.sqrt 1 ≤ Real.sqrt ((2 : ℝ) ^ R) := Real.sqrt_le_sqrt h2
    rw [hs]
    simpa only [Real.sqrt_one] using! h3
  have ha1 : (1 : ℝ) ≤ (W : ℝ) * (T : ℝ) := by
    have hw : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    have ht : (1 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT
    have hh : (W : ℝ) * 1 ≤ (W : ℝ) * (T : ℝ) := by
      exact mul_le_mul_of_nonneg_left ht (by positivity)
    nlinarith [hh, hw]
  set x : ℝ := Real.sqrt 2 * (W : ℝ) * (T : ℝ) * s with hx
  have hx1 : (1 : ℝ) ≤ x := by
    rw [hx]
    have h1 : (1 : ℝ) ≤ (W : ℝ) * (T : ℝ) * s := by
      have h := mul_le_mul_of_nonneg_right ha1 (le_of_lt hsp)
      nlinarith [hsp1]
    have h2 : (W : ℝ) * (T : ℝ) * s ≤
        Real.sqrt 2 * ((W : ℝ) * (T : ℝ) * s) := by
      have hh := mul_le_mul_of_nonneg_left hsqrt2
        (by positivity : (0 : ℝ) ≤ (W : ℝ) * (T : ℝ) * s)
      convert! hh using 1 <;> ring
    nlinarith
  have hceil : x ≤ (Nat.ceil x : ℝ) := by exact_mod_cast (Nat.le_ceil x)
  have hceilpos : (1 : ℕ) ≤ Nat.ceil x := by
    exact_mod_cast (le_trans (show (1 : ℝ) ≤ x from hx1) hceil)
  have hceil1 : (Nat.ceil x : ℝ) ≤ x + 1 := by
    have hlt : ((Nat.ceil x - 1 : ℕ) : ℝ) < x := by
      have h := (Nat.lt_ceil (α := ℝ)).mp
        (show (Nat.ceil x - 1 : ℕ) < Nat.ceil x from by omega)
      exact_mod_cast h
    have hcast : ((Nat.ceil x - 1 : ℕ) : ℝ) = (Nat.ceil x : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      norm_num
    rw [hcast] at hlt
    linarith
  have harg : fairBitBudgetArgmin W T R = x := by
    unfold fairBitBudgetArgmin
    rw [← hs]
  have hn_eq : tightFairBitCount W T R = Nat.ceil x := by
    rw [tightFairBitCount, harg]
    omega
  have hn : (1 : ℕ) ≤ tightFairBitCount W T R := by
    rw [hn_eq]
    exact hceilpos
  have hnx : x ≤ (tightFairBitCount W T R : ℝ) := by
    rw [hn_eq]
    exact hceil
  have hnx1 : (tightFairBitCount W T R : ℝ) ≤ x + 1 := by
    rw [hn_eq]
    exact hceil1
  have hn0 : (0 : ℝ) < (tightFairBitCount W T R : ℝ) := by
    have hne : tightFairBitCount W T R ≠ 0 := by
      rw [hn_eq]
      exact Nat.ne_of_gt hceilpos
    have hpos : 0 < tightFairBitCount W T R := Nat.pos_of_ne_zero hne
    exact_mod_cast hpos
  have hdiv : 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 /
        (Real.sqrt 2 * (W : ℝ) * (T : ℝ) * s)
      = Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s := by
    have hden : Real.sqrt 2 * (W : ℝ) * (T : ℝ) * s ≠ 0 := by positivity
    have hne : s ≠ 0 := ne_of_gt hsp
    rw [(div_eq_div_iff hden hne)]
    have h2 : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
    ring_nf
    rw [h2]
  have hkey1 : 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (tightFairBitCount W T R : ℝ) ≤
      Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s := by
    have hle : (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (tightFairBitCount W T R : ℝ)) ≤
        (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 /
          (Real.sqrt 2 * (W : ℝ) * (T : ℝ) * s)) := by
      have hone : (1 : ℝ) / (tightFairBitCount W T R : ℝ) ≤
          1 / (Real.sqrt 2 * (W : ℝ) * (T : ℝ) * s) := by
        exact one_div_le_one_div_of_le
          (by positivity : (0 : ℝ) < Real.sqrt 2 * (W : ℝ) * (T : ℝ) * s) (by linarith [hx])
      have hm := mul_le_mul_of_nonneg_left hone
        (by positivity : (0 : ℝ) ≤ 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2)
      convert! hm using 1 <;> ring
    rw [hdiv] at hle
    exact hle
  have hxs : x / s ^ 2 = Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s := by
    rw [hx]
    have hne : s ≠ 0 := ne_of_gt hsp
    rw [div_eq_div_iff (by positivity) hne]
    ring
  have hkey2 : (tightFairBitCount W T R : ℝ) / s ^ 2 ≤
      Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s + 1 / s ^ 2 := by
    have h1 : (tightFairBitCount W T R : ℝ) / s ^ 2 ≤ (x + 1) / s ^ 2 := by
      exact div_le_div_of_nonneg_right (by linarith) (by positivity)
    have h2 : (x + 1) / s ^ 2 ≤
        Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s + 1 / s ^ 2 := by
      have heq : (x + 1) / s ^ 2 = x / s ^ 2 + 1 / s ^ 2 := by ring
      rw [heq, hxs]
    linarith
  have hmain : 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (tightFairBitCount W T R : ℝ) +
      (tightFairBitCount W T R : ℝ) / s ^ 2 ≤
      2 * Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s + 1 / s ^ 2 := by
    have h1 : 2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (tightFairBitCount W T R : ℝ) ≤
        Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s := hkey1
    have h2 : (tightFairBitCount W T R : ℝ) / s ^ 2 ≤
        Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s + 1 / s ^ 2 := hkey2
    calc
      (2 * (W : ℝ) ^ 2 * (T : ℝ) ^ 2 / (tightFairBitCount W T R : ℝ) +
          (tightFairBitCount W T R : ℝ) / s ^ 2)
          ≤ (Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s) +
            (Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s + 1 / s ^ 2) := add_le_add h1 h2
      _ = 2 * Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s + 1 / s ^ 2 := by ring
  have hmin : fairBitBudgetMin W T R = 2 * Real.sqrt 2 * (W : ℝ) * (T : ℝ) / s := by
    unfold fairBitBudgetMin
    rw [← hs]
  rw [fairBitBudget, hmin, ← hsq]
  exact hmain

/-- Under the stated parameter relation and comparison inequalities, the qDRIFT simulation count
is at most the phase-estimation count expression. -/
theorem tableIQdriftCount_le_peCount (lam t eps deltaE pf : ℝ)
    (hlam : 0 < lam) (hdelta : 0 < deltaE) (hpf : 0 < pf)
    (hbudget : eps = deltaE ^ 2 * pf ^ 2) (hcmp : 2 * t ^ 2 * pf ≤ 133)
    (hB : 1 ≤ 133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3)) :
    tableIQdriftCount lam t eps ≤ tableIQdriftPeCount lam deltaE pf := by
  have hkey : 2 * lam ^ 2 * t ^ 2 * (deltaE ^ 2 * pf ^ 3) ≤
      (133 * lam ^ 2) * (deltaE ^ 2 * pf ^ 2) := by
    have h1 : 2 * t ^ 2 * pf ≤ 133 := hcmp
    field_simp
    nlinarith [h1]
  rw [tableIQdriftCount, tableIQdriftPeCount, hbudget]
  have hdiv := (div_le_div_iff₀ (by positivity : (0 : ℝ) < deltaE ^ 2 * pf ^ 2)
    (by positivity : (0 : ℝ) < deltaE ^ 2 * pf ^ 3)).2 hkey
  have hceil : Nat.ceil (2 * lam ^ 2 * t ^ 2 / (deltaE ^ 2 * pf ^ 2)) ≤
      Nat.ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3)) := Nat.ceil_le_ceil hdiv
  have hBceil : (1 : ℕ) ≤ Nat.ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3)) := by
    have hge := Nat.le_ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3))
    have hlt : (0 : ℝ) < (Nat.ceil (133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3)) : ℝ) :=
      lt_of_lt_of_le (by linarith) hge
    exact Nat.succ_le_of_lt (by exact_mod_cast hlt)
  exact Nat.max_le.mpr ⟨hBceil, hceil⟩

/-- Each phase-estimation chain error share equals its squared evolution time times the share at
index zero. -/
theorem peChainErrorShare_proportional (deltaE pf : ℝ) (j : ℕ) :
    peChainErrorShare deltaE pf j =
      (peChainTimes j) ^ 2 * peChainErrorShare deltaE pf 0 := by
  unfold peChainErrorShare
  simp only [peChainTimes]
  ring

/-- Collects successful-scan guarantees, dyadic numerator space bounds, rational-program node
counts, and the bit-time and bit-space identities. -/
theorem clause19_endpoint :
    (∀ (eps : ℝ) (qeps qt : ℕ → ℚ),
      (∀ k, ∃ m : ℤ, qeps k = m / ((2 : ℚ) ^ k)) →
      (∀ k, (qeps k : ℝ) ≤ eps) →
      (∀ k, eps - (qeps k : ℝ) ≤ (1 / 2 : ℝ) ^ k) →
      (∀ k (m : ℤ), qeps k = m / ((2 : ℚ) ^ k) →
        |m| ≤ ((2 : ℕ) ^ k) * (Nat.ceil |eps| + 1)) →
      ∀ (fuel T : ℕ),
        (∃ k, k ≤ fuel ∧ scanCert (qt k) (qeps k) T k = true) →
        0 < correctedBudget (qeps (scanPrecision fuel qt qeps T))
            (scanPrecision fuel qt qeps T) ∧
          (correctedBudget (qeps (scanPrecision fuel qt qeps T))
            (scanPrecision fuel qt qeps T) : ℝ) ≤ eps ∧
          |(qt (scanPrecision fuel qt qeps T) : ℝ)| ≤ (T : ℝ)) ∧
    (∀ (x : ℝ) (q : ℕ → ℚ) (k : ℕ) (m : ℤ), q k = m / ((2 : ℚ) ^ k) →
      |m| ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1) →
      |m| + k + 1 ≤ dyadicReadSpace x k) ∧
    (∀ (p : RatProgram), RatProgram.nodes p = (RatProgram.cost p).total) ∧
    (∀ (c : RatCost) (B : ℕ), c.bitTime B = c.total * (B + 2) * (B + 2) ∧
      c.bitSpace B = 3 * (B + 2)) ∧
    (∀ (L : ℕ) (x : ℝ) (k : ℕ),
      dyadicReadSpace x k ≤ scanRunBitLength L x k ∧
      digitTableSpace L x k ≤ scanRunBitLength L x k) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro eps qeps qt h1 h2 h3 h4 fuel T hex
    exact scanPrecision_bounds
      { exact_form := h1, lower := h2, deficit := h3, numerator_bound := h4 }
      fuel T hex
  · intro x q k m hm hb
    have hstep : |m| + k + 1 ≤ ((2 : ℕ) ^ k) * (Nat.ceil |x| + 1) + k + 1 := by
      omega
    exact hstep
  · intro p
    exact ratProgram_nodes_cost p
  · intro c B
    exact ⟨ratCost_bitTime c B, ratCost_bitSpace c B⟩
  · intro L x k
    exact ⟨scanRunBitLength_read, scanRunBitLength_table⟩

/-- Collects the lower bound and rounded-choice upper bound for fair-bit budgets together with
the protocol synthesis resource identities. -/
theorem clause20_endpoint : ∀ (W T R : ℕ) (n : ℕ), 0 < n →
    fairBitBudgetMin W T R ≤ fairBitBudget W T R n ∧
    (∀ (W' T' R' : ℕ), 0 < W' → 0 < T' →
      fairBitBudget W' T' R' (tightFairBitCount W' T' R') ≤
        fairBitBudgetMin W' T' R' + 1 / ((2 : ℝ) ^ R')) ∧
    (∀ (m n : ℕ),
      protocolGateBudget m n = n * synthGateBudget m ∧
      protocolSpaceBudget m = m + (m + 1) ∧
      protocolClassicalSpace n = Nat.clog 2 (max 1 n) ∧
      synthGateBudget m = 128 * (m + 1) ^ 2 * 4 ^ m) := by
  intro W T R n hn
  refine ⟨fairBitBudget_min W T R n hn, ?_, ?_⟩
  · intro W' T' R' hW hT
    exact fairBitBudget_at_tight_count W' T' R' hW hT
  · intro m n
    exact ⟨rfl, rfl, rfl, rfl⟩

/-- Combines the conditional comparison of qDRIFT count expressions with proportional allocation
of phase-estimation chain errors. -/
theorem clause21_endpoint : ∀ (lam t eps deltaE pf : ℝ),
    0 < lam → 0 < eps → 0 < deltaE → 0 < pf →
    eps = deltaE ^ 2 * pf ^ 2 → 2 * t ^ 2 * pf ≤ 133 →
    1 ≤ 133 * lam ^ 2 / (deltaE ^ 2 * pf ^ 3) →
    tableIQdriftCount lam t eps ≤ tableIQdriftPeCount lam deltaE pf ∧
    (∀ (deltaE pf : ℝ) (j : ℕ),
      peChainErrorShare deltaE pf j =
        (peChainTimes j) ^ 2 * peChainErrorShare deltaE pf 0) := by
  intro lam t eps deltaE pf hlam heps hdelta hpf hbudget hcmp hB
  refine ⟨tableIQdriftCount_le_peCount lam t eps deltaE pf hlam hdelta hpf hbudget hcmp hB,
    ?_⟩
  intro deltaE pf j
  exact peChainErrorShare_proportional deltaE pf j

end Qatlib.Concepts.RandCompile.ChannelBudget.FiniteDiamondQdriftRefined
