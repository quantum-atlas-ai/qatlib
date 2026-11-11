/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# Search core of Jeffery--Kothari--Magniez (arXiv:1112.5855v2, Section 2.2)

Corollary 2.2 and Corollary 2.3 of the fixed arXiv v2 source are variations of
Grover search that the paper cites from [BBHT98] and re-derives at the level of
query accounting.  This module formalizes the accounting that the paper itself
performs:

* the amplification ledger: `K` independent attempts, each failing with weight
  at most `3/4`, leave total failure weight at most `(3/4)^K`, and some
  `K` makes this at most `1/N`;
* the uniform-step cost of one attempt at search scale `t`;
* the backward parameter accounting of `SearchAll`: every successful round
  satisfies `t_j ≥ s - j + 1` when `s` marked elements are removed;
* the telescoping bound `∑_{k < s} 1/√(k+1) ≤ 2√s` for the successful rounds;
* the halving ledger for unsuccessful rounds (`≤ log₂ N + 1` of them, each of
  cost at most `√N`), and the resulting `Õ(√(N(s+1)))` cost bound.

The Grover success-probability theorem that supplies the per-attempt guarantee
is the cited [BBHT98] result; it is consumed as the paper's input, not
re-derived here.
-/

namespace Qatlib.Papers.BoolMatMult11.MainResults.SearchCore

open scoped BigOperators

set_option autoImplicit false

/-- Number of marked elements `t_f = |f ⁻¹' {1}|` of a Boolean predicate on a
finite universe. -/
def markedCount {U : Type*} [Fintype U] (f : U → Bool) : ℕ :=
  (Finset.univ.filter fun x => f x = true).card

/-- Query cost of one Grover attempt on a universe of size `N` at search scale
`t`, the `Õ(√(|U|/t))` quantity of Corollary 2.2 (polylogarithmic factors are
carried separately by the repetition count). -/
noncomputable def attemptCost (N t : ℕ) : ℝ :=
  Real.sqrt ((N : ℝ) / (t : ℝ))

/-- The cost `√(N/t)` is monotone decreasing in the search scale `t`. -/
theorem attemptCost_le_of_le {N t₁ t₂ : ℕ} (ht : 0 < t₁) (htt : t₁ ≤ t₂) :
    attemptCost N t₂ ≤ attemptCost N t₁ := by
  unfold attemptCost
  apply Real.sqrt_le_sqrt
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by exact_mod_cast ht)
    (by exact_mod_cast htt)

/-- Amplification ledger of Corollary 2.2: if a single attempt leaves failure
weight at most `3/4`, then `K` repetitions leave at most `(3/4)^K`.  Once
`(4/3)^K ≥ N` this is at most `1/N`, i.e. `1 - 1/poly(|U|)` success. -/
theorem failure_weight_le_inverse {N K : ℕ} (hN : 0 < N)
    (hK : (N : ℝ) ≤ ((4 : ℝ) / 3) ^ K) :
    ((3 : ℝ) / 4) ^ K ≤ (N : ℝ)⁻¹ := by
  have h34 : ((3 : ℝ) / 4) = (((4 : ℝ) / 3)⁻¹) := by norm_num
  rw [h34, inv_pow]
  exact inv_anti₀ (by exact_mod_cast hN) hK

/-- There is a finite repetition count reaching failure weight `1/N`, the
`O(log |U|)` of the Corollary 2.2 amplification. -/
theorem exists_repetition_count (N : ℕ) (hN : 0 < N) :
    ∃ K : ℕ, ((3 : ℝ) / 4) ^ K ≤ (N : ℝ)⁻¹ := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (N : ℝ) (by norm_num : (1 : ℝ) < 4 / 3)
  exact ⟨K, failure_weight_le_inverse hN hK.le⟩

/-- Backward parameter accounting of `SearchAll`: if a successful round
decreases the parameter by at least one (`ts (j+1) + 1 ≤ ts j`) and the final
successful round has parameter at least one, then the `j`-th successful round
has parameter at least `s - j`.  This is the paper's
`t_{i_{T-j}} ≥ t_{i_{T-j+1}} + 1` argument. -/
theorem success_parameter_lower_bound (s : ℕ) (ts : ℕ → ℕ)
    (hstep : ∀ j, j + 1 < s → ts (j + 1) + 1 ≤ ts j)
    (hlast : 1 ≤ ts (s - 1)) :
    ∀ j, j < s → s - j ≤ ts j := by
  have key : ∀ k, ∀ j, j + k = s - 1 → k + 1 ≤ ts j := by
    intro k
    induction k with
    | zero =>
        intro j hj
        have hjs : j = s - 1 := by omega
        rw [hjs]
        simpa using hlast
    | succ k ih =>
        intro j hj
        have hj' : j + 1 + k = s - 1 := by omega
        have hnext := ih (j + 1) hj'
        have hstepj := hstep j (by omega)
        omega
  intro j hj
  obtain ⟨k, hk⟩ : ∃ k, j + k = s - 1 := ⟨s - 1 - j, by omega⟩
  have := key k j hk
  omega

/-- The telescoping inequality `1/√(k+1) ≤ 2(√(k+1) - √k)`. -/
theorem one_div_sqrt_succ_le (k : ℕ) :
    1 / Real.sqrt ((k : ℝ) + 1) ≤
      2 * (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ)) := by
  have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have h1 : (0 : ℝ) < (k : ℝ) + 1 := by linarith
  have hpos : 0 < Real.sqrt ((k : ℝ) + 1) := Real.sqrt_pos.2 h1
  rw [div_le_iff₀ hpos]
  have ha : Real.sqrt ((k : ℝ) + 1) ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt h1.le
  have hb : Real.sqrt (k : ℝ) ^ 2 = (k : ℝ) := Real.sq_sqrt hk
  nlinarith [ha, hb, sq_nonneg (Real.sqrt ((k : ℝ) + 1) - Real.sqrt (k : ℝ)),
    Real.sqrt_nonneg ((k : ℝ) + 1), Real.sqrt_nonneg (k : ℝ)]

/-- Summing the telescoping inequality gives the classic `2√s` bound on the
successful-round cost. -/
theorem sum_one_div_sqrt_range (s : ℕ) :
    (∑ j ∈ Finset.range s, 1 / Real.sqrt ((j : ℝ) + 1)) ≤ 2 * Real.sqrt (s : ℝ) := by
  have h := Finset.sum_le_sum (fun k (_ : k ∈ Finset.range s) => one_div_sqrt_succ_le k)
  calc
    (∑ j ∈ Finset.range s, 1 / Real.sqrt ((j : ℝ) + 1))
        ≤ ∑ j ∈ Finset.range s,
            2 * (Real.sqrt ((j : ℝ) + 1) - Real.sqrt (j : ℝ)) := h
    _ = 2 * ∑ j ∈ Finset.range s,
            (Real.sqrt ((j : ℝ) + 1) - Real.sqrt (j : ℝ)) := by
          rw [Finset.mul_sum]
    _ = 2 * (Real.sqrt (s : ℝ) - Real.sqrt (0 : ℝ)) := by
          congr 1
          simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] using
            (Finset.sum_range_sub (fun n : ℕ => Real.sqrt (n : ℝ)) s)
    _ = 2 * Real.sqrt (s : ℝ) := by norm_num

/-- Successful rounds of `SearchAll` cost at most `2√(N s)`: the paper's
Cauchy--Schwarz-led estimate, here via backward parameters and telescoping. -/
theorem success_phase_cost {N s : ℕ} (ts : ℕ → ℕ)
    (hstep : ∀ j, j + 1 < s → ts (j + 1) + 1 ≤ ts j)
    (hlast : 1 ≤ ts (s - 1)) :
    (∑ j ∈ Finset.range s, Real.sqrt ((N : ℝ) / (ts j : ℝ))) ≤
      2 * Real.sqrt ((N : ℝ) * s) := by
  have hparam : ∀ j, j < s → s - j ≤ ts j :=
    success_parameter_lower_bound s ts hstep hlast
  have hpos : ∀ j, j < s → 0 < ts j := by
    intro j hj
    have := hparam j hj
    omega
  have hbound : (∑ j ∈ Finset.range s, Real.sqrt ((N : ℝ) / (ts j : ℝ))) ≤
      ∑ j ∈ Finset.range s, Real.sqrt ((N : ℝ) / ((s - j : ℕ) : ℝ)) := by
    apply Finset.sum_le_sum
    intro j hj
    apply Real.sqrt_le_sqrt
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg N)
    · have hj' : j < s := Finset.mem_range.mp hj
      exact_mod_cast (by omega : 0 < s - j)
    · exact_mod_cast hparam j (Finset.mem_range.mp hj)
  have hreindex : (∑ j ∈ Finset.range s, Real.sqrt ((N : ℝ) / ((s - j : ℕ) : ℝ))) =
      ∑ j ∈ Finset.range s, Real.sqrt ((N : ℝ) / ((j : ℝ) + 1)) := by
    rw [← Finset.sum_range_reflect (fun k => Real.sqrt ((N : ℝ) / ((k : ℝ) + 1))) s]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j < s := Finset.mem_range.mp hj
    have hcast : ((s - 1 - j : ℕ) : ℝ) + 1 = ((s - j : ℕ) : ℝ) := by
      have hn : s - 1 - j + 1 = s - j := by omega
      calc
        ((s - 1 - j : ℕ) : ℝ) + 1 = ((s - 1 - j + 1 : ℕ) : ℝ) := by push_cast; ring
        _ = ((s - j : ℕ) : ℝ) := by rw [hn]
    rw [hcast]
  have hfactor : (∑ j ∈ Finset.range s, Real.sqrt ((N : ℝ) / ((j : ℝ) + 1))) =
      Real.sqrt (N : ℝ) * ∑ j ∈ Finset.range s, 1 / Real.sqrt ((j : ℝ) + 1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    have hj1 : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    rw [show (N : ℝ) / ((j : ℝ) + 1) = (N : ℝ) * (1 / ((j : ℝ) + 1)) by ring]
    rw [Real.sqrt_mul (Nat.cast_nonneg N), Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1)]
    simp
  calc
    (∑ j ∈ Finset.range s, Real.sqrt ((N : ℝ) / (ts j : ℝ)))
        ≤ ∑ j ∈ Finset.range s, Real.sqrt ((N : ℝ) / ((s - j : ℕ) : ℝ)) := hbound
    _ = ∑ j ∈ Finset.range s, Real.sqrt ((N : ℝ) / ((j : ℝ) + 1)) := hreindex
    _ = Real.sqrt (N : ℝ) * ∑ j ∈ Finset.range s, 1 / Real.sqrt ((j : ℝ) + 1) := hfactor
    _ ≤ Real.sqrt (N : ℝ) * (2 * Real.sqrt (s : ℝ)) := by
          exact mul_le_mul_of_nonneg_left (sum_one_div_sqrt_range s) (Real.sqrt_nonneg _)
    _ = 2 * Real.sqrt ((N : ℝ) * s) := by
          rw [Real.sqrt_mul (Nat.cast_nonneg N)]
          ring

/-- Halving ledger of the unsuccessful rounds: if `t` starts at `N`, at most
halves between successive unsuccessful rounds (successful rounds only decrease
`t` further), and stays at least `1` for `F` rounds, then `F ≤ log₂ N + 1`. -/
theorem halving_failure_count {N F : ℕ} (hN : 0 < N) (t : ℕ → ℕ) (h0 : t 0 = N)
    (hstep : ∀ i, t (i + 1) ≤ t i / 2) (hpos : ∀ i, i < F → 1 ≤ t i) :
    F ≤ Nat.log2 N + 1 := by
  have hle : ∀ i, t i ≤ N / 2 ^ i := by
    intro i
    induction i with
    | zero => simpa using h0.le
    | succ i ih =>
        calc
          t (i + 1) ≤ t i / 2 := hstep i
          _ ≤ (N / 2 ^ i) / 2 := Nat.div_le_div_right ih
          _ = N / 2 ^ (i + 1) := by rw [Nat.div_div_eq_div_mul, ← pow_succ]
  have hnonempty : F = 0 ∨ 0 < F := Nat.eq_zero_or_pos F
  rcases hnonempty with hF | hF
  · omega
  · have hi : F - 1 < F := by omega
    have h1 : 1 ≤ N / 2 ^ (F - 1) := (hpos (F - 1) hi).trans (hle (F - 1))
    have h2 : 1 * 2 ^ (F - 1) ≤ N := (Nat.le_div_iff_mul_le (pow_pos (by norm_num) _)).mp h1
    have h3 : F - 1 ≤ Nat.log2 N := (Nat.le_log2 (Nat.ne_of_gt hN)).mpr (by simpa using h2)
    omega

/-- Cost ledger of Corollary 2.3: `F` unsuccessful rounds of cost at most `√N`
each, plus `2√(N s)` for the successful rounds, is at most
`(F + 2)√(N (s + 1))`. -/
theorem searchAll_ledger_bound {N s F : ℕ} (hN : 1 ≤ N) :
    (F : ℝ) * Real.sqrt (N : ℝ) + 2 * Real.sqrt ((N : ℝ) * s) ≤
      ((F : ℝ) + 2) * Real.sqrt ((N : ℝ) * (s + 1)) := by
  have hNs : (N : ℝ) ≤ (N : ℝ) * (s + 1) := by
    have : (0 : ℝ) ≤ (N : ℝ) * s := by positivity
    nlinarith
  have hroot : Real.sqrt (N : ℝ) ≤ Real.sqrt ((N : ℝ) * (s + 1)) :=
    Real.sqrt_le_sqrt hNs
  have hrootN : Real.sqrt ((N : ℝ) * s) ≤ Real.sqrt ((N : ℝ) * (s + 1)) := by
    apply Real.sqrt_le_sqrt
    have : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith
  have hF : (0 : ℝ) ≤ (F : ℝ) := Nat.cast_nonneg F
  nlinarith

/-- `SearchAll` cost bound of Corollary 2.3: after the halving ledger, the
total is at most `(log₂ N + 3)√(N (s + 1))`, i.e. `Õ(√(|U| (t_f + 1)))`. -/
theorem searchAll_cost_bound {N s F : ℕ} (hN : 0 < N)
    (hF : F ≤ Nat.log2 N + 1) :
    (F : ℝ) * Real.sqrt (N : ℝ) + 2 * Real.sqrt ((N : ℝ) * s) ≤
      (Nat.log2 N + 3 : ℝ) * Real.sqrt ((N : ℝ) * (s + 1)) := by
  have h1 : (F : ℝ) * Real.sqrt (N : ℝ) + 2 * Real.sqrt ((N : ℝ) * s) ≤
      ((F : ℝ) + 2) * Real.sqrt ((N : ℝ) * (s + 1)) :=
    searchAll_ledger_bound (by omega : 1 ≤ N)
  have h2 : ((F : ℝ) + 2) * Real.sqrt ((N : ℝ) * (s + 1)) ≤
      (Nat.log2 N + 3 : ℝ) * Real.sqrt ((N : ℝ) * (s + 1)) := by
    have hcast : (F : ℝ) + 2 ≤ (Nat.log2 N : ℝ) + 3 := by
      have : (F : ℝ) ≤ (Nat.log2 N + 1 : ℕ) := by exact_mod_cast hF
      push_cast at this
      linarith
    exact mul_le_mul_of_nonneg_right hcast (Real.sqrt_nonneg _)
  exact h1.trans h2

end Qatlib.Papers.BoolMatMult11.MainResults.SearchCore
