/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.PeriodSampling.OrderRecovery.RandomBaseFactor

set_option backward.isDefEq.respectTransparency false

/-!
# NumTheory12.MainResults — Lemma 1 (Miller's success probability)

Source: Wim van Dam and Yoshitaka Sasaki, *Quantum algorithms for problems in
number theory, algebraic geometry, and group theory*, fixed arXiv:1206.6126
(2012). Lemma 1, §3.1, page 5 (line 128 of the pinned text).

Paper statement. Let `a` be chosen uniformly at random from `(ℤ/Nℤ)ˣ`, where
`N` is an odd integer with at least two distinct prime factors. Then with
probability at least `1/2` the multiplicative order `r` of `a` modulo `N` is
even and `a^{r/2} ≢ −1 (mod N)`.

The formalization separates the event and its probability:

* `lemma1_event_characterization` — the *event* "`r` even and `a^{r/2} ≠ −1`" is
  exactly the success event of the checked factor program
  (`randomBaseGood`), via `random_base_exact_order_factor_characterization`;
* `lemma1_success_probability` — under the uniform law on `(ZMod N)ˣ` the
  success mass is at least `1/2`, obtained from the counting bound
  `random_base_crt_success_bound` at `k = 2` prime factors;
* `lemma1_probability_of_characterized_event` — the same bound written directly
  for the paper's event `{a | Even (orderOf a) ∧ a^{orderOf a/2} ≠ −1}`.

Both dependencies live in
`Qatlib.Papers.ShorFactoring97.OrderRecovery`.
The uniform distribution is Mathlib's `Fintype` counting
measure on `(ZMod N)ˣ`; no sampling oracle is postulated.
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.NumTheory12.MainResults

open Qatlib.Concepts.PeriodSampling.OrderRecovery

/-- **Lemma 1, event** (arXiv:1206.6126, p. 5): for odd `1 < N` and a unit
`a : (ZMod N)ˣ`, the checked factor program succeeds (`randomBaseGood N a`) iff
the order `orderOf a` is even and `a^{orderOf a / 2} : ZMod N` is not `−1`.

Uses the theorem
`Qatlib.Papers.ShorFactoring97.OrderRecovery.random_base_exact_order_factor_characterization`. -/
theorem lemma1_event_characterization (N : ℕ) [NeZero N] (a : (ZMod N)ˣ)
    (hN : 1 < N) (hodd : Odd N) :
    randomBaseGood N a ↔ Even (orderOf a) ∧
      ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1 :=
  random_base_exact_order_factor_characterization N a hN hodd

/-- **Lemma 1, probability bound** (arXiv:1206.6126, p. 5): if `N` is odd, `1 < N`
and `N` has at least two distinct prime factors, then a uniformly random unit
`a : (ZMod N)ˣ` succeeds — i.e. `orderOf a` is even and `a^{orderOf a/2} ≠ −1`
— with probability at least `1/2`.

`randomBaseSuccess N` is the uniform success mass
`|(ZMod N)ˣ|⁻¹ · |{a | randomBaseGood N a}|`. The proof instantiates the
counting bound `random_base_crt_success_bound` at
`k = N.primeFactors.card ≥ 2` and bounds `2^{-(k-1)} ≤ 1/2`. -/
theorem lemma1_success_probability (N : ℕ) [NeZero N] (hN : 1 < N) (hodd : Odd N)
    (hk : 2 ≤ N.primeFactors.card) :
    (1 / 2 : ℝ) ≤ randomBaseSuccess N := by
  have hbound := random_base_crt_success_bound N hN hodd hk
  have hle : -(N.primeFactors.card - 1 : ℤ) ≤ (-1 : ℤ) := by
    have hkz : (2 : ℤ) ≤ (N.primeFactors.card : ℤ) := by exact_mod_cast hk
    omega
  have hpow : (2 : ℝ) ^ (-(N.primeFactors.card - 1 : ℤ)) ≤ (1 / 2 : ℝ) := by
    have h := (zpow_le_zpow_iff_right₀ (a := (2 : ℝ)) (by norm_num)).mpr hle
    have h2 : (2 : ℝ) ^ (-1 : ℤ) = 1 / 2 := by norm_num
    rwa [h2] at h
  nlinarith

/-- **Lemma 1, paper event** (arXiv:1206.6126, p. 5): explicitly for the event
`{a : (ZMod N)ˣ | Even (orderOf a) ∧ a^{orderOf a/2} ≠ −1}`, its uniform
probability is at least `1/2`.

This is `lemma1_success_probability` after rewriting the success set through
`lemma1_event_characterization`. -/
theorem lemma1_probability_of_characterized_event (N : ℕ) [NeZero N]
    (hN : 1 < N) (hodd : Odd N) (hk : 2 ≤ N.primeFactors.card) :
    (1 / 2 : ℝ) ≤ (Fintype.card ((ZMod N)ˣ) : ℝ)⁻¹ *
      ((Finset.univ.filter (fun a : (ZMod N)ˣ =>
        Even (orderOf a) ∧
          ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1)).card : ℝ) := by
  classical
  have hgood := lemma1_success_probability N hN hodd hk
  have hset : (Finset.univ.filter (fun a : (ZMod N)ˣ => randomBaseGood N a)) =
      Finset.univ.filter (fun a : (ZMod N)ˣ =>
        Even (orderOf a) ∧
          ((a ^ (orderOf a / 2) : (ZMod N)ˣ) : ZMod N) ≠ -1) := by
    apply Finset.filter_congr
    intro a _
    exact lemma1_event_characterization N a hN hodd
  unfold randomBaseSuccess at hgood
  rw [hset] at hgood
  exact hgood

end Qatlib.Papers.NumTheory12.MainResults
