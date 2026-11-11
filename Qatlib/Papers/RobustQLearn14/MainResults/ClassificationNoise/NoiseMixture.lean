/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic

set_option backward.isDefEq.respectTransparency false

/-!
# RobustQLearn14.MainResults.ClassificationNoise — classification noise does not hurt

Fixed source: Cross--Smith--Smolin, *Quantum learning robust to noise*,
arXiv:1407.5088v1 (18 Jul 2014).

Claim `c004` (Sec. IV A, Eq. (8), p. 3): with the result qubit flipped by `σ_x`
with probability `η`, the Hadamard-transformed oracle output is the mixture of
Eq. (7), `(1/√2)(|0^n,0⟩+|a,1⟩)`, with probability `1-η`, and of Eq. (8),
`(1/√2)(|0^n,1⟩+|a,0⟩)`, with probability `η`.  In *both* branches the query
register contains `a` with probability `1/2`, so the per-query probability is
`1/2` independent of `η`.  Repeating `k` queries, the probability of observing
`a` at least once is `1 - (1/2)^k`, and the failure probability `(1/2)^k` is
exponentially small in `k` and independent of `n`.

This file records the mixture algebra and the exact finite counting statement
for `k` independent rounds.
-/

namespace Qatlib.Papers.RobustQLearn14.MainResults

noncomputable section

/-! ## Per-query mixture -/

/-- `c004`: probability that the query register contains `a` when the output is
the classification-noise mixture.  Source: arXiv:1407.5088v1, Sec. IV A, p. 3
("the probability that the query register contains a remains 1/2, independent
of η"). -/
def perQueryQueryRegisterProb (η : ℝ) : ℝ :=
  (1 - η) * (1 / 2) + η * (1 / 2)

/-- The mixture probability is exactly `1/2`, independent of `η`.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3 (mixture of Eqs. (7) and (8)). -/
theorem perQueryQueryRegisterProb_eq (η : ℝ) : perQueryQueryRegisterProb η = 1 / 2 := by
  unfold perQueryQueryRegisterProb
  ring

/-- Failure of a single query: the observed query register is not `a`.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3 (complement of the `1/2` event). -/
def perQueryFailureProb (η : ℝ) : ℝ := 1 - perQueryQueryRegisterProb η

/-- Per-query failure probability is `1/2` for every noise rate `η`.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3 (complement of the `1/2` event). -/
theorem perQueryFailureProb_eq (η : ℝ) : perQueryFailureProb η = 1 / 2 := by
  unfold perQueryFailureProb
  rw [perQueryQueryRegisterProb_eq]
  norm_num

/-! ## `k` independent rounds -/

/-- The failure event over `k` rounds: no round shows `a`.  Modelled on the
`k`-element Boolean cube, one bit per round.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3 (`k` independent repetitions). -/
def kRoundFailureProb (k : ℕ) : ℚ :=
  ((Finset.univ.filter (fun s : Fin k → Bool => ∀ i, s i = false)).card : ℚ) /
    (2 : ℚ) ^ k

/-- The success event over `k` rounds: at least one round shows `a`.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3 (`k` independent repetitions). -/
def kRoundSuccessProb (k : ℕ) : ℚ :=
  ((Finset.univ.filter (fun s : Fin k → Bool => ∃ i, s i = true)).card : ℚ) /
    (2 : ℚ) ^ k

/-- The all-false outcomes form the singleton of the constant-false string.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3 (failure event of `k` rounds). -/
theorem allFalse_filter_eq (k : ℕ) :
    (Finset.univ.filter (fun s : Fin k → Bool => ∀ i, s i = false)) =
      ({fun _ => false} : Finset (Fin k → Bool)) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    exact h i
  · intro h i
    rw [h]

/-- The success outcomes are the complement of the all-false outcomes.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3 (success event of `k` rounds). -/
theorem success_filter_eq_sdiff (k : ℕ) :
    (Finset.univ.filter (fun s : Fin k → Bool => ∃ i, s i = true)) =
      Finset.univ \ (Finset.univ.filter (fun s : Fin k → Bool => ∀ i, s i = false)) := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
  constructor
  · rintro ⟨i, hi⟩ hall
    have hf : s i = false := hall i
    rw [hi] at hf
    cases hf
  · intro h
    by_contra hnone
    apply h
    intro i
    cases hs : s i with
    | false => rfl
    | true => exact absurd ⟨i, hs⟩ hnone

/-- Number of `k`-round failure outcomes is `1`.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3 (only the all-false outcome fails). -/
theorem allFalse_filter_card (k : ℕ) :
    (Finset.univ.filter (fun s : Fin k → Bool => ∀ i, s i = false)).card = 1 := by
  rw [allFalse_filter_eq]
  simp

/-- Number of `k`-round success outcomes is `2^k - 1`.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3 (all but one of `2^k` outcomes). -/
theorem success_filter_card (k : ℕ) :
    (Finset.univ.filter (fun s : Fin k → Bool => ∃ i, s i = true)).card = 2 ^ k - 1 := by
  rw [success_filter_eq_sdiff k, Finset.card_sdiff_of_subset (Finset.filter_subset _ _),
    allFalse_filter_card, Finset.card_univ, Fintype.card_pi_const, Fintype.card_bool]

/-- `c004`: after `k` queries the failure probability is exactly `(1/2)^k`,
exponentially small in `k` and independent of `n`.  Source:
arXiv:1407.5088v1, Sec. IV A, p. 3. -/
theorem kRoundFailureProb_eq (k : ℕ) : kRoundFailureProb k = (1 / 2 : ℚ) ^ k := by
  unfold kRoundFailureProb
  rw [allFalse_filter_card, div_eq_mul_inv, Nat.cast_one, one_mul, ← inv_pow]
  rw [show (2 : ℚ)⁻¹ = 1 / 2 by norm_num]

/-- `c004`: after `k` queries the success probability is `1 - (1/2)^k`.
Source: arXiv:1407.5088v1, Sec. IV A, p. 3. -/
theorem kRoundSuccessProb_eq (k : ℕ) : kRoundSuccessProb k = 1 - (1 / 2 : ℚ) ^ k := by
  unfold kRoundSuccessProb
  rw [success_filter_card]
  have hle : 1 ≤ 2 ^ k := by
    induction k with
    | zero => norm_num
    | succ m ih =>
        rw [pow_succ]
        have h2m : (0 : ℕ) ≤ 2 ^ m := Nat.zero_le _
        nlinarith
  rw [Nat.cast_sub hle, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
  rw [show (1 / 2 : ℚ) = (2 : ℚ)⁻¹ by norm_num, inv_pow]
  rw [sub_div, div_self (pow_ne_zero k (by norm_num : (2 : ℚ) ≠ 0)), one_div]

end

end Qatlib.Papers.RobustQLearn14.MainResults
