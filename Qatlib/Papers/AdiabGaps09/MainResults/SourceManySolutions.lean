/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.AdiabGaps09.MainResults.ManySolutions

@[expose] public section



set_option backward.isDefEq.respectTransparency false

/-!
# SourceManySolutions — `k` disparate solutions and polynomial retries

Fixed arXiv:0909.4766v2, Section III, pages 12–14, equations (10)–(13).

When there are `k` mutually disparate satisfying assignments and all but one are
penalized, the second-order corrections satisfy

```
e_r^(2) - e_0^(2) = Σ_{i=1}^n d_{ri} ,                                    (Eq. 10–11 base)
```

and after randomizing the beginning Hamiltonian (`c_i ∈ {1/2,3/2}`, `P = 1/2`)

```
ẽ_r^(2) - ẽ_0^(2) = Σ_{i=1}^n c_i^2 d_{ri} .                             (Eq. 11)
```

The algorithm succeeds iff all `k-1` differences are positive.  The paper shows
that, for large `n`, the differences are approximately jointly Gaussian with
pairwise correlation `1/2` (equation 12), and hence

* the probability that a random draw `{c_i}` succeeds is at worst polynomially
  small in `k` (equation 13 and the tail estimates on page 15);
* therefore a number of randomizations polynomial in `k` yields success with high
  probability.

This module models the differences, defines the success event and its uniform
probability, and proves a polynomial lower bound under an explicit positive-cone
condition on the coefficient rows. This condition is stronger than the paper's
Gaussian assumptions and the result does not establish the general Gaussian claim.
-/

set_option autoImplicit false
noncomputable section

open Finset Filter
open scoped BigOperators

open Qatlib.Papers.AdiabGaps09.MainResults.ManySolutions

namespace Qatlib.Papers.AdiabGaps09.MainResults.ManySolutions

/-- The squared random coefficient `c_i^2` (`1/4` or `9/4` with probability
`1/2`). -/
def cSq (b : Bool) : ℝ := if b then (9 / 4 : ℝ) else (1 / 4 : ℝ)

/-- The single-index randomized difference `Σ_i c_i^2 d_i` (the `k = 1` case). -/
def secondOrderGap {n : ℕ} (d : Fin n → ℝ) (z : Fin n → Bool) : ℝ :=
  ∑ i, cSq (z i) * d i

/-- Under an eventual positive-cone condition on every coefficient row, every Boolean
configuration succeeds and the success probability has a polynomial lower bound. The unrestricted
claim is false for identically zero coefficients. This is a restricted algebraic sufficient
condition, rather than the paper's joint-Gaussian approximation. -/
theorem success_probability_polynomial (d : (n k : ℕ) → Fin k → Fin n → ℝ)
    (hpos : ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ r i, 0 ≤ d n k r i) ∧ ∀ r, 0 < ∑ i, d n k r i) :
    ∃ C c : ℕ, 0 < C ∧ ∀ k : ℕ, 1 ≤ k → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (1 : ℝ) / ((C : ℝ) * (k : ℝ) ^ c) ≤ successFraction (d n k) := by
  classical
  refine ⟨1, 0, by omega, ?_⟩
  intro k hk
  obtain ⟨N, hN⟩ := hpos k hk
  refine ⟨N, ?_⟩
  intro n hn
  obtain ⟨hnonneg, hsum⟩ := hN n hn
  have hsucc : ∀ z : Fin n → Bool, MultiSuccess (d n k) z := by
    intro z r
    have hbound : (1 / 4 : ℝ) * (∑ i, d n k r i) ≤ multiGap (d n k) z r := by
      unfold multiGap
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro i _
      have hweight : (1 / 4 : ℝ) ≤
          Qatlib.Papers.AdiabGaps09.MainResults.cSq (z i) := by
        cases z i <;> norm_num [Qatlib.Papers.AdiabGaps09.MainResults.cSq]
      exact mul_le_mul_of_nonneg_right hweight (hnonneg r i)
    exact lt_of_lt_of_le (mul_pos (by norm_num) (hsum r)) hbound
  have hfrac : successFraction (d n k) = 1 := by
    unfold successFraction
    simp only [hsucc, Finset.filter_true, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
    exact div_self (ne_of_gt (pow_pos (by norm_num : (0 : ℝ) < 2) n))
  simp [hfrac]

/-- Constant unit coefficient rows satisfy the primitive positive-cone premise once the
number of coordinates is positive. This supplies a concrete nonempty family of inputs. -/
theorem unitRows_pos (k : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (∀ (_r : Fin k) (_i : Fin n), 0 ≤ (1 : ℝ)) ∧
        ∀ _r : Fin k, 0 < ∑ _i : Fin n, (1 : ℝ) := by
  refine ⟨1, ?_⟩
  intro n hn
  constructor
  · intro _ _
    norm_num
  · intro _
    have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
    simpa using hpos

/-- Zero coefficients make every single-row weighted gap zero, so the strict success
event is empty. Thus arbitrary coefficient arrays cannot satisfy the original lower bound. -/
theorem zeroRow_fail (n : ℕ) :
    successFraction (fun (_r : Fin 1) (_i : Fin n) => (0 : ℝ)) = 0 := by
  classical
  have hnot : ∀ z : Fin n → Bool,
      ¬ MultiSuccess (fun (_r : Fin 1) (_i : Fin n) => (0 : ℝ)) z := by
    intro z hz
    have hzero := hz (0 : Fin 1)
    simp [multiGap] at hzero
  simp [successFraction, hnot]

end Qatlib.Papers.AdiabGaps09.MainResults.ManySolutions
