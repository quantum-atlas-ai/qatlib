/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt

set_option backward.isDefEq.respectTransparency false

/-!
# Quantum Zeno effect and the circuit success probability

Source: R. D. Somma, S. Boixo, H. Barnum, *Quantum Simulated Annealing*,
fixed arXiv:0712.1008v1 (6 Dec 2007).

This file covers Section III (p.4, the paragraph below Eq. (20)) and
Appendix B, Eq. (B12), p.7.

* Section III / quantum Zeno effect: each adjacent-temperature overlap obeys
  Eq. (18), `|⟨φ0(βk)|φ0(βk−1)⟩|² = 1 − O(ν²)`; after `Q = O(1/ν)` projective
  measurements (PEA calls) the success probability is bounded below by
  `1 − O(ν)`.  The numerical content is Bernoulli's inequality followed by
  `Qν ≤ C`.
* Eq. (B12): `P0 ≥ [(1−O(ν²))^Q − (Q−1)O(ν²)]² ≥ 1 − τ'Qν²`, again with an
  explicit constant `τ' = 4c` for the per-step coefficient `c`.

The constant `c` absorbs the `O(1)` in Eq. (18); no other modeling assumption
is made, and both bounds are sharp statements in terms of `c`.
-/

set_option autoImplicit false
noncomputable section

open scoped Classical BigOperators

namespace Qatlib.Papers.QAnnealing07.MainResults.SourceZeno

/-- Fixed arXiv:0712.1008v1, p.4 (paragraph below Eq. (20)): if each of the
`Q` Zeno projections succeeds with probability at least `1 − cν²` (Eq. (18)),
and `Qν ≤ C` (the `Q = O(1/ν)` choice), then the overall success probability
is at least `1 − cCν = 1 − O(ν)`. -/
theorem zeno_success_probability (ν c C : ℝ) (Q : ℕ)
    (hν : 0 < ν) (hc : 0 ≤ c) (hQν : (Q : ℝ) * ν ≤ C) (hcν : c * ν ^ 2 ≤ 1) :
    1 - c * C * ν ≤ (1 - c * ν ^ 2) ^ Q := by
  have hbern : 1 + (Q : ℝ) * (-(c * ν ^ 2)) ≤ (1 + -(c * ν ^ 2)) ^ Q :=
    one_add_mul_le_pow (a := -(c * ν ^ 2)) (by linarith) Q
  have hQc : (Q : ℝ) * (c * ν ^ 2) ≤ c * C * ν := by
    have hνc : 0 ≤ c * ν := mul_nonneg hc hν.le
    calc (Q : ℝ) * (c * ν ^ 2) = ((Q : ℝ) * ν) * (c * ν) := by ring_nf
      _ ≤ C * (c * ν) := mul_le_mul_of_nonneg_right hQν hνc
      _ = c * C * ν := by ring_nf
  have hbase : (1 + -(c * ν ^ 2)) = 1 - c * ν ^ 2 := by ring_nf
  calc 1 - c * C * ν ≤ 1 - (Q : ℝ) * (c * ν ^ 2) := by linarith
    _ = 1 + (Q : ℝ) * (-(c * ν ^ 2)) := by ring_nf
    _ ≤ (1 + -(c * ν ^ 2)) ^ Q := hbern
    _ = (1 - c * ν ^ 2) ^ Q := by rw [hbase]

/-- Fixed arXiv:0712.1008v1, Eq. (B12), p.7, first inequality: the success
probability of the projected circuit is at least the square of the
`Q`-fold amplitude `(1−cν²)^Q` minus the accumulated `(Q−1)` leakage terms
`(Q−1)cν²`.  Here `c` is the constant inside the paper's `O(ν²)`. -/
theorem eqB12_amplitude_lower_bound (ν c : ℝ) (Q : ℕ)
    (hν : 0 < ν) (hc : 0 ≤ c) (hcν : c * ν ^ 2 ≤ 1) (hQ : 1 ≤ Q) :
    1 - 4 * (Q : ℝ) * c * ν ^ 2 ≤
      ((1 - c * ν ^ 2) ^ Q - ((Q : ℝ) - 1) * (c * ν ^ 2)) ^ 2 := by
  set x := c * ν ^ 2 with hx
  have hx0 : 0 ≤ x := by ring_nf; positivity
  have hx1 : x ≤ 1 := hcν
  have hQ1 : (1 : ℝ) ≤ (Q : ℝ) := by exact_mod_cast hQ
  have hbern : 1 - (Q : ℝ) * x ≤ (1 - x) ^ Q := by
    have h := one_add_mul_le_pow (a := -x) (by linarith) Q
    have hbase : 1 + -x = 1 - x := by ring_nf
    rw [hbase] at h
    linarith [h]
  set base : ℝ := (1 - x) ^ Q - ((Q : ℝ) - 1) * x with hbase_def
  have hbase_lb : 1 - 2 * ((Q : ℝ) * x) ≤ base := by
    have h1 : (1 - x) ^ Q - ((Q : ℝ) - 1) * x
        ≥ 1 - (Q : ℝ) * x - ((Q : ℝ) - 1) * x := by linarith
    have h2 : 1 - (Q : ℝ) * x - ((Q : ℝ) - 1) * x
        = 1 - 2 * ((Q : ℝ) * x) + x := by ring_nf
    rw [hbase_def]
    linarith [h1, h2, hx0]
  have hbase_le : base ≤ 1 := by
    have hp : (1 - x) ^ Q ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
    have hsub : 0 ≤ ((Q : ℝ) - 1) * x := mul_nonneg (by linarith) hx0
    rw [hbase_def]
    linarith
  by_cases hy : (Q : ℝ) * x ≤ 1 / 4
  · have hpos : 0 ≤ 1 - 2 * ((Q : ℝ) * x) := by linarith
    have hsq : (1 - 2 * ((Q : ℝ) * x)) * (1 - 2 * ((Q : ℝ) * x)) ≤ base * base :=
      mul_self_le_mul_self hpos hbase_lb
    have hsq2 : 1 - 4 * (Q : ℝ) * x ≤ (1 - 2 * ((Q : ℝ) * x)) ^ 2 := by
      nlinarith [sq_nonneg ((Q : ℝ) * x)]
    calc 1 - 4 * (Q : ℝ) * c * ν ^ 2 = 1 - 4 * (Q : ℝ) * x := by rw [hx]; ring_nf
      _ ≤ (1 - 2 * ((Q : ℝ) * x)) ^ 2 := hsq2
      _ = (1 - 2 * ((Q : ℝ) * x)) * (1 - 2 * ((Q : ℝ) * x)) := by ring_nf
      _ ≤ base * base := hsq
      _ = base ^ 2 := by ring_nf
  · have hgt : 1 / 4 < (Q : ℝ) * x := lt_of_not_ge hy
    have hneg : 1 - 4 * (Q : ℝ) * x < 0 := by linarith
    have hsq0 : 0 ≤ base ^ 2 := sq_nonneg base
    calc 1 - 4 * (Q : ℝ) * c * ν ^ 2 = 1 - 4 * (Q : ℝ) * x := by rw [hx]; ring_nf
      _ ≤ 0 := le_of_lt hneg
      _ ≤ base ^ 2 := hsq0

/-- Fixed arXiv:0712.1008v1, Eq. (B12), p.7, second inequality: with
`x = cν²`, the bound `[(1−x)^Q − (Q−1)x]² ≥ 1 − 4Qx` is the paper's
`P0 ≥ 1 − τ'Qν²` with the explicit constant `τ' = 4c`. -/
theorem eqB12_success_lower_bound (ν c : ℝ) (Q : ℕ)
    (hν : 0 < ν) (hc : 0 ≤ c) (hcν : c * ν ^ 2 ≤ 1) (hQ : 1 ≤ Q) :
    1 - 4 * c * (Q : ℝ) * ν ^ 2 ≤
      ((1 - c * ν ^ 2) ^ Q - ((Q : ℝ) - 1) * (c * ν ^ 2)) ^ 2 := by
  have h := eqB12_amplitude_lower_bound ν c Q hν hc hcν hQ
  calc 1 - 4 * c * (Q : ℝ) * ν ^ 2 = 1 - 4 * (Q : ℝ) * c * ν ^ 2 := by ring_nf
    _ ≤ _ := h

end Qatlib.Papers.QAnnealing07.MainResults.SourceZeno
