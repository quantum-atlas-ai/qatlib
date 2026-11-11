/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# GrandUnif21 Theorem 6 — exactness when `n ≥ m`

Source: arXiv:2105.02859v3, Theorem 6 (Sec. V A 2, metadata line 831).

If the target phase is an `m`-bit number and the algorithm runs `n ≥ m`
iterations (and the QSVT sign function is implemented exactly), then at the end
of the procedure `θ = φ` exactly — no rounding error is incurred because every
rounding step is exact on representable inputs.

Two paper-layer statements:

* `source_theorem6_tail`: the final value `thetaIter` equals the `m`-bit
  fraction `0.φ₁…φ_m`, i.e. the trailing zero digits of the `n`-bit expansion
  add nothing (Lemma 11 plus `binFrac_eq_of_bits_zero`);
* `source_theorem6_exact`: nearest-`n`-bit rounding is the identity on
  numbers representable with `m ≤ n` bits.

Boundary: the arithmetic exactness only; the hypothesis "the sign function can
be implemented exactly through QSVT" is not represented (it is the same
assumption that makes every iteration exact in the paper).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation

/-- GrandUnif21 Theorem 6 (arXiv:2105.02859v3, metadata line 831): if all
digits of `φ` beyond the `m`-th vanish and `n ≥ m`, the final phase register
after `n` iterations is exactly the `m`-bit fraction `φ = 0.φ₁…φ_m`. -/
theorem source_theorem6_tail (φ : ℕ → Bool) {m n : ℕ} (hmn : m ≤ n)
    (hbits : ∀ i, m < i → φ i = false) :
    thetaIter φ n n = binFrac φ m := by
  have h1 : thetaIter φ n n = tailFrac φ 0 n := by
    have h := thetaIter_eq_tailFrac φ n n (le_refl n)
    simpa using h
  rw [h1, tailFrac_eq φ (Nat.zero_le n), binFrac_eq_of_bits_zero hmn hbits]
  simp [binFrac]

/-- GrandUnif21 Theorem 6, rounding form: if `Φ` is an `m`-bit number and
`n ≥ m`, rounding `Φ` to `n` binary places returns `Φ` unchanged — the reason
the procedure makes no error at all in the `n ≥ m` case. -/
theorem source_theorem6_exact {Φ : ℝ} {m n : ℕ} (hmn : m ≤ n) {N : ℤ}
    (hΦ : Φ = (N : ℝ) / (2 : ℝ) ^ m) : roundDyadic n Φ = Φ := by
  refine roundDyadic_eq_of_int (N := N * (2 : ℤ) ^ (n - m)) ?_
  have hsplit : (2 : ℝ) ^ n = (2 : ℝ) ^ m * (2 : ℝ) ^ (n - m) := by
    rw [← pow_add, Nat.add_sub_cancel' hmn]
  rw [hΦ, hsplit]
  have hm : (2 : ℝ) ^ m ≠ 0 := by positivity
  push_cast
  field_simp

end Qatlib.Papers.GrandUnif21.MainResults.PhaseEstimation
