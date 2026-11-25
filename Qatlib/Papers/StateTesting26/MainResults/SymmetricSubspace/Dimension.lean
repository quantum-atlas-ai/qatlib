/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Qatlib.Papers.StateTesting26.MainResults.Model.StateModel

@[expose] public section

/-!
# The dimension of the symmetric subspace

Definition 2.4 of the paper uses the symbol `d^[n]` for the dimension of the symmetric subspace
`∨^n ℂ^d`, and states that this dimension is `choose (d + n - 1) n`. The model layer keeps both
readings separate: `Qatlib.Papers.StateTesting26.MainResults.Model.dPowRising` is the rising
factorial `d(d+1)…(d+n-1)` and `Qatlib.Papers.StateTesting26.MainResults.Model.dimSym` is the
binomial coefficient.

The two are *not* equal: already for `d = n = 2` the rising factorial is `6` while the binomial
coefficient is `3`. What holds, and is what the moment computations of Lemma 2.5 actually need, is
that the rising factorial is `n!` times the dimension. This module proves that identity
(`factorial_mul_dimSym_eq_dPowRising`) together with the explicit counterexample witnessing the
discrepancy, so that the factor `n!` is not silently dropped. (The `n!` is exactly the normalising
constant of the symmetric projector in Eq. (2.5).)

Paper: [arXiv:2604.07460v2](https://arxiv.org/abs/2604.07460v2), Definition 2.4 and Eq. (2.5).
-/

set_option autoImplicit false

namespace Qatlib.Papers.StateTesting26.MainResults.SymmetricSubspace

open Qatlib.Papers.StateTesting26.MainResults.Model

/-- **Definition 2.4, corrected form**: the rising factorial `d^[k]` is `k!` times the dimension
`choose (d + k - 1) k` of the symmetric subspace `∨^k ℂ^d`. -/
theorem factorial_mul_dimSym_eq_dPowRising (d k : ℕ) :
    k.factorial * dimSym d k = dPowRising d k := by
  rw [dimSym, dPowRising, ← Nat.ascFactorial_eq_factorial_mul_choose' d k,
    Nat.ascFactorial_eq_prod_range]

/-- The dimension of `∨² ℂ²` is `3`. -/
theorem dimSym_two_two : dimSym 2 2 = 3 := by
  decide

/-- The rising factorial `2^[2] = 2 · 3` is `6`. -/
theorem dPowRising_two_two : dPowRising 2 2 = 6 := by
  decide

/-- The rising factorial and the symmetric-subspace dimension differ already at `d = k = 2`, so
`dPowRising d k = dimSym d k` is false in general; the correct relation carries the factor
`k!`. -/
theorem dPowRising_two_two_ne_dimSym_two_two : dPowRising 2 2 ≠ dimSym 2 2 := by
  rw [dPowRising_two_two, dimSym_two_two]
  norm_num

end Qatlib.Papers.StateTesting26.MainResults.SymmetricSubspace
