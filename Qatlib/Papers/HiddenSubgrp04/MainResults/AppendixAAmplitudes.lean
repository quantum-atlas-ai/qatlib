/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Group.DivInvMonoid
import Mathlib.Algebra.Group.Monoid
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Ring.Nat
import Mathlib.Algebra.Ring.Parity
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Basic.Complex.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.SetLike.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Finset.Filter
import Mathlib.Data.Finset.Range
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Tactic
import Qatlib.Papers.HiddenSubgrp04.MainResults.Defs

/-!
# Amplitude-estimate propositions for cyclic Fourier approximation

This module defines the propositions `lemma_A7Statement` through `lemma_A10Statement` for
Appendix A amplitude and modular-distance estimates. They express a pointwise bound on `Acoef`,
two reciprocal-distance sum bounds outside cells, and a squared-sum estimate for weighted
modular distances.

The development follows [Lomont2004].

## Main statements

* `lemma_A7Statement`: The proposition bounding the norm of `Acoef` by √(M/(LN)) times 2/π times
  the reciprocal modular distance, under positive size, index, and nonintegral phase-difference
  hypotheses.
* `lemma_A9Statement`: The proposition that the reciprocal modular-distance sum outside the
  cells is at most 4N log(N)/M, for odd N ≥ 13 and M ≥ 16N.
* `lemma_A10Statement`: The proposition bounding the sum over `k` of squared absolute weighted
  sums of modular distances outside cells by 22N log(N)²/M + 32N³/M², for a real vector of
  squared norm one and the supplied size hypotheses.

## References

* [Lomont, 2004][Lomont2004]
-/

set_option warningAsError false

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

/-- The proposition bounding the norm of `Acoef` by √(M/(LN)) times 2/π times the reciprocal
modular distance, under positive size, index, and nonintegral phase-difference hypotheses. -/
def lemma_A7Statement (L M N i k : ℕ) (hL : 0 < L) (hM : 0 < M) (hN : 0 < N)
    (hi : i < N) (hk : k < M)
    (hnotint : ¬ ∃ z : ℤ, (k : ℝ) / (M : ℝ) - (i : ℝ) / (N : ℝ) = (z : ℝ)) : Prop :=
    ‖Acoef L M N i k‖ ≤
      Real.sqrt ((M : ℝ) / ((L : ℝ) * (N : ℝ))) * (2 / Real.pi) *
        (1 / distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)))

/-- The proposition bounding the sum of reciprocal modular distances over indices whose cells
exclude `k` by the displayed logarithmic expression, for odd N > 2 and M > 2N. -/
def lemma_A8Statement (M N k : ℕ) (hN : 2 < N) (hM : 2 * N < M) (hNodd : Odd N)
    (hk : k < M) : Prop :=
    (∑ i ∈ (Finset.range N).filter (fun i => k ∉ cell M N i),
        1 / distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ))) ≤
      (2 * (N : ℝ) / (M : ℝ)) *
        (1 / (1 / 2 - (N : ℝ) / (M : ℝ)) +
          Real.log |(((N : ℝ) - 1) /
            (2 * (1 / 2 - (N : ℝ) / (M : ℝ)) + 1))|)

/-- The proposition that the reciprocal modular-distance sum outside the cells is at most 4N
log(N)/M, for odd N ≥ 13 and M ≥ 16N. -/
def lemma_A9Statement (M N k : ℕ) (hN : 13 ≤ N) (hM : 16 * N ≤ M) (hNodd : Odd N)
    (hk : k < M) : Prop :=
    (∑ i ∈ (Finset.range N).filter (fun i => k ∉ cell M N i),
        1 / distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ))) ≤
      4 * (N : ℝ) * Real.log (N : ℝ) / (M : ℝ)

/-- The proposition bounding the sum over `k` of squared absolute weighted sums of modular
distances outside cells by 22N log(N)²/M + 32N³/M², for a real vector of squared norm one
and the supplied size hypotheses. -/
def lemma_A10Statement (M N : ℕ) (hN : 13 ≤ N) (hM : 16 * N ≤ M) (hNodd : Odd N)
    (x : Fin N → ℝ) (hx : ∑ i : Fin N, x i ^ 2 = 1) : Prop :=
    (∑ k : Fin M, |∑ i : Fin N,
        if k.val ∈ cell M N i.val then 0 else
          x i * distMod (M : ℝ) ((k.val : ℝ) - (M : ℝ) / (N : ℝ) * (i.val : ℝ))| ^ 2)
      ≤ 22 * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (M : ℝ) +
          32 * (N : ℝ) ^ 3 / (M : ℝ) ^ 2

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
