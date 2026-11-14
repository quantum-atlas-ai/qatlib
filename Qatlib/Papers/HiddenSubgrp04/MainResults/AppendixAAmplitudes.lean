/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Algebra.Group.Monoid
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Ring.Nat
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Analysis.Complex.Norm
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Finset.Filter
public import Mathlib.Data.Finset.Range
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Data.Nat.Cast.Defs
public import Mathlib.Data.Nat.Init
public import Mathlib.Tactic
public import Qatlib.Papers.HiddenSubgrp04.MainResults.Defs

@[expose] public section

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

set_option autoImplicit false

open scoped BigOperators

namespace Qatlib.Papers.HiddenSubgrp04.MainResults

noncomputable section

/-- The proposition bounding the norm of `Acoef` by √(M/(LN)) times 2/π times the reciprocal
modular distance, under positive size, index, and nonintegral phase-difference hypotheses. -/
def lemma_A7Statement (L M N i k : ℕ) (_hL : 0 < L) (_hM : 0 < M) (_hN : 0 < N)
    (_hi : i < N) (_hk : k < M)
    (_hnotint : ¬ ∃ z : ℤ, (k : ℝ) / (M : ℝ) - (i : ℝ) / (N : ℝ) = (z : ℝ)) : Prop :=
    ‖Acoef L M N i k‖ ≤
      Real.sqrt ((M : ℝ) / ((L : ℝ) * (N : ℝ))) * (2 / Real.pi) *
        (1 / distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ)))

/-- The proposition bounding the sum of reciprocal modular distances over indices whose cells
exclude `k` by the displayed logarithmic expression, for odd N > 2 and M > 2N. -/
def lemma_A8Statement (M N k : ℕ) (_hN : 2 < N) (_hM : 2 * N < M) (_hNodd : Odd N)
    (_hk : k < M) : Prop :=
    (∑ i ∈ (Finset.range N).filter (fun i => k ∉ cell M N i),
        1 / distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ))) ≤
      (2 * (N : ℝ) / (M : ℝ)) *
        (1 / (1 / 2 - (N : ℝ) / (M : ℝ)) +
          Real.log |(((N : ℝ) - 1) /
            (2 * (1 / 2 - (N : ℝ) / (M : ℝ)) + 1))|)

/-- The proposition that the reciprocal modular-distance sum outside the cells is at most 4N
log(N)/M, for odd N ≥ 13 and M ≥ 16N. -/
def lemma_A9Statement (M N k : ℕ) (_hN : 13 ≤ N) (_hM : 16 * N ≤ M) (_hNodd : Odd N)
    (_hk : k < M) : Prop :=
    (∑ i ∈ (Finset.range N).filter (fun i => k ∉ cell M N i),
        1 / distMod (M : ℝ) ((k : ℝ) - (M : ℝ) / (N : ℝ) * (i : ℝ))) ≤
      4 * (N : ℝ) * Real.log (N : ℝ) / (M : ℝ)

/-- The proposition bounding the sum over `k` of squared absolute weighted sums of modular
distances outside cells by 22N log(N)²/M + 32N³/M², for a real vector of squared norm one
and the supplied size hypotheses. -/
def lemma_A10Statement (M N : ℕ) (_hN : 13 ≤ N) (_hM : 16 * N ≤ M) (_hNodd : Odd N)
    (x : Fin N → ℝ) (_hx : ∑ i : Fin N, x i ^ 2 = 1) : Prop :=
    (∑ k : Fin M, |∑ i : Fin N,
        if k.val ∈ cell M N i.val then 0 else
          x i * distMod (M : ℝ) ((k.val : ℝ) - (M : ℝ) / (N : ℝ) * (i.val : ℝ))| ^ 2)
      ≤ 22 * (N : ℝ) * (Real.log (N : ℝ)) ^ 2 / (M : ℝ) +
          32 * (N : ℝ) ^ 3 / (M : ℝ) ^ 2

end

end Qatlib.Papers.HiddenSubgrp04.MainResults
