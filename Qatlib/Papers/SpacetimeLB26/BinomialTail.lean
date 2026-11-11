/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.ProbabilityCore.SharpBinomial

/-!
# A native binomial Chernoff bound

This module packages the upper-tail estimate for `nativeTail` in the form needed for
[BhartiHaugTanggara2026]. `binomial_chernoff` combines the exponential binary-relative-entropy
bound with positivity of its rate when `0 < p < Δ < 1`.

## Main statements

* `binomial_chernoff`: For `0 < p < Δ < 1`, the native binomial upper tail is at most `exp (-N *
  binaryKL Δ p)`, and the binary relative entropy is positive.

## References

* [Bharti et al., 2026][BhartiHaugTanggara2026]
-/

set_option autoImplicit false
open scoped NNReal
namespace Qatlib.Papers.SpacetimeLB26.BinomialTail
open Qatlib.Foundations.ProbabilityCore.SharpBinomial

/-- For `0 < p < Δ < 1`, the native binomial upper tail is at most `exp (-N * binaryKL Δ p)`,
and the binary relative entropy is positive. See [BhartiHaugTanggara2026]. -/
theorem binomial_chernoff (N : ℕ) (p : ℝ≥0) (hp : 0 < p) (Δ : ℝ)
    (hpΔ : (p : ℝ) < Δ) (hΔ1 : Δ < 1) :
    nativeTail N p (by exact_mod_cast hpΔ.le.trans hΔ1.le) Δ ≤
      Real.exp (-(N : ℝ)*binaryKL Δ p) ∧ 0 < binaryKL Δ p :=
  native_chernoff N p hp Δ hpΔ hΔ1

end Qatlib.Papers.SpacetimeLB26.BinomialTail
