/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Concepts.AmpTransform.NoiseEnvelope.ErrorExpectationMinimizedAtMinLStat

/-!
# Minimizer of the expected-noise envelope

`errorExpectationMinimizedAtMinL` proves that the stated square-root expression minimizes the
rational noise envelope over its open real domain. This is the algebraic minimization step used
in the expected-noise analysis of [Cornwell2014].

## Main statements

* `errorExpectationMinimizedAtMinL`: For M ≥ 2 and N > 0, the stated square-root value of MinL
  minimizes (L+M²)/((N−L−M)(L+M)) over −M < L < N−M; see [Cornwell2014].

## References

* [Cornwell, 2014][Cornwell2014]
-/

set_option autoImplicit false

namespace Qatlib.Concepts.AmpTransform.NoiseEnvelope

/-- For M ≥ 2 and N > 0, the stated square-root value of MinL minimizes (L+M²)/((N−L−M)(L+M))
over −M < L < N−M; see [Cornwell2014]. -/
theorem errorExpectationMinimizedAtMinL : ErrorExpectationMinimizedAtMinL := by
  intro M N hM hN
  let m : ℝ := M
  let n : ℝ := N
  let A : ℝ := m * (m - 1)
  let s : ℝ := Real.sqrt (A * (A + n))
  let t : ℝ := -m ^ 2 + s
  have hm : 2 ≤ m := by change 2 ≤ (M : ℝ); exact_mod_cast hM
  have hn : 0 < n := by change 0 < (N : ℝ); exact_mod_cast hN
  have hA : 0 < A := mul_pos (by linarith) (by linarith)
  have hAn : 0 < A + n := add_pos hA hn
  have hdisc : 0 < A * (A + n) := mul_pos hA hAn
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hsq : s ^ 2 = A * (A + n) := Real.sq_sqrt hdisc.le
  have hlo : A < s := (Real.lt_sqrt hA.le).mpr (by nlinarith [mul_pos hA hn])
  have hhi : s < A + n := (Real.sqrt_lt hdisc.le hAn.le).mpr
    (by nlinarith [mul_pos hAn hn])
  have htm : 0 < t + m := by dsimp [t, A] at *; nlinarith
  have hnt : 0 < n - t - m := by dsimp [t, A] at *; nlinarith
  have hdt : 0 < (n - t - m) * (t + m) := mul_pos hnt htm
  dsimp only
  intro L hLlo hLhi
  change (t + m ^ 2) / ((n - t - m) * (t + m)) ≤
    (L + m ^ 2) / ((n - L - m) * (L + m))
  have hdL : 0 < (n - L - m) * (L + m) :=
    mul_pos (by change L < n - m at hLhi; linarith)
      (by change -m < L at hLlo; linarith)
  apply (div_le_div_iff₀ hdt hdL).mpr
  have hid : (L + m ^ 2) * ((n - t - m) * (t + m)) -
      (t + m ^ 2) * ((n - L - m) * (L + m)) = s * (L - t) ^ 2 := by
    calc
      _ = s * (L - t) ^ 2 + (L - t) * (s ^ 2 - A * (A + n)) := by
        dsimp [t, A]
        ring
      _ = _ := by rw [hsq]; ring
  have hnonneg : 0 ≤ s * (L - t) ^ 2 := mul_nonneg hs (sq_nonneg _)
  linarith

end Qatlib.Concepts.AmpTransform.NoiseEnvelope
