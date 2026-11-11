/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgRank11.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SpanProgRank11 — Subroutine 15 (claim c006)

Belovs, *Span-program-based quantum algorithm for the rank problem*,
arXiv:1103.0842v1, Subroutine 15 in Sec. 5.3, p. 14 (proof p. 14–15).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgRank11.MainResults.Subroutine15

open Qatlib.Papers.SpanProgRank11.MainResults
open scoped BigOperators ENNReal

/-- The sparse-column loading complexity of Subroutine 15:
`O(k √m log n)` (p. 14). -/
def sparseColumnLoadingFactor (k m n : ℕ) : ℝ :=
  (k : ℝ) * Real.sqrt (m : ℝ) * Real.log (n : ℝ)

/-- The elementary radical identity behind Subroutine 15:
`√(k log n) · √(k m log n) = k √m log n`, for `k, m > 0` and `n > 1`. -/
theorem sqrt_sparse_column_factor (k m n : ℕ) (hk : 0 < k) (hm : 0 < m) (hn : 1 < n) :
    Real.sqrt ((k : ℝ) * Real.log (n : ℝ))
        * Real.sqrt ((k : ℝ) * (m : ℝ) * Real.log (n : ℝ))
      = sparseColumnLoadingFactor k m n := by
  unfold sparseColumnLoadingFactor
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast le_of_lt hn)
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := by positivity
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := by positivity
  have ha : 0 ≤ (k : ℝ) * Real.log (n : ℝ) := mul_nonneg hk0 hlogn
  rw [← Real.sqrt_mul ha]
  have hprod : (k : ℝ) * Real.log (n : ℝ) * ((k : ℝ) * (m : ℝ) * Real.log (n : ℝ))
      = ((k : ℝ) * Real.sqrt (m : ℝ) * Real.log (n : ℝ)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hm0]
    ring
  rw [hprod]
  exact Real.sqrt_sq (by positivity)

/-- **Fixed arXiv:1103.0842v1, Subroutine 15 (Sec. 5.3, p. 14).**
Any high-level span program `𝒫` for `n × m` matrices can be implemented as an
actual span program with witness size at most
`O(k √m · wsize(𝒫) · log n)`, assuming each column of `A` has at most `k`
non-zero entries and the `j`-th column is represented by `(c_{i,j}, x_{i,j})`
for `i = 1,…,k`.

Source proof (p. 14–15): `m` vector-loading subroutines `Lⱼ` (cost `O(k wⱼ²)`)
plus `km` demultiplexors `D_{i,j}` (cost `O(wⱼ² log n)`).  Hence the positive
witness size is `O(k ‖w‖² log n)` and the negative witness size is
`O(km ‖w'‖² log n)`; the geometric mean is `O(k √m · wsize(𝒫) · log n)`.

Here `w₁`, `w₀` are the source `wsize₁`, `wsize₀`, and the two component bounds
`k log n · w₁`, `k m log n · w₀` are the composed witness sizes; the radical
identity `√(k log n · k m log n) = k √m log n` is
`sqrt_sparse_column_factor`. -/
theorem source_subroutine15 (k m n : ℕ) (hk : 0 < k) (hm : 0 < m) (hn : 1 < n)
    (w1 w0 : ℝ) (h1 : 0 ≤ w1) (h0 : 0 ≤ w0) :
    geometricWitnessSize ((k : ℝ) * Real.log (n : ℝ) * w1)
        ((k : ℝ) * (m : ℝ) * Real.log (n : ℝ) * w0)
      ≤ sparseColumnLoadingFactor k m n * geometricWitnessSize w1 w0 := by
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast le_of_lt hn)
  have ha : 0 ≤ (k : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg (by positivity) hlogn
  have hb : 0 ≤ (k : ℝ) * (m : ℝ) * Real.log (n : ℝ) := by positivity
  have h := geometricWitnessSize_scale ((k : ℝ) * Real.log (n : ℝ))
    ((k : ℝ) * (m : ℝ) * Real.log (n : ℝ)) w1 w0 ha hb h1 h0
  rw [h, sqrt_sparse_column_factor k m n hk hm hn]

end Qatlib.Papers.SpanProgRank11.MainResults.Subroutine15
