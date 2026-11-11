/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SpanProgRank11.MainResults.SourceModel

set_option backward.isDefEq.respectTransparency false

/-!
# SpanProgRank11 — Subroutine 16 (claim c007)

Belovs, *Span-program-based quantum algorithm for the rank problem*,
arXiv:1103.0842v1, Subroutine 16 in Sec. 5.3, p. 15 (proof p. 15–16).
-/

set_option autoImplicit false
noncomputable section

namespace Qatlib.Papers.SpanProgRank11.MainResults.Subroutine16

open Qatlib.Papers.SpanProgRank11.MainResults
open scoped BigOperators ENNReal

/-- The sparse row+column loading complexity of Subroutine 16:
`O(√(k ℓ (k+ℓ)) · log(m+n))` (p. 15). -/
def sparseRowColumnLoadingFactor (k l m n : ℕ) : ℝ :=
  Real.sqrt ((k : ℝ) * (l : ℝ) * ((k + l : ℕ) : ℝ)) * Real.log (((m + n : ℕ) : ℝ))

/-- The elementary radical identity behind Subroutine 16:
`√(k log(m+n)) · √(ℓ(k+ℓ) log(m+n)) = √(k ℓ (k+ℓ)) · log(m+n)`. -/
theorem sqrt_sparse_row_column_factor (k l m n : ℕ) (hk : 0 < k) (hl : 0 < l)
    (hmn : 1 < m + n) :
    Real.sqrt ((k : ℝ) * Real.log (((m + n : ℕ) : ℝ)))
        * Real.sqrt ((l : ℝ) * ((k + l : ℕ) : ℝ) * Real.log (((m + n : ℕ) : ℝ)))
      = sparseRowColumnLoadingFactor k l m n := by
  unfold sparseRowColumnLoadingFactor
  have hlogn : 0 ≤ Real.log (((m + n : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast le_of_lt hmn)
  have ha : 0 ≤ (k : ℝ) * Real.log (((m + n : ℕ) : ℝ)) :=
    mul_nonneg (by positivity) hlogn
  rw [← Real.sqrt_mul ha]
  have hprod : (k : ℝ) * Real.log (((m + n : ℕ) : ℝ))
        * ((l : ℝ) * ((k + l : ℕ) : ℝ) * Real.log (((m + n : ℕ) : ℝ)))
      = (Real.sqrt ((k : ℝ) * (l : ℝ) * ((k + l : ℕ) : ℝ))
          * Real.log (((m + n : ℕ) : ℝ))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [hprod]
  exact Real.sqrt_sq (by positivity)

/-- **Fixed arXiv:1103.0842v1, Subroutine 16 (Sec. 5.3, p. 15).**
Any high-level span program `𝒫` for `n × m` matrices can be implemented as an
actual span program with witness size at most
`O(√(k ℓ (k+ℓ)) · wsize(𝒫) · log(m+n))`, assuming at most `k` non-zero entries
per column, at most `ℓ` non-zero entries per row, and the column/row sparse
representations `(c_{i,j}, x_{i,j})` and `(d_{i,1},…,d_{i,ℓ})` are given.

Source proof (p. 15–16): `m` vector loads `Lⱼ` plus `km` demultiplexors `D_{i,j}`
plus `nℓ` multiplexors `M_{i,j}`.  Positive witness size `O(k ‖w‖² log(m+n))`;
negative witness size `O(ℓ(k+ℓ) ‖w'‖² log(m+n))`; the geometric mean is
`O(√(k ℓ (k+ℓ)) · wsize(𝒫) · log(m+n))`.

Here `w₁`, `w₀` are the source `wsize₁`, `wsize₀`; the two component bounds are
`k log(m+n) · w₁` and `ℓ(k+ℓ) log(m+n) · w₀`; the radical identity is
`sqrt_sparse_row_column_factor`. -/
theorem source_subroutine16 (k l m n : ℕ) (hk : 0 < k) (hl : 0 < l) (hmn : 1 < m + n)
    (w1 w0 : ℝ) (h1 : 0 ≤ w1) (h0 : 0 ≤ w0) :
    geometricWitnessSize ((k : ℝ) * Real.log (((m + n : ℕ) : ℝ)) * w1)
        ((l : ℝ) * ((k + l : ℕ) : ℝ) * Real.log (((m + n : ℕ) : ℝ)) * w0)
      ≤ sparseRowColumnLoadingFactor k l m n * geometricWitnessSize w1 w0 := by
  have hlogn : 0 ≤ Real.log (((m + n : ℕ) : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast le_of_lt hmn)
  have ha : 0 ≤ (k : ℝ) * Real.log (((m + n : ℕ) : ℝ)) :=
    mul_nonneg (by positivity) hlogn
  have hb : 0 ≤ (l : ℝ) * ((k + l : ℕ) : ℝ) * Real.log (((m + n : ℕ) : ℝ)) := by
    positivity
  have h := geometricWitnessSize_scale ((k : ℝ) * Real.log (((m + n : ℕ) : ℝ)))
    ((l : ℝ) * ((k + l : ℕ) : ℝ) * Real.log (((m + n : ℕ) : ℝ))) w1 w0 ha hb h1 h0
  rw [h, sqrt_sparse_row_column_factor k l m n hk hl hmn]

end Qatlib.Papers.SpanProgRank11.MainResults.Subroutine16
