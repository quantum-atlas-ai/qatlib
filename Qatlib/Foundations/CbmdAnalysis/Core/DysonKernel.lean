/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Foundations.CbmdAnalysis.Core.KernelLCU
import Qatlib.Foundations.CbmdAnalysis.Core.DysonPiecewise

/-!
# Kernel truncation bounds for Dyson propagators

This module applies explicit kernel order, spacing, and cutoff choices to continuous and
piecewise Dyson propagators with Hermitian and positive semidefinite matrix fields. For an error
budget in `(0, 1]`, it bounds the difference between the auxiliary-corrected infinite integer
sample series and the finite integer sample sum. These estimates supply the quantitative series
truncation step for [WangEtAl2026].

## Main statements

* `dysonKernel_series_error_le`: the continuous-field corrected series differs from its finite
  sample sum by at most `δ`.
* `dysonPiecewiseKernel_series_error_le`: the same estimate holds for continuous pieces on a
  monotone time grid.

## References

* [Wang et al., 2026][WangEtAl2026]
-/

set_option warningAsError false

namespace Qatlib.Foundations.CbmdAnalysis.Core

set_option autoImplicit false
namespace CBMD
open MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder

/-- For continuous Hermitian `H`, continuous positive semidefinite `L`, `s ≤ t`, and `0 < δ ≤
1`, choosing kernel order, spacing, and cutoff from `δ / 2` and the integrated norm of `L`
bounds the difference between the auxiliary-corrected infinite Dyson sample series and
`integerLCUSum` by `δ`. -/
theorem dysonKernel_series_error_le {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℝ → Matrix I I ℂ) (hH : Continuous H) (hL : Continuous L)
    (hHherm : ∀ u, (H u).IsHermitian) (hLpos : ∀ u, (L u).PosSemidef)
    (s t : ℝ) (hst : s ≤ t) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let ρ := ∫ u in s..t, ‖L u‖
    let m := kernelOrder (δ / 2)
    let a := kernelSpacing ρ (δ / 2) m
    let K := kernelCutoff a (δ / 2)
    let U := dysonPropagator H L s t
    ‖((∑' k : ℤ, integerSample m a U k) - integerAuxiliaryCorrection m a U) -
      integerLCUSum m a K U‖ ≤ δ := by
  apply integerLCU_series_error_le _ hδ hδ1
  · intro x
    exact dysonPropagator_norm_le_lower H L hH hL hHherm hLpos s t hst x (by simp)
  · simpa using dysonPropagator_norm_le_upper H L hH hL hHherm hLpos s t hst
      (2 * Complex.I) (by norm_num)
  · intro r _
    simpa using dysonPropagator_norm_le_upper H L hH hL hHherm hLpos s t hst
      ((r : ℂ) + Complex.I) (by norm_num)

/-- For continuous Hermitian and positive semidefinite matrix pieces on a monotone time grid and
`0 < δ ≤ 1`, the kernel choices from `δ / 2` and `dysonPiecewiseBudget` bound the difference
between the auxiliary-corrected infinite sample series and its finite `integerLCUSum` by
`δ`. -/
theorem dysonPiecewiseKernel_series_error_le {I : Type} [Fintype I] [DecidableEq I]
    (H L : ℕ → ℝ → Matrix I I ℂ) (hH : ∀ j, Continuous (H j))
    (hL : ∀ j, Continuous (L j)) (hHherm : ∀ j u, (H j u).IsHermitian)
    (hLpos : ∀ j u, (L j u).PosSemidef) (τ : ℕ → ℝ) (hτ : Monotone τ) (n : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    let ρ := dysonPiecewiseBudget L τ n
    let m := kernelOrder (δ / 2)
    let a := kernelSpacing ρ (δ / 2) m
    let K := kernelCutoff a (δ / 2)
    let U := dysonPiecewise H L τ n
    ‖((∑' k : ℤ, integerSample m a U k) - integerAuxiliaryCorrection m a U) -
      integerLCUSum m a K U‖ ≤ δ := by
  apply integerLCU_series_error_le _ hδ hδ1
  · intro x
    simpa using dysonPiecewise_norm_le H L hH hL hHherm hLpos τ hτ n (x : ℂ)
  · simpa using dysonPiecewise_norm_le H L hH hL hHherm hLpos τ hτ n (2 * Complex.I)
  · intro r _
    simpa using dysonPiecewise_norm_le H L hH hL hHherm hLpos τ hτ n ((r : ℂ) + Complex.I)

end CBMD

end Qatlib.Foundations.CbmdAnalysis.Core
