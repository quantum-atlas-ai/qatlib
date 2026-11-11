/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceBeurlingWeight
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lemma 1: Wiener's lemma for the weighted Wiener algebra `A_w` (c005)

Fixed source: arXiv:2603.02021v1 (2026-03-02), Lemma 1, p.8.

If `f ∈ A_w` and `0 ∉ f(𝕋)` then `1/f ∈ A_w`.

The paper proves this through Gelfand theory: the spectrum of `f` in `A_w` equals
its range `f(𝕋)`, because every bounded complex homomorphism `h` of `A_w` satisfies
`|h(e^{iθ})| = 1` by the growth condition iii of strong Beurling weights (p.8).
Wiener's lemma is then the statement that `A_w` is inverse-closed in the algebra
of continuous functions.

Here we formalize the *elementary Neumann-series case* of that inverse-closure:
if `f` is a unit perturbation of the identity, `f = 1 - x` with `‖x‖ < 1`, then
`f` is invertible with inverse given by the geometric series `∑ x^n`, and the
inverse norm is bounded by `(1 - ‖x‖)⁻¹`.  This is the convergence mechanism
underlying the paper's functional-calculus step, isolated in an arbitrary normed
ring.  The full Gelfand-spectrum identification for `A_w` is *not* formalized.

The full statement is recorded for reference:

```
theorem wiener_lemma (W : StrongBeurlingWeight) (f : CircleT → ℂ) (hf : MemAW W f)
    (h0 : ∀ x : CircleT, f x ≠ 0) : MemAW W (fun x => (f x)⁻¹)
```
-/

open scoped BigOperators
open MeasureTheory Filter Topology

set_option autoImplicit false

open Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

namespace Qatlib.Papers.SU2Fourier26.MainResults

noncomputable section

/-- Neumann-series case of Wiener's lemma (arXiv:2603.02021v1, Lemma 1, p.8):
in any normed ring with summable geometric series, a perturbation `1 - x` of the
identity with `‖x‖ < 1` is a unit.  This is the convergence core of the paper's
Gelfand-theoretic inverse-closure argument for `A_w`. -/
theorem wiener_near_one_isUnit {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    (x : R) (hx : ‖x‖ < 1) : IsUnit (1 - x) :=
  isUnit_one_sub_of_norm_lt_one hx

/-- Norm bound for the Neumann-series inverse: under `‖x‖ < 1`, the inverse of
`1 - x` is bounded by `(1 - ‖x‖)⁻¹` (the value of the geometric series
`∑ ‖x‖^n`).  This is the quantitative form of Lemma 1 used throughout the
paper's estimates. -/
theorem wiener_near_one_inverse_norm {R : Type*} [NormedRing R] [NormMulClass R]
    [NormOneClass R] [HasSummableGeomSeries R] (x : R) (hx : ‖x‖ < 1) :
    ‖Ring.inverse (1 - x)‖ ≤ (1 - ‖x‖)⁻¹ := by
  have hsum : Summable fun i : ℕ => ‖x ^ i‖ := by
    have hs := summable_geometric_of_norm_lt_one (R := ℝ) (x := ‖x‖) (by simpa using hx)
    exact hs.congr (fun i => (norm_pow x i).symm)
  have hgeom : ‖∑' i : ℕ, x ^ i‖ ≤ (1 - ‖x‖)⁻¹ := by
    calc ‖∑' i : ℕ, x ^ i‖ ≤ ∑' i : ℕ, ‖x ^ i‖ := norm_tsum_le_tsum_norm hsum
      _ = ∑' i : ℕ, ‖x‖ ^ i := by simp_rw [norm_pow]
      _ = (1 - ‖x‖)⁻¹ := tsum_geometric_of_norm_lt_one (by simpa using hx)
  rwa [← geom_series_eq_inverse x hx]

end

end Qatlib.Papers.SU2Fourier26.MainResults
