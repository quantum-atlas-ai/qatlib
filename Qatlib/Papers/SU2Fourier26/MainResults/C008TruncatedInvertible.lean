/-
Copyright (c) 2026 Qatlib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qatlib Contributors
-/

import Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup.SourceCoefficientOps
import Qatlib.Papers.SU2Fourier26.MainResults.C005WienerLemma
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Lemma 4: invertibility of the truncated operator `Pₙ C Pₙ` (c008)

Fixed source: arXiv:2603.02021v1 (2026-03-02), Lemma 4, p.9.

If `‖P_{>n}(b/a*)‖_{A_w} < 1/2`, then `Pₙ C Pₙ` is invertible on `Pₙ Y_w` and
`‖(Pₙ C Pₙ)⁻¹‖ ≤ (‖a‖_{A_w} + 2‖1/a‖_{A_w})(‖a‖_{A_w} + ‖b‖_{A_w})²`.

The paper's proof (pp.9–11) splits the operator as `T₁ + T₂`, where `T₁` is an
explicit invertible operator on `P₋ A_w ⊕ P_{>n} A_w` (with the diagonal part
`diag(a, a*)`) and `T₂` is the off-diagonal perturbation whose norm is controlled
by `‖P_{>n}(b/a*)‖_{A_w} < 1/2`.  The chain of estimates is

`‖(T₁ + T₂)⁻¹‖ ≤ ‖T₁⁻¹‖ / (1 - ‖T₁⁻¹ T₂‖) ≤ 2‖1/a‖_{A_w}`,

i.e. the operator version of the geometric/Neumann series `(1 - x)⁻¹ = ∑ x^n`.

Here we formalize the *abstract Neumann inversion* underlying this step, valid in
any normed ring with a summable geometric series: a unit `u` perturbed by `v`
with `‖u⁻¹ v‖ < 1` remains a unit.  The concrete operator `Pₙ C Pₙ`, the bound
`‖P_{>n}(b/a*)‖ < 1/2` and the resulting operator-norm constant for `Y_w` are
*not* formalized (no normed/complete structure is installed on `YCoeff`).

The full statement is recorded for reference:

```
theorem truncated_operator_invertible (W : StrongBeurlingWeight) (a b : CircleT → ℂ)
    (h : OuterSetup W a b) (n : ℤ)
    (hsmall : truncatedAWnorm W (fun x => b x / starFun a x) n < 1 / 2) :
    ∃ T : YCoeff → YCoeff, ... (inverse + norm bound)
```
-/

open scoped BigOperators Matrix
open Matrix MeasureTheory Filter Topology

set_option autoImplicit false

open Qatlib.Papers.SU2Fourier26.MainResults.SourceSetup

namespace Qatlib.Papers.SU2Fourier26.MainResults

noncomputable section

/-- Abstract Neumann inversion (the analytic core of arXiv:2603.02021v1,
Lemma 4, p.9): in a normed ring with summable geometric series, if `u` is a unit
and the normalized perturbation `u⁻¹ v` has norm `< 1`, then `u + v` is again a
unit.  This is the paper's `T₁ + T₂` invertibility, stated in the operator
algebra rather than for the specific `Pₙ C Pₙ`. -/
theorem neumann_add_isUnit {R : Type*} [NormedRing R] [HasSummableGeomSeries R]
    {u : Rˣ} {v : R} (h : ‖(↑u⁻¹ : R) * v‖ < 1) : IsUnit ((u : R) + v) := by
  have hu : IsUnit (1 - (-((↑u⁻¹ : R) * v))) := by
    apply isUnit_one_sub_of_norm_lt_one
    simpa using h
  have hmul : (↑u : R) * (1 - (-((↑u⁻¹ : R) * v))) = (↑u : R) + v := by
    rw [sub_neg_eq_add, mul_add, mul_one, ← mul_assoc, Units.mul_inv, one_mul]
  exact hmul ▸ (u.isUnit.mul hu)

/-- The geometric bound on the Neumann inverse behind Lemma 4: `‖u⁻¹ v‖ < 1`
implies `‖Ring.inverse (1 + u⁻¹ v)‖ ≤ (1 - ‖u⁻¹ v‖)⁻¹`.  This is the quantitative
`‖(T₁ + T₂)⁻¹‖ ≤ ‖T₁⁻¹‖ / (1 - ‖T₁⁻¹ T₂‖)` estimate of p.10, stated for the
scalar factor. -/
theorem neumann_geometric_bound {R : Type*} [NormedRing R] [NormMulClass R]
    [NormOneClass R] [HasSummableGeomSeries R] (s : R) (hs : ‖s‖ < 1) :
    ‖Ring.inverse (1 + s)‖ ≤ (1 - ‖s‖)⁻¹ := by
  have h : ‖-s‖ < 1 := by simpa using hs
  have hb := wiener_near_one_inverse_norm (-s) h
  simpa [sub_neg_eq_add] using hb

end

end Qatlib.Papers.SU2Fourier26.MainResults
